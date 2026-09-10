#!/usr/bin/env python3
"""
十四源行业新闻采集【并行优化版】
优化清单（新增第10项并行优化）：
1. 修复MIMEBase邮件参数错误，稳定发送
2. 标题+摘要合并单次翻译，减少一半API请求，缓解限流
3. 翻译渠道遇到429/请求超限自动休眠，降低QPS
4. 新增全局跨站点URL去重，报表无重复新闻
5. 修复brand_kr_name江波龙key拼写错误，解决KeyError崩溃
6. 腾讯翻译修复传参bug，各翻译入口增加随机延时防超限
7. 邮件附件兼容标准RFC编码，解决163 SMTP 500语法报错
8. 修复send_email缺少script_path参数，恢复脚本附件功能
9. 原有404修复、URL拼接、敏感过滤、Selenium兼容全部保留
10. 【新增】并行化处理：源站6并发、详情页15并发、翻译8并发，目标50分钟
11. 【修正】AI洞察单层3次重试，超时递进25s→40s→40s，不用极简降级文本填充
"""
import requests
import sys
from bs4 import BeautifulSoup
import re
import smtplib
import ssl
import json
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.mime.base import MIMEBase
from email import encoders
import base64
from datetime import datetime, timedelta
import time
import os
import random
from functools import lru_cache
import hashlib
from urllib.parse import urljoin
import signal, atexit
# ===== 改动1：新增并行导入 =====
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock
import threading

# ============================================================================
# SIGTERM/SIGINT 防护：收到信号时记录位置再退出，保证锁文件被清理
# ============================================================================
_LOCK_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".collector.lock")
_SCRIPT_STOPPING = False

def _cleanup_lock():
    """安全清理锁文件（仅清理自己写的 PID，防止误删其他实例）"""
    try:
        if os.path.exists(_LOCK_FILE):
            with open(_LOCK_FILE, "r") as f:
                stored = f.read().strip()
            if stored and int(stored) == os.getpid():
                os.unlink(_LOCK_FILE)
    except Exception:
        pass

def _sig_handler(signum, frame):
    global _SCRIPT_STOPPING
    if _SCRIPT_STOPPING:
        return
    _SCRIPT_STOPPING = True
    sig_name = signal.Signals(signum).name
    print(f"\n⚠️  收到 {sig_name} 信号，正在安全退出（报告未完成将在下次补发）...")
    _cleanup_lock()
    os._exit(0)

signal.signal(signal.SIGTERM, _sig_handler)
signal.signal(signal.SIGINT,  _sig_handler)
atexit.register(_cleanup_lock)
# 腾讯云翻译标准导入
from tencentcloud.common import credential
from tencentcloud.tmt.v20180321 import tmt_client
# Selenium 经济观察专用
from selenium import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.common.exceptions import TimeoutException, WebDriverException
# requests异常分类
from requests.exceptions import HTTPError, ConnectionError, Timeout
# 抑制 sumy numpy 除零警告（numpy 仅用于 sumy；云端无 numpy 时跳过）
import warnings
try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False
warnings.filterwarnings('ignore', category=RuntimeWarning, module='sumy')

# 翻译超时保护（秒）
TRANSLATE_TIMEOUT = 60

class TranslationTimeoutError(Exception):
    """翻译超时异常"""
    pass

def timeout_handler(signum, frame):
    raise TranslationTimeoutError(f"翻译超时（{TRANSLATE_TIMEOUT}s）")
# 智能摘要（textrank4zh 中文专用 + sumy 通用降级）
try:
    from textrank4zh import TextRank4Keyword, TextRank4Sentence
    HAS_TEXTRANK4ZH = True
except ImportError:
    HAS_TEXTRANK4ZH = False
try:
    from sumy.parsers.plaintext import PlaintextParser
    from sumy.nlp.tokenizers import Tokenizer
    from sumy.summarizers.lsa import LsaSummarizer
    from sumy.summarizers.lex_rank import LexRankSummarizer
    from sumy.nlp.stemmers import Stemmer
    from sumy.utils import get_stop_words
    HAS_SUMY = True
except ImportError:
    HAS_SUMY = False

# ==================== 全局配置 ====================
DEBUG_PRINT_ALL_HREF = False
REQUEST_RETRY_TIMES = 2
PAGE_DELAY_MIN = 0.4   # 列表页请求间隔（云端网速好，可缩短）
PAGE_DELAY_MAX = 1.2
TRANSLATE_DELAY_MIN = 0.15
TRANSLATE_DELAY_MAX = 0.5
LIMIT_SLEC = 8
# 无效链接黑名单前缀
INVALID_HREF_PREFIX = ("javascript:", "#", "mailto:", "tel:")
# 敏感词
SENSITIVE_WORDS = ["焦虑", "危险", "思想", "奶奶", "蜘蛛侠", "维修", "歌手", "下载", "午夜", "色情", "王者", "热浪", "警方", "纠纷", "取证", "好友", "拟退", "吐槽", "老登", "七旬", "脑梗", "化粪池", "华语", "电影", "顺风车", "索要", "诈骗", "立案", "暴雨", "红警", "足球协会", "男足", "无良", "医疗", "垃圾", "致癌", "偶遇", "为政者", "游客", "举报", "污染", "查获", "夹藏", "偷听", "独守", "深山", "520", "七夕", "电诈", "逮捕", "不雅"]
SENSITIVE_PATTERN = re.compile("|".join([re.escape(word) for word in SENSITIVE_WORDS]), re.IGNORECASE)

def has_sensitive_text(text: str) -> bool:
    return SENSITIVE_PATTERN.search(text) is not None

# 翻译配置【主备腾讯密钥 + 百度 + 其他免费渠道】
# 敏感密钥从环境变量读取，不再硬编码；本地可用 .env 文件，GitHub 用 Secrets
TENCENT_SECRET_ID_1 = os.environ.get("TENCENT_SECRET_ID_1", "")
TENCENT_SECRET_KEY_1 = os.environ.get("TENCENT_SECRET_KEY_1", "")
TENCENT_SECRET_ID_2 = os.environ.get("TENCENT_SECRET_ID_2", "")
TENCENT_SECRET_KEY_2 = os.environ.get("TENCENT_SECRET_KEY_2", "")
BAIDU_APP_ID = os.environ.get("BAIDU_APP_ID", "")
BAIDU_SECRET_KEY = os.environ.get("BAIDU_SECRET_KEY", "")
FROM_LANG = "zh"
TO_LANG = "ko"
BAIDU_TO_LANG = "kor"
TRANSLATE_ORDER = ["tencent1", "tencent2", "baidu", "youdao", "mymemory", "google"]
# 分割标记，用于合并标题摘要一次性翻译
SPLIT_TITLE_TAG = "###TITLE###"
SPLIT_SUMMARY_TAG = "###SUMMARY###"

# ==================== 智谱AI摘要配置 ====================
# 免费额度：每月100万token，注册即得 https://open.bigmodel.cn
ZHIPU_API_KEY = os.environ.get("ZHIPU_API_KEY", "")
AI_SUMMARY_ENABLED = True
AI_SUMMARY_MODEL = "glm-4-flash"
AI_SUMMARY_MAX_TOKENS = 512
AI_SUMMARY_TIMEOUT = 20
AI_SUMMARY_MIN_CHARS = 200
AI_SUMMARY_RATE_LIMIT = 1.0

AI_SUMMARY_PROMPT = """你是一位半导体/手机/汽车/科技行业分析师。请根据以下新闻内容，用中文写一段简洁专业的摘要（250-350字）。
要求：
1. 提取核心事实和关键数据（金额、份额、时间节点等）
2. 点明对相关品牌/行业/产业链的影响或意义
3. 语言精炼专业，不做无意义的铺垫和评价
4. 如果内容完全不涉及科技/手机/汽车/半导体/存储行业，返回"SKIP"

新闻标题：{title}
新闻正文：{body}"""

# ==================== 智谱AI市场洞察配置【最终版：单层3次重试】 ====================
AI_INSIGHT_ENABLED = True
AI_INSIGHT_MODEL = "glm-4-flash"
AI_INSIGHT_MAX_TOKENS = 320
AI_INSIGHT_TIMEOUT = 25           # 首次超时25s
AI_INSIGHT_RETRY_TIMEOUT = 40     # 重试超时40s（更长）
AI_INSIGHT_MAX_RETRIES = 2        # 失败后再试2次，共3次确定
AI_INSIGHT_MIN_CHARS = 150
AI_INSIGHT_TARGET_CHARS = 150
AI_INSIGHT_MAX_CHARS = 200
AI_INSIGHT_RATE_LIMIT = 1.0       # 调用间隔

AI_INSIGHT_PROMPT = """你是一位资深半导体/手机/汽车行业分析师，擅长从单一事件推断产业链与竞争格局变化。
请基于以下新闻，用中文写一段 130-160字 的"市场洞察"短文。
要求：
1. 视角：聚焦"对相关品牌、产业链上下游、竞品、市场格局的潜在影响"
2. 允许适度推断(基于行业常识)，但不要编造未提及的数据
3. 一段话直接输出，不要分点
4. 如果完全无法判断影响，返回"SKIP"

新闻标题：{title}
新闻正文：{body}
相关品牌：{brand}
"""

# 行业关键词
TARGET_BRANDS = {
    "OPPO": ["OPPO", "一加", "OnePlus", "Realme", "真我"],
    "vivo": ["vivo", "iQOO"],
    "荣耀": ["荣耀", "HONOR", "Honor", "honor"],
    "传音": ["传音", "Transsion", "TECNO", "Infinix", "itel"],
    "手机市场": ["智能手机", "手机", "手机出货", "手机发货量", "手机销量", "手机市场份额", "折叠屏", "平板", "PC", "平板电脑", "平板市场", "PC市场", "PC出货量"],
    "腾讯": ["腾讯", "Tencent", "微信"],
    "比亚迪": ["比亚迪", "BYD", "仰望", "腾势"],
    "小鹏": ["小鹏", "XPeng", "Xpeng", "XPENG"],
    "江波龙": ["江波龙", "Longsys", "FORESEE", "雷克沙", "Lexar"],
    "长鑫": ["长鑫", "CXMT"],
    "长存": ["长江存储", "YMTC", "长存"],
    "存储(DRAM,NAND)": ["DRAM", "NAND", "闪存", "SSD", "内存芯片", "美光", "三星"],
    "MTK SOC": ["联发科", "MTK", "天玑", "MediaTek"],
    "高通 SOC": ["高通", "Qualcomm"],
    "Robotics": ["人形机器人", "智元", "宇树"],
}
brand_order = [
    "OPPO", "vivo", "荣耀", "传音", "手机市场",
    "腾讯", "比亚迪", "小鹏", "江波龙", "长鑫", "长存",
    "存储(DRAM,NAND)", "MTK SOC", "高通 SOC", "Robotics"
]
brand_colors = {
    'OPPO': '#1BA784', 'vivo': '#415FFF', '荣耀': '#0AB2E6', '传音': '#FF6B35',
    '手机市场': '#9C27B0', '腾讯': '#0052D9', '比亚迪': '#E60012', '小鹏': '#FF7D00',
    '江波龙': '#009688', '长鑫': '#607D8B', '长存': '#795548',
    '存储(DRAM,NAND)': '#3F51B5', 'MTK SOC': '#CDDC39', '高通 SOC': '#F44336',
    'Robotics': '#8E44AD',
}
# 修复KeyError：江波龙key正确匹配
brand_kr_name = {
    'OPPO': 'OPPO', 'vivo': 'vivo', '荣耀': '아너(Honor)', '传音': '트랜션(Transsion)',
    '手机市场': '스마트폰 시장', '腾讯': '텐센트(Tencent)', '比亚迪': '비야디(BYD)', '小鹏': '샤오펑(XPeng)',
    '江波龙': '롱시스(Longsys)', '长鑫': '창신(CXMT)', '长存': '장강스토리지(YMTC)',
    '存储(DRAM,NAND)': '메모리(DRAM/NAND)', 'MTK SOC': '미디어텍(MTK)', '高通 SOC': '퀄컴(Qualcomm)',
    'Robotics': '로보틱스(Robotics)'
}

# 邮箱（敏感信息从环境变量读取）
SMTP_SERVER = os.environ.get("SMTP_SERVER", "smtp.163.com")
SMTP_PORT = int(os.environ.get("SMTP_PORT", "465"))
SENDER_EMAIL = os.environ.get("SENDER_EMAIL", "")
SENDER_PASSWORD = os.environ.get("SENDER_PASSWORD", "")
_recipients = os.environ.get("RECIPIENT_EMAILS", "")
RECIPIENT_EMAILS = [e.strip() for e in _recipients.split(",") if e.strip()] if _recipients else []

# 站点URL
ITHOME_URL = 'https://www.ithome.com/'
NETEASE_NEW_URL = 'https://news.163.com/'
CFM_NEWS_URL = "https://www.chinaflashmarket.com/newsflash/"
SINA_INDEX_URL = "https://www.sina.com.cn/"
SINA_NEWS_URL = "https://news.sina.com.cn/"
SINA_FINANCE_URL = "https://finance.sina.com.cn/"
DRAMX_URL = "https://www.dramx.com/Info/"
MYDRIVERS_INDEX = "https://news.mydrivers.com/"
MYDRIVERS_TECH = "https://news.mydrivers.com/technewsall.html/"
CNMO_URL = "https://m.cnmo.com/news/"
CNMO_PC_MAIN_URL = "https://www.cnmo.com/"  # PC首页
LAOYAOBA_URL = "https://www.laoyaoba.com/"
WSCN_NEWS_URL = "https://wallstreetcn.com/news/global/"
EEO_MAIN = "https://www.eeo.com.cn/"  # 注意：eeo.com 已非经济观察网（域名易主），正确域名是 eeo.com.cn
EEO_KUAIXUN = "https://www.eeo.com.cn/jg/kuaixun/"
# ZOL科技新闻 → 替换为三个海外可达的国内科技源
SOHU_TECH_URL = "https://it.sohu.com/"
IFENG_TECH_URL = "https://tech.ifeng.com/"
PCONLINE_URL = "https://news.pconline.com.cn/"
ZOL_NEWS_URL = "https://news.zol.com.cn/"
# UA池
HEADERS_POOL = [
    'Mozilla/5.0 (Windows NT 10.0; Win64) Chrome/120.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64) Edge/119.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 Chrome/118.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) Chrome/124.0.0.0 Safari/537.36'
]

# 保存路径（优先用户工作区，兜底系统临时目录）
# 保存路径：固定使用云端工作区，避免依赖 HOME（定时任务隔离会话 HOME=/tmp 会被清理导致报告丢失）
OUTPUT_DIR = os.environ.get("NEWS_OUTPUT_DIR", "/home/node/.openclaw/workspace/ithome_reports")
os.makedirs(OUTPUT_DIR, exist_ok=True)
print(f"📂 报告输出目录：{OUTPUT_DIR}")

# ==================== 公共工具 ====================
def get_random_header():
    ua = random.choice(HEADERS_POOL)
    return {
        'User-Agent': ua,
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8',
        'Accept-Language': 'zh-CN,zh;q=0.9,en;q=0.8',
        'Accept-Encoding': 'gzip, deflate',
        'Connection': 'keep-alive',
        'Upgrade-Insecure-Requests': '1',
        'Sec-Fetch-Site': 'same-origin',
        'Sec-Fetch-Mode': 'navigate',
        'Sec-Fetch-User': '?1',
        'Sec-Fetch-Dest': 'document',
    }

def safe_request(url, timeout=30):
    delay = random.uniform(PAGE_DELAY_MIN, PAGE_DELAY_MAX)
    time.sleep(delay)
    for retry in range(REQUEST_RETRY_TIMES + 1):
        try:
            resp = requests.get(url, headers=get_random_header(), timeout=timeout)
            resp.raise_for_status()
            # 编码智能检测：优先从HTML meta标签提取，确保中文不乱码
            detected = resp.apparent_encoding
            if detected and detected.lower() in ('utf-8', 'utf8', 'gbk', 'gb2312', 'gb18030', 'utf-8-sig'):
                resp.encoding = detected
            elif detected and detected.lower() in ('utf-8-sig',):  # utf-8-sig → utf-8
                resp.encoding = 'utf-8'
            else:
                # apparent_encoding 可能是 ISO-8859-1 / None（压缩内容）等误判，从HTML内容中找真实编码
                content_sample = resp.content[:4096]
                meta_match = re.search(rb'charset[="\s]+([a-zA-Z0-9\-_]+)', content_sample, re.IGNORECASE)
                if meta_match:
                    try:
                        charset = meta_match.group(1).decode('ascii').lower()
                        if charset in ('utf-8', 'utf8', 'gbk', 'gb2312', 'gb18030', 'big5'):
                            resp.encoding = charset
                        else:
                            resp.encoding = 'utf-8'
                    except:
                        resp.encoding = 'utf-8'
                else:
                    resp.encoding = 'utf-8'
            return resp
        except HTTPError as e:
            if 400 <= resp.status_code < 500:
                print(f"页面永久失效{resp.status_code}，跳过 {url}")
                return None
            print(f"服务器错误，第{retry+1}次重试 {url} err:{str(e)}")
            time.sleep(random.uniform(1, 2))
        except (ConnectionError, Timeout) as e:
            print(f"连接/超时，第{retry+1}次重试 {url} err:{str(e)}")
            time.sleep(random.uniform(1, 2))
        except Exception as e:
            print(f"未知请求异常 {url} err:{str(e)}")
            return None
    print(f"请求彻底失败 {url}")
    return None

# Selenium驱动
def get_selenium_driver():
    chrome_options = Options()
    chrome_options.add_argument("--headless=new")
    chrome_options.add_argument("--no-sandbox")
    chrome_options.add_argument("--disable-dev-shm-usage")
    chrome_options.add_argument("--disable-blink-features=AutomationControlled")
    chrome_options.add_experimental_option("excludeSwitches", ["enable-automation"])
    chrome_options.add_experimental_option("useAutomationExtension", False)
    chrome_options.add_argument("--disable-images")
    chrome_options.page_load_strategy = "eager"
    ua = random.choice(HEADERS_POOL)
    chrome_options.add_argument(f"user-agent={ua}")
    driver = webdriver.Chrome(options=chrome_options)
    driver.set_page_load_timeout(12)
    driver.implicitly_wait(3)
    driver.execute_script("Object.defineProperty(navigator, 'webdriver', {get: () => undefined})")
    return driver

# 翻译入口缓存 + 限流自动休眠 + 超时保护
@lru_cache(maxsize=2048)
def translate_text(text: str) -> str:
    text = text.strip()
    if not text:
        return ""
    # 平台检测：Windows 不支持 SIGALRM，跳过信号超时保护（依赖各渠道 requests 内部 timeout）
    _has_sigalrm = hasattr(signal, 'SIGALRM')
    if _has_sigalrm:
        signal.signal(signal.SIGALRM, timeout_handler)
        signal.alarm(TRANSLATE_TIMEOUT)
    try:
        # 每次翻译随机小幅延时，压低瞬时QPS
        time.sleep(random.uniform(TRANSLATE_DELAY_MIN, TRANSLATE_DELAY_MAX))
        for channel in TRANSLATE_ORDER:
            try:
                if channel == "tencent1":
                    res = tencent_translate(q=text, secret_id=TENCENT_SECRET_ID_1, secret_key=TENCENT_SECRET_KEY_1)
                elif channel == "tencent2":
                    res = tencent_translate(q=text, secret_id=TENCENT_SECRET_ID_2, secret_key=TENCENT_SECRET_KEY_2)
                elif channel == "baidu":
                    res = baidu_translate_api(text)
                elif channel == "mymemory":
                    res = mymemory_translate(text)
                elif channel == "google":
                    res = google_free_translate(text)
                elif channel == "youdao":
                    res = youdao_free_translate(text)
                else:
                    continue
                if res and res.strip():
                    if _has_sigalrm:
                        signal.alarm(0)  # 取消超时
                    return res
            except TranslationTimeoutError:
                print(f"翻译超时（{TRANSLATE_TIMEOUT}s），跳过该条使用原文")
                if _has_sigalrm:
                    signal.alarm(0)
                return text
            except Exception as e:
                err_msg = str(e)
                # 识别限流错误，加长等待再切换渠道
                if "429" in err_msg or "RequestLimitExceeded" in err_msg:
                    print(f"渠道[{channel}]触发限流，等待{LIMIT_SLEC}秒切换")
                    time.sleep(LIMIT_SLEC)
                print(f"翻译渠道[{channel}]异常，切换下一个 | {err_msg[:120]}")
                continue
        print("全部翻译接口失效，使用原文中文")
        if _has_sigalrm:
            signal.alarm(0)
        return text
    except TranslationTimeoutError:
        print(f"翻译整体超时（{TRANSLATE_TIMEOUT}s），使用原文")
        if _has_sigalrm:
            signal.alarm(0)
        return text
    except Exception as e:
        print(f"翻译未预期异常: {e}，使用原文")
        if _has_sigalrm:
            signal.alarm(0)
        return text

# ==================== 腾讯翻译【call_json兼容版，支持多组密钥】 ====================
def tencent_translate(q: str, secret_id: str = None, secret_key: str = None) -> str:
    """腾讯翻译，支持传入密钥参数，默认使用主密钥"""
    sid = secret_id or TENCENT_SECRET_ID_1
    skey = secret_key or TENCENT_SECRET_KEY_1
    try:
        cred = credential.Credential(sid, skey)
        client = tmt_client.TmtClient(cred, "ap-guangzhou")
        params = {
            "SourceText": q,
            "Source": FROM_LANG,
            "Target": TO_LANG,
            "ProjectId": 0
        }
        resp = client.call_json("TextTranslate", params)
        return resp["Response"]["TargetText"]
    except Exception as e:
        print(f"【腾讯翻译详细异常】{repr(e)}")
        raise Exception(f"腾讯翻译失败: {e}")

# 百度翻译API
def baidu_translate_api(q: str) -> str:
    salt = str(random.randint(32768, 65536))
    sign_raw = BAIDU_APP_ID + q + salt + BAIDU_SECRET_KEY
    sign = hashlib.md5(sign_raw.encode("utf-8")).hexdigest()
    params = {"q": q, "from": FROM_LANG, "to": BAIDU_TO_LANG, "appid": BAIDU_APP_ID, "salt": salt, "sign": sign}
    resp = requests.get("https://fanyi-api.baidu.com/api/trans/vip/translate", params=params, timeout=10)
    resp.raise_for_status()
    data = resp.json()
    if "error_code" in data:
        raise Exception(f"百度API错误码: {data['error_code']}")
    return data["trans_result"][0]["dst"]

def mymemory_translate(q: str) -> str:
    resp = requests.get("https://api.mymemory.translated.net/get", params={"q": q, "langpair": f"{FROM_LANG}|{TO_LANG}"}, timeout=10)
    resp.raise_for_status()
    data = resp.json()
    if data.get("responseStatus") != 200:
        raise Exception(data.get("responseDetails"))
    return data["responseData"]["translatedText"]

def google_free_translate(q: str) -> str:
    resp = requests.get("https://translate.googleapis.com/translate_a/single", params={"client": "gtx", "sl": FROM_LANG, "tl": TO_LANG, "dt": "t", "q": q}, timeout=10)
    resp.raise_for_status()
    data = resp.json()
    return "".join([item[0] for item in data[0]])

def youdao_free_translate(q: str) -> str:
    headers = {"User-Agent": random.choice(HEADERS_POOL), "Referer": "https://fanyi.youdao.com/"}
    salt = str(random.randint(100000, 999999))
    sign_raw = f"fanyideskweb{q}{salt}Y2FYu%TNSbMCxc6iV"
    sign = hashlib.md5(sign_raw.encode()).hexdigest()
    data = {"i": q, "from": FROM_LANG, "to": TO_LANG, "smartresult": "dict", "client": "fanyideskweb", "salt": salt, "sign": sign}
    resp = requests.post("https://fanyi.youdao.com/translate", data=data, headers=headers, timeout=10)
    resp.raise_for_status()
    data = resp.json()
    return "".join([i[0] for i in data["translateResult"][0]])

# ==================== 通用时间解析工具 ====================
# 各站点发布时间格式映射
TIME_FORMATS = [
    # ISO 8601格式：2026-08-11T11:55:00+08:00 或 2026-08-11T11:55:00Z
    (re.compile(r'(\d{4})-(\d{1,2})-(\d{1,2})T(\d{1,2}):(\d{2})(?::(\d{2}))?'), '%Y-%m-%d %H:%M:%S'),
    # 标准格式：2026-08-11 11:55:00
    (re.compile(r'(\d{4})[-/](\d{1,2})[-/](\d{1,2})\s+(\d{1,2}):(\d{2})(?::(\d{2}))?'), '%Y-%m-%d %H:%M:%S'),
    # 中文格式：2026年8月3日 14:30
    (re.compile(r'(\d{4})\s*年\s*(\d{1,2})\s*月\s*(\d{1,2})\s*日\s*(\d{1,2}):(\d{2})(?::(\d{2}))?'), '%Y年%m月%d日 %H:%M'),
    # 数字时间戳（10位秒级）
    (re.compile(r'\b(1[5-9]\d{8})\b'), 'timestamp'),
    # 简短格式：08-03 14:30
    (re.compile(r'(\d{2})-(\d{2})\s+(\d{1,2}):(\d{2})'), '%m-%d %H:%M'),
    # 纯月-日格式：08-10（CNMO首页非当天新闻）
    (re.compile(r'^(\d{2})-(\d{2})$'), '%m-%d'),
    # 纯时:分格式：13:10（CNMO首页当天新闻，无"今天"前缀）
    (re.compile(r'^(\d{1,2}):(\d{2})$'), 'today_time_only'),
    # "刚刚"（几分钟前发布）
    (re.compile(r'刚刚'), 'just_now'),
    # "X小时前" / "X分钟前"
    (re.compile(r'(\d+)\s*小时前'), 'hours_ago'),
    (re.compile(r'(\d+)\s*分钟前'), 'minutes_ago'),
    (re.compile(r'(\d+)\s*天前'), 'days_ago'),
    # 今天/昨天 + 时间（兼容"今日"和"今天"无时分的情况）
    (re.compile(r'(?:今天|今日)\s*(\d{1,2}):(\d{2})'), 'today'),
    (re.compile(r'昨天\s*(\d{1,2}):(\d{2})'), 'yesterday'),
    (re.compile(r'^(?:今天|今日)$'), 'today_no_time'),
]

def parse_time_from_text(text, base_time=None):
    """从文本中提取发布时间，返回 datetime 或 None"""
    if base_time is None:
        base_time = datetime.now()
    for pattern, fmt in TIME_FORMATS:
        m = pattern.search(text)
        if not m:
            continue
        try:
            if fmt == 'timestamp':
                return datetime.fromtimestamp(int(m.group(1)))
            elif fmt == 'hours_ago':
                return base_time - timedelta(hours=int(m.group(1)))
            elif fmt == 'minutes_ago':
                return base_time - timedelta(minutes=int(m.group(1)))
            elif fmt == 'days_ago':
                return base_time - timedelta(days=int(m.group(1)))
            elif fmt == 'today':
                h, mi = int(m.group(1)), int(m.group(2))
                return base_time.replace(hour=h, minute=mi, second=0, microsecond=0)
            elif fmt == 'yesterday':
                h, mi = int(m.group(1)), int(m.group(2))
                return (base_time - timedelta(days=1)).replace(hour=h, minute=mi, second=0, microsecond=0)
            elif fmt == 'today_no_time':
                # "今天"无具体时间 → 当天23:59:59（宽容到当天结束）
                return base_time.replace(hour=23, minute=59, second=59, microsecond=0)
            elif fmt == 'today_time_only':
                # 纯时:分格式（如"13:10"），无"今天"前缀 → 当天该时间
                h, mi = int(m.group(1)), int(m.group(2))
                return base_time.replace(hour=h, minute=mi, second=0, microsecond=0)
            elif fmt == 'just_now':
                # "刚刚" → 当前时间减5分钟
                return base_time - timedelta(minutes=5)
            elif fmt == '%m-%d':
                # 纯月-日格式（如"08-10"）→ 当年的该月日 23:59:59
                mon, day = int(m.group(1)), int(m.group(2))
                return base_time.replace(month=mon, day=day, hour=23, minute=59, second=59, microsecond=0)
            elif fmt == '%m-%d %H:%M':
                mon, day, h, mi = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4))
                return base_time.replace(month=mon, day=day, hour=h, minute=mi, second=0, microsecond=0)
            else:
                groups = m.groups()
                y, mo, d = int(groups[0]), int(groups[1]), int(groups[2])
                h = int(groups[3]) if len(groups) > 3 else 0
                mi = int(groups[4]) if len(groups) > 4 else 0
                s = int(groups[5]) if len(groups) > 5 and groups[5] else 0
                return datetime(y, mo, d, h, mi, s)
        except (ValueError, OSError):
            continue
    return None

def is_within_24h(dt, base_time=None):
    """判断时间是否在24小时内"""
    if dt is None:
        return False
    if base_time is None:
        base_time = datetime.now()
    return (base_time - dt).total_seconds() <= 86400

# ==================== 通用抓取函数（带时间过滤） ====================
def fetch_general_news(page_url, source_name, time_extractor=None):
    """通用新闻抓取，支持时间提取和时间过滤
    time_extractor: 可选函数(tag_element) -> datetime，用于从列表页提取时间
    """
    now = datetime.now()
    print(f'[{now.strftime("%Y-%m-%d %H:%M:%S")}] 开始抓取 {source_name}')
    news_items = []
    seen_urls = set()
    time_filtered = 0
    try:
        resp = safe_request(page_url)
        if not resp:
            print(f'{source_name} 页面访问失败')
            return []
        soup = BeautifulSoup(resp.text, 'html.parser')
        for a in soup.find_all('a', href=True):
            href = a['href'].strip()
            if href.startswith(INVALID_HREF_PREFIX):
                continue
            title = a.get_text(strip=True)
            if len(title) < 5 or not re.search(r'\d', href):
                continue
            full_url = urljoin(page_url, href)
            if full_url in seen_urls:
                continue
            seen_urls.add(full_url)

            # 尝试从列表页提取时间
            pub_time = None
            if time_extractor:
                try:
                    pub_time = time_extractor(a)
                except:
                    pass
            # 如果没有专用提取器，尝试从父元素文本中解析
            if pub_time is None:
                parent_text = a.parent.get_text(strip=True) if a.parent else title
                pub_time = parse_time_from_text(parent_text, now)

            # 时间过滤：如果列表页能提取到时间且超过24小时，直接跳过
            if pub_time is not None and not is_within_24h(pub_time, now):
                time_filtered += 1
                continue

            news_items.append({
                "title": title, "url": full_url, "source": source_name,
                "list_time": pub_time  # 列表页提取的初步时间
            })
    except Exception as e:
        print(f"{source_name} 抓取异常：{str(e)}")
    print(f'{source_name} 共抓取 {len(news_items)} 条（过滤超24h：{time_filtered}条）')
    return news_items

# IT之家抓取（requests，带时间提取）
# 深度优化 v2：修复标题/时间/URL三大问题
# 1. 标题：IT之家列表页 <a> 文字通过 CSS ::before content 生成，get_text() 为空，改为取 a['title'] 属性
# 2. 时间：时间在 <li> 的 data-time 属性或 span.date 中，不在 <a> 父元素可见文本里
# 3. URL：lapin.ithome.com 等子站 URL 缺协议前缀，自动补全
def fetch_ithome_news():
    source = "IT之家"
    print(f'[{datetime.now().strftime("%Y-%m-%d %H:%M:%S")}] 开始抓取 {source}')
    now = datetime.now()
    news_items = []
    seen_urls = set()
    time_filtered = 0
    # IT之家时间格式：2026/8/3 7:22:45（可能在 data-time 属性、span.date 或 ::before content）
    time_pattern = re.compile(r'(\d{4})/(\d{1,2})/(\d{1,2})\s+(\d{1,2}):(\d{2}):(\d{2})')
    try:
        resp = safe_request(ITHOME_URL)
        if not resp:
            print(f"{source} 页面访问失败")
            return []
        soup = BeautifulSoup(resp.text, 'html.parser')
        # 关键修复：遍历 #news > .fr#nnews 区域内的所有 <a> 标签
        news_root = soup.find(id='nnews')  # IT之家新闻主体区域
        if not news_root:
            news_root = soup.find(id='news')  # 兜底
        if not news_root:
            print(f"{source} 未找到 #news 或 #nnews 区域")
            return []
        for a in news_root.find_all('a', href=True):
            href = a['href'].strip()
            if href.startswith(INVALID_HREF_PREFIX):
                continue
            # 修复1：优先取 a['title']（CSS ::before 生成的文字不在 DOM text 里）
            title = a.get('title', '').strip()
            if not title:
                title = a.get_text(strip=True)
            if len(title) < 5:
                continue
            # 修复2：URL 协议补全（lapin.ithome.com 等相对 URL）
            full_url = urljoin(ITHOME_URL, href)
            if full_url.startswith('://'):  # 缺少协议
                full_url = 'https:' + full_url
            # 过滤：只保留 ithome.com 域名的文章链接，排除软件/APP下载等子页
            if 'ithome.com' not in full_url and not full_url.startswith('https:'):
                continue
            if full_url in seen_urls:
                continue
            seen_urls.add(full_url)
            # 修复3：时间从 <a> 的直接父 <li> 的 data-time 属性中提取
            pub_time = None
            li_parent = a.parent
            if li_parent and li_parent.name == 'li':
                # 方案A：data-time 属性
                dt_val = li_parent.get('data-time', '')
                if dt_val:
                    try:
                        pub_time = datetime.strptime(dt_val, '%Y/%m/%d %H:%M:%S')
                    except:
                        pass
                # 方案B：data-id 隐含时间序列（兜底）
                if pub_time is None:
                    dt_val2 = li_parent.get('data-id', '')
                    # 方案C：找同级或附近的 span.date / span.time
            # 方案B：找 <a> 同级或父级内的 span.date / span.time
            if pub_time is None:
                for selector in [
                    a.find_next_sibling('span', class_=re.compile('date|time|time-show', re.I)),
                    (li_parent.find('span', class_=re.compile('date|time', re.I)) if li_parent else None),
                    a.find('span', class_=re.compile('date|time', re.I)),
                ]:
                    if selector:
                        tm = time_pattern.search(selector.get_text(strip=True))
                        if tm:
                            try:
                                pub_time = datetime(int(tm.group(1)), int(tm.group(2)), int(tm.group(3)),
                                                  int(tm.group(4)), int(tm.group(5)), int(tm.group(6)))
                                break
                            except:
                                pass
            # 方案C：直接搜父元素文本中的时间（兼容部分特殊结构）
            if pub_time is None and li_parent:
                tm = time_pattern.search(li_parent.get_text(strip=True))
                if tm:
                    try:
                        pub_time = datetime(int(tm.group(1)), int(tm.group(2)), int(tm.group(3)),
                                          int(tm.group(4)), int(tm.group(5)), int(tm.group(6)))
                    except:
                        pass
            # 如果列表页取不到时间，在详情页二次确认时不跳过（时间过滤延后到详情页）
            if pub_time is not None and not is_within_24h(pub_time, now):
                time_filtered += 1
                continue
            news_items.append({"title": title, "url": full_url, "source": source, "list_time": pub_time})
    except Exception as e:
        print(f"{source} 抓取异常：{str(e)}")
    print(f'{source} 共抓取 {len(news_items)} 条（过滤超24h：{time_filtered}条）')
    return news_items

# 网易新闻时间提取器：从 <a> 父元素中提取
def _extract_netease_time(tag):
    parent = tag.parent
    if parent:
        text = parent.get_text(strip=True)
        return parse_time_from_text(text)
    return None

# CFM闪存市场时间提取器
def _extract_cfm_time(tag):
    parent = tag.parent
    if parent:
        text = parent.get_text(strip=True)
        return parse_time_from_text(text)
    return None

# 新浪新闻时间提取器
def _extract_sina_time(tag):
    parent = tag.parent
    if parent:
        text = parent.get_text(strip=True)
        return parse_time_from_text(text)
    return None

# 新浪财经时间提取器（URL含日期，优先从URL提取）
def _extract_sina_finance_time(tag):
    href = tag.get('href', '') if hasattr(tag, 'get') else ''
    m = re.search(r'(\d{4})-(\d{2})-(\d{2})', href)
    if m:
        try:
            return datetime(int(m.group(1)), int(m.group(2)), int(m.group(3)))
        except ValueError:
            pass
    parent = tag.parent
    if parent:
        return parse_time_from_text(parent.get_text(strip=True))
    return None

# DRAMX时间提取器
def _extract_dramx_time(tag):
    parent = tag.parent
    if parent:
        text = parent.get_text(strip=True)
        return parse_time_from_text(text)
    return None

# 驱动之家时间提取器
def _extract_mydrivers_time(tag):
    parent = tag.parent
    if parent:
        text = parent.get_text(strip=True)
        return parse_time_from_text(text)
    return None

# CNMO时间提取器
def _extract_cnmo_time(tag):
    parent = tag.parent
    if parent:
        text = parent.get_text(strip=True)
        return parse_time_from_text(text)
    return None

# 爱集微时间提取器
def _extract_laoyaoba_time(tag):
    parent = tag.parent
    if parent:
        text = parent.get_text(strip=True)
        return parse_time_from_text(text)
    return None

# ZOL时间提取器
def _extract_zol_time(tag):
    parent = tag.parent
    if parent:
        text = parent.get_text(strip=True)
        return parse_time_from_text(text)
    return None

# 各站点入口（均带时间提取）
def fetch_netease_news(): return fetch_general_news(NETEASE_NEW_URL, "网易新闻", _extract_netease_time)
# CFM闪存市场（列表页无独立标题：<a><p>整段正文</p></a>，标题从正文首句提取）
_CFM_LEAD_PREFIXES = ["据媒体报道", "业界消息指出", "据报道", "消息人士称", "知情人士透露", "媒体消息称", "外媒报道称", "供应链消息称"]

def _extract_cfm_title(body_text):
    """从 CFM 快讯正文提取标题：取首句并清理引语前缀，保持完整不截断"""
    text = (body_text or '').strip()
    if not text:
        return text
    first = re.split(r'[。！？!?]', text)[0].strip()
    if not first:
        first = text
    for pfx in _CFM_LEAD_PREFIXES:
        if first.startswith(pfx):
            first = first[len(pfx):].lstrip('，,、；;：: ')
            break
    return first

def fetch_cfm_news():
    source = "CFM闪存市场"
    print(f'[{datetime.now().strftime("%Y-%m-%d %H:%M:%S")}] 开始抓取 {source}')
    news_items = []
    seen_urls = set()
    try:
        resp = safe_request(CFM_NEWS_URL)
        if not resp:
            print(f'{source} 页面访问失败')
            return []
        soup = BeautifulSoup(resp.text, 'html.parser')
        for a in soup.select('div.jx-news a[href*="/newsflash/"]'):
            href = a['href'].strip()
            body = a.get_text(strip=True)
            if len(body) < 20:
                continue
            full_url = urljoin(CFM_NEWS_URL, href)
            if full_url in seen_urls:
                continue
            seen_urls.add(full_url)
            news_items.append({
                "title": _extract_cfm_title(body),
                "url": full_url,
                "source": source,
                "list_time": None,  # 列表页无时间显示，交给详情页二次确认
            })
    except Exception as e:
        print(f"{source} 抓取异常：{str(e)}")
    print(f'{source} 共抓取 {len(news_items)} 条（列表页无时间，详情页确认）')
    return news_items
def fetch_sina_news():
    list1 = fetch_general_news(SINA_INDEX_URL, "新浪首页", _extract_sina_time)
    list2 = fetch_general_news(SINA_NEWS_URL, "新浪新闻频道", _extract_sina_time)
    all1 = list1 + list2
    uniq = []
    s = set()
    for i in all1:
        if i["url"] not in s:
            s.add(i["url"])
            uniq.append(i)
    print(f'新浪渠道合并共抓取 {len(uniq)} 条')
    return uniq
def fetch_sina_finance_news():
    """新浪财经频道采集"""
    return fetch_general_news(SINA_FINANCE_URL, "新浪财经", _extract_sina_finance_time)
def fetch_dramx_news(): return fetch_general_news(DRAMX_URL, "DRAMX闪存资讯", _extract_dramx_time)
def fetch_mydrivers_news():
    l1 = fetch_general_news(MYDRIVERS_INDEX, "驱动之家首页", _extract_mydrivers_time)
    l2 = fetch_general_news(MYDRIVERS_TECH, "驱动之家科技频道", _extract_mydrivers_time)
    all1 = l1 + l2
    uniq = []
    s = set()
    for i in all1:
        if i["url"] not in s:
            s.add(i["url"])
            uniq.append(i)
    print(f'驱动之家合并共抓取 {len(uniq)} 条')
    return uniq
def fetch_cnmo_news():
    """CNMO新闻抓取：PC首页 + 移动端
    PC首页（www.cnmo.com）为单页抓取（无分页），含大量当日新闻
    移动端（m.cnmo.com/news）作为补充源
    """
    now = datetime.now()
    cutoff = now - timedelta(hours=25)  # 宽容1小时
    seen_urls = set()
    all_items = []

    # ── PC首页抓取（单页，无分页） ──
    print(f'[{now.strftime("%Y-%m-%d %H:%M:%S")}] 开始抓取 CNMO手机资讯 (PC首页: {CNMO_PC_MAIN_URL})')
    try:
        resp = safe_request(CNMO_PC_MAIN_URL, timeout=20)
        if resp:
            soup = BeautifulSoup(resp.text, 'html.parser')
            pc_main_links = []
            for a in soup.find_all('a', href=True):
                href = a['href'].strip()
                # 匹配 /news/数字ID.html（支持协议相对URL和绝对URL）
                if not re.search(r'/news/\d{6,}\.html', href):
                    continue
                title = a.get('title') or a.get_text(strip=True)
                if len(title) < 8:
                    continue
                # 处理协议相对URL (//xxx.cnmo.com/...)
                if href.startswith('//'):
                    full_url = 'https:' + href
                elif href.startswith('http'):
                    full_url = href
                else:
                    full_url = urljoin(CNMO_PC_MAIN_URL, href)
                if full_url in seen_urls:
                    continue
                seen_urls.add(full_url)
                # PC首页时间在a标签的next_sibling文本节点中
                list_time = None
                if a.next_sibling and a.next_sibling.string:
                    time_text = a.next_sibling.string.strip()
                    list_time = parse_time_from_text(time_text, now)
                pc_main_links.append({
                    "title": title, "url": full_url,
                    "source": "CNMO手机资讯", "list_time": list_time
                })
            all_items.extend(pc_main_links)
            has_recent = any(
                item['list_time'] and item['list_time'] > cutoff
                for item in pc_main_links
            )
            print(f'  PC首页抓取 {len(pc_main_links)} 条，{"有" if has_recent else "无"}24h内新闻')
        else:
            print(f'  PC首页访问失败')
    except Exception as e:
        print(f'  PC首页异常：{str(e)[:60]}')

    # ── 移动端补充抓取 ──
    try:
        m_items = fetch_general_news(CNMO_URL, "CNMO手机资讯", _extract_cnmo_time)
        for item in m_items:
            if item['url'] not in seen_urls:
                seen_urls.add(item['url'])
                all_items.append(item)
    except Exception as e:
        print(f'  CNMO移动端异常：{str(e)[:60]}')

    print(f'CNMO渠道合并共抓取 {len(all_items)} 条')
    return all_items
def fetch_laoyaoba_news(): return fetch_general_news(LAOYAOBA_URL, "爱集微产业资讯", _extract_laoyaoba_time)
# 华尔街见闻（SPA站点，requests拿不到列表，改用官方JSON API）
def fetch_wallstreetcn_news():
    source = "华尔街见闻"
    print(f'[{datetime.now().strftime("%Y-%m-%d %H:%M:%S")}] 开始抓取 {source}')
    news_items = []
    seen_urls = set()
    time_filtered = 0
    now = datetime.now()
    api_urls = [
        "https://api-one.wallstcn.com/apiv1/content/information-flow?channel=global-channel&accept=article&limit=50",
        "https://api-one.wallstcn.com/apiv1/content/lives?channel=global-channel&limit=50",
    ]
    for api_url in api_urls:
        try:
            resp = safe_request(api_url, timeout=15)
            if not resp or resp.status_code != 200:
                print(f'{source} API 访问失败：{api_url[:60]}')
                continue
            data = resp.json()
            items = data.get('data', {}).get('items', []) if isinstance(data.get('data'), dict) else []
            for it in items:
                r = it.get('resource', {}) or {}
                title = (r.get('title') or '').strip()
                uri = (r.get('uri') or '').strip()
                if len(title) < 5 or not uri:
                    continue
                full_url = uri if uri.startswith('http') else urljoin("https://wallstreetcn.com", uri)
                if full_url in seen_urls:
                    continue
                seen_urls.add(full_url)
                pub_time = None
                ts = r.get('display_time')
                if ts:
                    try:
                        pub_time = datetime.fromtimestamp(int(ts))
                    except Exception:
                        pass
                if pub_time is not None and not is_within_24h(pub_time, now):
                    time_filtered += 1
                    continue
                news_items.append({"title": title, "url": full_url, "source": source, "list_time": pub_time})
        except Exception as e:
            print(f"{source} API 异常：{str(e)[:80]}")
    print(f'{source} 共抓取 {len(news_items)} 条（过滤超24h：{time_filtered}条）')
    return news_items
def fetch_starmarket_news(): return fetch_general_news("https://www.chinastarmarket.cn/", "科创板日报")
def fetch_sohu_tech_news(): return fetch_general_news(SOHU_TECH_URL, "搜狐科技")
def fetch_ifeng_tech_news(): return fetch_general_news(IFENG_TECH_URL, "凤凰科技")
def fetch_pconline_news(): return fetch_general_news(PCONLINE_URL, "太平洋科技网")
def fetch_zol_news(): return fetch_general_news(ZOL_NEWS_URL, "ZOL科技新闻", _extract_zol_time)
# 经济观察网（requests，URL格式 /2026/0806/988512.shtml，日期在URL路径中）
def fetch_eeo_news():
    print(f'[{datetime.now().strftime("%Y-%m-%d %H:%M:%S")}] 抓取经济观察网')
    page_list = [EEO_MAIN, EEO_KUAIXUN]
    all_links = []
    skip = ['video', 'pic', 'ad']
    # 实际URL格式：https://www.eeo.com.cn/2026/0806/988512.shtml（年份/月日/文章ID）
    pat_eeo = re.compile(r'/\d{4}/\d{4}/\d+\.shtml')
    now = datetime.now()
    for page in page_list:
        try:
            resp = safe_request(page)
            if not resp:
                continue
            soup = BeautifulSoup(resp.text, 'html.parser')
            for a in soup.find_all('a', href=True):
                href = a['href'].strip()
                if href.startswith(INVALID_HREF_PREFIX):
                    continue
                title = a.get_text(strip=True)
                if len(title) < 5 or not pat_eeo.search(href) or any(k in title.lower() for k in skip):
                    continue
                full_url = urljoin(page, href)
                # 从URL提取发布日期（如 /2026/0806/ → 2026-08-06）做粗过滤：超2天直接丢弃，其余交给详情页确认
                pub_time = None
                m = re.search(r'/(\d{4})/(\d{4})/', href)
                if m:
                    try:
                        y, mmdd = int(m.group(1)), m.group(2)
                        d = datetime(y, int(mmdd[:2]), int(mmdd[2:4]))
                        if d > now:
                            d = datetime(y - 1, int(mmdd[:2]), int(mmdd[2:4]))
                        pub_time = d
                    except Exception:
                        pub_time = None
                if pub_time is not None and pub_time < now - timedelta(days=2):
                    continue  # URL日期太旧，直接丢弃
                all_links.append({"title": title, "url": full_url, "source": "经济观察网", "list_time": None})
        except Exception as e:
            print(f"经济观察网 {page} 抓取异常：{str(e)}")
    # 去重：同一URL（快讯页标题+摘要两个a指向同URL）保留标题更短的
    uniq = {}
    for i in all_links:
        if i["url"] not in uniq or len(i["title"]) < len(uniq[i["url"]]["title"]):
            uniq[i["url"]] = i
    print(f'经济观察网共抓取 {len(uniq)} 条')
    return list(uniq.values())

# ==================== 详情页深度抓取 ====================

# 各站点正文容器选择器（按优先级排列）
SITE_CONTENT_SELECTORS = {
    "IT之家": [
        ('div', {'id': 'paragraph'}),
    ],
    "网易新闻": [
        ('div', {'class': re.compile(r'post_(body|content|article|text)', re.I)}),
        ('div', {'id': re.compile(r'(article|content|endText|post_content|news_content)', re.I)}),
        ('div', {'class': re.compile(r'(article|content|text|body)', re.I)}),
        ('article', {}),
    ],
    "驱动之家首页": [
        ('div', {'class': re.compile(r'(article|content|news_content|detail|news_body|news_text|art_context)', re.I)}),
        ('div', {'id': re.compile(r'(article|content|main|news|art_context)', re.I)}),
    ],
    "驱动之家科技频道": [
        ('div', {'class': re.compile(r'(article|content|news_content|detail|news_body|news_text|art_context)', re.I)}),
        ('div', {'id': re.compile(r'(article|content|main|news|art_context)', re.I)}),
    ],
    "ZOL科技新闻": [
        ('div', {'class': re.compile(r'(article|content|main|detail|news-text|news_content)', re.I)}),
        ('div', {'id': re.compile(r'(article|content|main|news)', re.I)}),
        ('article', {}),
    ],
    "搜狐科技": [
        ('div', {'class': re.compile(r'(article|content|main|text|news_text|article-info)', re.I)}),
        ('div', {'id': re.compile(r'(article|content|main|text)', re.I)}),
        ('article', {}),
    ],
    "凤凰科技": [
        ('div', {'class': re.compile(r'(article|content|main|news_content|news-text|text)', re.I)}),
        ('div', {'id': re.compile(r'(article|content|main|news)', re.I)}),
        ('article', {}),
    ],
    "太平洋科技网": [
        ('div', {'class': re.compile(r'(article|content|main|news_content|news-text|detail)', re.I)}),
        ('div', {'id': re.compile(r'(article|content|main|news)', re.I)}),
        ('article', {}),
    ],
    "新浪首页": [
        ('div', {'class': re.compile(r'(article|content|main-body|artical)', re.I)}),
        ('div', {'id': re.compile(r'(article|artibody|content)', re.I)}),
        ('article', {}),
    ],
    "新浪新闻频道": [
        ('div', {'class': re.compile(r'(article|content|main-body|artical)', re.I)}),
        ('div', {'id': re.compile(r'(article|artibody|content)', re.I)}),
        ('article', {}),
    ],
    "新浪财经": [
        ('div', {'id': 'artibody'}),
        ('div', {'class': re.compile(r'(article|content|main-body)', re.I)}),
        ('article', {}),
    ],
    "CFM闪存市场": [
        ('div', {'class': re.compile(r'(content|article|detail|news-detail|news-content|news_body|text)', re.I)}),
        ('div', {'id': re.compile(r'(content|article|detail|text)', re.I)}),
        ('article', {}),
    ],
    "CNMO手机资讯": [
        ('div', {'class': re.compile(r'(article|content|detail|news-text|news-content|news-detail)', re.I)}),
        ('div', {'id': re.compile(r'(article|content|detail)', re.I)}),
        ('article', {}),
    ],
    "爱集微产业资讯": [
        ('div', {'class': re.compile(r'(article|content|detail|news-body)', re.I)}),
        ('article', {}),
    ],
    "DRAMX闪存资讯": [
        ('div', {'class': re.compile(r'(content|article|detail)', re.I)}),
    ],
    "科创板日报": [
        ('div', {'class': re.compile(r'(article|content|detail)', re.I)}),
        ('article', {}),
    ],
    "华尔街见闻": [
        ('div', {'class': re.compile(r'(article|content|detail|rich-text)', re.I)}),
        ('article', {}),
    ],
    "经济观察网": [
        ('div', {'class': re.compile(r'(article|content|detail)', re.I)}),
        ('article', {}),
    ],
}

def _extract_clean_text(container, min_chars=80):
    """从 BeautifulSoup 容器中提取干净的正文文本，返回 (文本, 是否有效)"""
    if container is None:
        return "", False
    try:
        # 深度克隆，避免修改原 soup
        clone = BeautifulSoup(str(container), 'html.parser')
        # 移除明确不需要的元素（但不删 div/span/p 等正文标签！）
        for tag in clone.find_all(['script', 'style', 'noscript', 'iframe', 'form', 'input', 'button']):
            tag.decompose()
        # 移除常见的导航/侧边栏/广告类元素
        noise_classes = [
            'nav', 'navigation', 'sidebar', 'aside', 'footer', 'header', 'comment',
            'share', 'recommend', 'related', 'ad', 'advertisement', 'hot', 'popular',
            'breadcrumb', 'toolbar', 'copyright', 'pagination'
        ]
        for tag_name in ['div', 'section', 'ul', 'nav', 'aside', 'header', 'footer']:
            for tag in clone.find_all(tag_name):
                try:
                    tag_classes = tag.get('class')
                    tag_class_str = ' '.join(tag_classes).lower() if tag_classes else ''
                    tag_id_str = (tag.get('id') or '').lower()
                    combined = tag_class_str + ' ' + tag_id_str
                    if any(nc in combined for nc in noise_classes):
                        tag.decompose()
                except Exception:
                    pass

        text = clone.get_text(separator='\n', strip=True)
        # 清理空行和多余空白
        lines = [l.strip() for l in text.split('\n') if l.strip()]
        # 过滤明显不是正文的行
        clean_lines = []
        for line in lines:
            if len(line) < 5:
                continue
            if line in ('首页', '上一页', '下一页', '返回顶部', '更多', '展开全文', '阅读全文'):
                continue
            clean_lines.append(line)
        text = ' '.join(clean_lines)
        text = re.sub(r'\s+', ' ', text).strip()
        return text, len(text) >= min_chars
    except Exception:
        return "", False

# ==================== AI 智能摘要加工 ====================
def _ai_enhance_summary(title, body_text, source=""):
    """调用智谱GLM-4-Flash对新闻内容进行AI分析加工，生成行业分析级摘要。"""
    if not ZHIPU_API_KEY or not AI_SUMMARY_ENABLED:
        return ""
    if not body_text or len(body_text) < AI_SUMMARY_MIN_CHARS:
        return ""
    if not title:
        title = body_text[:100].replace('\n', ' ').strip()
    body = body_text[:3000] if len(body_text) > 3000 else body_text
    prompt = AI_SUMMARY_PROMPT.format(title=title, body=body)
    url = "https://open.bigmodel.cn/api/paas/v4/chat/completions"
    headers = {"Authorization": f"Bearer {ZHIPU_API_KEY}", "Content-Type": "application/json"}
    data = {"model": AI_SUMMARY_MODEL, "messages": [{"role": "user", "content": prompt}],
            "max_tokens": AI_SUMMARY_MAX_TOKENS, "temperature": 0.3}
    try:
        resp = requests.post(url, headers=headers, json=data, timeout=AI_SUMMARY_TIMEOUT)
        if resp.status_code != 200:
            print(f"  🤖 AI摘要API返回{resp.status_code}：{resp.text[:80]}")
            return ""
        summary = resp.json()["choices"][0]["message"]["content"].strip()
        if not summary or summary.upper() == "SKIP" or len(summary) < 20:
            return ""
        for prefix in ["摘要：", "摘要:", "总结：", "总结:", "核心要点："]:
            if summary.startswith(prefix):
                summary = summary[len(prefix):].strip()
        print(f"  🤖 AI摘要生成成功（{len(summary)}字）")
        return summary
    except requests.exceptions.Timeout:
        print(f"  ⚠️ AI摘要超时，降级到抽取式摘要")
        return ""
    except Exception as e:
        print(f"  ⚠️ AI摘要异常：{str(e)[:80]}，降级到抽取式摘要")
        return ""


# ==================== AI 市场洞察【最终版：单层3次重试，无降级填充】 ====================

def _trim_insight(text: str) -> str:
    """把 AI 输出收紧到 AI_INSIGHT_MIN_CHARS..AI_INSIGHT_MAX_CHARS,优先在句末标点切"""
    text = (text or "").strip()
    if not text:
        return ""
    # 去除Markdown符号
    for ch in ["#", "*", "•", "·"]:
        text = text.replace(ch, "")
    # 收紧多余空白与换行
    text = re.sub(r"\s+", " ", text).strip()
    if len(text) <= AI_INSIGHT_MAX_CHARS:
        return text
    # 在 target 上下的句末标点处截断
    for sep in ["。", "！", "?", "?", "!", ".", ";", "；"]:
        idx = text.rfind(sep, AI_INSIGHT_MIN_CHARS - 20, AI_INSIGHT_MAX_CHARS + 30)
        if idx != -1:
            return text[: idx + 1].strip()
    # 兜底:在 AI_INSIGHT_MAX_CHARS 附近切
    return text[: AI_INSIGHT_MAX_CHARS].rstrip(" ,;:、,;") + "..."


def _ai_market_insight(title: str, body_text: str, brand: str = "") -> str:
    """
    【唯一重试层】调用智谱API生成市场洞察。
    共3次尝试：25s → 40s → 40s，递增超时。
    全部失败返回空字符串，绝不编造。
    """
    if not ZHIPU_API_KEY or not AI_INSIGHT_ENABLED:
        return ""
    if not body_text or len(body_text) < 80:
        return ""
    if not title:
        title = (body_text[:80] or "").replace("\n", " ").strip()
    
    body = body_text[:2200] if len(body_text) > 2200 else body_text
    prompt = AI_INSIGHT_PROMPT.format(title=title or "", body=body, brand=brand or "未指明")
    url = "https://open.bigmodel.cn/api/paas/v4/chat/completions"
    headers = {"Authorization": f"Bearer {ZHIPU_API_KEY}", "Content-Type": "application/json"}
    
    # 3次尝试：首次25s，重试40s、40s
    timeouts = [AI_INSIGHT_TIMEOUT] + [AI_INSIGHT_RETRY_TIMEOUT] * AI_INSIGHT_MAX_RETRIES
    
    for attempt, timeout in enumerate(timeouts, 1):
        try:
            if attempt > 1:
                wait = AI_INSIGHT_RATE_LIMIT + (attempt - 1)  # 2s, 3s
                print(f"  💡 AI洞察第{attempt}次尝试({timeout}s)，等待{wait}s...")
                time.sleep(wait)
            else:
                time.sleep(AI_INSIGHT_RATE_LIMIT)
            
            data = {
                "model": AI_INSIGHT_MODEL,
                "messages": [{"role": "user", "content": prompt}],
                "max_tokens": AI_INSIGHT_MAX_TOKENS,
                "temperature": 0.45,
            }
            resp = requests.post(url, headers=headers, json=data, timeout=timeout)
            
            if resp.status_code != 200:
                print(f"  💡 API返回{resp.status_code}，继续重试...")
                continue
            
            raw = resp.json()["choices"][0]["message"]["content"].strip()
            if not raw or raw.upper() == "SKIP":
                print(f"  💡 返回空/SKIP，继续重试...")
                continue
            
            # 清理前缀
            for pfx in ["市场洞察:", "市场洞察：", "洞察:", "洞察：", "📈 ", "💡 "]:
                if raw.startswith(pfx):
                    raw = raw[len(pfx):].strip()
            
            result = _trim_insight(raw)
            if len(result) >= 60:
                print(f"  ✅ AI洞察成功（第{attempt}次，{len(result)}字）")
                return result
            else:
                print(f"  💡 输出太短({len(result)}字)，继续重试...")
                continue
                
        except requests.exceptions.Timeout:
            print(f"  ⏱️ 超时({timeout}s)，继续重试...")
            continue
        except Exception as e:
            print(f"  ⚠️ 异常：{str(e)[:60]}，继续重试...")
            continue
    
    # 3次全失败
    print(f"  ❌ AI洞察3次全失败：{title[:40]}...")
    return ""


# 【已删除】_insight_fallback() —— 不再使用极简降级文本填充


def _generate_market_insight(title: str, body_text: str, brand: str = "") -> str:
    """
    【直通包装】单层调用，无额外重试，无降级填充。
    失败时返回空字符串，由调用方处理（留空）。
    """
    if not body_text or len(body_text) < 80:
        return ""
    return _ai_market_insight(title or "", body_text, brand or "")


def _trim_summary(text, target_len=280):
    """智能截取摘要，尽量在句子边界截断，目标 250-300 字"""
    if len(text) <= target_len + 30:
        return text
    # 尝试在 target_len 附近的句号处截断
    truncated = text[:target_len + 50]
    # 找最后一个句号、问号或感叹号
    for sep in ['。', '！', '？', '.', '!', '?']:
        idx = truncated.rfind(sep)
        if idx > target_len - 60 and idx < target_len + 50:
            return text[:idx + 1] + '...'
    # 退而求其次找空格
    idx = truncated.rfind(' ')
    if idx > target_len - 40:
        return text[:idx] + '...'
    return text[:target_len] + '...'


def _generate_base_summary(full_text, sentence_count=3, target_chars=280):
    """
    智能摘要生成（抽取式）：优先 textrank4zh，降级 sumy，最后回退截断。
    full_text: 完整正文（中文）
    sentence_count: 期望提取的句子数
    target_chars: 目标摘要字符数
    返回：中文摘要字符串
    """
    if not full_text or len(full_text) < 60:
        return _trim_summary(full_text, target_chars)

    # ── 方案一：textrank4zh 中文专用 ──
    if HAS_TEXTRANK4ZH:
        try:
            tr4s = TextRank4Sentence()
            tr4s.analyze(text=full_text, lower=True, source='no_stop_words')
            top_sentences = tr4s.get_key_sentences(num=sentence_count)
            if top_sentences:
                # 按原文顺序排列，保证可读性
                top_indices = sorted([s.index for s in top_sentences])
                ordered = []
                sentences = full_text.replace('！', '。').replace('？', '。').replace('?', '.').replace('!', '.').split('。')
                for idx in top_indices:
                    if idx < len(sentences) and sentences[idx].strip():
                        ordered.append(sentences[idx].strip())
                result = '。'.join(ordered) + '。'
                # 控制长度
                if len(result) > target_chars + 100:
                    result = _trim_summary(result, target_chars)
                if len(result) >= 40:
                    return result
        except Exception as e:
            pass  # 静默降级

    # ── 方案二：sumy LexRank（适合新闻）──
    if HAS_SUMY:
        try:
            parser = PlaintextParser.from_string(full_text, Tokenizer("chinese"))
            # LexRank 对新闻类文本效果更好
            summarizer = LexRankSummarizer(Stemmer("chinese"))
            summarizer.stop_words = get_stop_words("chinese")
            summary_sents = summarizer(parser.document, sentence_count)
            if summary_sents:
                result = ' '.join([str(s) for s in summary_sents])
                if len(result) > target_chars + 100:
                    result = _trim_summary(result, target_chars)
                if len(result) >= 40:
                    return result
        except Exception:
            # 降级 LSA
            try:
                parser = PlaintextParser.from_string(full_text, Tokenizer("chinese"))
                summarizer = LsaSummarizer(Stemmer("chinese"))
                summarizer.stop_words = get_stop_words("chinese")
                summary_sents = summarizer(parser.document, sentence_count)
                if summary_sents:
                    result = ' '.join([str(s) for s in summary_sents])
                    if len(result) > target_chars + 100:
                        result = _trim_summary(result, target_chars)
                    if len(result) >= 40:
                        return result
            except Exception:
                pass

    # ── 方案三：回退截断 ──
    return _trim_summary(full_text, target_chars)


def _generate_smart_summary(full_text, title="", source="", sentence_count=3, target_chars=280):
    """
    智能摘要生成（AI增强版）：
    优先调用智谱AI进行行业分析级摘要，失败则降级到抽取式摘要。
    """
    base_summary = _generate_base_summary(full_text, sentence_count, target_chars)
    if AI_SUMMARY_ENABLED and ZHIPU_API_KEY and len(full_text) >= AI_SUMMARY_MIN_CHARS:
        try:
            time.sleep(AI_SUMMARY_RATE_LIMIT)
            ai_summary = _ai_enhance_summary(title or "", full_text, source or "")
            if ai_summary and len(ai_summary) >= 30:
                return ai_summary
        except Exception:
            pass
    return base_summary


# ==================== 各站点专用详情解析 ====================

def fetch_ithome_detail(url):
    """IT之家详情页"""
    try:
        resp = safe_request(url)
        if not resp:
            return None, "【页面失效】"
        soup = BeautifulSoup(resp.text, 'html.parser')
        pub_time = None
        time_el = soup.find('span', id='pubtime_baidu')
        if time_el:
            try:
                pub_time = datetime.strptime(time_el.text.strip(), '%Y/%m/%d %H:%M:%S')
            except:
                pass
        # 精确获取 #paragraph 正文
        para = soup.find('div', id='paragraph')
        if para:
            text, ok = _extract_clean_text(para, min_chars=60)
            if ok:
                return pub_time, _generate_smart_summary(text)
        # 后备：找 article 或 content 容器
        for sel in [('article', {}), ('div', {'class': re.compile(r'(article|content|post)', re.I)})]:
            tag, attrs = sel
            container = soup.find(tag, attrs)
            if container:
                text, ok = _extract_clean_text(container, min_chars=60)
                if ok:
                    return pub_time, _generate_smart_summary(text)
        # 最后兜底：p 标签聚合
        body = soup.find('body')
        if body:
            p_texts = []
            for p in body.find_all('p'):
                pt = p.get_text(strip=True)
                if len(pt) > 30:
                    p_texts.append(pt)
            if p_texts:
                combined = ' '.join(p_texts)
                if len(combined) >= 60:
                    return pub_time, _generate_smart_summary(combined)
        return pub_time, "【摘要提取失败】"
    except Exception as e:
        print(f"    ⚠️ [IT之家] 详情页异常: {str(e)[:80]}")
        return None, "【页面读取失败】"

def fetch_generic_detail(url, source_name):
    """通用详情页，使用站点专用选择器"""
    try:
        resp = safe_request(url)
        if not resp:
            return None, "【页面失效】"
        soup = BeautifulSoup(resp.text, 'html.parser')
        pub_time = None

        # 1. 时间提取（全 try 保护）
        try:
            for meta_name in ['pubdate', 'publishdate', 'article:published_time', 'date', 'weibo:article:create_at']:
                meta = soup.find('meta', {'name': meta_name}) or soup.find('meta', {'property': meta_name})
                if meta and meta.get('content'):
                    t = parse_time_from_text(meta['content'])
                    if t:
                        pub_time = t
                        break
            if pub_time is None:
                for cls in ['time', 'date', 'pubtime', 'pub-time', 'article-time', 'post-time', 'info-time', 'source-time']:
                    el = soup.find(class_=re.compile(cls, re.I))
                    if el:
                        t = parse_time_from_text(el.get_text(strip=True))
                        if t:
                            pub_time = t
                            break
            if pub_time is None:
                page_text = soup.get_text(separator=' ', strip=True)[:800]
                pub_time = parse_time_from_text(page_text)
        except Exception:
            pass

        # 2. 正文提取：优先使用站点专用选择器
        selectors = SITE_CONTENT_SELECTORS.get(source_name, [])
        selectors = selectors + [
            ('article', {}),
            ('div', {'class': re.compile(r'(article|content|main-body|post-body|detail-content|news-content|entry-content)', re.I)}),
            ('div', {'id': re.compile(r'(article|content|main|post|detail|entry)', re.I)}),
            ('section', {'class': re.compile(r'(article|content)', re.I)}),
        ]

        for tag_name, attrs in selectors:
            try:
                container = soup.find(tag_name, attrs)
            except:
                continue
            if container:
                try:
                    text, ok = _extract_clean_text(container, min_chars=60)
                    if ok:
                        return pub_time, _generate_smart_summary(text)
                except Exception:
                    continue

        # 3. 最后的兜底：从 body 中提取
        try:
            body = soup.find('body')
            if body:
                # 先尝试从 body 中找最大的文本块
                paragraphs = body.find_all('p')
                if paragraphs:
                    p_texts = []
                    for p in paragraphs:
                        pt = p.get_text(strip=True)
                        if len(pt) > 30:
                            p_texts.append(pt)
                    if p_texts:
                        combined = ' '.join(p_texts)
                        if len(combined) >= 60:
                            return pub_time, _generate_smart_summary(combined)

                text, ok = _extract_clean_text(body, min_chars=30)
                if ok:
                    return pub_time, _generate_smart_summary(text)
        except Exception:
            pass

        return pub_time, "【摘要提取失败】"
    except Exception as e:
        print(f"    ⚠️ [{source_name}] 详情页异常: {str(e)[:80]}")
        return None, "【页面读取失败】"

# CNMO专属详情解析：三重时间提取 + ctext正文选择器
def fetch_cnmo_detail(url):
    """CNMO详情页：三重时间提取（meta → JSON-LD → URL日期）+ ctext正文"""
    try:
        resp = safe_request(url)
        if not resp:
            return None, "【页面失效】"
        soup = BeautifulSoup(resp.text, 'html.parser')
        pub_time = None

        # ── 三重时间提取 ──
        # 方案1: meta property="article:published_time"
        try:
            meta = soup.find('meta', {'property': 'article:published_time'})
            if meta and meta.get('content'):
                t = parse_time_from_text(meta['content'])
                if t:
                    pub_time = t
        except Exception:
            pass

        # 方案2: JSON-LD datePublished
        if pub_time is None:
            try:
                for script in soup.find_all('script', type='application/ld+json'):
                    text = script.get_text()
                    m = re.search(r'"datePublished"\s*:\s*"([^"]+)"', text)
                    if m:
                        t = parse_time_from_text(m.group(1))
                        if t:
                            pub_time = t
                            break
            except Exception:
                pass

        # 方案3: meta name="pubdate" 或其他变体
        if pub_time is None:
            try:
                for meta_name in ['pubdate', 'publishdate', 'date', 'weibo:article:create_at']:
                    meta = soup.find('meta', {'name': meta_name}) or soup.find('meta', {'property': meta_name})
                    if meta and meta.get('content'):
                        t = parse_time_from_text(meta['content'])
                        if t:
                            pub_time = t
                            break
            except Exception:
                pass

        # 方案4: URL中的日期（部分CNMO URL含日期路径）
        if pub_time is None:
            try:
                m = re.search(r'/(\d{4})/(\d{2})/(\d{2})/', url)
                if m:
                    pub_time = datetime(int(m.group(1)), int(m.group(2)), int(m.group(3)))
            except Exception:
                pass

        # ── 正文提取：优先 class=ctext ──
        text, ok = "", False
        ctext = soup.find('div', class_='ctext')
        if ctext:
            text, ok = _extract_clean_text(ctext, min_chars=60)
        if not ok:
            # 后备：通用选择器
            for sel in [('div', {'class': re.compile(r'(article|content|detail|news-text|news-content)', re.I)}),
                        ('article', {})]:
                tag, attrs = sel
                container = soup.find(tag, attrs)
                if container:
                    text, ok = _extract_clean_text(container, min_chars=60)
                    if ok:
                        break

        summary = _generate_smart_summary(text) if ok else "【摘要提取失败】"
        return pub_time, summary
    except Exception as e:
        print(f"    ⚠️ [CNMO] 详情页异常: {str(e)[:80]}")
        return None, "【页面读取失败】"

# 创建各站点的详情抓取函数
# CFM闪存市场专用详情：进详情页抓取真实标题(h1)与正文摘要，并确认时间
def fetch_cfm_detail(url):
    """CFM 闪存市场：详情页抓 h1 标题 + 正文摘要 + 时间二次确认，返回 (pub_time, summary, title)"""
    try:
        resp = safe_request(url)
        if not resp:
            return None, None, None
        soup = BeautifulSoup(resp.text, 'html.parser')
        pub_time = None
        # 时间提取（meta → class → 页面文本前800字符，与通用详情一致）
        try:
            for meta_name in ['pubdate', 'publishdate', 'article:published_time', 'date', 'weibo:article:create_at']:
                meta = soup.find('meta', {'name': meta_name}) or soup.find('meta', {'property': meta_name})
                if meta and meta.get('content'):
                    t = parse_time_from_text(meta['content'])
                    if t:
                        pub_time = t
                        break
            if pub_time is None:
                for cls in ['time', 'date', 'pubtime', 'pub-time', 'article-time', 'post-time', 'info-time', 'source-time']:
                    el = soup.find(class_=re.compile(cls, re.I))
                    if el:
                        t = parse_time_from_text(el.get_text(strip=True))
                        if t:
                            pub_time = t
                            break
            if pub_time is None:
                page_text = soup.get_text(separator=' ', strip=True)[:800]
                pub_time = parse_time_from_text(page_text)
        except Exception:
            pass

        # 标题：详情页真实 h1
        title = None
        try:
            h1 = soup.find('h1')
            if h1:
                t = h1.get_text(strip=True)
                if t:
                    title = t
        except Exception:
            pass

        # 正文摘要：CFM 详情页 = h1 标题 + 完整快讯列表（时间倒序），
        # 当前新闻正文需按 URL id 在 flash-listbox 中精确匹配 flash-item
        summary = None
        try:
            nid = re.search(r'/(\d+)$', url)
            flash = soup.find('div', class_='flash-listbox')
            target_item = None
            if flash and nid:
                for fi in flash.find_all('div', class_='flash-item'):
                    a = fi.find('a')
                    if a and a.get('href') and a['href'].rstrip('/').endswith('/' + nid.group(1)):
                        target_item = fi
                        break
            if target_item is None and flash:
                target_item = flash.find('div', class_='flash-item')
            if target_item:
                tb = target_item.find('div', class_='text-box')
                text = tb.get_text(' ', strip=True) if tb else target_item.get_text(' ', strip=True)
                if len(text) >= 60:
                    summary = _generate_smart_summary(text)
        except Exception:
            pass
        if summary is None:
            # 兜底：站点选择器 + 通用选择器（与 fetch_generic_detail 一致）
            try:
                selectors = SITE_CONTENT_SELECTORS.get("CFM闪存市场", []) + [
                    ('article', {}),
                    ('div', {'class': re.compile(r'(article|content|main-body|post-body|detail-content|news-content|entry-content)', re.I)}),
                    ('div', {'id': re.compile(r'(article|content|main|post|detail|entry)', re.I)}),
                    ('section', {'class': re.compile(r'(article|content)', re.I)}),
                ]
                for tag_name, attrs in selectors:
                    try:
                        container = soup.find(tag_name, attrs)
                    except Exception:
                        continue
                    if container:
                        try:
                            text, ok = _extract_clean_text(container, min_chars=60)
                            if ok:
                                summary = _generate_smart_summary(text)
                                break
                        except Exception:
                            continue
                if summary is None:
                    body = soup.find('body')
                    if body:
                        paragraphs = body.find_all('p')
                        p_texts = [p.get_text(strip=True) for p in paragraphs if len(p.get_text(strip=True)) > 30]
                        if p_texts:
                            combined = ' '.join(p_texts)
                            if len(combined) >= 60:
                                summary = _generate_smart_summary(combined)
            except Exception:
                pass

        return pub_time, summary, title
    except Exception as e:
        print(f"    ⚠️ [CFM闪存市场] 详情页异常: {str(e)[:80]}")
        return None, None, None

# 华尔街见闻详情页（站点为SPA空壳，走官方API取正文）
def fetch_wallstreetcn_detail(url):
    """华尔街见闻专用详情：lives API 优先，信息流 API 按 uri 匹配兜底"""
    m = re.search(r'/(?:livenews|articles|member/articles)/(\d+)', url)
    if not m:
        return None, None
    nid = m.group(1)
    # 1. lives 单条 API
    try:
        r = safe_request(f'https://api-one.wallstcn.com/apiv1/content/lives/{nid}', timeout=15)
        if r and r.status_code == 200:
            d = r.json().get('data') or {}
            ct = d.get('content_text') or d.get('content') or ''
            if len(ct) >= 20:
                pt = None
                ts = d.get('display_time')
                if ts:
                    try:
                        pt = datetime.fromtimestamp(int(ts))
                    except Exception:
                        pass
                return pt, _generate_smart_summary(ct)
    except Exception as e:
        print(f'  华尔街见闻 lives API 异常：{str(e)[:60]}')
    # 2. 信息流按 uri 匹配（article 类：无正文，用 content_short 摘要兜底）
    try:
        r2 = safe_request('https://api-one.wallstcn.com/apiv1/content/information-flow?channel=global-channel&limit=50', timeout=15)
        if r2 and r2.status_code == 200:
            for it in (r2.json().get('data') or {}).get('items', []):
                res = it.get('resource') or {}
                if str(res.get('id')) == nid or (res.get('uri') or '').rstrip('/').endswith(f'/{nid}'):
                    ct = res.get('content_text') or res.get('content') or res.get('content_short') or ''
                    if len(ct) >= 20:
                        pt = None
                        ts = res.get('display_time')
                        if ts:
                            try:
                                pt = datetime.fromtimestamp(int(ts))
                            except Exception:
                                pass
                        return pt, _generate_smart_summary(ct)
    except Exception as e:
        print(f'  华尔街见闻信息流 API 异常：{str(e)[:60]}')
    return None, None

def _make_detail_func(source_name):
    def _f(url):
        return fetch_generic_detail(url, source_name)
    return _f

DETAIL_MAP = {
    "IT之家": fetch_ithome_detail,
    "华尔街见闻": fetch_wallstreetcn_detail,
    "CFM闪存市场": fetch_cfm_detail,
    "CNMO手机资讯": fetch_cnmo_detail,
}
for src_name in ["网易新闻", "新浪首页", "新浪新闻频道", "新浪财经",
                 "DRAMX闪存资讯", "驱动之家首页", "驱动之家科技频道",
                 "爱集微产业资讯",
                 "科创板日报", "经济观察网", "ZOL科技新闻", "搜狐科技", "凤凰科技", "太平洋科技网"]:
    DETAIL_MAP[src_name] = _make_detail_func(src_name)

# 过滤匹配新闻（双重时间检查：列表页预过滤 + 详情页确认）
# ===== 改动2：新增并行版过滤函数 =====
def filter_brand_news_parallel(raw_all_list, hours=24):
    clean_news_list = []
    drop_sensitive = 0
    drop_ascii_only = 0
    # 纯数字/英文字母/标点符号标题的正则
    ascii_only_pattern = re.compile(r'^[a-zA-Z0-9\s\.\,\-\+\/\(\)\[\]\{\}\:\;\!\?\@\#\$\%\^\&\*\_\=\~\`\'\"\\\|<>]+$')
    for item in raw_all_list:
        title = item['title']
        if has_sensitive_text(title):
            drop_sensitive += 1
            print(f"🚫 过滤敏感词：【{title[:40]}...】")
            continue
        if ascii_only_pattern.match(title):
            drop_ascii_only += 1
            print(f"🔤 过滤纯英文/数字标题：【{title[:40]}...】")
            continue
        clean_news_list.append(item)
    print(f"\n敏感词过滤完成，丢弃 {drop_sensitive} 条；纯英文/数字标题过滤，丢弃 {drop_ascii_only} 条；剩余 {len(clean_news_list)} 条待匹配")

    now = datetime.now()
    cutoff_time = now - timedelta(hours=hours)
    brand_count = {}
    matched_news = []
    time_skipped_list = 0
    time_skipped_detail = 0
    processed = 0
    
    # 先品牌预过滤，减少并行时的无效请求
    brand_candidates = []
    for item in clean_news_list:
        title = item['title']
        match_brand = None
        for bname, kwlist in TARGET_BRANDS.items():
            for kw in kwlist:
                if kw.lower() in title.lower():
                    match_brand = bname
                    break
            if match_brand:
                break
        if match_brand:
            item['_pre_brand'] = match_brand
            brand_candidates.append(item)
    
    print(f"品牌预过滤：{len(clean_news_list)} → {len(brand_candidates)} 条候选")
    
    # 进度锁
    _prog_lock = Lock()
    _progress = [0, len(brand_candidates), 0]
    
    def _process_one(item):
        title = item['title']
        url = item['url']
        source = item['source']
        list_time = item.get('list_time')
        match_brand = item['_pre_brand']
        
        with _prog_lock:
            _progress[0] += 1
            p = _progress[0]
            if p % 50 == 0 or p == _progress[1]:
                print(f"  💓 详情进度 {p}/{_progress[1]}，已匹配 {_progress[2]} 条...")
        
        # 列表页时间预过滤
        if list_time is not None and list_time < cutoff_time:
            return ('TIME_SKIP', None)
        
        # 品牌计数上限
        cnt = brand_count.get(match_brand, 0)
        if cnt >= 500:
            return None
        
        # 抓取详情
        get_detail = DETAIL_MAP.get(source)
        if not get_detail:
            return None
        
        try:
            r = get_detail(url)
            if isinstance(r, tuple) and len(r) >= 3:
                pt, sm, detail_title = r[0], r[1], r[2]
            else:
                pt, sm = r[0], r[1]
                detail_title = None
        except Exception:
            return None
        
        if detail_title:
            title = detail_title
        
        # 时间二次确认
        final_time = pt if pt else list_time
        if final_time is None or final_time < cutoff_time:
            return ('TIME_SKIP_DETAIL', None)
        
        brand_count[match_brand] = brand_count.get(match_brand, 0) + 1
        
        # 【最终版】单次AI洞察调用，3次内层重试，无额外外层重试，无降级填充
        insight = _generate_market_insight(title, sm or title, match_brand)
        
        # 最终无洞察则留空，不填充
        if not insight:
            print(f"  ⚠️ 该新闻无AI洞察：{title[:40]}...")
        
        with _prog_lock:
            _progress[2] += 1
        
        return {
            'title': title, 'url': url, 'source': source,
            'brand': match_brand, 'pub_time': final_time, 'summary': sm,
            'insight': insight,  # 可能为空
        }
    
    # 15并发执行详情抓取
    print(f"\n🚀 并行详情抓取：{len(brand_candidates)}条，15并发...")
    t0 = time.time()
    with ThreadPoolExecutor(max_workers=15) as executor:
        futures = {executor.submit(_process_one, item): item for item in brand_candidates}
        for future in as_completed(futures):
            try:
                result = future.result(timeout=45)
                if result and isinstance(result, dict):
                    matched_news.append(result)
                elif result and result[0] == 'TIME_SKIP':
                    time_skipped_list += 1
                elif result and result[0] == 'TIME_SKIP_DETAIL':
                    time_skipped_detail += 1
            except Exception:
                pass
    
    print(f"⏱ 详情并行完成: {time.time()-t0:.1f}s | 匹配{len(matched_news)}条")
    print(f"  列表页时间过滤：{time_skipped_list} 条；详情页时间过滤：{time_skipped_detail} 条")
    
    matched_news.sort(key=lambda x: x['pub_time'] if x['pub_time'] else datetime.min, reverse=True)
    return matched_news

# 生成HTML报告【合并标题摘要单次翻译，减少API请求】
def generate_html_report(news_items, report_date):
    brand_groups = {}
    for item in news_items:
        b = item['brand']
        if b not in brand_groups:
            brand_groups[b] = []
        brand_groups[b].append(item)
    time_str = report_date.strftime('%Y-%m-%d %H:%M')
    date_cn = report_date.strftime('%Y年%m月%d日')
    date_kr = report_date.strftime('%Y년 %m월 %d일')
    html_parts = []
    html_parts.append(f'''<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>South China Sales Daily MI Briefing | {date_cn}</title>
<style>
    :root {{
        --primary: #1a2332;
        --primary-light: #2c3e50;
        --accent: #c9a96e;
        --accent-light: #f0e6d3;
        --bg: #f4f6f8;
        --card-bg: #ffffff;
        --text: #2d3436;
        --text-secondary: #636e72;
        --text-muted: #b2bec3;
        --border: #dfe6e9;
        --border-light: #eef1f3;
        --zh-tag: #2c3e50;
        --kr-tag: #c9a96e;
        --zh-bg: #eef2f7;
        --kr-bg: #faf6ef;
        --shadow-sm: 0 1px 3px rgba(0,0,0,0.06);
        --shadow-md: 0 4px 12px rgba(0,0,0,0.08);
    }}
    * {{ margin:0; padding:0; box-sizing:border-box; }}
    body {{
        font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", "Microsoft YaHei", "Malgun Gothic", "Apple SD Gothic Neo", sans-serif;
        background: var(--bg);
        color: var(--text);
        line-height: 1.7;
        -webkit-font-smoothing: antialiased;
    }}
    .container {{ max-width: 1100px; margin: 0 auto; padding: 24px 20px; }}

    /* === 顶部品牌横幅 === */
    .header {{
        background: #ffffff;
        color: var(--text);
        padding: 5px 50px;
        border-radius: 0;
        margin-bottom: 10px;
        box-shadow: 0 2px 8px rgba(0,0,0,0.06);
        display: flex;
        align-items: center;
        justify-content: space-between;
        gap: 24px;
    }}
    .header-left {{
        flex: 1;
        min-width: 0;
    }}
    .header h1 {{
        font-size: 25px;
        font-weight: 700;
        letter-spacing: 0.5px;
        margin-bottom: 0;
        color: var(--primary);
    }}
    .header .subtitle {{
        font-size: 14px;
        color: var(--text-secondary);
        font-weight: 600;
        line-height: 1.4;
        margin-top: 2px;
    }}

    /* === 统计概览 - 右侧竖排 === */
    .header-stats {{
        display: flex;
        flex-direction: column;
        align-items: flex-end;
        gap: 0px;
        flex-shrink: 0;
    }}
    .header-stat {{
        display: flex;
        align-items: center;
        gap: 6px;
        font-size: 13px;
        color: var(--text-secondary);
        white-space: nowrap;
    }}
    .header-stat strong {{
        font-size: 18px;
        font-weight: 700;
        color: var(--primary);
    }}

    /* === 内容主体 === */
    .content {{
        background: var(--card-bg);
        padding: 20px 48px;
        border-radius: 0 0 8px 8px;
        box-shadow: var(--shadow-md);
    }}

    /* === 品牌分区 - 蓝色渐变圆角卡片 === */
    .brand-section {{
        margin-bottom: 24px;
    }}
    .brand-section:last-child {{ margin-bottom: 0; }}
    .brand-header {{
        display: flex;
        align-items: center;
        gap: 12px;
        padding: 12px 24px;
        background: linear-gradient(135deg, #2d6db5 0%, #5ba3e8 100%);
        border-radius: 0;
        color: #fff;
        margin-bottom: 16px;
        box-shadow: 0 2px 12px rgba(45, 109, 181, 0.2);
    }}
    .brand-name {{
        font-size: 20px;
        font-weight: 700;
        color: #fff;
        letter-spacing: 0.5px;
    }}
    .brand-name-kr {{
        font-size: 14px;
        color: rgba(255,255,255,0.7);
        font-weight: 400;
        margin-left: 6px;
    }}
    .brand-count {{
        margin-left: auto;
        font-size: 14px;
        font-weight: 600;
        color: #fff;
        background: rgba(255,255,255,0.2);
        padding: 4px 14px;
        border-radius: 20px;
    }}

    /* === 新闻条目 - 左右双语布局 === */
    .news-item {{
        padding: 5px 0;
        border-bottom: 1px solid var(--border-light);
        transition: background 0.2s;
    }}
    .news-item:last-child {{ border-bottom: none; }}
    .news-item:hover {{ background: #fafbfc; }}

    /* 左右两栏布局 */
    .news-bilingual {{
        display: grid;
        grid-template-columns: 1fr 1fr;
        gap: 24px;
        margin-bottom: 10px;
    }}
    .news-col {{
        min-width: 0;
    }}
    .news-col.zh {{
        padding-right: 20px;
        border-right: 1px solid var(--border-light);
    }}
    .news-col.kr {{
        padding-left: 4px;
    }}

    /* 语言标签 */
    .lang-tag {{
        display: inline-block;
        font-size: 10px;
        font-weight: 700;
        padding: 2px 8px;
        border-radius: 3px;
        margin-bottom: 8px;
        letter-spacing: 0.5px;
        text-transform: uppercase;
    }}
    .lang-tag.zh {{
        background: var(--zh-bg);
        color: var(--zh-tag);
    }}
    .lang-tag.kr {{
        background: var(--kr-bg);
        color: var(--kr-tag);
    }}

    /* 标题 */
    .news-title {{
        font-size: 15px;
        font-weight: 600;
        line-height: 1.5;
        margin-bottom: 6px;
    }}
    .news-title a {{
        color: var(--primary);
        text-decoration: none;
        transition: color 0.2s;
    }}
    .news-title a:hover {{
        color: var(--accent);
        text-decoration: underline;
    }}

    /* 摘要 */
    .news-summary {{
        font-size: 12px;
        color: var(--text-secondary);
        line-height: 1.6;
        margin-top: 4px;
    }}
    /* AI 市场洞察(与摘要同格式:左对齐、无背景) */
    .news-insight {{
        font-size: 12px;
        color: var(--text-secondary);
        line-height: 1.6;
        margin-top: 4px;
    }}
    .insight-label {{
        display: block;
        font-weight: 700;
        color: var(--text-secondary);
        margin-bottom: 2px;
    }}
    .news-meta {{
        display: flex;
        align-items: center;
        gap: 12px;
        flex-wrap: wrap;
        font-size: 11px;
        color: var(--text-muted);
        margin-top: 6px;
        padding-top: 6px;
        border-top: 1px dotted var(--border-light);
    }}
    .news-meta .meta-item {{
        display: flex;
        align-items: center;
        gap: 3px;
    }}
    .source-tag {{
        background: var(--bg);
        color: var(--text-secondary);
        font-size: 11px;
        padding: 2px 8px;
        border-radius: 3px;
        font-weight: 500;
    }}
    .link-btn {{
        color: var(--accent);
        text-decoration: none;
        font-weight: 500;
        font-size: 12px;
        transition: color 0.2s;
    }}
    .link-btn:hover {{ color: var(--primary); text-decoration: underline; }}

    /* === 无内容提示 === */
    .no-news {{
        text-align: center;
        padding: 60px 20px;
        color: var(--text-muted);
    }}
    .no-news .empty-icon {{
        font-size: 48px;
        margin-bottom: 12px;
        opacity: 0.5;
    }}

    /* === 页脚 === */
    .footer {{
        text-align: center;
        padding: 24px 20px;
        color: var(--text-muted);
        font-size: 12px;
    }}
    .footer p {{ margin-bottom: 4px; }}
    .footer .divider {{
        width: 40px;
        height: 1px;
        background: var(--border);
        margin: 12px auto;
    }}

    /* === 响应式：窄屏时切换为上下布局 === */
    @media (max-width: 768px) {{
        .header {{ padding: 24px 20px; }}
        .header h1 {{ font-size: 20px; }}
        .summary-bar {{ padding: 16px 20px; gap: 16px; }}
        .content {{ padding: 20px; }}
        .news-bilingual {{
            grid-template-columns: 1fr;
            gap: 12px;
        }}
        .news-col.zh {{
            padding-right: 0;
            border-right: none;
            border-bottom: 1px solid var(--border-light);
            padding-bottom: 12px;
        }}
    }}
</style>
</head>
<body>
<div class="container">

<!-- 顶部横幅 -->
<div class="header">
    <div class="header-left">
        <h1>South China Sales Daily MI Briefing</h1>
        <div class="subtitle">华南销售每日市场情报简报 · 남중국 세일즈 데일리 MI 브리핑 | {time_str} (24小时内新闻 / 최근 24시간 뉴스)</div>
    </div>
    <div class="header-stats">
        <div class="header-stat">📰 匹配资讯 <strong>{len(news_items)}</strong> 条</div>
        <div class="header-stat">🏷️ 覆盖品类 <strong>{len(brand_groups)}</strong> 个</div>
        <div class="header-stat">🕐 统计周期 近24小时</div>
    </div>
</div>

<!-- 内容主体 -->
<div class="content">
''')
    for b in brand_order:
        if b not in brand_groups:
            continue
        item_list = brand_groups[b]
        color = brand_colors[b]
        kr_name = brand_kr_name[b]
        count_kr = len(item_list)
        html_parts.append(f'''<div class="brand-section">
    <div class="brand-header">
        <span class="brand-name">{b}</span>
        <span class="brand-name-kr">/ {kr_name}</span>
        <span class="brand-count">{len(item_list)} 条 · {count_kr}건</span>
    </div>''')
        for item in item_list:
            tc = item['title']
            sc = item['summary'] if item['summary'] else ""
            src = item['source']
            url = item['url']
            t_show = item['pub_time'].strftime('%Y-%m-%d %H:%M') if item['pub_time'] else "时间未知"

            # 翻译带异常保护，单条失败不影响后续
            try:
                # 合并标题+摘要，一次翻译，减少API调用
                combine_text = f"{SPLIT_TITLE_TAG}{tc}{SPLIT_SUMMARY_TAG}{sc}"
                combine_kr = translate_text(combine_text)
                if SPLIT_TITLE_TAG in combine_kr and SPLIT_SUMMARY_TAG in combine_kr:
                    kr_title, kr_summary = combine_kr.split(SPLIT_SUMMARY_TAG, 1)
                    kr_title = kr_title.replace(SPLIT_TITLE_TAG, "").strip()
                    kr_summary = kr_summary.strip()
                else:
                    # 分割标记丢失，降级两次翻译
                    kr_title = translate_text(tc)
                    kr_summary = translate_text(sc)
            except Exception as e:
                print(f"翻译单条异常: {e}，使用原文")
                kr_title = tc
                kr_summary = sc

            # 存储翻译结果，供Excel生成使用
            item['kr_title'] = kr_title
            item['kr_summary'] = kr_summary

            # ---- AI 市场洞察(中) + 译韩 ----
            ic = (item.get('insight') or "").strip()
            kr_insight = ""
            if ic:
                try:
                    kr_insight_raw = translate_text(ic)
                    if kr_insight_raw and kr_insight_raw.strip():
                        kr_insight = kr_insight_raw.strip()
                except Exception as e:
                    print(f"洞察翻译异常: {e}")
                    kr_insight = ""
            item['kr_insight'] = kr_insight

            # 摘要为空时隐藏摘要行（如 CFM 只抓标题不抓摘要）
            zh_summary_html = f'<div class="news-summary">{sc}</div>' if sc else ''
            kr_summary_html = f'<div class="news-summary">{kr_summary}</div>' if kr_summary else ''
            zh_insight_html = f'<div class="news-insight"><span class="insight-label">💡 市场洞察</span>{ic}</div>' if ic else ''
            kr_insight_html = f'<div class="news-insight kr"><span class="insight-label">💡 시사점</span>{kr_insight}</div>' if kr_insight else ''

            html_parts.append(f'''
<div class="news-item">
    <div class="news-bilingual">
        <!-- 左侧：中文 -->
        <div class="news-col zh">
            <div class="news-title"><a href="{url}" target="_blank" rel="noopener">{tc}</a></div>
            {zh_summary_html}
            {zh_insight_html}
            <div class="news-meta">
                <span class="source-tag">{src}</span>
                <span class="meta-item">🕐 {t_show}</span>
                <a class="link-btn" href="{url}" target="_blank" rel="noopener">Source Hyperlink →</a>
            </div>
        </div>
        <!-- 右侧：韩文 -->
        <div class="news-col kr">
            <div class="news-title" style="font-weight:500;"><a href="{url}" target="_blank" rel="noopener">{kr_title}</a></div>
            {kr_summary_html}
            {kr_insight_html}
        </div>
    </div>
</div>''')
        html_parts.append('</div>')
    if len(brand_groups) == 0:
        html_parts.append('<div class="no-news"><p>📭 过去24小时无匹配行业资讯</p></div>')
    html_parts.append(f'''
</div>
<!-- /content -->

<div class="footer">
    <div class="divider"></div>
    <p>South China Sales Daily MI Briefing By Sam Sun</p>
    <p>19源采集 · 全局去重 · 中韩双语 · 腾讯机器翻译 · 商务简报</p>
    <p style="margin-top:6px;">© {report_date.year} Automated Industry Intelligence Report</p>
</div>

</div>
<!-- /container -->
</body>
</html>''')
    return ''.join(html_parts)

# ==================== 邮件发送【含Excel附件：中韩双语新闻表】 ====================
def _generate_excel(news_items, report_date):
    """生成Excel：每条新闻一行两列，左中文右韩文（xlsxwriter，富文本可靠）"""
    import io as _io
    try:
        import xlsxwriter
    except ImportError:
        print("⚠️ xlsxwriter未安装，跳过Excel生成")
        return None

    buf = _io.BytesIO()
    wb = xlsxwriter.Workbook(buf, {'in_memory': True})
    ws = wb.add_worksheet('中韩双语新闻')

    # 列宽
    ws.set_column('A:A', 55)
    ws.set_column('B:B', 55)

    # 格式定义
    title_fmt = wb.add_format({
        'font_name': 'Microsoft YaHei', 'font_size': 14, 'bold': True,
        'font_color': '#1A2332', 'align': 'center', 'valign': 'vcenter',
        'border': 0,
    })
    header_fmt = wb.add_format({
        'font_name': 'Microsoft YaHei', 'font_size': 11, 'bold': True,
        'font_color': '#FFFFFF', 'bg_color': '#1A2332',
        'align': 'center', 'valign': 'vcenter',
        'border': 1, 'border_color': '#DFE6E9',
    })
    brand_fmt = wb.add_format({
        'font_name': 'Microsoft YaHei', 'font_size': 10, 'bold': True,
        'font_color': '#1A2332', 'bg_color': '#F0E6D3',
        'align': 'left', 'valign': 'vcenter',
        'border': 1, 'border_color': '#DFE6E9',
    })
    # 中文列基础格式
    cn_base_fmt = wb.add_format({
        'font_name': 'Microsoft YaHei', 'font_size': 10,
        'font_color': '#2D3436', 'bg_color': '#EEF2F7',
        'text_wrap': True, 'valign': 'top',
        'border': 1, 'border_color': '#DFE6E9',
    })
    # 韩文列基础格式
    kr_base_fmt = wb.add_format({
        'font_name': 'Malgun Gothic', 'font_size': 10,
        'font_color': '#2D3436', 'bg_color': '#FAF6EF',
        'text_wrap': True, 'valign': 'top',
        'border': 1, 'border_color': '#DFE6E9',
    })
    # 富文本用到的片段格式
    cn_title_frag = wb.add_format({
        'font_name': 'Microsoft YaHei', 'font_size': 10, 'bold': True,
        'font_color': '#1A2332',
    })
    cn_text_frag = wb.add_format({
        'font_name': 'Microsoft YaHei', 'font_size': 10,
        'font_color': '#2D3436',
    })
    cn_meta_frag = wb.add_format({
        'font_name': 'Microsoft YaHei', 'font_size': 9,
        'font_color': '#636E72',
    })
    cn_insight_label_frag = wb.add_format({
        'font_name': 'Microsoft YaHei', 'font_size': 10, 'bold': True,
        'font_color': '#2D3436',
    })
    cn_insight_text_frag = wb.add_format({
        'font_name': 'Microsoft YaHei', 'font_size': 10,
        'font_color': '#2D3436',
    })
    kr_title_frag = wb.add_format({
        'font_name': 'Malgun Gothic', 'font_size': 10, 'bold': True,
        'font_color': '#1A2332',
    })
    kr_text_frag = wb.add_format({
        'font_name': 'Malgun Gothic', 'font_size': 10,
        'font_color': '#2D3436',
    })
    kr_insight_label_frag = wb.add_format({
        'font_name': 'Malgun Gothic', 'font_size': 10, 'bold': True,
        'font_color': '#2D3436',
    })
    kr_insight_text_frag = wb.add_format({
        'font_name': 'Malgun Gothic', 'font_size': 10,
        'font_color': '#2D3436',
    })

    # 第1行：大标题
    date_str = report_date.strftime('%Y-%m-%d')
    ws.merge_range(0, 0, 0, 1, f'South China Sales Daily MI Briefing  {date_str}', title_fmt)
    ws.set_row(0, 30)

    # 第2行：表头
    ws.write(1, 0, '中文 (Chinese)', header_fmt)
    ws.write(1, 1, '한국어 (Korean)', header_fmt)
    ws.set_row(1, 25)

    row = 2  # 第3行开始（0-based）
    brand_order = [
        "OPPO", "vivo", "荣耀", "传音", "手机市场",
        "腾讯", "比亚迪", "小鹏", "江波龙", "长鑫", "长存",
        "存储(DRAM,NAND)", "MTK SOC", "高通 SOC", "Robotics"
    ]

    for brand in brand_order:
        brand_items = [it for it in news_items if it.get('brand') == brand]
        if not brand_items:
            continue

        # 品牌分隔行（合并A、B列）
        ws.merge_range(row, 0, row, 1, f'■ {brand}  ({len(brand_items)} 条)', brand_fmt)
        ws.set_row(row, 24)
        row += 1

        for item in brand_items:
            url = item.get('url', '')
            src = item.get('source', '')
            t_show = item['pub_time'].strftime('%Y-%m-%d %H:%M') if item.get('pub_time') else ''

            # ---- 左列：中文富文本 ----
            cn_segments = [
                cn_title_frag, f"【{src}】{item.get('title', '')}",
                cn_text_frag, "\n",
            ]
            if item.get('summary'):
                cn_segments.extend([
                    cn_text_frag, f"摘要：{item['summary']}",
                    cn_text_frag, "\n",
                ])
            if item.get('insight'):
                cn_segments.extend([
                    cn_insight_label_frag, "AI市场洞察:\n",
                    cn_insight_text_frag, item['insight'],
                    cn_text_frag, "\n",
                ])
            cn_segments.extend([
                cn_meta_frag, f"\n{t_show}  |  {url}",
            ])
            ws.write_rich_string(row, 0, *cn_segments, cn_base_fmt)

            # ---- 右列：韩文富文本 ----
            kr_title = item.get('kr_title', '')
            kr_summary = item.get('kr_summary', '')
            kr_insight = item.get('kr_insight', '')
            kr_segments = []
            if kr_title:
                kr_segments.extend([
                    kr_title_frag, kr_title,
                    kr_text_frag, "\n",
                ])
            if kr_summary:
                kr_segments.extend([
                    kr_text_frag, kr_summary,
                    kr_text_frag, "\n",
                ])
            if kr_insight:
                kr_segments.extend([
                    kr_insight_label_frag, "AI시사점:\n",
                    kr_insight_text_frag, kr_insight,
                ])
            if kr_segments:
                ws.write_rich_string(row, 1, *kr_segments, kr_base_fmt)
            else:
                ws.write_blank(row, 1, None, kr_base_fmt)

            ws.set_row(row, 130)  # 加高,容纳 insight
            row += 1

    # 冻结表头（第3行起）
    ws.freeze_panes(2, 0)

    wb.close()
    buf.seek(0)
    return buf.getvalue()


def _generate_outlook_table_html(news_items, report_date):
    """生成Outlook兼容的HTML表格邮件正文：两列（中文/韩文），列宽18cm"""
    brand_order = [
        "OPPO", "vivo", "荣耀", "传音", "手机市场",
        "腾讯", "比亚迪", "小鹏", "江波龙", "长鑫", "长存",
        "存储(DRAM,NAND)", "MTK SOC", "高通 SOC", "Robotics"
    ]
    date_str = report_date.strftime('%Y-%m-%d')
    time_str = report_date.strftime('%Y-%m-%d %H:%M')
    total_count = len(news_items)

    # 按品牌分组
    brand_groups = {}
    for item in news_items:
        b = item['brand']
        if b not in brand_groups:
            brand_groups[b] = []
        brand_groups[b].append(item)

    # 18cm ≈ 680px，Outlook 中建议用固定宽度
    col_width = 680  # 两列各约340px，总计约18cm

    html_parts = []
    html_parts.append(f'''<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>South China Sales Daily MI Briefing | {date_str}</title>
<!--[if gte mso 9]><xml><o:OfficeDocumentSettings><o:AllowPNG/><o:PixelsPerInch>96</o:PixelsPerInch></o:OfficeDocumentSettings></xml><![endif]-->
<style>
    body {{
        margin: 0; padding: 0;
        font-family: "Microsoft YaHei", "Malgun Gothic", "Apple SD Gothic Neo", Arial, sans-serif;
        background-color: #f4f6f8;
        -webkit-text-size-adjust: 100%;
        -ms-text-size-adjust: 100%;
    }}
    .email-wrapper {{
        max-width: 800px; margin: 0 auto; background-color: #ffffff;
    }}
    /* 标题区域 */
    .email-header {{
        padding: 20px 24px;
        background: linear-gradient(135deg, #1a2332 0%, #2c3e50 100%);
        color: #ffffff;
    }}
    .email-header h1 {{
        margin: 0 0 4px 0; font-size: 18px; font-weight: 700;
        color: #ffffff; letter-spacing: 0.5px;
    }}
    .email-header .subtitle {{
        font-size: 12px; color: #b2bec3; font-weight: 400;
    }}
    .email-header .stats {{
        margin-top: 8px; font-size: 12px; color: #c9a96e;
    }}

    /* 品牌分隔行 */
    .brand-row td {{
        padding: 8px 24px;
        background-color: #f0e6d3;
        font-size: 13px; font-weight: 700; color: #1a2332;
        border-bottom: 1px solid #dfe6e9;
    }}

    /* 新闻行 */
    .news-row td {{
        padding: 10px 24px;
        vertical-align: top;
        border-bottom: 1px solid #eef1f3;
    }}
    .col-zh {{
        width: 340px;
        background-color: #eef2f7;
    }}
    .col-kr {{
        width: 340px;
        background-color: #faf6ef;
    }}

    /* 新闻标题 */
    .news-title {{
        font-size: 13px; font-weight: 700; color: #1a2332;
        line-height: 1.5; margin-bottom: 4px;
    }}
    .news-title a {{
        color: #1a2332; text-decoration: none;
    }}

    /* 摘要 */
    .news-summary {{
        font-size: 11px; color: #636e72; line-height: 1.6;
        margin-bottom: 4px;
    }}

    /* 元信息 */
    .news-meta {{
        font-size: 10px; color: #b2bec3;
        margin-top: 4px; padding-top: 4px;
        border-top: 1px dotted #dfe6e9;
    }}
    .source-tag {{
        display: inline-block;
        background: #dfe6e9; color: #636e72;
        padding: 1px 6px; border-radius: 2px;
        font-size: 10px; margin-right: 6px;
    }}

    /* AI 市场洞察(与摘要同格式:左对齐、无背景) */
    .news-insight {{
        font-size: 11px; color: #636e72; line-height: 1.6;
        margin-bottom: 4px;
    }}
    .insight-label {{
        display: block;
        font-weight: 700;
        color: #636e72;
        margin-bottom: 2px;
    }}

    /* 页脚 */
    .email-footer {{
        padding: 16px 24px; text-align: center;
        font-size: 11px; color: #b2bec3;
        background-color: #f4f6f8;
    }}
</style>
</head>
<body>
<div class="email-wrapper">

<!-- 顶部 -->
<div class="email-header">
    <h1>South China Sales Daily MI Briefing</h1>
    <div class="subtitle">华南销售每日市场情报简报 · 남중국 세일즈 데일리 MI 브리핑 | {time_str}</div>
    <div class="stats">📰 匹配资讯 {total_count} 条 · 🏷️ 覆盖品类 {len(brand_groups)} 个 · 🕐 统计周期 近24小时</div>
</div>

<!-- 表格 -->
<table width="100%" cellpadding="0" cellspacing="0" border="0" style="width:100%; max-width:800px; table-layout:fixed;">
    <!-- 表头 -->
    <tr>
        <td class="col-zh" style="width:340px; padding:8px 24px; background-color:#1a2332; font-size:12px; font-weight:700; color:#ffffff; text-align:center; border-right:1px solid #2c3e50;">中文 (Chinese)</td>
        <td class="col-kr" style="width:340px; padding:8px 24px; background-color:#1a2332; font-size:12px; font-weight:700; color:#ffffff; text-align:center;">한국어 (Korean)</td>
    </tr>
''')

    for brand in brand_order:
        if brand not in brand_groups:
            continue
        items = brand_groups[brand]
        kr_name = brand_kr_name.get(brand, brand)

        # 品牌分隔行
        html_parts.append(f'''    <tr class="brand-row">
        <td colspan="2" style="padding:8px 24px; background-color:#f0e6d3; font-size:13px; font-weight:700; color:#1a2332; border-bottom:1px solid #dfe6e9;">
            ■ {brand} / {kr_name} ({len(items)} 条 · {len(items)}건)
        </td>
    </tr>
''')

        for item in items:
            title_cn = item.get('title', '')
            summary_cn = item.get('summary', '')
            url = item.get('url', '')
            src = item.get('source', '')
            t_show = item['pub_time'].strftime('%Y-%m-%d %H:%M') if item.get('pub_time') else ''
            kr_title = item.get('kr_title', '')
            kr_summary = item.get('kr_summary', '')
            insight_cn = item.get('insight', '') or ''
            kr_insight = item.get('kr_insight', '') or ''

            # HTML转义
            title_cn_esc = title_cn.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;').replace('"', '&quot;')
            summary_cn_esc = summary_cn.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;').replace('"', '&quot;') if summary_cn else ''
            kr_title_esc = kr_title.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;').replace('"', '&quot;') if kr_title else ''
            kr_summary_esc = kr_summary.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;').replace('"', '&quot;') if kr_summary else ''
            insight_cn_esc = insight_cn.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;').replace('"', '&quot;') if insight_cn else ''
            kr_insight_esc = kr_insight.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;').replace('"', '&quot;') if kr_insight else ''

            cn_cell = f'<div class="news-title"><a href="{url}">{title_cn_esc}</a></div>'
            if summary_cn_esc:
                cn_cell += f'<div class="news-summary">{summary_cn_esc}</div>'
            if insight_cn_esc:
                cn_cell += f'<div class="news-insight"><span class="insight-label">💡 市场洞察</span>{insight_cn_esc}</div>'
            cn_cell += f'<div class="news-meta"><span class="source-tag">{src}</span> 🕐 {t_show}</div>'

            kr_cell = f'<div class="news-title"><a href="{url}">{kr_title_esc}</a></div>'
            if kr_summary_esc:
                kr_cell += f'<div class="news-summary">{kr_summary_esc}</div>'
            if kr_insight_esc:
                kr_cell += f'<div class="news-insight kr"><span class="insight-label">💡 시사점</span>{kr_insight_esc}</div>'

            html_parts.append(f'''    <tr class="news-row">
        <td class="col-zh" style="width:340px; padding:10px 24px; vertical-align:top; background-color:#eef2f7; border-bottom:1px solid #eef1f3;">
            {cn_cell}
        </td>
        <td class="col-kr" style="width:340px; padding:10px 24px; vertical-align:top; background-color:#faf6ef; border-bottom:1px solid #eef1f3;">
            {kr_cell}
        </td>
    </tr>
''')

    html_parts.append(f'''</table>

<!-- 页脚 -->
<div class="email-footer">
    <p style="margin:0 0 4px 0;">South China Sales Daily MI Briefing By Sam Sun</p>
    <p style="margin:0;">19源采集 · 全局去重 · 中韩双语 · 腾讯机器翻译 · 商务简报</p>
    <p style="margin:4px 0 0 0;">© {report_date.year} Automated Industry Intelligence Report</p>
</div>

</div>
</body>
</html>''')

    return ''.join(html_parts)


def send_email(html_content, report_date, script_path=None, item_count=0, news_items=None):
    date_str = report_date.strftime('%Y%m%d')
    subject = f'South China Sales Daily MI Briefing {report_date.strftime("%Y-%m-%d")} ({item_count} items)'
    msg = MIMEMultipart('mixed')
    msg['From'] = SENDER_EMAIL
    msg['To'] = ','.join(RECIPIENT_EMAILS)
    msg['Subject'] = subject

    # 邮件正文（alternative: plain + outlook表格html）
    body_part = MIMEMultipart('alternative')
    plain_text = f'十四源行业资讯日报 {date_str}\n优化说明：\n1. 全局跨站点新闻去重\n2. 标题摘要合并单次翻译，减少API限流\n3. 翻译触发429自动延时等待\n4. 邮件附带当前采集脚本\n附件：HTML中韩双语简报 + Excel新闻明细表'

    # 生成Outlook兼容的表格HTML作为邮件正文
    if news_items:
        outlook_html = _generate_outlook_table_html(news_items, report_date)
    else:
        outlook_html = html_content

    body_part.attach(MIMEText(plain_text, 'plain', 'utf-8'))
    body_part.attach(MIMEText(outlook_html, 'html', 'utf-8'))
    msg.attach(body_part)

    # Excel附件：中韩双语新闻明细
    if news_items:
        try:
            excel_data = _generate_excel(news_items, report_date)
            if excel_data:
                excel_att = MIMEBase('application', 'vnd.openxmlformats-officedocument.spreadsheetml.sheet')
                excel_att.set_payload(excel_data)
                encoders.encode_base64(excel_att)
                excel_att.add_header('Content-Disposition', 'attachment',
                                     filename=f'South China Sales Daily MI Briefing_{date_str}.xlsx')
                msg.attach(excel_att)
                print(f"✅ 已附加Excel新闻明细表")
        except Exception as e:
            print(f"⚠️ Excel生成失败：{str(e)}")

    # HTML报表附件
    html_att = MIMEBase('text', 'html')
    html_att.set_payload(html_content.encode('utf-8'))
    encoders.encode_base64(html_att)
    html_att.add_header('Content-Disposition', 'attachment', filename=f'South China Sales Daily MI Briefing_{date_str}.html')
    msg.attach(html_att)

    # 脚本附件
    if script_path and os.path.exists(script_path):
        try:
            with open(script_path, 'rb') as f:
                script_data = f.read()
            script_att = MIMEBase("application", "octet-stream")
            script_att.set_payload(script_data)
            encoders.encode_base64(script_att)
            script_fn = os.path.basename(script_path)
            script_att.add_header(
                "Content-Disposition",
                "attachment",
                **{
                    "filename": f"采集脚本_{date_str}.py",
                    "filename*": f"utf-8''{script_fn}"
                }
            )
            msg.attach(script_att)
            print(f"✅ 已附加采集脚本：{script_fn}")
        except Exception as e:
            print(f"⚠️ 脚本附件读取失败，跳过：{str(e)}")

    try:
        with smtplib.SMTP_SSL(SMTP_SERVER, SMTP_PORT, timeout=30) as server:
            server.login(SENDER_EMAIL, SENDER_PASSWORD)
            server.sendmail(SENDER_EMAIL, RECIPIENT_EMAILS, msg.as_string())
        print(f'✅ 邮件发送成功，收件人：{",".join(RECIPIENT_EMAILS)}')
        return True
    except Exception as e:
        print(f'❌ 邮件发送失败：{str(e)}')
        return False


# 主程序【全局URL去重 + 时间严格过滤 + 详情深度抓取】
# ===== 改动3：main函数改为并行抓取源站 + 并行详情过滤 =====
def main():
    SCRIPT_START_TIME = datetime.now()
    print("="*72)
    print("十四源行业新闻采集【并行优化版 - AI洞察单层重试版】")
    print(f"脚本执行时间：{SCRIPT_START_TIME.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"时间窗口：24小时（{ (SCRIPT_START_TIME - timedelta(hours=24)).strftime('%Y-%m-%d %H:%M:%S')} ~ {SCRIPT_START_TIME.strftime('%Y-%m-%d %H:%M:%S')}）")
    print("="*72)
    try:
        os.makedirs(OUTPUT_DIR, exist_ok=True)
        print(f"📂 报告目录：{OUTPUT_DIR}")
    except Exception as e:
        print(f"目录创建失败：{e}")
        return

    source_funcs = [
        fetch_ithome_news, fetch_netease_news, fetch_cfm_news, fetch_sina_news,
        fetch_sina_finance_news,
        fetch_dramx_news, fetch_mydrivers_news, fetch_cnmo_news, fetch_laoyaoba_news,
        fetch_wallstreetcn_news, fetch_starmarket_news, fetch_eeo_news, fetch_zol_news,
        fetch_sohu_tech_news, fetch_ifeng_tech_news, fetch_pconline_news
    ]

    # ====== 源站并行抓取（改动点：6并发）======
    all_news = []
    global_url_set = set()
    url_lock = Lock()
    
    def _fetch_wrapper(func):
        try:
            lst = func()
            new_items = []
            for item in lst:
                with url_lock:
                    if item["url"] not in global_url_set:
                        global_url_set.add(item["url"])
                        new_items.append(item)
            return new_items
        except Exception as e:
            print(f"站点{func.__name__}整体异常，跳过：{str(e)[:80]}")
            return []
    
    print("\n🚀 开始并行抓取各站点（6并发），全局实时去重...")
    t0 = time.time()
    with ThreadPoolExecutor(max_workers=6) as executor:
        futures = {executor.submit(_fetch_wrapper, f): f.__name__ for f in source_funcs}
        for future in as_completed(futures):
            fn = futures[future]
            try:
                items = future.result(timeout=120)
                all_news.extend(items)
                print(f"  ✅ {fn.replace('fetch_','')}: +{len(items)}条")
            except Exception as e:
                print(f"  ❌ {fn}: {e}")
    print(f"⏱ 源站并行完成: {time.time()-t0:.1f}s | 总计{len(all_news)}条")
    # ====== 源站并行结束 ======

    if len(all_news) == 0:
        print("❌ 所有站点无新闻，程序退出")
        return

    # 使用并行版过滤（改动点：15并发详情抓取）
    matched = filter_brand_news_parallel(all_news, hours=24)
    print(f"\n📊 匹配行业资讯总数：{len(matched)}")
    brand_stat = {}
    for item in matched:
        b = item['brand']
        brand_stat[b] = brand_stat.get(b, 0) + 1
    for b in brand_order:
        print(f"  {b}：{brand_stat.get(b, 0)} 条")

    print("\n🔤 开始批量翻译（标题+摘要合并调用，降低API次数）...")
    now = datetime.now()
    print(f"\n📝 开始生成HTML报告（{len(matched)}条匹配新闻）...")
    html_text = generate_html_report(matched, now)
    file_name = f'South China Sales Daily MI Briefing_{now.strftime("%Y%m%d_%H%M%S")}.html'
    save_full = os.path.join(OUTPUT_DIR, file_name)
    with open(save_full, 'w', encoding='utf-8') as f:
        f.write(html_text)
    print(f"\n📄 简报已本地保存：{save_full}")

    print("\n📧 执行邮件发送...")
    print(f"📄 报告文件：{save_full}")
    # 携带脚本参数，自动附加当前py文件
    email_ok = send_email(html_text, now, script_path=__file__, item_count=len(matched), news_items=matched)
    
    print("\n✅ 全部任务执行完毕！")

if __name__ == "__main__":
    # 启动时写锁文件（写 Python 自身 PID，方便外层 shell 检测）
    try:
        with open(_LOCK_FILE, "w") as f:
            f.write(str(os.getpid()))
    except Exception:
        pass
    try:
        main()
    finally:
        _cleanup_lock()

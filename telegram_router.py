import os
import sys
import time
import requests
import psycopg2
import asyncio
import aiohttp
import re
import json
import base64
import mimetypes
import subprocess
import signal
import atexit
import threading

from telethon import TelegramClient, events
from telethon.sessions import StringSession
from telethon.tl.custom import Button
# --- تغییرات: ایمپورت خطاهای مربوط به باطل شدن سشن و محدودیت ارسال ---
from telethon.errors import AuthKeyUnregisteredError, FloodWaitError

TELEGRAM_API_ID = int(os.environ.get("TELEGRAM_API_ID", 0))
TELEGRAM_API_HASH = os.environ.get("TELEGRAM_API_HASH", "").strip()
SESSION_STRING = os.environ.get("SESSION_STRING", "").strip()
CONTROL_BOT_TOKEN = os.environ.get("CONTROL_BOT_TOKEN", "").strip()
ADMIN_ID = int(os.environ.get("ADMIN_ID", 0))
EXTRA_ADMINS = os.environ.get("EXTRA_ADMINS", "").strip()

_raw_bale = os.environ.get("BALE_TOKEN_ROUTER", "").strip() or os.environ.get("BALE_TOKEN", "").strip()
BALE_TOKEN = _raw_bale[3:] if _raw_bale.lower().startswith("bot") else _raw_bale

_raw_rubika = os.environ.get("RUBIKA_TOKEN", "").strip()
RUBIKA_TOKEN = _raw_rubika[3:] if _raw_rubika.lower().startswith("bot") else _raw_rubika

_raw_eitaa = os.environ.get("EITAA_TOKEN", "").strip()
EITAA_TOKEN = _raw_eitaa

GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY_ROUTER", "").strip() 
DATABASE_URL = os.environ.get("ROUTER_DATABASE_URL", "").strip()

DIRECT_PROXY = {"http": None, "https": None}
VLESS_PROXY_URL = "http://127.0.0.1:10809"
VLESS_PROXY = {"http": VLESS_PROXY_URL, "https": VLESS_PROXY_URL}

def _rewind_files_arg(files_arg):
    if not files_arg or not isinstance(files_arg, dict):
        return
    for val in files_arg.values():
        f_obj = val[1] if isinstance(val, (tuple, list)) and len(val) > 1 else val
        if hasattr(f_obj, "seek"):
            try:
                f_obj.seek(0)
            except Exception:
                pass

def _rubika_post(url, **kwargs):
    """اولویت روبیکا: ۱. پروکسی VLESS -> ۲. در صورت خطا، اتصال مستقیم"""
    kwargs.pop("proxies", None)
    last_exc = None
    for idx, (px, px_name) in enumerate([(VLESS_PROXY, "پروکسی VLESS"), (DIRECT_PROXY, "اتصال مستقیم")]):
        if idx > 0:
            _rewind_files_arg(kwargs.get("files"))
        try:
            res = requests.post(url, proxies=px, **kwargs)
            if res.status_code < 500:
                try:
                    res.json()
                    return res
                except Exception:
                    if idx == 0:
                        print(f"⚠️ پاسخ غیر JSON از روبیکا با {px_name}؛ تلاش با مسیر جایگزین (مستقیم)...", flush=True)
                        continue
                    return res
            if idx == 0:
                print(f"⚠️ خطای HTTP {res.status_code} در روبیکا با {px_name}؛ تلاش با مسیر جایگزین (مستقیم)...", flush=True)
                continue
            return res
        except Exception as e:
            last_exc = e
            if idx == 0:
                print(f"⚠️ خطا در ارتباط با روبیکا از طریق {px_name} ({e})؛ تلاش با اتصال مستقیم...", flush=True)
    raise last_exc

def _bale_eitaa_post(url, **kwargs):
    """اولویت بله و ایتا: ۱. اتصال مستقیم -> ۲. در صورت خطا، پروکسی VLESS به عنوان جایگزین"""
    kwargs.pop("proxies", None)
    last_exc = None
    for idx, (px, px_name) in enumerate([(DIRECT_PROXY, "اتصال مستقیم"), (VLESS_PROXY, "پروکسی جایگزین VLESS")]):
        if idx > 0:
            _rewind_files_arg(kwargs.get("files"))
        try:
            res = requests.post(url, proxies=px, **kwargs)
            if res.status_code < 500:
                return res
            if idx == 0:
                print(f"⚠️ خطای HTTP {res.status_code} در {px_name}؛ تلاش با پروکسی جایگزین VLESS...", flush=True)
                continue
            return res
        except Exception as e:
            last_exc = e
            if idx == 0:
                print(f"⚠️ خطا در {px_name} ({e})؛ تلاش با پروکسی جایگزین VLESS...", flush=True)
    raise last_exc

def _bale_eitaa_get(url, **kwargs):
    """دریافت آپدیت‌های بله: ۱. اتصال مستقیم -> ۲. در صورت خطا، پروکسی VLESS"""
    kwargs.pop("proxies", None)
    last_exc = None
    for idx, (px, px_name) in enumerate([(DIRECT_PROXY, "اتصال مستقیم"), (VLESS_PROXY, "پروکسی جایگزین VLESS")]):
        try:
            res = requests.get(url, proxies=px, **kwargs)
            if res.status_code < 500:
                return res
        except Exception as e:
            last_exc = e
    if last_exc:
        raise last_exc
    return res

# ==========================================
# سیستم جامع مدیریت Cache در رم (صفر کردن درگیری دیتابیس در طول اجرا)
# ==========================================
_ROUTES_CACHE = []
_ROUTES_LOADED = False
_ROUTES_CHANGED = False

_STATE_CACHE = {}
_STATE_CHANGED = False

_ADMINS_CACHE = set()
_ADMINS_LOADED = False
_ADMINS_CHANGED = False

_MSG_MAP_CACHE = {}
_MSG_MAP_DIRTY = {}
_MSG_MAP_LOADED = False
_MSG_MAP_LOCK = threading.Lock()

# ==========================================
# افزونه‌های امنیتی: کنترل ترافیک و جلوگیری از تداخل (Race Condition)
# ==========================================
_GLOBAL_FETCH_STATE = {}
_ROUTES_AWAITING_SYNC = set()
_DELAY_QUEUE = {}
_PROCESSING_SEMAPHORE = asyncio.Semaphore(3) # محدودیت حداکثر ۳ پردازش همزمان
_DEDUP_LOCK = asyncio.Lock() # قفل جلوگیری از دریافت تکراری در لحظه
_RECENT_MSGS = [] # کش موقت پیام‌های اخیر روی رم
# ==========================================

def init_router_db():
    if not DATABASE_URL:
        print("❌ ارور: آدرس دیتابیس ROUTER_DATABASE_URL یافت نشد.", flush=True)
        return
    try:
        conn = psycopg2.connect(DATABASE_URL)
        conn.autocommit = True 
        cursor = conn.cursor()
        
        cursor.execute('''
        CREATE TABLE IF NOT EXISTS router_routes (
            id SERIAL PRIMARY KEY,
            name VARCHAR(100),
            src_channels TEXT,
            bale_channels TEXT,
            rubika_channels TEXT,
            custom_prompt TEXT,
            blacklist TEXT DEFAULT '',
            use_ai_media BOOLEAN DEFAULT FALSE,
            bale_max_size INTEGER DEFAULT 50,
            rubika_max_size INTEGER DEFAULT 50
        )
        ''')

        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN bale_max_size INTEGER DEFAULT 50")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN rubika_max_size INTEGER DEFAULT 50")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN ai_enabled BOOLEAN DEFAULT TRUE")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN ai_add_hashtags BOOLEAN DEFAULT FALSE")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN ai_translation VARCHAR(50) DEFAULT ''")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN bale_enabled BOOLEAN DEFAULT TRUE")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN rubika_enabled BOOLEAN DEFAULT TRUE")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN allow_no_caption BOOLEAN DEFAULT TRUE")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN eitaa_channels TEXT DEFAULT ''")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN eitaa_max_size INTEGER DEFAULT 50")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN eitaa_enabled BOOLEAN DEFAULT TRUE")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN bale_delay BOOLEAN DEFAULT FALSE")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN rubika_delay BOOLEAN DEFAULT FALSE")
        except: pass
        try: cursor.execute("ALTER TABLE router_routes ADD COLUMN eitaa_delay BOOLEAN DEFAULT TRUE")
        except: pass

        cursor.execute('''
        CREATE TABLE IF NOT EXISTS router_channel_state (
            channel_id VARCHAR(50) PRIMARY KEY,
            last_msg_id INTEGER
        )
        ''')

        cursor.execute('''
        CREATE TABLE IF NOT EXISTS router_admins (
            admin_id VARCHAR(50) PRIMARY KEY
        )
        ''')

        cursor.execute('''
        CREATE TABLE IF NOT EXISTS router_msg_map (
            route_id INTEGER,
            tg_chat_id VARCHAR(50),
            tg_msg_id INTEGER,
            platform VARCHAR(20),
            dest_chat_id VARCHAR(100),
            dest_msg_id VARCHAR(50),
            msg_type VARCHAR(20),
            media_id VARCHAR(100) DEFAULT '',
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (route_id, tg_chat_id, tg_msg_id, platform, dest_chat_id)
        )
        ''')
        try: cursor.execute("ALTER TABLE router_msg_map ADD COLUMN media_id VARCHAR(100) DEFAULT ''")
        except: pass
        cursor.execute('CREATE INDEX IF NOT EXISTS idx_router_msg_map ON router_msg_map (route_id, tg_chat_id, tg_msg_id)')
        
        try:
            cursor.execute("DELETE FROM router_msg_map WHERE created_at < NOW() - INTERVAL '7 days'")
        except: pass
        
        if ADMIN_ID != 0:
            try: cursor.execute('INSERT INTO router_admins (admin_id) VALUES (%s) ON CONFLICT DO NOTHING', (str(ADMIN_ID),))
            except: pass
            
        if EXTRA_ADMINS:
            for ex_admin in EXTRA_ADMINS.split(","):
                if ex_admin.strip():
                    try: cursor.execute('INSERT INTO router_admins (admin_id) VALUES (%s) ON CONFLICT DO NOTHING', (ex_admin.strip(),))
                    except: pass
                    
        conn.close()
        print("✅ دیتابیس مسیریاب و جدول نگاشت پیام‌ها آماده شد.", flush=True)
    except Exception as e:
        print(f"❌ خطای دیتابیس در مقداردهی اولیه: {e}", flush=True)

def load_all_msg_mappings():
    global _MSG_MAP_CACHE, _MSG_MAP_LOADED
    if _MSG_MAP_LOADED or not DATABASE_URL:
        return
    try:
        conn = psycopg2.connect(DATABASE_URL)
        cursor = conn.cursor()
        cursor.execute('''
            SELECT route_id, tg_chat_id, tg_msg_id, platform, dest_chat_id, dest_msg_id, msg_type, COALESCE(media_id, '')
            FROM router_msg_map
        ''')
        rows = cursor.fetchall()
        cursor.close()
        conn.close()
        with _MSG_MAP_LOCK:
            for r_id, cid, mid, plat, d_cid, d_mid, m_type, med_id in rows:
                key = (int(r_id), std_id(cid), int(mid))
                if key not in _MSG_MAP_CACHE:
                    _MSG_MAP_CACHE[key] = {}
                _MSG_MAP_CACHE[key][(str(plat), str(d_cid))] = (str(d_mid), str(m_type), str(med_id))
            _MSG_MAP_LOADED = True
    except Exception as e:
        print(f"⚠️ خطا در بارگذاری اولیه نگاشت پیام‌ها در رم: {e}", flush=True)

def save_msg_mapping(route_id, tg_chat_id, tg_msg_id, platform, dest_chat_id, dest_msg_id, msg_type, media_id=""):
    global _MSG_MAP_CACHE, _MSG_MAP_DIRTY
    if not DATABASE_URL or not dest_msg_id:
        return
    if not _MSG_MAP_LOADED:
        load_all_msg_mappings()
    clean_cid = std_id(tg_chat_id)
    try:
        r_id = int(route_id)
        m_id = int(tg_msg_id)
        plat = str(platform)
        d_cid = str(dest_chat_id)
        val = (str(dest_msg_id), str(msg_type), str(media_id))
        key = (r_id, clean_cid, m_id)
        with _MSG_MAP_LOCK:
            if key not in _MSG_MAP_CACHE:
                _MSG_MAP_CACHE[key] = {}
            _MSG_MAP_CACHE[key][(plat, d_cid)] = val
            _MSG_MAP_DIRTY[(r_id, clean_cid, m_id, plat, d_cid)] = val
    except Exception as e:
        print(f"⚠️ خطا در ذخیره نگاشت پیام در رم: {e}", flush=True)

def get_msg_mappings(route_id, tg_chat_id, tg_msg_id):
    if not DATABASE_URL:
        return []
    if not _MSG_MAP_LOADED:
        load_all_msg_mappings()
    clean_cid = std_id(tg_chat_id)
    try:
        key = (int(route_id), clean_cid, int(tg_msg_id))
        with _MSG_MAP_LOCK:
            dest_map = _MSG_MAP_CACHE.get(key, {})
            return [(plat, d_cid, val[0], val[1], val[2]) for (plat, d_cid), val in dest_map.items()]
    except Exception as e:
        print(f"⚠️ خطا در واکشی نگاشت پیام از رم: {e}", flush=True)
        return []

# ----------------- توابع ادمین (فقط روی رم) -----------------
def load_all_admins():
    global _ADMINS_CACHE, _ADMINS_LOADED
    if not _ADMINS_LOADED:
        try:
            conn = psycopg2.connect(DATABASE_URL)
            cursor = conn.cursor()
            cursor.execute("SELECT admin_id FROM router_admins")
            for row in cursor.fetchall():
                _ADMINS_CACHE.add(str(row[0]))
            conn.close()
        except Exception:
            pass
        if str(ADMIN_ID) != "0":
            _ADMINS_CACHE.add(str(ADMIN_ID))
        if EXTRA_ADMINS:
            for ex in EXTRA_ADMINS.split(","):
                if ex.strip(): _ADMINS_CACHE.add(ex.strip())
        _ADMINS_LOADED = True

def get_all_admins():
    if not _ADMINS_LOADED: load_all_admins()
    return list(_ADMINS_CACHE)

def add_admin(new_id):
    global _ADMINS_CACHE, _ADMINS_CHANGED
    if not _ADMINS_LOADED: load_all_admins()
    _ADMINS_CACHE.add(str(new_id))
    _ADMINS_CHANGED = True
    return True

def remove_admin(del_id):
    global _ADMINS_CACHE, _ADMINS_CHANGED
    if not _ADMINS_LOADED: load_all_admins()
    if str(del_id) in _ADMINS_CACHE:
        _ADMINS_CACHE.remove(str(del_id))
        _ADMINS_CHANGED = True
        return True
    return False

# ----------------- توابع مسیرها (فقط روی رم) -----------------
def get_routes():
    global _ROUTES_CACHE, _ROUTES_LOADED
    if not _ROUTES_LOADED:
        try:
            conn = psycopg2.connect(DATABASE_URL)
            cursor = conn.cursor()
            cursor.execute('''
            SELECT id, name, src_channels, bale_channels, rubika_channels, 
            custom_prompt, blacklist, use_ai_media, 
            COALESCE(bale_max_size, 45), COALESCE(rubika_max_size, 45),
            COALESCE(ai_enabled, TRUE), COALESCE(ai_add_hashtags, FALSE), COALESCE(ai_translation, ''),
            COALESCE(bale_enabled, TRUE), COALESCE(rubika_enabled, TRUE),
            COALESCE(allow_no_caption, TRUE),
            COALESCE(eitaa_channels, ''), COALESCE(eitaa_max_size, 50), COALESCE(eitaa_enabled, TRUE),
            COALESCE(bale_delay, FALSE), COALESCE(rubika_delay, FALSE), COALESCE(eitaa_delay, TRUE)
            FROM router_routes ORDER BY id ASC
            ''')
            _ROUTES_CACHE = cursor.fetchall()
            conn.close()
            _ROUTES_LOADED = True
        except Exception as e: 
            print(f"❌ خطا در بارگذاری مسیرها: {e}")
            return []
    return _ROUTES_CACHE

def update_route_field(route_id, field_column, value):
    global _ROUTES_CACHE, _ROUTES_CHANGED
    if not _ROUTES_LOADED: get_routes()
    
    col_to_idx = {
        "name": 1, "src_channels": 2, "bale_channels": 3, "rubika_channels": 4,
        "custom_prompt": 5, "blacklist": 6, "use_ai_media": 7, "bale_max_size": 8,
        "rubika_max_size": 9, "ai_enabled": 10, "ai_add_hashtags": 11,
        "ai_translation": 12, "bale_enabled": 13, "rubika_enabled": 14,
        "allow_no_caption": 15,
        "eitaa_channels": 16, "eitaa_max_size": 17, "eitaa_enabled": 18,
        "bale_delay": 19, "rubika_delay": 20, "eitaa_delay": 21
    }
    
    idx = col_to_idx.get(field_column)
    if idx is not None:
        for i, r in enumerate(_ROUTES_CACHE):
            if str(r[0]) == str(route_id):
                new_r = list(r)
                while len(new_r) <= idx:
                    new_r.append(True)
                new_r[idx] = value
                _ROUTES_CACHE[i] = tuple(new_r)
                _ROUTES_CHANGED = True
                break

# ----------------- توابع وضعیت پیام‌ها (ایزوله شده بر اساس مسیر) -----------------
def load_all_states():
    global _STATE_CACHE
    try:
        conn = psycopg2.connect(DATABASE_URL)
        cursor = conn.cursor()
        cursor.execute("SELECT channel_id, last_msg_id FROM router_channel_state")
        rows = cursor.fetchall()
        conn.close()
        for r in rows:
            # در سیستم جدید، channel_id در واقع رشته ترکیبی r{route_id}_c{channel_id} است
            _STATE_CACHE[str(r[0])] = r[1]
    except Exception:
        pass

# --- یکسان‌سازی آیدی‌های تلگرام برای رفع مشکل دوگانگی ---
def std_id(cid):
    s = str(cid)
    if s.startswith("-100"): return s[4:]
    if s.startswith("-"): return s[1:]
    return s

def get_last_processed_id(route_id, channel_id):
    key = f"r{route_id}_c{std_id(channel_id)}"
    return _STATE_CACHE.get(key, 0)

def set_last_processed_id(route_id, channel_id, msg_id):
    global _STATE_CACHE, _STATE_CHANGED
    key = f"r{route_id}_c{std_id(channel_id)}"
    if _STATE_CACHE.get(key) != msg_id:
        _STATE_CACHE[key] = msg_id
        _STATE_CHANGED = True

# ----------------- شبیه‌ساز دقیق تابع idle در Pyrogram برای اجرای atexit -----------------
async def custom_idle():
    stop_event = asyncio.Event()
    loop = asyncio.get_event_loop()
    
    def signal_handler():
        stop_event.set()
        
    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            loop.add_signal_handler(sig, signal_handler)
        except NotImplementedError:
            pass
            
    await stop_event.wait()

# ----------------- همگام‌ساز نهایی (هنگام ریستارت) -----------------
def flush_all_to_db():
    global _STATE_CACHE, _STATE_CHANGED, _ADMINS_CACHE, _ADMINS_CHANGED, _ROUTES_CACHE, _ROUTES_CHANGED, _MSG_MAP_DIRTY
    
    with _MSG_MAP_LOCK:
        has_msg_map_changes = bool(_MSG_MAP_DIRTY)
        dirty_items = list(_MSG_MAP_DIRTY.items()) if has_msg_map_changes else []

    if not _STATE_CHANGED and not _ADMINS_CHANGED and not _ROUTES_CHANGED and not has_msg_map_changes:
        return

    try:
        conn = psycopg2.connect(DATABASE_URL)
        cursor = conn.cursor()
        
        if _STATE_CHANGED:
            for cid, mid in _STATE_CACHE.items():
                cursor.execute('''
                INSERT INTO router_channel_state (channel_id, last_msg_id) 
                VALUES (%s, %s) ON CONFLICT (channel_id) DO UPDATE SET last_msg_id = EXCLUDED.last_msg_id
                ''', (str(cid), mid))
            _STATE_CHANGED = False
            
        if _ADMINS_CHANGED:
            cursor.execute("DELETE FROM router_admins")
            for admin_id in _ADMINS_CACHE:
                cursor.execute("INSERT INTO router_admins (admin_id) VALUES (%s)", (str(admin_id),))
            _ADMINS_CHANGED = False
            
        if _ROUTES_CHANGED:
            cursor.execute("DELETE FROM router_routes")
            for r in _ROUTES_CACHE:
                cursor.execute('''
                INSERT INTO router_routes 
                (id, name, src_channels, bale_channels, rubika_channels, custom_prompt, blacklist, use_ai_media, bale_max_size, rubika_max_size, ai_enabled, ai_add_hashtags, ai_translation, bale_enabled, rubika_enabled, allow_no_caption, eitaa_channels, eitaa_max_size, eitaa_enabled, bale_delay, rubika_delay, eitaa_delay) 
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                ''', (r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11], r[12], r[13], r[14], (r[15] if len(r)>15 else True), (r[16] if len(r)>16 else ''), (r[17] if len(r)>17 else 50), (r[18] if len(r)>18 else True), (r[19] if len(r)>19 else False), (r[20] if len(r)>20 else False), (r[21] if len(r)>21 else True)))
            _ROUTES_CHANGED = False

        if dirty_items:
            for (r_id, clean_cid, m_id, plat, d_cid), (d_mid, m_type, med_id) in dirty_items:
                cursor.execute('''
                    INSERT INTO router_msg_map (route_id, tg_chat_id, tg_msg_id, platform, dest_chat_id, dest_msg_id, msg_type, media_id)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                    ON CONFLICT (route_id, tg_chat_id, tg_msg_id, platform, dest_chat_id)
                    DO UPDATE SET dest_msg_id = EXCLUDED.dest_msg_id, msg_type = EXCLUDED.msg_type, media_id = EXCLUDED.media_id, created_at = CURRENT_TIMESTAMP
                ''', (r_id, clean_cid, m_id, plat, d_cid, d_mid, m_type, med_id))
            with _MSG_MAP_LOCK:
                for k, _ in dirty_items:
                    _MSG_MAP_DIRTY.pop(k, None)

        conn.commit()
        conn.close()
        print("✅ تمامی اطلاعات رم (پیام‌ها، نگاشت‌ها، ادمین‌ها و مسیرها) با موفقیت در دیتابیس ذخیره شد.", flush=True)
    except Exception as e:
        print(f"❌ خطای همگام‌سازی دیتابیس در زمان خروج: {e}", flush=True)

atexit.register(flush_all_to_db)

init_router_db()

def is_ffmpeg_installed():
    try:
        subprocess.run(["ffmpeg", "-version"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
        return True
    except Exception:
        print("❌ ابزار ffmpeg در سیستم یافت نشد.", flush=True)
        return False

def get_media_duration(file_path):
    try:
        result = subprocess.run(["ffprobe", "-v", "error", "-show_entries",
                                 "format=duration", "-of",
                                 "default=noprint_wrappers=1:nokey=1", file_path],
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE,
                                text=True)
        return float(result.stdout.strip())
    except Exception as e:
        print(f"⚠️ خطا در خواندن مدت زمان ({file_path}): {e}", flush=True)
        return None

def compress_media(input_path, output_path, target_size_mb, file_type):
    if not is_ffmpeg_installed():
        return False

    duration = get_media_duration(input_path)
    if not duration or duration <= 0:
        print("❌ امکان تعیین مدت زمان برای فشرده‌سازی این فایل وجود ندارد.", flush=True)
        return False

    # حاشیه امنیت بیشتر: 80 درصد حجم هدف به جای 85 درصد برای اطمینان صد درصدی
    safe_target_size_mb = float(target_size_mb) * 0.80
    target_total_bitrate_kbps = (safe_target_size_mb * 8192) / duration
    is_video = (file_type == 'video')

    print(f"🗜 شروع فشرده‌سازی مدیا... حجم: {os.path.getsize(input_path)/(1024*1024):.2f}MB | هدف: <{safe_target_size_mb:.2f}MB | زمان: {duration:.0f} ثانیه", flush=True)

    try:
        if is_video:
            # تخصیص هوشمند بیت‌ریت بر اساس طول ویدیو
            if target_total_bitrate_kbps < 64:
                audio_bitrate_kbps = 16  # کیفیت پایین صدا برای فیلم‌های بسیار طولانی
            elif target_total_bitrate_kbps < 128:
                audio_bitrate_kbps = 32
            else:
                audio_bitrate_kbps = 48
                
            target_video_bitrate_kbps = int(target_total_bitrate_kbps - audio_bitrate_kbps)
            if target_video_bitrate_kbps < 10:
                target_video_bitrate_kbps = 10 # حداقل ممکن برای فرونپاشیدن تصویر
            
            orig_size_mb = os.path.getsize(input_path) / (1024 * 1024)
            ratio = orig_size_mb / safe_target_size_mb
            
            vf_scale = ""
            fps = ""
            # فیلترهای بی‌رحمانه برای فیلم‌های حجیم و طولانی
            if ratio > 10 or target_video_bitrate_kbps < 50:
                vf_scale = "scale=-2:240"
                fps = "10" # کاهش فریم ریت به 10 برای جلوگیری از شطرنجی شدن مطلق
            elif ratio > 5 or target_video_bitrate_kbps < 150:
                vf_scale = "scale=-2:360"
                fps = "15"
            elif ratio > 2:
                vf_scale = "scale=-2:480"
                fps = "24"

            command = [
                "ffmpeg", "-y", "-i", input_path,
                "-map", "0:v:0",  # فقط اولین لاین تصویر (حذف کاورها و ویدیوهای اضافه)
                "-map", "0:a:0?", # فقط اولین لاین صدا (حذف دوبله‌های اضافه)
                "-c:v", "libx264",
                "-b:v", f"{target_video_bitrate_kbps}k",
                "-maxrate", f"{target_video_bitrate_kbps}k",
                "-bufsize", f"{target_video_bitrate_kbps * 2}k",
                "-preset", "faster" # بهتر از veryfast برای رعایت دقیق حجم نهایی
            ]
            
            if vf_scale:
                command.extend(["-vf", vf_scale])
            if fps:
                command.extend(["-r", fps])
                
            command.extend([
                "-c:a", "aac",
                "-b:a", f"{audio_bitrate_kbps}k",
                output_path
            ])
        else:
            target_audio_bitrate_kbps = max(16, int(target_total_bitrate_kbps))
            command = [
                "ffmpeg", "-y", "-i", input_path,
                "-vn", 
                "-c:a", "aac",
                "-b:a", f"{target_audio_bitrate_kbps}k",
                output_path
            ]
            
        process = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        
        if process.returncode != 0:
            print(f"❌ خطای FFmpeg در حین فشرده‌سازی: {process.stderr[-300:]}", flush=True)
            return False

        if os.path.exists(output_path):
            new_size = os.path.getsize(output_path) / (1024 * 1024)
            print(f"✅ فشرده‌سازی موفقیت‌آمیز بود. حجم جدید: {new_size:.2f} MB", flush=True)
            return True
        return False
        
    except Exception as e:
        print(f"❌ خطای نامشخص در فشرده‌سازی: {e}", flush=True)
        return False

async def process_with_ai(text, custom_prompt, smart_filter, media_paths=None, ai_enabled=True, ai_hashtags=False, ai_translation=""):
    if not ai_enabled: return text or ""
    # بررسی می‌کنیم که آیا متن یا فایلی وجود دارد یا خیر
    if not text and not media_paths: return ""
    if not GEMINI_API_KEY: return text or ""
    
    if not custom_prompt and not smart_filter and not ai_hashtags and not ai_translation and not media_paths:
        return text or ""

    try:
        sys_msg = "تو یک دستیار هوشمند هستی.\n"
        
        if smart_filter:
            sys_msg += f"مرحله اول (فیلتر هوشمند): به دقت بررسی کن آیا محتوای کاربر با این شرط/قانون مغایرت دارد: ({smart_filter})\n"
            sys_msg += "⚠️ اگر محتوا کاملاً مغایرت داشت یا غیرمجاز بود، فقط و فقط کلمه 'FILTERED' را برگردان و هیچ تغییر دیگری (حتی هشتگ) اعمال نکن.\n"
            
        step_two = []
        if custom_prompt:
            step_two.append(f"این دستور/فرمان را روی محتوا اجرا کن: {custom_prompt}")
        if ai_translation:
            step_two.append(f"متن نهایی را با لحنی روان به زبان '{ai_translation}' ترجمه کن.")
        if ai_hashtags:
            step_two.append("در انتهای متن، ۳ الی ۵ هشتگ کاملاً مرتبط با موضوع استخراج و اضافه کن.")
            
        if step_two:
            sys_msg += f"مرحله دوم: اگر محتوا کاملاً مجاز بود، تغییرات زیر را به ترتیب روی آن اعمال کن:\n- " + "\n- ".join(step_two) + "\n"
        else:
            sys_msg += f"مرحله دوم: اگر محتوا کاملاً مجاز بود، دقیقاً همان محتوای اصلی را عینا تکرار کن.\n"

        user_text = text or 'محتوای متنی وجود ندارد (فایل‌ها پیوست شده‌اند).'
        parts = [{"text": user_text}]

        # پشتیبانی از آلبوم‌ها (تبدیل به لیست در صورت نیاز)
        if media_paths and not isinstance(media_paths, list):
            media_paths = [media_paths]
            
        if media_paths:
            for path in media_paths[:5]:
                if path and os.path.exists(path):
                    file_size_mb = os.path.getsize(path) / (1024 * 1024)
                    mime_type, _ = mimetypes.guess_type(path)
                    if not mime_type: mime_type = "application/octet-stream"
                    
                    supported_prefixes = ('image/', 'video/', 'audio/', 'application/', 'text/')
                    if mime_type.startswith(supported_prefixes) and file_size_mb <= 19.5:
                        try:
                            def read_file_sync(p=path):
                                with open(p, "rb") as f:
                                    return base64.b64encode(f.read()).decode('utf-8')
                            
                            b64_data = await asyncio.to_thread(read_file_sync)
                            parts.append({"inlineData": {"mimeType": mime_type, "data": b64_data}})
                        except Exception as e:
                            print(f"⚠️ خطا در پردازش فایل آلبوم: {e}", flush=True)

        models = [
            "gemini-3.7-flash", "gemini-3.6-flash", "gemini-3.5-flash", 
            "gemini-3.5-flash-lite", "gemini-2.5-flash", "gemini-3-flash-preview", 
            "gemini-3.1-pro-preview", "gemini-2.5-pro"
        ]
        
        payload = {
            "system_instruction": {"parts": [{"text": sys_msg}]},
            "contents": [{"role": "user", "parts": parts}]
        }

        async with aiohttp.ClientSession() as session:
            for m in models:
                url = f"https://generativelanguage.googleapis.com/v1beta/models/{m}:generateContent?key={GEMINI_API_KEY}"
                for attempt in range(3):
                    try:
                        async with session.post(url, json=payload, timeout=45) as res:
                            if res.status == 200:
                                data = await res.json()
                                candidates = data.get('candidates', [])
                                if not candidates:
                                    # اینجا فیلتر را برنمی‌گردانیم چون ممکن است پاسخ خالی به خاطر ارور باشد
                                    return text or ""
                                
                                content_parts = candidates[0].get('content', {}).get('parts', [])
                                if not content_parts: return text or ""
                                    
                                result_text = content_parts[0].get('text', '').strip()
                                if "FILTERED" in result_text.upper():
                                    return "FILTERED"
                                    
                                return result_text
                                
                            elif res.status == 429:
                                wait_time = (attempt + 1) * 5 
                                print(f"⏳ لیمیت گوگل (429) روی {m}. تلاش {attempt+1}/3... مکث {wait_time} ثانیه", flush=True)
                                await asyncio.sleep(wait_time)
                                continue
                            elif res.status == 404:
                                break
                            else:
                                break
                    except asyncio.TimeoutError:
                        print(f"⏳ تایم‌اوت جمینی روی {m} (تلاش {attempt+1})", flush=True)
                        await asyncio.sleep(2)
                        continue
                    except Exception:
                        break
                        
        # +++ اگر تمام حلقه‌ها تمام شد و به اینجا رسیدیم، یعنی گوگل کاملا از دسترس خارج است +++
        print("❌ تمام تلاش‌های ارتباط با سرورهای هوش مصنوعی با شکست مواجه شد.", flush=True)
        return "__API_ERROR__"
                
    except Exception as e:
        print(f"❌ خطای سراسری در تابع هوش مصنوعی: {e}", flush=True)
        return "__API_ERROR__"

async def notify_admin(post_link, platform, reason):
    try:
        admins = get_all_admins()
        if admins:
            await bot_app.send_message(int(admins[0]), f"⚠️ **خطا در انتقال پست**\n\nلینک پست اصلی: {post_link or 'نامشخص'}\nمقصد: {platform}\nعلت:\n`{reason}`")
    except: pass

def format_channel_id(c_id):
    c_id = c_id.strip()
    if not c_id: return ""
    c_id = re.sub(r'[^a-zA-Z0-9_\-@]', '', c_id)
    if not c_id.startswith('@') and not c_id.startswith('-') and not c_id.isdigit():
        c_id = '@' + c_id
    return c_id

def get_mime_type(file_name, media_type):
    mime_type, _ = mimetypes.guess_type(file_name)
    if mime_type: return mime_type
    if media_type == 'video': return 'video/mp4'
    if media_type == 'photo': return 'image/jpeg'
    if media_type == 'audio': return 'audio/mpeg'
    if media_type == 'voice': return 'audio/ogg'
    return 'application/octet-stream'

# ==========================================
# سیستم مدیریت پیام‌های در حال پردازش و قفل همزمانی
# ==========================================
_MSG_PROCESSING_LOCKS = {}
_MSG_LOCKS_GUARD = asyncio.Lock()
_IN_FLIGHT_MSGS = set()
_IN_FLIGHT_GUARD = asyncio.Lock()

async def get_msg_lock(chat_id, msg_or_id):
    cid = std_id(chat_id)
    if hasattr(msg_or_id, 'grouped_id') and msg_or_id.grouped_id:
        key = f"{cid}_grp_{msg_or_id.grouped_id}"
    elif hasattr(msg_or_id, 'id'):
        key = f"{cid}_msg_{msg_or_id.id}"
    else:
        key = f"{cid}_msg_{msg_or_id}"
        
    async with _MSG_LOCKS_GUARD:
        if len(_MSG_PROCESSING_LOCKS) > 2000:
            unlocked_keys = [k for k, v in _MSG_PROCESSING_LOCKS.items() if not v.locked()]
            for k in unlocked_keys[:1000]:
                del _MSG_PROCESSING_LOCKS[k]
        if key not in _MSG_PROCESSING_LOCKS:
            _MSG_PROCESSING_LOCKS[key] = asyncio.Lock()
        return _MSG_PROCESSING_LOCKS[key]

def get_telegram_media_id(message):
    try:
        if not message or not getattr(message, 'media', None):
            return ""
        if getattr(message, 'photo', None):
            return f"photo_{message.photo.id}"
        if getattr(message, 'video', None):
            return f"video_{message.video.id}"
        if getattr(message, 'document', None):
            return f"doc_{message.document.id}"
        if getattr(message, 'audio', None):
            return f"audio_{message.audio.id}"
        if getattr(message, 'voice', None):
            return f"voice_{message.voice.id}"
        return "media_other"
    except Exception:
        return ""

def delete_from_bale(channel_id, message_id):
    if not BALE_TOKEN or not message_id: return False
    channel_id = format_channel_id(channel_id)
    try:
        res = _bale_eitaa_post(f"https://tapi.bale.ai/bot{BALE_TOKEN}/deleteMessage", 
                               json={'chat_id': channel_id, 'message_id': int(message_id)}, 
                               proxies=DIRECT_PROXY, timeout=(10, 20))
        return res.status_code == 200 and res.json().get("ok", False)
    except Exception: 
        return False

def delete_from_rubika(channel_id, message_id):
    if not RUBIKA_TOKEN or not message_id: return False
    channel_id = format_channel_id(channel_id)
    try:
        res = _rubika_post(f"https://botapi.rubika.ir/v3/{RUBIKA_TOKEN}/deleteMessage", 
                           json={'chat_id': channel_id, 'message_id': str(message_id)}, 
                           headers={"User-Agent": "Mozilla/5.0"}, 
                           proxies=DIRECT_PROXY, timeout=(10, 20))
        return res.status_code == 200 and res.json().get("status") == "OK"
    except Exception: 
        return False

def send_text_to_bale(text, channel_id):
    if not BALE_TOKEN or not text: return True, "توکن یا متن خالی است"
    channel_id = format_channel_id(channel_id)
    print(f"🔄 در حال ارسال متن به بله ({channel_id})...", flush=True)
    
    last_err = ""
    # +++ افزودن حلقه تلاش مجدد (حداکثر ۳ بار) +++
    for attempt in range(1, 4):
        try:
            res = _bale_eitaa_post(f"https://tapi.bale.ai/bot{BALE_TOKEN}/sendMessage", json={'chat_id': channel_id, 'text': text}, proxies=DIRECT_PROXY, timeout=(10, 30))
            if res.status_code == 200:
                print(f"✅ متن با موفقیت به بله ({channel_id}) ارسال شد.", flush=True)
                msg_id = res.json().get("result", {}).get("message_id")
                return True, str(msg_id)
            
            err_detail = f"HTTP {res.status_code} - Body: {res.text}"
            last_err = err_detail
            print(f" ⚠️ تلاش {attempt}: خطای بله در ارسال متن: {err_detail}", flush=True)
            
        except Exception as e: 
            err_detail = f"Exception: {str(e)}"
            last_err = err_detail
            print(f" ⚠️ تلاش {attempt}: استثنا در شبکه برای بله: {err_detail}", flush=True)
        
        # وقفه ۳ ثانیه‌ای پیش از تلاش مجدد
        time.sleep(3)
        
    print(f"❌ تمام تلاش‌ها برای ارسال متن به بله ({channel_id}) شکست خورد.", flush=True)
    return False, last_err
    
def send_single_media_to_bale(caption, channel_id, file_path, file_name, media_type):
    if not BALE_TOKEN: return True, "توکن بله خالی است"
    channel_id = format_channel_id(channel_id)
    
    file_key = 'video' if media_type == 'video' else ('document' if media_type == 'document' else ('audio' if media_type in ['audio', 'voice'] else 'photo'))
    url = f"https://tapi.bale.ai/bot{BALE_TOKEN}/send{file_key.capitalize()}"
    mime_type = get_mime_type(file_name, media_type)
    
    print(f"🔄 در حال ارسال تک‌فایل ({file_key} - {file_name}) به بله ({channel_id})...", flush=True)
    
    last_err = ""
    # +++ حلقه تلاش مجدد برای تک‌فایل +++
    for attempt in range(1, 4):
        try:
            # فایل درون حلقه باز می‌شود تا در صورت خطا، مجدداً از ابتدا خوانده شود
            with open(file_path, 'rb') as f:
                files = {file_key: (file_name, f, mime_type)}
                res = _bale_eitaa_post(url, data={'chat_id': channel_id, 'caption': caption}, files=files, proxies=DIRECT_PROXY, timeout=(15, 60))
                
                if res.status_code == 200:
                    print(f"✅ تک‌فایل با موفقیت به بله ({channel_id}) ارسال شد.", flush=True)
                    msg_id = res.json().get("result", {}).get("message_id")
                    return True, str(msg_id)
                
                err_detail = f"HTTP {res.status_code} - Body: {res.text}"
                last_err = err_detail
                print(f" ⚠️ تلاش {attempt}: خطای بله در ارسال فایل: {err_detail}", flush=True)
        except Exception as e:
            err_detail = f"Exception: {str(e)}"
            last_err = err_detail
            print(f" ⚠️ تلاش {attempt}: استثنا در ارسال فایل به بله: {err_detail}", flush=True)
            
        time.sleep(3)
        
    print(f"❌ تمام تلاش‌ها برای ارسال فایل به بله ({channel_id}) شکست خورد.", flush=True)
    return False, last_err

def send_album_to_bale(caption, channel_id, files_list):
    if not BALE_TOKEN: return True, "توکن بله خالی است"
    channel_id = format_channel_id(channel_id)
    print(f"🔄 در حال ارسال آلبوم ({len(files_list)} فایل) به بله ({channel_id})...", flush=True)
    
    media_json = []
    files_dict = {}
    opened_files = []

    try:
        for idx, f_obj in enumerate(files_list):
            if idx >= 10: break 
            attach_name = f"file{idx}"
            m_type = 'video' if f_obj['type'] == 'video' else ('document' if f_obj['type'] == 'document' else 'photo')
            file_name = f_obj['name']
            mime_type = get_mime_type(file_name, f_obj['type'])
            
            media_item = {"type": m_type, "media": f"attach://{attach_name}"}
            if idx == 0 and caption: 
                media_item["caption"] = caption
            media_json.append(media_item)

            f = open(f_obj['path'], 'rb')
            opened_files.append(f)
            files_dict[attach_name] = (file_name, f, mime_type)

        last_err = ""
        needs_fallback = False
        
        # +++ حلقه تلاش مجدد برای ارسال آلبوم +++
        for attempt in range(1, 4):
            try:
                # برگرداندن نشانگرِ خواندن تمام فایل‌ها به نقطه صفر پیش از هر تلاش
                for f in opened_files: f.seek(0)
                
                res = _bale_eitaa_post(f"https://tapi.bale.ai/bot{BALE_TOKEN}/sendMediaGroup", data={"chat_id": channel_id, "media": json.dumps(media_json)}, files=files_dict, proxies=DIRECT_PROXY, timeout=(15, 120))
                
                if res.status_code == 200:
                    print(f"✅ آلبوم با موفقیت به بله ({channel_id}) ارسال شد.", flush=True)
                    result_list = res.json().get("result", [])
                    first_id = result_list[0].get("message_id") if result_list else ""
                    return True, str(first_id)
                                    
                if res.status_code == 400 and "UNSUPPORTED_FILE" in res.text:
                    print(f"⚠️ خطای بله در ارسال آلبوم (UNSUPPORTED_FILE). تغییر استراتژی به ارسال تکی...", flush=True)
                    needs_fallback = True
                    break # این یک خطای دائمی است، حلقه تلاش مجدد را می‌شکنیم تا به بخش Fallback برود
                
                err_detail = f"HTTP {res.status_code} - Body: {res.text}"
                last_err = err_detail
                print(f" ⚠️ تلاش {attempt}: خطای بله در ارسال آلبوم: {err_detail}", flush=True)
                
            except Exception as e:
                err_detail = f"Exception: {str(e)}"
                last_err = err_detail
                print(f" ⚠️ تلاش {attempt}: استثنا در شبکه برای آلبوم بله: {err_detail}", flush=True)
                
            time.sleep(3)

        # اجرای استراتژی جایگزین (ارسال تکی) در صورت شکست آلبوم
        if needs_fallback:
            print(f"⚠️ در حال ارسال فایل‌های آلبوم به صورت تکی (Fallback)...", flush=True)
            all_ok = True
            first_sent_id = ""
            for idx, f_obj in enumerate(files_list):
                if idx >= 10: break
                c = caption if idx == 0 else ""
                s_ok, s_id = send_single_media_to_bale(c, channel_id, f_obj['path'], f_obj['name'], f_obj['type'])
                if not s_ok:
                    all_ok = False
                    last_err = s_id
                elif idx == 0 and s_id:
                    first_sent_id = s_id
                time.sleep(1)
                
            if all_ok:
                return True, str(first_sent_id)
            return False, f"خطا در ارسال تکی پس از شکست آلبوم: {last_err}"

        print(f"❌ تمام تلاش‌ها برای ارسال آلبوم به بله ({channel_id}) شکست خورد.", flush=True)
        return False, last_err

    finally:
        for f in opened_files: f.close()

def utf16_len(s):
    return len(s.encode('utf-16-le')) // 2

def parse_markdown_to_rubika(md_text):
    if not md_text:
        return "", None

    current_text = str(md_text)
    meta_parts = []

    patterns = [
        (re.compile(r'\[([^\]\n]+)\]\((https?://[^\s\)]+|tg://[^\s\)]+|[^\)]+)\)'), 'Link', True),
        (re.compile(r'```(?:\w+\n)?([\s\S]+?)```'), 'Pre', False),
        (re.compile(r'`([^`\n]+)`'), 'Mono', False),
        # در دو خط زیر، [^\[\]\n] اضافه شده تا بولد و ایتالیک داخل لینک‌ها نفوذ نکنند
        (re.compile(r'\*\*([^*\[\]\n]+)\*\*|__([^_\[\]\n]+)__'), 'Bold', False),
        (re.compile(r'(?<!\*)\*([^*\[\]\n]+)\*(?!\*)|(?<!_)_([^_\[\]\n]+)_(?!_)'), 'Italic', False),
        (re.compile(r'\|\|([^|]+)\|\|'), 'Spoiler', False),
        (re.compile(r'~~([^~]+)~~|~([^~]+)~'), 'Strike', False),
    ]

    while True:
        earliest_match = None
        earliest_pos = None
        matched_pattern_info = None

        for regex, r_type, has_url in patterns:
            m = regex.search(current_text)
            if m:
                if earliest_pos is None or m.start() < earliest_pos:
                    earliest_pos = m.start()
                    earliest_match = m
                    matched_pattern_info = (r_type, has_url)

        if not earliest_match:
            break

        r_type, has_url = matched_pattern_info
        start_char_idx = earliest_match.start()
        end_char_idx = earliest_match.end()

        prefix = current_text[:start_char_idx]
        from_index = utf16_len(prefix)

        if has_url:
            raw_label = earliest_match.group(1)
            url = earliest_match.group(2)
            clean_label = re.sub(r'[\*\_\`~\|]', '', raw_label)
            replacement = clean_label
            match_len = utf16_len(replacement)

            meta_parts.append({
                "type": r_type,
                "from_index": from_index,
                "length": match_len,
                "link_url": url
            })
        else:
            content = earliest_match.group(1) or (earliest_match.group(2) if earliest_match.lastindex and earliest_match.lastindex >= 2 else "")
            clean_content = re.sub(r'[\*\_\`~\|]', '', content)
            replacement = clean_content
            match_len = utf16_len(replacement)

            meta_parts.append({
                "type": r_type,
                "from_index": from_index,
                "length": match_len
            })

        current_text = current_text[:start_char_idx] + replacement + current_text[end_char_idx:]

        if len(meta_parts) >= 30:
            break

    metadata = {"meta_data_parts": meta_parts} if meta_parts else None
    return current_text, metadata

def send_text_to_rubika(text, channel_id, reply_to_message_id=None):
    if not RUBIKA_TOKEN or not text: return True, "توکن یا متن روبیکا خالی است"
    channel_id = format_channel_id(channel_id)
    text = str(text).strip()
    if not text: return True, ""

    plain_text, metadata = parse_markdown_to_rubika(text)
    if not plain_text: return True, ""
    if len(plain_text) > 4000: plain_text = plain_text[:4000] + "..."
    print(f"🔄 در حال ارسال متن به روبیکا ({channel_id})...", flush=True)
 
    headers = {"User-Agent": "Mozilla/5.0"}
    payload = {"chat_id": channel_id, "text": plain_text}
    if metadata:
        payload["metadata"] = metadata
        
    # +++ این دو خط برای پشتیبانی از ریپلای اضافه شد +++
    if reply_to_message_id:
        payload["reply_to_message_id"] = str(reply_to_message_id)
    # +++ پایان +++

    try:
        res_obj = _rubika_post(
            f"https://botapi.rubika.ir/v3/{RUBIKA_TOKEN}/sendMessage",
            json=payload,
            headers=headers,
            proxies=DIRECT_PROXY,
            timeout=(10, 30)
        )
        try:
            res = res_obj.json()
            if res.get('status') == 'OK':
                print(f"✅ متن با موفقیت به روبیکا ({channel_id}) ارسال شد.", flush=True)
                msg_id = res.get("data", {}).get("message_id") or res.get("message_id")
                return True, str(msg_id)
            err_detail = f"API Error: {res}"
            print(f"❌ خطای روبیکا در ارسال متن: {err_detail}", flush=True)
            return False, err_detail
        except Exception:
            err_detail = f"HTTP {res_obj.status_code} - Invalid JSON: {res_obj.text[:100]}"
            print(f"❌ پاسخ نامعتبر روبیکا: {err_detail}", flush=True)
            return False, err_detail
    except Exception as e:
        err_detail = f"Network Exception: {e}"
        print(f"❌ استثنا در ارتباط با روبیکا: {err_detail}", flush=True)
        return False, err_detail


# =======================================================================
# بخش اختصاصی پیام‌رسان ایتا (Eitaa - سامانه ایتایار)
# =======================================================================

def format_text_for_eitaa(text):
    """تبدیل تگ‌های HTML تلگرام به استایل مارک‌داون استاندارد و لینک‌های ایتا"""
    if not text: return ""
    text = str(text)
    
    # ۱. تبدیل هایپرلینک‌های HTML: <a href="url">text</a> -> [text](url)
    def repl_a(m):
        href = m.group(1).strip()
        link_text = m.group(2).strip() or href
        return f"[{link_text}]({href})"
    text = re.sub(r'<a\s+(?:[^>]*?\s+)?href=["\'](.*?)["\'][^>]*>(.*?)</a>', repl_a, text, flags=re.DOTALL | re.IGNORECASE)
    
    # ۲. تبدیل بولد HTML: <b>...</b> و <strong>...</strong> -> **...**
    text = re.sub(r'<(?:b|strong)[^>]*>(.*?)</(?:b|strong)>', r'**\1**', text, flags=re.DOTALL | re.IGNORECASE)
    
    # ۳. تبدیل ایتالیک HTML: <i>...</i> و <em>...</em> -> __...__
    text = re.sub(r'<(?:i|em)[^>]*>(.*?)</(?:i|em)>', r'__\1__', text, flags=re.DOTALL | re.IGNORECASE)
    
    # ۴. تبدیل کد و پیش‌فرمت HTML: <code>...</code> -> `...` و <pre>...</pre> -> ```...```
    text = re.sub(r'<pre[^>]*>(.*?)</pre>', r'```\n\1\n```', text, flags=re.DOTALL | re.IGNORECASE)
    text = re.sub(r'<code[^>]*>(.*?)</code>', r'`\1`', text, flags=re.DOTALL | re.IGNORECASE)
    
    # ۵. تبدیل خط جدید HTML
    text = re.sub(r'<br\s*/?>', '\n', text, flags=re.IGNORECASE)
    
    # ۶. حذف سایر تگ‌های HTML باقیمانده بدون تغییر محتوا (مانند <u>, <s>, <span> و غیره)
    text = re.sub(r'</?[a-zA-Z][^>]*>', '', text)
    
    return text.strip()

def extract_inline_button_links(message):
    """استخراج دکمه‌های شیشه‌ای لینک‌دار از پیام تلگرام"""
    links = []
    try:
        reply_markup = getattr(message, 'reply_markup', None)
        if reply_markup and hasattr(reply_markup, 'rows'):
            for row in reply_markup.rows:
                for btn in getattr(row, 'buttons', []):
                    url = getattr(btn, 'url', None)
                    text = getattr(btn, 'text', None)
                    if url and text:
                        links.append((text.strip(), url.strip()))
    except Exception as e:
        print(f"⚠️ خطا در استخراج دکمه‌های شیشه‌ای: {e}", flush=True)
    return links

def extract_poll_as_text(message, msg_link=""):
    """تبدیل نظرسنجی و کوئیز تلگرام به پیام متنی شکیل همراه با ایموجی"""
    try:
        poll_media = getattr(message, 'media', None)
        if not poll_media or not hasattr(poll_media, 'poll'):
            return None
        poll_obj = poll_media.poll
        q = getattr(poll_obj.question, 'text', None) or str(getattr(poll_obj, 'question', 'نظرسنجی'))
        
        emoji_numbers = ["1️⃣", "2️⃣", "3️⃣", "4️⃣", "5️⃣", "6️⃣", "7️⃣", "8️⃣", "9️⃣", "🔟"]
        lines = [f"📊 **نظرسنجی:**\n«{q}»\n"]
        
        answers = getattr(poll_obj, 'answers', [])
        for idx, ans in enumerate(answers):
            ans_text = getattr(ans.text, 'text', None) or str(getattr(ans, 'text', ''))
            prefix = emoji_numbers[idx] if idx < len(emoji_numbers) else f"▫️ {idx+1}."
            lines.append(f"{prefix} {ans_text}")
            
        if msg_link and msg_link != "نامشخص":
            lines.append(f"\n🗳 [شرکت در نظرسنجی در تلگرام]({msg_link})")
            
        return "\n".join(lines)
    except Exception as e:
        print(f"⚠️ خطا در تبدیل نظرسنجی به متن: {e}", flush=True)
        return None

def extract_geo_as_text(message):
    """تبدیل موقعیت مکانی تلگرام به متن و لینک‌های نقشه"""
    try:
        media = getattr(message, 'media', None)
        geo = getattr(media, 'geo', None)
        if geo and hasattr(geo, 'lat') and hasattr(geo, 'long'):
            lat, lon = geo.lat, geo.long
            neshan_url = f"https://neshan.org/maps/@{lat},{lon},15z"
            google_url = f"https://maps.google.com/?q={lat},{lon}"
            return (f"📍 **موقعیت مکانی:**\n"
                    f"مختصات: `{lat}, {lon}`\n\n"
                    f"🗺 [مشاهده در نشان]({neshan_url})\n"
                    f"🌍 [مشاهده در گوگل‌مپ]({google_url})")
    except Exception as e:
        print(f"⚠️ خطا در استخراج موقعیت مکانی: {e}", flush=True)
    return None

def extract_contact_as_text(message):
    """تبدیل کارت مخاطب تلگرام به متن حاوی نام و شماره"""
    try:
        media = getattr(message, 'media', None)
        if media and hasattr(media, 'phone_number'):
            phone = getattr(media, 'phone_number', '')
            fn = getattr(media, 'first_name', '') or ''
            ln = getattr(media, 'last_name', '') or ''
            name = f"{fn} {ln}".strip() or "مخاطب"
            return (f"👤 **کارت مخاطب:**\n"
                    f"نام: **{name}**\n"
                    f"شماره تماس: `{phone}`")
    except Exception as e:
        print(f"⚠️ خطا در استخراج کارت مخاطب: {e}", flush=True)
    return None

def convert_ogg_to_mp3(input_path, output_path):
    """تبدیل ویس OGG تلگرام به فایل صوتی استاندارد MP3"""
    if not is_ffmpeg_installed(): return False
    try:
        cmd = ["ffmpeg", "-y", "-i", input_path, "-c:a", "libmp3lame", "-q:a", "4", output_path]
        res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return res.returncode == 0 and os.path.exists(output_path) and os.path.getsize(output_path) > 0
    except Exception as e:
        print(f"⚠️ خطا در تبدیل ویس به mp3: {e}", flush=True)
        return False

def convert_video_to_gif(input_path, output_path):
    """تبدیل استیکر ویدیویی WebM به فایل گیف متحرک"""
    if not is_ffmpeg_installed(): return False
    try:
        cmd = ["ffmpeg", "-y", "-i", input_path, "-vf", "fps=15,scale=320:-1:flags=lanczos", "-c:v", "gif", output_path]
        res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return res.returncode == 0 and os.path.exists(output_path) and os.path.getsize(output_path) > 0
    except Exception as e:
        print(f"⚠️ خطا در تبدیل ویدیو به گیف: {e}", flush=True)
        return False

def clean_eitaa_channel(c_id):
    """پاکسازی آیدی کانال ایتا از لینک و کاراکترهای اضافه"""
    if not c_id: return ""
    c_id = str(c_id).strip()
    c_id = re.sub(r'^https?://(?:www\.)?eitaa\.com/', '', c_id, flags=re.IGNORECASE)
    c_id = re.sub(r'^eitaa\.com/', '', c_id, flags=re.IGNORECASE)
    c_id = c_id.lstrip('@').strip()
    c_id = re.sub(r'[^a-zA-Z0-9_\-]', '', c_id)
    return c_id

async def notify_admin_all_platforms(text):
    """ارسال اخطار فوری به ادمین در تلگرام و بله و چاپ در کنسول"""
    print(f"\n📢 اخطار سیستم:\n{text}\n", flush=True)
    
    # ۱. تلگرام
    try:
        admins = get_all_admins()
        for a in admins:
            if a and str(a).isdigit():
                try:
                    await bot_app.send_message(int(a), text)
                except Exception:
                    try:
                        await user_app.send_message(int(a), text)
                    except Exception as e_tg:
                        print(f"⚠️ خطا در ارسال اخطار به ادمین در تلگرام: {e_tg}", flush=True)
    except Exception as e:
        print(f"⚠️ خطا در ارسال اخطار به ادمین در تلگرام: {e}", flush=True)

    # ۲. بله
    try:
        bale_admin = os.environ.get("BALE_ADMIN_ID", "").strip()
        if BALE_TOKEN and bale_admin and bale_admin.lstrip('-').isdigit():
            await asyncio.to_thread(send_to_platform, "bale", int(bale_admin), text, None)
    except Exception as e:
        print(f"⚠️ خطا در ارسال اخطار به ادمین در بله: {e}", flush=True)

def send_text_to_eitaa(text, channel_id):
    """ارسال متن ساده به کانال ایتا"""
    if not EITAA_TOKEN: return True, "توکن ایتا تنظیم نشده"
    channel_id = clean_eitaa_channel(channel_id)
    if not channel_id: return False, "شناسه کانال ایتا خالی است"
    
    text = format_text_for_eitaa(text)
    token = EITAA_TOKEN.strip()
    url = f"https://eitaayar.ir/api/{token}/sendMessage"
    print(f"🔄 در حال ارسال متن به ایتا (@{channel_id})...", flush=True)
    payload = {"chat_id": channel_id, "text": text}
    
    for attempt in range(1, 4):
        try:
            res = _bale_eitaa_post(url, data=payload, proxies=DIRECT_PROXY, timeout=30)
            if res.status_code == 200:
                try:
                    data = res.json()
                    if data.get("ok"):
                        msg_id = str(data.get("result", {}).get("message_id") or "")
                        print(f"✅ متن با موفقیت به ایتا (@{channel_id}) ارسال شد.", flush=True)
                        return True, msg_id
                    err_msg = data.get("description", str(data))
                    print(f" ❌ خطای پاسخ ایتا (@{channel_id}): {err_msg}", flush=True)
                    if attempt < 3: time.sleep(3)
                    else: return False, err_msg
                except Exception as json_err:
                    err_msg = f"پاسخ غیر JSON از ایتا: {res.text[:120]}"
                    print(f" ❌ {err_msg}", flush=True)
                    if attempt < 3: time.sleep(3)
                    else: return False, err_msg
            else:
                err_msg = f"HTTP {res.status_code}: {res.text[:120]}"
                print(f" ❌ خطای سرور ایتا (@{channel_id}): {err_msg}", flush=True)
                if attempt < 3: time.sleep(3)
                else: return False, err_msg
        except Exception as e:
            err_msg = f"استثنا در ارتباط با ایتا: {e}"
            print(f" ❌ {err_msg}", flush=True)
            if attempt < 3: time.sleep(3)
            else: return False, err_msg
            
    return False, "تلاش‌های مکرر برای ارسال متن به ایتا ناموفق بود"

def process_eitaa_media(caption, channel_id, file_path, file_name, media_type='photo'):
    """ارسال فایل مدیا به ایتا با متد sendFile"""
    if not EITAA_TOKEN: return True, "توکن ایتا تنظیم نشده"
    channel_id = clean_eitaa_channel(channel_id)
    if not channel_id: return False, "شناسه کانال ایتا خالی است"
    caption = format_text_for_eitaa(caption) if caption else ""
    
    # برای گیف طبق مستندات ایتایار پسوند باید .gif باشد
    if media_type == 'gif' and not file_name.lower().endswith('.gif'):
        file_name = os.path.splitext(file_name)[0] + '.gif'
        
    token = EITAA_TOKEN.strip()
    url = f"https://eitaayar.ir/api/{token}/sendFile"
    
    for attempt in range(1, 4):
        try:
            print(f" ➤ [تلاش {attempt}] ارسال فایل ({file_name}) به ایتا (@{channel_id})...", flush=True)
            with open(file_path, 'rb') as f:
                files = {'file': (file_name, f)}
                data = {
                    'chat_id': channel_id,
                    'caption': caption,
                    'title': file_name
                }
                res = _bale_eitaa_post(url, files=files, data=data, proxies=DIRECT_PROXY, timeout=120)
                
            if res.status_code == 200:
                resp_json = res.json()
                if resp_json.get("ok"):
                    msg_id = str(resp_json.get("result", {}).get("message_id") or "")
                    print(f"✅ فایل با موفقیت به ایتا (@{channel_id}) ارسال شد.", flush=True)
                    return True, msg_id
                else:
                    err_msg = resp_json.get("description", str(resp_json))
                    print(f" ❌ خطای ایتا: {err_msg}", flush=True)
                    if attempt < 3: time.sleep(3)
                    else: return False, err_msg
            else:
                err_msg = f"HTTP {res.status_code}: {res.text[:120]}"
                print(f" ❌ خطای سرور ایتا: {err_msg}", flush=True)
                if attempt < 3: time.sleep(3)
                else: return False, err_msg
        except Exception as e:
            err_msg = f"استثنا در پروسه ایتا: {e}"
            print(f" ❌ خطا: {err_msg}", flush=True)
            if attempt < 3: time.sleep(3)
            else: return False, err_msg
    return False, "تلاش‌های مکرر ناموفق بود"

async def run_delayed_sender(q_key, delay_seconds=600):
    """تسک زمان‌بندی‌شده برای ارسال محتوا به مقاصد دارای تاخیر پس از ۱۰ دقیقه"""
    try:
        await asyncio.sleep(delay_seconds)
        item = _DELAY_QUEUE.pop(q_key, None)
        if not item: return
        
        r_id = item["route_id"]
        cid_clean = item["cid_clean"]
        main_msg_id = item["main_msg_id"]
        caption = item["caption"]
        pending_dir = item["pending_dir"]
        messages = item["messages"]
        chat_username = item.get("chat_username", cid_clean)
        msg_link = item.get("msg_link", "")
        delayed_platforms = item.get("platforms", [])
        
        try:
            # ۱. ارسال به روبیکا در صورت وجود در صف تاخیر
            if "rubika" in delayed_platforms:
                r_rubika = item.get("r_rubika", "")
                r_files = item.get("rubika_files", [])
                rubika_dests = [format_channel_id(x) for x in r_rubika.split(',') if x.strip()]
                for r_channel in rubika_dests:
                    if r_files:
                        total_files = len(r_files)
                        for idx, file_obj in enumerate(r_files):
                            is_last = (idx == total_files - 1)
                            cap = caption if is_last else ""
                            rubika_success, rubika_res = await asyncio.to_thread(process_rubika_media, cap, r_channel, file_obj['path'], file_obj['name'], file_obj['type'])
                            if rubika_success:
                                if rubika_res and is_last:
                                    for m in messages:
                                        save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'rubika', r_channel, rubika_res, 'media', get_telegram_media_id(m) if hasattr(m, 'id') else "")
                            else:
                                await notify_admin(msg_link, f"روبیکا ({r_channel})", f"خطا:\n{rubika_res}")
                            await asyncio.sleep(2)
                    elif caption:
                        rubika_success, rubika_res = await asyncio.to_thread(send_text_to_rubika, caption, r_channel)
                        if rubika_success and rubika_res:
                            for m in messages:
                                save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'rubika', r_channel, rubika_res, 'text', "")
                        elif not rubika_success:
                            await notify_admin(msg_link, f"روبیکا ({r_channel})", f"خطا:\n{rubika_res}")
                        await asyncio.sleep(2)

            # ۲. ارسال به بله در صورت وجود در صف تاخیر
            if "bale" in delayed_platforms:
                r_bale = item.get("r_bale", "")
                b_files = item.get("bale_files", [])
                bale_dests = [format_channel_id(x) for x in r_bale.split(',') if x.strip()]
                for b_channel in bale_dests:
                    bale_success = True
                    bale_res = None
                    if len(b_files) > 1:
                        bale_success, bale_res = await asyncio.to_thread(send_album_to_bale, caption, b_channel, b_files)
                        if bale_success and bale_res:
                            for m in messages:
                                save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'bale', b_channel, bale_res, 'album', get_telegram_media_id(m) if hasattr(m, 'id') else "")
                    elif len(b_files) == 1:
                        f_obj = b_files[0]
                        bale_success, bale_res = await asyncio.to_thread(send_single_media_to_bale, caption, b_channel, f_obj['path'], f_obj['name'], f_obj['type'])
                        if bale_success and bale_res:
                            for m in messages:
                                save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'bale', b_channel, bale_res, 'media', get_telegram_media_id(m) if hasattr(m, 'id') else "")
                    elif caption:
                        bale_success, bale_res = await asyncio.to_thread(send_text_to_bale, caption, b_channel)
                        if bale_success and bale_res:
                            for m in messages:
                                save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'bale', b_channel, bale_res, 'text', "")
                    
                    if not bale_success:
                        await notify_admin(msg_link, f"بله ({b_channel})", f"خطا:\n{bale_res}")
                    await asyncio.sleep(3)

            # ۳. ارسال به ایتا در صورت وجود در صف تاخیر (همراه با مدیریت محدودیت ۱۰۲۴ کاراکتر کپشن)
            if "eitaa" in delayed_platforms:
                r_eitaa = item.get("r_eitaa", "")
                e_files = item.get("eitaa_files", [])
                eitaa_dests = [clean_eitaa_channel(x) for x in r_eitaa.split(',') if clean_eitaa_channel(x)]
                
                eitaa_caption = format_text_for_eitaa(caption)
                is_long_caption = len(eitaa_caption) > 1024

                for e_channel in eitaa_dests:
                    eitaa_success = True
                    if e_files:
                        total_f = len(e_files)
                        for idx, f_obj in enumerate(e_files):
                            is_last = (idx == total_f - 1)
                            # در صورت طولانی بودن کپشن (>1024)، کپشن روی فایل الصاق نمی‌شود تا متن ناقص نشود
                            cap = (eitaa_caption if not is_long_caption else "") if is_last else ""
                            success, res = await asyncio.to_thread(process_eitaa_media, cap, e_channel, f_obj['path'], f_obj['name'], f_obj['type'])
                            if success:
                                if res and is_last:
                                    for m in messages:
                                        save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'eitaa', e_channel, res, 'media', get_telegram_media_id(m) if hasattr(m, 'id') else "")
                            else:
                                eitaa_success = False
                                await notify_admin_all_platforms(f"⚠️ **خطا در ارسال با تاخیر به ایتا**\n\nکانال مبدا: {chat_username}\nمقصد ایتا: {e_channel}\nعلت: {res}\nلینک: {msg_link}")
                            await asyncio.sleep(2)
                            
                        # اگر کپشن بیش از ۱۰۲۴ کاراکتر بود، کل متن بلافاصله پس از فایل‌ها به صورت پیام متنی ارسال می‌شود
                        if is_long_caption and eitaa_caption:
                            print(f"📄 کپشن طولانی ({len(eitaa_caption)} کاراکتر) به صورت پیام متنی مجزا به ایتا ارسال می‌شود...", flush=True)
                            t_success, t_res = await asyncio.to_thread(send_text_to_eitaa, eitaa_caption, e_channel)
                            if not t_success:
                                await notify_admin_all_platforms(f"⚠️ **خطا در ارسال متن طولانی با تاخیر به ایتا**\n\nکانال مبدا: {chat_username}\nمقصد ایتا: {e_channel}\nعلت: {t_res}\nلینک: {msg_link}")
                            await asyncio.sleep(2)
                            
                    elif eitaa_caption:
                        success, res = await asyncio.to_thread(send_text_to_eitaa, eitaa_caption, e_channel)
                        if success and res:
                            for m in messages:
                                save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'eitaa', e_channel, res, 'text', "")
                        elif not success:
                            await notify_admin_all_platforms(f"⚠️ **خطا در ارسال با تاخیر به ایتا**\n\nکانال مبدا: {chat_username}\nمقصد ایتا: {e_channel}\nعلت: {res}\nلینک: {msg_link}")
                    await asyncio.sleep(2)

        finally:
            if pending_dir and os.path.exists(pending_dir):
                shutil.rmtree(pending_dir, ignore_errors=True)
                
    except asyncio.CancelledError:
        pass
    except Exception as e:
        print(f"❌ خطا در پردازش تسک صف تاخیر ({q_key}): {e}", flush=True)
def process_rubika_media(caption, channel_id, file_path, file_name, media_type='photo'):
    if not RUBIKA_TOKEN: return True, "توکن روبیکا تنظیم نشده"
    
    channel_id = format_channel_id(channel_id)
    caption = str(caption).strip() if caption else ""
    
    plain_caption, metadata = parse_markdown_to_rubika(caption) if caption else ("", None)
    print(f"🔄 در حال ارسال فایل ({file_name}) به روبیکا ({channel_id})...", flush=True)
    
    # سیستم جداسازی هوشمند کپشن‌های طولانی
    send_as_separate_text = False
    if plain_caption and len(plain_caption) > 1000:
        print(f"⚠️ کپشن طولانی است ({len(plain_caption)} کاراکتر). تصویر بدون کپشن و متن به صورت پیام جداگانه ارسال خواهد شد.", flush=True)
        send_as_separate_text = True
        plain_caption = "" # خالی کردن کپشن برای ارسال موفق فایل
        metadata = None    # حذف متادیتا از فایل
    
    file_bytes_size = os.path.getsize(file_path)
    mime_type = get_mime_type(file_name, media_type)
    
    if media_type == 'video': original_file_type = "Video"
    elif media_type in ['document', 'audio', 'voice']: original_file_type = "File" 
    else: original_file_type = "Image"
    
    headers = {"User-Agent": "Mozilla/5.0"}
    types_to_try = [original_file_type]
    if original_file_type != "File":
        types_to_try.append("File")
        
    try:
        with open(file_path, 'rb') as f:
            file_data = f.read()
    except Exception as e:
        return False, f"خطا در خواندن فایل از دیسک: {e}"

    last_err = ""
    for current_type in types_to_try:
        for attempt in range(1, 4): 
            try:
                print(f" ➤ [تلاش {attempt}] دریافت لینک آپلود (نوع: {current_type})...", flush=True)
                req_res = _rubika_post(
                    f"https://botapi.rubika.ir/v3/{RUBIKA_TOKEN}/requestSendFile",
                    json={"type": current_type, "size": file_bytes_size, "file_name": file_name},
                    headers=headers,
                    proxies=DIRECT_PROXY,
                    timeout=(10, 20)
                )
                try: res = req_res.json()
                except: 
                    last_err = f"خطای پارس جیسون درخواست آپلود: {req_res.text[:100]}"
                    print(f" ❌ خطا: {last_err}", flush=True)
                    time.sleep(3); continue
                    
                if res.get('status') != 'OK':
                    last_err = f"درخواست آپلود رد شد: {res}"
                    print(f" ❌ خطا: {last_err}", flush=True)
                    time.sleep(3); continue
                    
                upload_url = res.get('data', {}).get('upload_url')
                if not upload_url: 
                    last_err = f"لینک آپلود در خروجی یافت نشد: {res}"
                    print(f" ❌ خطا: {last_err}", flush=True)
                    time.sleep(3); continue
                    
                print(f" ➤ [تلاش {attempt}] آپلود در سرور روبیکا (حجم: {file_bytes_size/(1024*1024):.2f}MB)...", flush=True)
                try:
                    up_res_raw = _rubika_post(
                        upload_url,
                        files={'file': (file_name, file_data, mime_type)}, 
                        headers=headers,
                        proxies=DIRECT_PROXY,
                        timeout=(15, 120)
                    )
                except Exception as upload_err:
                    last_err = f"خطای شبکه در آپلود: {upload_err}"
                    print(f" ❌ خطا: {last_err}", flush=True)
                    time.sleep(3); continue
                    
                try: up_res = up_res_raw.json()
                except: 
                    last_err = f"خطای پارس جیسون هنگام آپلود: {up_res_raw.text[:100]}"
                    print(f" ❌ خطا: {last_err}", flush=True)
                    time.sleep(3); continue
                    
                if up_res.get('status') != 'OK':
                    last_err = f"آپلود در سرور روبیکا ناموفق: {up_res}"
                    print(f" ❌ خطا: {last_err}", flush=True)
                    time.sleep(3); continue
                    
                file_id = up_res.get('data', {}).get('file_id')
                if file_id:
                    print(f" ➤ [تلاش {attempt}] ارسال نهایی پست به کانال روبیکا...", flush=True)
                    payload = {"chat_id": channel_id, "file_id": file_id}
                    if plain_caption:
                        payload["text"] = plain_caption
                    if metadata:
                        payload["metadata"] = metadata
                        
                    send_res = _rubika_post(
                        f"https://botapi.rubika.ir/v3/{RUBIKA_TOKEN}/sendFile",
                        json=payload,
                        headers=headers,
                        proxies=DIRECT_PROXY,
                        timeout=(10, 30)
                    )
                    
                    try: res_send = send_res.json()
                    except: 
                        last_err = f"خطای پارس جیسون ارسال نهایی: {send_res.text[:100]}"
                        print(f" ❌ خطا: {last_err}", flush=True)
                        time.sleep(3); continue
                        
                    if res_send.get('status') == 'OK':
                        print(f"✅ فایل با موفقیت به روبیکا ({channel_id}) ارسال شد.", flush=True)
                        
                        sent_data = res_send.get('data', {}) if isinstance(res_send.get('data'), dict) else {}
                        sent_message_id = sent_data.get('message_id') or res_send.get('message_id')
                        
                        # در صورتی که کپشن جداگانه فرستاده شده باشد، آیدی متن را برای ویرایش‌های بعدی برمی‌گردانیم
                        if send_as_separate_text:
                            time.sleep(1)
                            s_ok, s_id = send_text_to_rubika(caption, channel_id, reply_to_message_id=sent_message_id)
                            if s_ok and s_id:
                                return True, str(s_id)
                                
                        return True, str(sent_message_id or "")
                    else:
                        last_err = f"ارسال نهایی به چت ناموفق بود: {res_send}"
                        print(f" ❌ خطا: {last_err}", flush=True)
            except Exception as e:
                last_err = f"استثنا در پروسه روبیکا: {e}"
                print(f" ❌ خطا: {last_err}", flush=True)
            time.sleep(3)
            
    print(f"❌ تمام تلاش‌ها برای ارسال به روبیکا شکست خورد. آخرین ارور: {last_err}", flush=True)
    return False, last_err

def edit_text_to_bale(text, channel_id, message_id):
    if not BALE_TOKEN or not text or not message_id: return False, "پارامترهای ناقص"
    channel_id = format_channel_id(channel_id)
    print(f"🔄 در حال ویرایش متن پیام در بله ({channel_id} - پیام {message_id})...", flush=True)
    payload = {'chat_id': channel_id, 'message_id': int(message_id), 'text': text}
    try:
        res = _bale_eitaa_post(f"https://tapi.bale.ai/bot{BALE_TOKEN}/editMessageText", json=payload, proxies=DIRECT_PROXY, timeout=(10, 30))
        if res.status_code == 200 and res.json().get("ok"):
            print(f"✅ متن پیام در بله با موفقیت ویرایش شد.", flush=True)
            return True, ""
        return False, f"HTTP {res.status_code} - {res.text}"
    except Exception as e:
        return False, str(e)

def edit_caption_to_bale(caption, channel_id, message_id):
    if not BALE_TOKEN or not message_id: return False, "پارامترهای ناقص"
    channel_id = format_channel_id(channel_id)
    print(f"🔄 در حال ویرایش زیرنویس (کپشن) پیام در بله ({channel_id} - پیام {message_id})...", flush=True)
    payload = {'chat_id': channel_id, 'message_id': int(message_id), 'caption': caption or ""}
    try:
        res = _bale_eitaa_post(f"https://tapi.bale.ai/bot{BALE_TOKEN}/editMessageCaption", json=payload, proxies=DIRECT_PROXY, timeout=(10, 30))
        if res.status_code == 200 and res.json().get("ok"):
            print(f"✅ زیرنویس در بله با موفقیت ویرایش شد.", flush=True)
            return True, ""
        return False, f"HTTP {res.status_code} - {res.text}"
    except Exception as e:
        return False, str(e)

def edit_text_to_rubika(text, channel_id, message_id):
    if not RUBIKA_TOKEN or not text or not message_id: return False, "پارامترهای ناقص"
    channel_id = format_channel_id(channel_id)
    text = str(text).strip()
    plain_text, metadata = parse_markdown_to_rubika(text)
    if not plain_text: return True, ""
    if len(plain_text) > 4000: plain_text = plain_text[:4000] + "..."
    print(f"🔄 در حال ویرایش پیام در روبیکا ({channel_id} - پیام {message_id})...", flush=True)
    headers = {"User-Agent": "Mozilla/5.0"}
    payload = {"chat_id": channel_id, "message_id": str(message_id), "text": plain_text}
    if metadata:
        payload["metadata"] = metadata
    try:
        res_obj = _rubika_post(f"https://botapi.rubika.ir/v3/{RUBIKA_TOKEN}/editMessageText", json=payload, headers=headers, proxies=DIRECT_PROXY, timeout=(10, 30))
        res = res_obj.json()
        if res.get('status') == 'OK':
            print(f"✅ پیام در روبیکا با موفقیت ویرایش شد.", flush=True)
            return True, ""
        return False, f"API Error: {res}"
    except Exception as e:
        return False, str(e)

if not SESSION_STRING or not CONTROL_BOT_TOKEN:
    print("❌ ارور: SESSION_STRING یا CONTROL_BOT_TOKEN یافت نشد!", flush=True)
    exit(1)

# --- تغییرات ۱: اضافه کردن پارامترهای هویتی کلاینت (Spoofing Device Info) ---
user_app = TelegramClient(
    StringSession(SESSION_STRING), 
    TELEGRAM_API_ID, 
    TELEGRAM_API_HASH,
    device_model="PC 64bit",
    system_version="Windows 11",
    app_version="4.8.1",
    lang_code="en",
    system_lang_code="en"
)
user_app.parse_mode = 'md'
# کلاینت ربات مدیریت
bot_app = TelegramClient("admin_bot", TELEGRAM_API_ID, TELEGRAM_API_HASH)
bot_app.parse_mode = 'md'

admin_states = {}
media_groups_cache = {}
_PROCESSED_MEDIA_GROUPS = []

def get_main_keyboard():
    return [
        [Button.inline("➕ ساخت مسیر جدید", b"add_route")],
        [Button.inline("📋 مشاهده و ویرایش مسیرها", b"list_routes")],
        [Button.inline("👥 مدیریت دسترسی ادمین‌ها", b"manage_admins")]
    ]

def get_cancel_keyboard():
    return [[Button.inline("❌ لغو", b"cancel_action")]]

def get_ai_keyboard(route_id, ai_enabled, use_ai_media, ai_hashtags):
    kb = []
    ai_status = "فعال 🟢" if ai_enabled else "غیرفعال 🔴"
    
    kb.append([Button.inline(f"سوییچ اصلی هوش مصنوعی: {ai_status}", f"ai_toggle_{route_id}".encode('utf-8'))])
    
    if ai_enabled:
        media_st = "روشن 🟢" if use_ai_media else "خاموش 🔴"
        hash_st = "روشن 🟢" if ai_hashtags else "خاموش 🔴"
        
        kb.append([Button.inline("🤖 دستور اختصاصی (Prompt)", f"edit_{route_id}_prompt".encode('utf-8'))])
        kb.append([Button.inline("🚫 فیلتر هوشمند (کلمات/مفاهیم)", f"edit_{route_id}_blacklist".encode('utf-8'))])
        kb.append([Button.inline(f"👁 تحلیل تصویر/فایل: {media_st}", f"ai_media_{route_id}".encode('utf-8'))])
        kb.append([Button.inline(f"#️⃣ هشتگ‌ساز خودکار: {hash_st}", f"ai_hashtag_{route_id}".encode('utf-8'))])
        kb.append([Button.inline("🌐 زبان ترجمه", f"edit_{route_id}_aitrans".encode('utf-8'))])
        
    kb.append([Button.inline("🔙 بازگشت به منوی مسیر", f"select_edit_{route_id}".encode('utf-8'))])
    return kb

def get_route_main_keyboard(route_id):
    return [
        [Button.inline("⚙️ تنظیمات مسیر", f"route_settings_{route_id}".encode('utf-8')),
         Button.inline("🤖 تنظیمات هوش مصنوعی (AI)", f"ai_menu_{route_id}".encode('utf-8'))],
        [Button.inline("⬇️ فراخوانی پیام‌های گذشته", f"fetch_menu_{route_id}".encode('utf-8'))],
        [Button.inline("🗑 حذف کامل این مسیر", f"del_route_{route_id}".encode('utf-8'))],
        [Button.inline("🔙 بازگشت به لیست مسیرها", b"list_routes")]
    ]

def get_edit_keyboard(route_id, bale_en=True, rubika_en=True, allow_no_caption=True, eitaa_en=True, bale_delay=False, rubika_delay=False, eitaa_delay=True):
    bale_status = "روشن 🟢" if bale_en else "خاموش 🔴"
    rubika_status = "روشن 🟢" if rubika_en else "خاموش 🔴"
    eitaa_status = "روشن 🟢" if eitaa_en else "خاموش 🔴"
    no_cap_status = "روشن 🟢" if allow_no_caption else "خاموش 🔴"
    
    b_del_text = "۱۰ دقیقه ⏳" if bale_delay else "فوری ⚡️"
    r_del_text = "۱۰ دقیقه ⏳" if rubika_delay else "فوری ⚡️"
    e_del_text = "۱۰ دقیقه ⏳" if eitaa_delay else "فوری ⚡️"
    
    return [
        [Button.inline("✏️ تغییر نام مسیر", f"edit_{route_id}_name".encode('utf-8'))],
        [Button.inline("📡 مبدا تلگرام", f"edit_{route_id}_src".encode('utf-8'))],
        [Button.inline(f"ارسال بله: {bale_status}", f"toggle_{route_id}_baleen".encode('utf-8')),
         Button.inline(f"ارسال روبیکا: {rubika_status}", f"toggle_{route_id}_rubikaen".encode('utf-8')),
         Button.inline(f"ارسال ایتا: {eitaa_status}", f"toggle_{route_id}_eitaaen".encode('utf-8'))],
        [Button.inline(f"تاخیر بله: {b_del_text}", f"toggle_{route_id}_baledelay".encode('utf-8')),
         Button.inline(f"تاخیر روبیکا: {r_del_text}", f"toggle_{route_id}_rubikadelay".encode('utf-8')),
         Button.inline(f"تاخیر ایتا: {e_del_text}", f"toggle_{route_id}_eitaadelay".encode('utf-8'))],
        [Button.inline(f"ارسال فایل و آلبوم بدون کپشن: {no_cap_status}", f"toggle_{route_id}_nocap".encode('utf-8'))],
        [Button.inline("🎯 مقصد بله", f"edit_{route_id}_bale".encode('utf-8')),
         Button.inline("🎯 مقصد روبیکا", f"edit_{route_id}_rubika".encode('utf-8')),
         Button.inline("🎯 مقصد ایتا", f"edit_{route_id}_eitaa".encode('utf-8'))],
        [Button.inline("📦 حجم بله (MB)", f"edit_{route_id}_balemax".encode('utf-8')),
         Button.inline("📦 حجم روبیکا (MB)", f"edit_{route_id}_rubikamax".encode('utf-8')),
         Button.inline("📦 حجم ایتا (MB)", f"edit_{route_id}_eitaamax".encode('utf-8'))],
        [Button.inline("🔙 بازگشت به منوی مسیر", f"select_edit_{route_id}".encode('utf-8'))]
    ]
def get_fetch_target_keyboard(route_id, count):
    return [
        [Button.inline("🟡 بله", f"run_fetch_{route_id}_{count}_bale".encode('utf-8')),
         Button.inline("🟣 روبیکا", f"run_fetch_{route_id}_{count}_rubika".encode('utf-8')),
         Button.inline("🟠 ایتا", f"run_fetch_{route_id}_{count}_eitaa".encode('utf-8'))],
        [Button.inline("🌐 همه مقاصد", f"run_fetch_{route_id}_{count}_all".encode('utf-8'))],
        [Button.inline("🔙 بازگشت به منوی مسیر", f"select_edit_{route_id}".encode('utf-8'))]
    ]

@bot_app.on(events.NewMessage(func=lambda e: e.is_private))
async def admin_handler(event):
    message = event.message
    if str(message.chat_id) not in get_all_admins():
        return
        
    text = event.raw_text or event.text or ""
    chat_id = event.chat_id
    
    state = admin_states.get(chat_id, {}).get("step")
    
    if text == "/start":
        admin_states[chat_id] = {}
        admin_states[str(chat_id)] = {}
        msg = "👋 **به پنل مدیریت حرفه‌ای خوش آمدید.**\nاز طریق دکمه‌های زیر، مسیرهای انتقال را مدیریت کنید:"
        await message.reply(msg, buttons=get_main_keyboard())
        return

    clean_text = text.strip()
    if clean_text in ["❌ لغو", "لغو", "cancel"]:
        admin_states[chat_id] = {}
        admin_states[str(chat_id)] = {}
        await message.reply("❌ عملیات لغو شد.", buttons=get_main_keyboard())
        return

    if clean_text in ["🔙 بازگشت", "بازگشت", "منوی اصلی", "🔙 بازگشت به منوی اصلی"]:
        admin_states[chat_id] = {}
        admin_states[str(chat_id)] = {}
        await message.reply("👋 بازگشت به منوی اصلی:", buttons=get_main_keyboard())
        return

    if clean_text in ["➕ ساخت مسیر جدید", "ساخت مسیر جدید", "ساخت مسیر"]:
        admin_states[chat_id] = {"step": "WAITING_ROUTE_NAME"}
        admin_states[str(chat_id)] = {"step": "WAITING_ROUTE_NAME"}
        await message.reply("✏️ مرحله ۱: لطفاً یک **نام دلخواه** برای مسیر بفرستید:", buttons=get_cancel_keyboard())
        return

    if clean_text in ["📋 مشاهده و ویرایش مسیرها", "مشاهده و ویرایش مسیرها", "لیست مسیرها"]:
        routes = get_routes()
        if not routes:
            await message.reply("هیچ مسیری ثبت نشده است.", buttons=get_main_keyboard())
            return
        buttons = [[Button.inline(f"⚙️ {r[1]}", f"select_edit_{r[0]}".encode('utf-8'))] for r in routes]
        buttons.append([Button.inline("🔙 بازگشت", b"main_menu")])
        await message.reply("📋 مسیر مورد نظر را انتخاب کنید:", buttons=buttons)
        return

    if clean_text in ["👥 مدیریت دسترسی ادمین‌ها", "مدیریت دسترسی ادمین‌ها", "مدیریت ادمین"]:
        admins = get_all_admins()
        msg = "👥 **لیست ادمین‌های فعلی سیستم:**\n" + "\n".join([f"🔸 `{a}`" for a in admins])
        kb = [
            [Button.inline("➕ افزودن ادمین جدید", b"add_admin_prompt")],
            [Button.inline("➖ حذف یک ادمین", b"del_admin_prompt")],
            [Button.inline("🔙 بازگشت به منوی اصلی", b"main_menu")]
        ]
        await message.reply(msg, buttons=kb)
        return

    if state == "WAITING_ROUTE_NAME":
        admin_states[chat_id]["name"] = text
        admin_states[chat_id]["step"] = "WAITING_SRC"
        await message.reply("✅ مرحله ۲:\nلطفاً آیدی کانال‌های **مبدا در تلگرام** را بفرستید (با ویرگول جدا کنید):", buttons=get_cancel_keyboard())
        
    elif state == "WAITING_SRC":
        admin_states[chat_id]["src"] = text
        admin_states[chat_id]["step"] = "WAITING_BALE"
        await message.reply("✅ مرحله ۳:\nآیدی کانال‌های **مقصد در بله** را بفرستید:", buttons=get_cancel_keyboard())
        
    elif state == "WAITING_BALE":
        admin_states[chat_id]["bale"] = text
        admin_states[chat_id]["step"] = "WAITING_RUBIKA"
        await message.reply("✅ مرحله ۴:\nآیدی کانال‌های **مقصد در روبیکا** را بفرستید:", buttons=get_cancel_keyboard())
        
    elif state == "WAITING_RUBIKA":
        admin_states[chat_id]["rubika"] = text
        admin_states[chat_id]["step"] = "WAITING_EITAA"
        await message.reply("✅ مرحله ۵:\nآیدی کانال‌های **مقصد در ایتا** را بفرستید (یا 'خاموش' بفرستید):", buttons=get_cancel_keyboard())
        
    elif state == "WAITING_EITAA":
        admin_states[chat_id]["eitaa"] = text
        admin_states[chat_id]["step"] = "WAITING_PROMPT"
        await message.reply("✅ مرحله ۶ (آخر):\nآیا این مسیر دستور خاصی برای هوش مصنوعی دارد؟ (در غیر اینصورت لغو را بزنید یا رد کنید)", buttons=get_cancel_keyboard())
        
    elif state == "WAITING_PROMPT":
        admin_states[chat_id]["prompt"] = text
        await save_route_and_finish(message, admin_states[chat_id])
        
    elif state == "WAITING_ADD_ADMIN":
        if text.isdigit():
            if add_admin(text):
                await message.reply(f"✅ ادمین با آیدی `{text}` با موفقیت اضافه شد.", buttons=get_main_keyboard())
            else:
                await message.reply("❌ خطایی رخ داد.", buttons=get_main_keyboard())
        else:
            await message.reply("❌ آیدی باید کاملاً عددی باشد.", buttons=get_cancel_keyboard())
        admin_states[chat_id] = {}
        
    elif state == "WAITING_REMOVE_ADMIN":
        if text.isdigit():
            if remove_admin(text):
                await message.reply(f"✅ دسترسی ادمین با آیدی `{text}` قطع شد.", buttons=get_main_keyboard())
            else:
                await message.reply("❌ خطایی رخ داد.", buttons=get_main_keyboard())
        else:
            await message.reply("❌ آیدی باید کاملاً عددی باشد.", buttons=get_cancel_keyboard())
        admin_states[chat_id] = {}

    elif state == "WAITING_FETCH_COUNT":
        route_id = admin_states.get(chat_id, {}).get("route_id") or admin_states.get(str(chat_id), {}).get("route_id")
        
        fa_to_en = str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789")
        clean_num = text.strip().translate(fa_to_en)
        
        if not clean_num.isdigit() or int(clean_num) <= 0:
            await message.reply("❌ لطفاً یک عدد صحیح مثبت برای تعداد پیام‌ها ارسال کنید (مثلاً: 15 یا 50):", 
                                buttons=[[Button.inline("🔙 بازگشت به منوی مسیر", f"select_edit_{route_id}".encode('utf-8'))]])
            return
            
        count = int(clean_num)
        admin_states[chat_id] = {"current_route_id": str(route_id), "fetch_count": int(count)}
        admin_states[str(chat_id)] = {"current_route_id": str(route_id), "fetch_count": int(count)}
        _GLOBAL_FETCH_STATE[str(chat_id)] = {"route_id": str(route_id), "count": int(count)}
        
        msg = f"🎯 تعداد **{count} پیام** برای فراخوانی مشخص شد.\nلطفاً بستر مقصد را انتخاب کنید:"
        await message.reply(msg, buttons=get_fetch_target_keyboard(route_id, count))
        return

    elif state and state.startswith("WAITING_EDIT_"):
        field = state.split("_")[-1].lower()
        route_id = admin_states[chat_id].get("route_id")
        column_map = {"name": "name", "src": "src_channels", "bale": "bale_channels", "rubika": "rubika_channels", 
                      "eitaa": "eitaa_channels",
                      "prompt": "custom_prompt", "blacklist": "blacklist", 
                      "balemax": "bale_max_size", "rubikamax": "rubika_max_size", "eitaamax": "eitaa_max_size",
                      "aitrans": "ai_translation"}
        
        if field in column_map:
            val = text
            if field in ["balemax", "rubikamax", "eitaamax"]:
                if not text.isdigit() or int(text) <= 0:
                    await message.reply("❌ لطفاً یک عدد صحیح مثبت (به مگابایت) وارد کنید:", buttons=get_cancel_keyboard())
                    return
                val = int(text)
            elif field in ["aitrans", "eitaa"]:
                if text.strip() in ["خاموش", "حذف", "لغو", "هیچکدام"]:
                    val = ""

            update_route_field(route_id, column_map[field], val)
            admin_states[chat_id] = {}
            
            target_route = next((r for r in get_routes() if str(r[0]) == str(route_id)), None)
            if target_route:
                if field in ["prompt", "blacklist", "aitrans"]:
                    use_ai_media, ai_enabled, ai_hashtags = target_route[7], target_route[10], target_route[11]
                    await message.reply("✅ تنظیمات هوش مصنوعی ذخیره شد.", buttons=get_ai_keyboard(route_id, ai_enabled, use_ai_media, ai_hashtags))
                else:
                    allow_no_caption = target_route[15] if len(target_route) > 15 else True
                    eitaa_en = target_route[18] if len(target_route) > 18 else True
                    bale_delay = target_route[19] if len(target_route) > 19 else False
                    rubika_delay = target_route[20] if len(target_route) > 20 else False
                    eitaa_delay = target_route[21] if len(target_route) > 21 else True
                    await message.reply("✅ اطلاعات مسیر با موفقیت تغییر کرد.", buttons=get_edit_keyboard(route_id, target_route[13], target_route[14], allow_no_caption, eitaa_en, bale_delay, rubika_delay, eitaa_delay))

async def save_route_and_finish(message, data):
    global _ROUTES_CACHE, _ROUTES_CHANGED
    name, src, bale, rubika, eitaa, prompt = data.get("name"), data.get("src"), data.get("bale"), data.get("rubika"), data.get("eitaa", ""), data.get("prompt", "")
    if eitaa.strip() in ["خاموش", "حذف", "لغو", "هیچکدام"]:
        eitaa = ""
    try:
        new_id = 1
        if _ROUTES_CACHE:
            new_id = max([r[0] for r in _ROUTES_CACHE]) + 1
            
        new_route = (new_id, name, src, bale, rubika, prompt, '', False, 45, 45, True, False, '', True, True, True, eitaa, 50, True, False, False, True)
        _ROUTES_CACHE.append(new_route)
        _ROUTES_CHANGED = True
        
        admin_states[message.chat_id] = {}
        await message.reply(f"🎉 مسیر عالیِ `{name}` با موفقیت ساخته شد!", buttons=get_main_keyboard())
    except Exception as e: 
        await message.reply(f"❌ خطا: {e}")

@bot_app.on(events.CallbackQuery)
async def callback_handler(event):
    admins = get_all_admins()
    sender = getattr(event, 'sender_id', event.chat_id)
    if str(event.chat_id) not in admins and str(sender) not in admins:
        return
        
    data = event.data.decode('utf-8') if hasattr(event.data, 'decode') else str(event.data)
    chat_id = event.chat_id

    # --- پشتیبانی و نگاشت هوشمند متن دکمه‌های شیشه‌ای پلتفرم بله ---
    clean_data = str(data).strip()
    norm_data = re.sub(r'[\s_\u200c]+', ' ', clean_data).strip()
    
    # واکشی شناسه آخرین مسیر انتخاب‌شده برای این ادمین
    cur_rid = admin_states.get(chat_id, {}).get("current_route_id") or \
              admin_states.get(str(chat_id), {}).get("current_route_id")
    if not cur_rid:
        routes_all = get_routes()
        if len(routes_all) == 1:
            cur_rid = str(routes_all[0][0])
            
    fetch_cnt = admin_states.get(chat_id, {}).get("fetch_count") or \
                admin_states.get(str(chat_id), {}).get("fetch_count")
                
    MAIN_MENU_BTNS = ["🔙 بازگشت", "بازگشت", "منوی اصلی", "🔙 بازگشت به منوی اصلی", "بازگشت به منوی اصلی"]
    LIST_ROUTES_BTNS = ["📋 مشاهده و ویرایش مسیرها", "مشاهده و ویرایش مسیرها", "لیست مسیرها", "مشاهده مسیرها", "ویرایش مسیرها", "🔙 بازگشت به لیست مسیرها", "بازگشت به لیست مسیرها"]
    ADD_ROUTE_BTNS = ["➕ ساخت مسیر جدید", "ساخت مسیر جدید", "ساخت مسیر", "➕ ایجاد مسیر جدید", "ایجاد مسیر جدید"]
    MANAGE_ADMINS_BTNS = ["👥 مدیریت دسترسی ادمین‌ها", "👥 مدیریت دسترسی ادمینها", "مدیریت دسترسی ادمین‌ها", "مدیریت دسترسی ادمینها", "مدیریت ادمین‌ها", "مدیریت ادمینها"]
    CANCEL_BTNS = ["❌ لغو", "لغو"]
    
    # ۱. منوی اصلی، مدیریت ادمین، لغو و بازگشت
    if any(norm_data == re.sub(r'[\s_\u200c]+', ' ', b).strip() for b in LIST_ROUTES_BTNS):
        data = "list_routes"
    elif any(norm_data == re.sub(r'[\s_\u200c]+', ' ', b).strip() for b in ADD_ROUTE_BTNS):
        data = "add_route"
    elif any(norm_data == re.sub(r'[\s_\u200c]+', ' ', b).strip() for b in MANAGE_ADMINS_BTNS):
        data = "manage_admins"
    elif any(norm_data == re.sub(r'[\s_\u200c]+', ' ', b).strip() for b in MAIN_MENU_BTNS):
        data = "main_menu"
    elif any(norm_data == re.sub(r'[\s_\u200c]+', ' ', b).strip() for b in CANCEL_BTNS):
        data = "cancel_action"
    elif norm_data in ["➕ افزودن ادمین جدید", "افزودن ادمین جدید", "افزودن ادمین"]:
        data = "add_admin_prompt"
    elif norm_data in ["➖ حذف یک ادمین", "حذف یک ادمین", "حذف ادمین"]:
        data = "del_admin_prompt"

    # ۲. دکمه تنظیمات مسیر (قبل از بررسی نام مسیرها جهت جلوگیری از تداخل با آیکون ⚙️)
    elif "تنظیمات مسیر" in norm_data and "هوش مصنوعی" not in norm_data:
        data = f"route_settings_{cur_rid}" if cur_rid else "list_routes"

    # ۳. انتخاب مقصد در فراخوانی دستی (بله، روبیکا، ایتا، همه)
    is_dest_all = "همه" in norm_data or "هر دو" in norm_data or "🌐" in clean_data
    is_dest_eitaa = not is_dest_all and ("ایتا" in norm_data or "🟠" in clean_data)
    is_dest_rubika = not is_dest_all and not is_dest_eitaa and ("روبیکا" in norm_data or "🟣" in clean_data)
    is_dest_bale = not is_dest_all and not is_dest_rubika and not is_dest_eitaa and ("بله" in norm_data or "🟡" in clean_data)

    if (is_dest_bale or is_dest_rubika or is_dest_eitaa or is_dest_all) and not any(x in norm_data for x in ["وضعیت", "ارسال", "مقصد", "حجم", "مطمئنم", "تنظیمات"]):
        fetch_info = admin_states.get(chat_id, {}) if isinstance(admin_states.get(chat_id), dict) else {}
        if not fetch_info:
            fetch_info = admin_states.get(str(chat_id), {}) if isinstance(admin_states.get(str(chat_id)), dict) else {}
            
        g_info = _GLOBAL_FETCH_STATE.get(str(chat_id), {})
        target_rid = fetch_info.get("current_route_id") or fetch_info.get("route_id") or g_info.get("route_id") or cur_rid
        target_cnt = fetch_info.get("fetch_count") or g_info.get("count") or 10
        
        if not target_rid:
            routes_all = get_routes()
            if routes_all:
                target_rid = str(routes_all[0][0])
                
        if target_rid:
            if is_dest_all:
                data = f"run_fetch_{target_rid}_{target_cnt}_all"
            elif is_dest_eitaa:
                data = f"run_fetch_{target_rid}_{target_cnt}_eitaa"
            elif is_dest_rubika:
                data = f"run_fetch_{target_rid}_{target_cnt}_rubika"
            elif is_dest_bale:
                data = f"run_fetch_{target_rid}_{target_cnt}_bale"

    # ۴. دکمه‌های مربوط به صفحه یک مسیر مشخص
    elif cur_rid and any(k in norm_data for k in [
        "سوییچ اصلی", "هوش مصنوعی", "فراخوانی", "حذف کامل", "بازگشت به منوی مسیر",
        "بازگشت به تنظیمات مسیر", "تغییر نام", "مبدا", "مقصد بله", "مقصد روبیکا", "مقصد ایتا",
        "حجم بله", "حجم روبیکا", "حجم ایتا", "ارسال بله", "ارسال روبیکا", "ارسال ایتا", "تاخیر بله", "تاخیر روبیکا", "تاخیر ایتا", "بدون کپشن",
        "دستور اختصاصی", "فیلتر هوشمند", "تحلیل تصویر",
        "هشتگ", "زبان ترجمه", "مطمئنم", "انصراف", "منتقل کن", "نادیده بگیر"
    ]):
        if "سوییچ اصلی" in norm_data:
            data = f"ai_toggle_{cur_rid}"
        elif "هوش مصنوعی" in norm_data:
            data = f"ai_menu_{cur_rid}"
        elif "فراخوانی" in norm_data:
            data = f"fetch_menu_{cur_rid}"
        elif "حذف کامل" in norm_data:
            data = f"del_route_{cur_rid}"
        elif "بازگشت به منوی مسیر" in norm_data or "بازگشت به تنظیمات مسیر" in norm_data or "انصراف" in norm_data:
            data = f"select_edit_{cur_rid}"
        elif "تغییر نام" in norm_data:
            data = f"edit_{cur_rid}_name"
        elif "مبدا" in norm_data:
            data = f"edit_{cur_rid}_src"
        elif "مقصد بله" in norm_data:
            data = f"edit_{cur_rid}_bale"
        elif "مقصد روبیکا" in norm_data:
            data = f"edit_{cur_rid}_rubika"
        elif "مقصد ایتا" in norm_data:
            data = f"edit_{cur_rid}_eitaa"
        elif "حجم ایتا" in norm_data:
            data = f"edit_{cur_rid}_eitaamax"
        elif "ارسال ایتا" in norm_data:
            data = f"toggle_{cur_rid}_eitaaen"
        elif "حجم بله" in norm_data:
            data = f"edit_{cur_rid}_balemax"
        elif "حجم روبیکا" in norm_data:
            data = f"edit_{cur_rid}_rubikamax"
        elif "ارسال بله" in norm_data:
            data = f"toggle_{cur_rid}_baleen"
        elif "ارسال روبیکا" in norm_data:
            data = f"toggle_{cur_rid}_rubikaen"
        elif "تاخیر بله" in norm_data:
            data = f"toggle_{cur_rid}_baledelay"
        elif "تاخیر روبیکا" in norm_data:
            data = f"toggle_{cur_rid}_rubikadelay"
        elif "تاخیر ایتا" in norm_data:
            data = f"toggle_{cur_rid}_eitaadelay"
        elif "بدون کپشن" in norm_data:
            data = f"toggle_{cur_rid}_nocap"
        elif "دستور اختصاصی" in norm_data:
            data = f"edit_{cur_rid}_prompt"
        elif "فیلتر هوشمند" in norm_data:
            data = f"edit_{cur_rid}_blacklist"
        elif "تحلیل تصویر" in norm_data:
            data = f"ai_media_{cur_rid}"
        elif "هشتگ" in norm_data:
            data = f"ai_hashtag_{cur_rid}"
        elif "زبان ترجمه" in norm_data:
            data = f"edit_{cur_rid}_aitrans"
        elif "مطمئنم" in norm_data:
            data = f"confirm_del_{cur_rid}"
        elif "منتقل کن" in norm_data:
            data = f"sync_route_{cur_rid}"
        elif "نادیده بگیر" in norm_data:
            data = f"skip_route_{cur_rid}"

    # ۵. انتخاب یک مسیر بر اساس نام (مثلاً: ⚙️ تست)
    elif clean_data.startswith("⚙️ ") or norm_data.startswith("⚙️ "):
        clean_name = clean_data.replace("⚙️", "").strip()
        routes = get_routes()
        matched = next((r for r in routes if str(r[1]).strip() == clean_name), None)
        if matched:
            data = f"select_edit_{matched[0]}"
                

    if data == "cancel_action":
        admin_states[chat_id] = {}
        await event.edit("❌ عملیات لغو شد.", buttons=get_main_keyboard())
        return

    if data == "main_menu":
        admin_states[chat_id] = {}
        await event.edit("👋 بازگشت به منوی اصلی:", buttons=get_main_keyboard())
        
    elif data == "manage_admins":
        admins = get_all_admins()
        msg = "👥 **لیست ادمین‌های فعلی سیستم:**\n" + "\n".join([f"🔸 `{a}`" for a in admins])
        kb = [
            [Button.inline("➕ افزودن ادمین جدید", b"add_admin_prompt")],
            [Button.inline("➖ حذف یک ادمین", b"del_admin_prompt")],
            [Button.inline("🔙 بازگشت به منوی اصلی", b"main_menu")]
        ]
        await event.edit(msg, buttons=kb)
        
    elif data == "add_admin_prompt":
        admin_states[chat_id] = {"step": "WAITING_ADD_ADMIN"}
        await event.edit("✏️ لطفاً **آیدی عددی** کاربری که می‌خواهید ادمین شود را بفرستید:", buttons=get_cancel_keyboard())
        
    elif data == "del_admin_prompt":
        admin_states[chat_id] = {"step": "WAITING_REMOVE_ADMIN"}
        await event.edit("✏️ لطفاً **آیدی عددی** ادمینی که می‌خواهید حذف کنید را بفرستید:\n(دقت کنید که آیدی خودتان را حذف نکنید)", buttons=get_cancel_keyboard())

    elif data == "add_route":
        admin_states[chat_id] = {"step": "WAITING_ROUTE_NAME"}
        await event.edit("✏️ مرحله ۱: لطفاً یک **نام دلخواه** برای مسیر بفرستید:", buttons=get_cancel_keyboard())
        
    elif data == "list_routes":
        routes = get_routes()
        if not routes:
            await event.edit("هیچ مسیری ثبت نشده است.", buttons=get_main_keyboard())
            return
        buttons = [[Button.inline(f"⚙️ {r[1]}", f"select_edit_{r[0]}".encode('utf-8'))] for r in routes]
        buttons.append([Button.inline("🔙 بازگشت", b"main_menu")])
        await event.edit("📋 مسیر مورد نظر را انتخاب کنید:", buttons=buttons)
        
    elif data.startswith("select_edit_"):
        route_id = data.split("_")[2]
        admin_states[chat_id] = {"current_route_id": route_id}
        admin_states[str(chat_id)] = {"current_route_id": route_id}
        target_route = next((r for r in get_routes() if str(r[0]) == route_id), None)
        if target_route:
            r_name, r_src, r_bale, r_rubika = target_route[1:5]
            raw_b_max, raw_r_max = target_route[8], target_route[9]
            ai_enabled = target_route[10]
            bale_en = target_route[13]
            rubika_en = target_route[14]
            allow_no_caption = target_route[15] if len(target_route) > 15 else True
            r_eitaa = target_route[16] if len(target_route) > 16 else ""
            raw_e_max = target_route[17] if len(target_route) > 17 else 50
            eitaa_en = target_route[18] if len(target_route) > 18 else True
            bale_delay = target_route[19] if len(target_route) > 19 else False
            rubika_delay = target_route[20] if len(target_route) > 20 else False
            eitaa_delay = target_route[21] if len(target_route) > 21 else True
            
            b_max = raw_b_max if raw_b_max is not None else 50
            r_max = raw_r_max if raw_r_max is not None else 50
            e_max = raw_e_max if raw_e_max is not None else 50
            ai_status = "فعال 🟢" if ai_enabled else "غیرفعال 🔴"
            bale_status = "روشن 🟢" if bale_en else "خاموش 🔴"
            rubika_status = "روشن 🟢" if rubika_en else "خاموش 🔴"
            eitaa_status = "روشن 🟢" if eitaa_en else "خاموش 🔴"
            no_cap_status = "روشن 🟢" if allow_no_caption else "خاموش 🔴"
            
            b_del_text = "۱۰ دقیقه ⏳" if bale_delay else "فوری ⚡️"
            r_del_text = "۱۰ دقیقه ⏳" if rubika_delay else "فوری ⚡️"
            e_del_text = "۱۰ دقیقه ⏳" if eitaa_delay else "فوری ⚡️"
            
            msg = (f"📍 **مدیریت مسیر: {r_name}**\n\n"
                   f"📡 مبدا تلگرام: {r_src}\n"
                   f"🎯 مقصد بله: {r_bale} (حجم: {b_max}MB | {bale_status} | تاخیر: {b_del_text})\n"
                   f"🎯 مقصد روبیکا: {r_rubika} (حجم: {r_max}MB | {rubika_status} | تاخیر: {r_del_text})\n"
                   f"🎯 مقصد ایتا: {r_eitaa or 'تعریف نشده'} (حجم: {e_max}MB | {eitaa_status} | تاخیر: {e_del_text})\n"
                   f"🤖 هوش مصنوعی (AI): {ai_status}\n"
                   f"📁 ارسال فایل بدون کپشن: {no_cap_status}")
            await event.edit(msg, buttons=get_route_main_keyboard(route_id))

    elif data.startswith("route_settings_"):
        route_id = data.split("_")[2]
        admin_states[chat_id] = {"current_route_id": route_id}
        admin_states[str(chat_id)] = {"current_route_id": route_id}
        target_route = next((r for r in get_routes() if str(r[0]) == route_id), None)
        if target_route:
            bale_en = target_route[13]
            rubika_en = target_route[14]
            allow_no_caption = target_route[15] if len(target_route) > 15 else True
            eitaa_en = target_route[18] if len(target_route) > 18 else True
            bale_delay = target_route[19] if len(target_route) > 19 else False
            rubika_delay = target_route[20] if len(target_route) > 20 else False
            eitaa_delay = target_route[21] if len(target_route) > 21 else True
            msg = f"⚙️ **تنظیمات مسیر: {target_route[1]}**\n\nلطفاً گزینه مورد نظر را برای ویرایش یا تغییر وضعیت انتخاب کنید:"
            await event.edit(msg, buttons=get_edit_keyboard(route_id, bale_en, rubika_en, allow_no_caption, eitaa_en, bale_delay, rubika_delay, eitaa_delay))

    elif data.startswith("toggle_"):
        parts = data.split("_")
        route_id = parts[1]
        action = parts[2]
        
        target_route = next((r for r in get_routes() if str(r[0]) == route_id), None)
        if not target_route: return
        
        was_bale_en = target_route[13]
        was_rubika_en = target_route[14]
        was_eitaa_en = target_route[18] if len(target_route) > 18 else True
        was_off = not was_bale_en and not was_rubika_en and not was_eitaa_en
        
        if action == "baleen":
            new_bale_en = not was_bale_en
            new_rubika_en = was_rubika_en
            new_eitaa_en = was_eitaa_en
            is_now_on = new_bale_en or new_rubika_en or new_eitaa_en
            if was_off and is_now_on:
                _ROUTES_AWAITING_SYNC.add(str(route_id))
                update_route_field(route_id, "bale_enabled", new_bale_en)
                await event.edit("⏳ در حال بررسی کانال‌های مبدا برای یافتن پیام‌های زمان خاموشی...")
                asyncio.create_task(check_missed_and_prompt_admin(event, route_id, target_route))
                return
            else:
                update_route_field(route_id, "bale_enabled", new_bale_en)
        elif action == "rubikaen":
            new_bale_en = was_bale_en
            new_rubika_en = not was_rubika_en
            new_eitaa_en = was_eitaa_en
            is_now_on = new_bale_en or new_rubika_en or new_eitaa_en
            if was_off and is_now_on:
                _ROUTES_AWAITING_SYNC.add(str(route_id))
                update_route_field(route_id, "rubika_enabled", new_rubika_en)
                await event.edit("⏳ در حال بررسی کانال‌های مبدا برای یافتن پیام‌های زمان خاموشی...")
                asyncio.create_task(check_missed_and_prompt_admin(event, route_id, target_route))
                return
            else:
                update_route_field(route_id, "rubika_enabled", new_rubika_en)
        elif action == "eitaaen":
            new_bale_en = was_bale_en
            new_rubika_en = was_rubika_en
            new_eitaa_en = not was_eitaa_en
            is_now_on = new_bale_en or new_rubika_en or new_eitaa_en
            if was_off and is_now_on:
                _ROUTES_AWAITING_SYNC.add(str(route_id))
                update_route_field(route_id, "eitaa_enabled", new_eitaa_en)
                await event.edit("⏳ در حال بررسی کانال‌های مبدا برای یافتن پیام‌های زمان خاموشی...")
                asyncio.create_task(check_missed_and_prompt_admin(event, route_id, target_route))
                return
            else:
                update_route_field(route_id, "eitaa_enabled", new_eitaa_en)
        elif action == "baledelay":
            curr_b_del = target_route[19] if len(target_route) > 19 else False
            update_route_field(route_id, "bale_delay", not curr_b_del)
        elif action == "rubikadelay":
            curr_r_del = target_route[20] if len(target_route) > 20 else False
            update_route_field(route_id, "rubika_delay", not curr_r_del)
        elif action == "eitaadelay":
            curr_e_del = target_route[21] if len(target_route) > 21 else True
            update_route_field(route_id, "eitaa_delay", not curr_e_del)
        elif action == "nocap":
            curr_nocap = target_route[15] if len(target_route) > 15 else True
            update_route_field(route_id, "allow_no_caption", not curr_nocap)

        # به‌روزرسانی اطلاعات منو
        target_route = next((r for r in get_routes() if str(r[0]) == route_id), None)
        r_name, r_src, r_bale, r_rubika = target_route[1:5]
        r_eitaa = target_route[16] if len(target_route) > 16 else ""
        ai_status = "فعال 🟢" if target_route[10] else "غیرفعال 🔴"
        bale_en = target_route[13]
        rubika_en = target_route[14]
        allow_no_caption = target_route[15] if len(target_route) > 15 else True
        eitaa_en = target_route[18] if len(target_route) > 18 else True
        bale_delay = target_route[19] if len(target_route) > 19 else False
        rubika_delay = target_route[20] if len(target_route) > 20 else False
        eitaa_delay = target_route[21] if len(target_route) > 21 else True
        no_cap_status = "روشن 🟢" if allow_no_caption else "خاموش 🔴"
        
        b_del_text = "۱۰ دقیقه ⏳" if bale_delay else "فوری ⚡️"
        r_del_text = "۱۰ دقیقه ⏳" if rubika_delay else "فوری ⚡️"
        e_del_text = "۱۰ دقیقه ⏳" if eitaa_delay else "فوری ⚡️"
        
        msg = (f"🛠 **تنظیمات مسیر: {r_name}**\n\n"
               f"📡 مبدا: {r_src}\n"
               f"🎯 بله: {r_bale} (تاخیر: {b_del_text})\n"
               f"🎯 روبیکا: {r_rubika} (تاخیر: {r_del_text})\n"
               f"🎯 ایتا: {r_eitaa or 'تعریف نشده'} (تاخیر: {e_del_text})\n"
               f"🤖 هوش مصنوعی (AI): {ai_status}\n"
               f"📁 ارسال فایل و آلبوم بدون کپشن: {no_cap_status}")
        await event.edit(msg, buttons=get_edit_keyboard(route_id, bale_en, rubika_en, allow_no_caption, eitaa_en, bale_delay, rubika_delay, eitaa_delay))
    # --- هندلرهای پاسخ به پرسش ادمین ---
    elif data.startswith("sync_route_"):
        route_id = data.replace("sync_route_", "")
        _ROUTES_AWAITING_SYNC.discard(str(route_id))
        admin_states[chat_id].pop("skip_updates", None)
        await event.edit("✅ تنظیمات ذخیره شد.\nسیستم رادار طی چند دقیقه آینده تمام پیام‌های از دست رفته را واکشی و منتقل خواهد کرد.", buttons=get_main_keyboard())
        
    elif data.startswith("skip_route_"):
        route_id = data.replace("skip_route_", "")
        skip_updates = admin_states[chat_id].get("skip_updates", {})
        
        # ثبت شناسه‌های جدید تلگرام تا رادار از فاصله (گپ) به وجود آمده عبور کند
        for cid_str, new_last_id in skip_updates.items():
            set_last_processed_id(route_id, cid_str, new_last_id)
            
        _ROUTES_AWAITING_SYNC.discard(str(route_id))
        admin_states[chat_id].pop("skip_updates", None)
        await event.edit("✅ پیام‌های زمان خاموشی نادیده گرفته شدند.\nسیستم فقط پیام‌های جدید را از این لحظه پردازش می‌کند.", buttons=get_main_keyboard())
            
    elif data.startswith("ai_menu_"):
        route_id = data.replace("ai_menu_", "")
        target_route = next((r for r in get_routes() if str(r[0]) == str(route_id)), None)
        if target_route:
            r_prompt, blacklist, use_ai_media, ai_enabled, ai_hashtags, ai_translation = target_route[5], target_route[6], target_route[7], target_route[10], target_route[11], target_route[12]
            
            msg = f"🤖 **تنظیمات پیشرفته هوش مصنوعی (AI)**\n\n"
            msg += f"دستور اختصاصی: {r_prompt or 'ندارد'}\n"
            msg += f"فیلتر هوشمند: {blacklist or 'ندارد'}\n"
            msg += f"زبان ترجمه: {ai_translation or 'غیرفعال'}\n"
            
            await event.edit(msg, buttons=get_ai_keyboard(route_id, ai_enabled, use_ai_media, ai_hashtags))
            
    elif data.startswith("ai_toggle_") or data.startswith("ai_media_") or data.startswith("ai_hashtag_"):
        parts = data.split("_")
        action = parts[1]
        route_id = parts[2]
        
        target_route = next((r for r in get_routes() if str(r[0]) == route_id), None)
        if target_route:
            if action == "toggle":
                update_route_field(route_id, "ai_enabled", not target_route[10])
            elif action == "media":
                update_route_field(route_id, "use_ai_media", not target_route[7])
            elif action == "hashtag":
                update_route_field(route_id, "ai_add_hashtags", not target_route[11])
                
            target_route = next((r for r in get_routes() if str(r[0]) == route_id), None)
            r_prompt, blacklist, use_ai_media, ai_enabled, ai_hashtags, ai_translation = target_route[5], target_route[6], target_route[7], target_route[10], target_route[11], target_route[12]
            
            msg = f"🤖 **تنظیمات پیشرفته هوش مصنوعی (AI)**\n\n"
            msg += f"دستور اختصاصی: {r_prompt or 'ندارد'}\n"
            msg += f"فیلتر هوشمند: {blacklist or 'ندارد'}\n"
            msg += f"زبان ترجمه: {ai_translation or 'غیرفعال'}\n"
            
            await event.edit(msg, buttons=get_ai_keyboard(route_id, ai_enabled, use_ai_media, ai_hashtags))
            
    elif data.startswith("fetch_menu_"):
        route_id = data.replace("fetch_menu_", "")
        admin_states[chat_id] = {"step": "WAITING_FETCH_COUNT", "route_id": route_id, "current_route_id": route_id}
        admin_states[str(chat_id)] = {"step": "WAITING_FETCH_COUNT", "route_id": route_id, "current_route_id": route_id}
        msg = ("🔢 **فراخوانی پیام‌های گذشته**\n\n"
               "لطفاً **تعداد پیام‌های مدنظر** را به صورت عدد ارسال کنید (مثلاً: `15` یا `50`):\n\n"
               "💡 *توجه: اگر عدد واردشده بیشتر از کل پیام‌های کانال مبدا باشد، تمام پیام‌های موجود در کانال فراخوانی خواهند شد.*")
        await event.edit(msg, buttons=[[Button.inline("🔙 بازگشت به منوی مسیر", f"select_edit_{route_id}".encode('utf-8'))]])

    elif data.startswith("run_fetch_"):
        parts = data.split("_")
        route_id = parts[2]
        count = int(parts[3])
        platform = parts[4]
        
        target_fa = {"bale": "بله", "rubika": "روبیکا", "eitaa": "ایتا", "all": "همه مقاصد"}.get(platform, platform)
        await event.edit(f"⏳ فراخوانی {count} پیام از گذشته به مقصد **{target_fa}** آغاز شد...", buttons=get_main_keyboard())
        asyncio.create_task(run_historical_fetch(route_id, count, platform))

    elif data.startswith("edit_"):
        parts = data.split('_')
        route_id, field = parts[1], parts[2]
        
        admin_states[chat_id] = {"step": f"WAITING_EDIT_{field.upper()}", "route_id": route_id}
        names = {"name": "نام مسیر", "src": "کانال‌های مبدا", "bale": "کانال‌های بله", "rubika": "کانال‌های روبیکا", 
                 "eitaa": "کانال‌های ایتا",
                 "prompt": "دستور هوش مصنوعی", "blacklist": "فیلتر هوشمند", 
                 "balemax": "حداکثر حجم بله", "rubikamax": "حداکثر حجم روبیکا", "eitaamax": "حداکثر حجم ایتا",
                 "aitrans": "زبان مقصد برای ترجمه"}
                 
        extra_desc = ""
        if field == "aitrans":
            extra_desc = "\n(مثلاً تایپ کنید `فارسی` یا `English`. برای خاموش کردن قابلیت، کلمه `خاموش` را بفرستید)"
                 
        await event.edit(f"✏️ مقدار جدید برای **{names.get(field, field)}** را بفرستید:{extra_desc}", buttons=get_cancel_keyboard())

    elif data.startswith("del_route_"):
        route_id = data.replace("del_route_", "")
        target_route = next((r for r in get_routes() if str(r[0]) == route_id), None)
        r_name = target_route[1] if target_route else f"شناسه {route_id}"
        
        confirm_kb = [
            [Button.inline("🗑 بله، مطمئنم (حذف شود)", f"confirm_del_{route_id}".encode('utf-8'))],
            [Button.inline("🔙 خیر، انصراف و بازگشت", f"select_edit_{route_id}".encode('utf-8'))]
        ]
        await event.edit(
            f"⚠️ **هشدار حذف مسیر**\n\n"
            f"آیا مطمئن هستید که می‌خواهید مسیر **«{r_name}»** را به طور کامل حذف کنید؟\n"
            f"این عملیات غیرقابل بازگشت خواهد بود.",
            buttons=confirm_kb
        )

    elif data.startswith("confirm_del_"):
        route_id = data.replace("confirm_del_", "")
        global _ROUTES_CACHE, _ROUTES_CHANGED
        _ROUTES_CACHE = [r for r in _ROUTES_CACHE if str(r[0]) != route_id]
        _ROUTES_CHANGED = True
        await event.edit("🗑 مسیر با موفقیت از سیستم حذف شد.", buttons=get_main_keyboard())

async def check_missed_and_prompt_admin(event, route_id, target_route):
    chat_id = event.chat_id
    src_list = [x.strip().replace('@', '').replace('https://t.me/', '').replace('t.me/', '').lower() for x in re.split(r'[,،\n\s]+', target_route[2] if target_route[2] else "") if x.strip()]
    
    total_missed = 0
    channel_updates = {}
    
    for channel in src_list:
        try:
            chat_info = await user_app.get_entity(channel)
            chat_id_str = str(chat_info.id)
            last_saved_id = get_last_processed_id(route_id, chat_id_str)
            
            if last_saved_id > 0:
                # گرفتن آخرین پیام فعلی کانال
                async for msg in user_app.iter_messages(channel, limit=1):
                    current_tg_id = msg.id
                    if current_tg_id > last_saved_id:
                        total_missed += (current_tg_id - last_saved_id)
                        # شناسه جدید را نگه می‌داریم تا اگر ادمین دکمه "رد کردن" را زد، دیتابیس را به این آیدی ارتقا دهیم
                        channel_updates[chat_id_str] = current_tg_id
        except Exception:
            pass

    r_name = target_route[1]
    if total_missed > 0:
        admin_states[chat_id] = admin_states.get(chat_id, {})
        admin_states[chat_id]["skip_updates"] = channel_updates
        
        msg = (f"🛠 **مسیر: {r_name}**\n\n"
               f"⚠️ **توجه:** مسیر شما با موفقیت روشن شد، اما متوجه شدیم در زمانی که مسیر خاموش بوده، "
               f"حدود **{total_missed} پیام جدید** در کانال‌های مبدا ارسال شده است.\n\n"
               f"لطفاً مشخص کنید با این پیام‌ها چه کار کنیم:")
               
        kb = [
            [Button.inline("✅ تمام آن‌ها را الان منتقل کن", f"sync_route_{route_id}".encode('utf-8'))],
            [Button.inline("❌ نادیده بگیر و فقط پیام‌های جدید را بفرست", f"skip_route_{route_id}".encode('utf-8'))]
        ]
        await event.edit(msg, buttons=kb)
    else:
        # اگر پیام جدیدی نیامده بود، مستقیم منوی مدیریت مسیر را نشان بده
        _ROUTES_AWAITING_SYNC.discard(str(route_id))
        target_route = next((r for r in get_routes() if str(r[0]) == route_id), None)
        bale_en, rubika_en = target_route[13], target_route[14]
        allow_no_caption = target_route[15] if len(target_route) > 15 else True
        eitaa_en = target_route[18] if len(target_route) > 18 else True
        bale_delay = target_route[19] if len(target_route) > 19 else False
        rubika_delay = target_route[20] if len(target_route) > 20 else False
        eitaa_delay = target_route[21] if len(target_route) > 21 else True
        msg = f"✅ مسیر {r_name} با موفقیت روشن شد و آماده دریافت پیام است."
        await event.edit(msg, buttons=get_edit_keyboard(route_id, bale_en, rubika_en, allow_no_caption, eitaa_en, bale_delay, rubika_delay, eitaa_delay))

async def handle_edited_message(message, chat_username, active_routes):
    chat_id_str = str(message.chat_id)
    msg_id = message.id
    new_text = message.text or message.message or ""
    msg_link = f"https://t.me/c/{chat_id_str.replace('-100', '')}/{msg_id}"
    current_media_id = get_telegram_media_id(message)
    
    msg_lock = await get_msg_lock(message.chat_id, message)
    async with msg_lock:
        print(f"\n✏️ رویداد ویرایش پیام {msg_id} از {chat_username} دریافت شد! در حال بررسی وضعیت...", flush=True)
        
        for route in active_routes:
            r_id, r_name, r_src, r_bale, r_rubika, r_prompt, smart_filter, use_ai_media, raw_b_max, raw_r_max, ai_enabled, ai_hashtags, ai_translation, bale_enabled, rubika_enabled = route[:15]
            r_eitaa = route[16] if len(route) > 16 else ""
            eitaa_enabled = route[18] if len(route) > 18 else True

            # بررسی صف تاخیر ۱۰ دقیقه‌ای مشترک (بله، روبیکا، ایتا)
            cid_clean = std_id(chat_id_str)
            q_key = f"{r_id}_{cid_clean}_{msg_id}"
            if q_key in _DELAY_QUEUE:
                item = _DELAY_QUEUE[q_key]
                old_task = item.get("task")
                if old_task and not old_task.done():
                    old_task.cancel()
                
                # پردازش متن جدید با هوش مصنوعی در صورت فعال بودن
                processed_caption = new_text
                if new_text and ai_enabled:
                    processed_caption = await process_with_ai(
                        new_text, r_prompt, smart_filter, media_paths=None,
                        ai_enabled=ai_enabled, ai_hashtags=ai_hashtags, ai_translation=ai_translation
                    )
                    if processed_caption == "__API_ERROR__":
                        processed_caption = new_text
                    elif processed_caption.strip().upper() == "FILTERED":
                        print(f"🚫 متن ویرایش‌شده در صف تاخیر مسیر '{r_name}' مسدود شد.", flush=True)
                        p_dir = item.get("pending_dir")
                        if p_dir and os.path.exists(p_dir):
                            shutil.rmtree(p_dir, ignore_errors=True)
                        _DELAY_QUEUE.pop(q_key, None)
                        continue

                # تمدید تایمر ۱۰ دقیقه از لحظه ویرایش
                new_task = asyncio.create_task(run_delayed_sender(q_key, 600))
                item["task"] = new_task
                item["caption"] = processed_caption
                item["expire_at"] = time.time() + 600
                print(f"🔄 پیام {msg_id} در صف تاخیر مسیر '{r_name}' با متن جدید به‌روز شد و تایمر ۱۰ دقیقه از نو تمدید گردید.", flush=True)
            mappings = await asyncio.to_thread(get_msg_mappings, r_id, chat_id_str, msg_id)
            current_max = get_last_processed_id(r_id, chat_id_str)

            if not mappings:
                # اگر نگاشتی وجود نداشت، این تابع کاری انجام نمی‌دهد چون در route_message به عنوان پیام جدید مدیریت می‌شود
                continue
            
            # بررسی تغییر تصویر یا فایل مدیا
            stored_media_id = str(mappings[0][4] or "") if len(mappings[0]) > 4 else ""
            
            media_changed = False
            if stored_media_id and current_media_id and stored_media_id != current_media_id:
                media_changed = True
            elif stored_media_id and not current_media_id:
                media_changed = True
            elif not stored_media_id and current_media_id and mappings[0][3] == 'text':
                media_changed = True
            
            if media_changed:
                print(f"🖼 تصویر/فایل پیام {msg_id} تغییر کرده است! حذف پیام قبلی از کانال‌ها و ارسال مجدد...", flush=True)
                for platform, dest_chat_id, dest_msg_id, _, _ in mappings:
                    if platform == 'bale':
                        await asyncio.to_thread(delete_from_bale, dest_chat_id, dest_msg_id)
                    elif platform == 'rubika':
                        await asyncio.to_thread(delete_from_rubika, dest_chat_id, dest_msg_id)
                
                # اگر پیام بخشی از یک آلبوم است، کل آلبوم بازخوانی و ارسال می‌شود
                msgs_to_send = [message]
                if getattr(message, 'grouped_id', None):
                    try:
                        history = await user_app.get_messages(message.chat_id, limit=20, max_id=message.id + 10, min_id=message.id - 10)
                        fresh_group = sorted([m for m in history if m.grouped_id == message.grouped_id], key=lambda x: x.id)
                        if fresh_group:
                            msgs_to_send = fresh_group
                    except Exception: pass

                await process_single_or_group(msgs_to_send, chat_username, message.chat_id, [route], lock_already_held=True)
                continue

            # اگر فقط متن یا کپشن ویرایش شده باشد: ویرایش درجا
            processed_text = new_text
            if new_text and ai_enabled:
                processed_text = await process_with_ai(
                    new_text, r_prompt, smart_filter, media_paths=None,
                    ai_enabled=ai_enabled, ai_hashtags=ai_hashtags, ai_translation=ai_translation
                )
                if processed_text == "__API_ERROR__":
                    processed_text = new_text
                elif processed_text.strip().upper() == "FILTERED":
                    print(f"🚫 متن ویرایش‌شده در مسیر '{r_name}' مسدود شد.", flush=True)
                    continue

            for platform, dest_chat_id, dest_msg_id, msg_type, _ in mappings:
                if platform == 'bale' and bale_enabled:
                    if msg_type == 'text':
                        ok, err = await asyncio.to_thread(edit_text_to_bale, processed_text, dest_chat_id, dest_msg_id)
                    else:
                        ok, err = await asyncio.to_thread(edit_caption_to_bale, processed_text, dest_chat_id, dest_msg_id)
                    if not ok:
                        await notify_admin(msg_link, f"ویرایش بله ({dest_chat_id})", f"خطا:\n{err}")
                    await asyncio.sleep(1)
                elif platform == 'rubika' and rubika_enabled:
                    ok, err = await asyncio.to_thread(edit_text_to_rubika, processed_text, dest_chat_id, dest_msg_id)
                    if not ok:
                        await notify_admin(msg_link, f"ویرایش روبیکا ({dest_chat_id})", f"خطا:\n{err}")
                    await asyncio.sleep(1)
                elif platform == 'eitaa':
                    # ارسال هشدار به ادمین در تلگرام و بله به دلیل عدم امکان ادیت در ایتا
                    warn_msg = (f"⚠️ **هشدار ویرایش در ایتا**\n\n"
                                f"پیام شماره `{msg_id}` از کانال مبدا `{chat_username}` در تلگرام ویرایش شد.\n"
                                f"با توجه به اینکه این پیام قبلاً به کانال ایتا (`{dest_chat_id}`) منتقل شده است، به دلیل محدودیت‌های ایتا امکان ویرایش خودکار وجود ندارد.\n"
                                f"🔗 لینک پیام: {msg_link}")
                    await notify_admin_all_platforms(warn_msg)

            if msg_id > current_max:
                set_last_processed_id(r_id, chat_id_str, msg_id)

async def route_message(message, chat_username, active_routes, bypass_id_check=False, target_platform='all'):
    if not active_routes: return 

    chat_id_str = str(message.chat_id)
    msg_id = message.id
    edit_date = getattr(message, 'edit_date', None)
    edit_ts = int(edit_date.timestamp()) if edit_date else 0
    
    # مکانیزم امنیتی ضد تکرار (در زمان فراخوانی دستی نادیده گرفته می‌شود)
    if not bypass_id_check:
        async with _DEDUP_LOCK:
            msg_key = f"{chat_id_str}_{msg_id}_{edit_ts}"
            if msg_key in _RECENT_MSGS:
                return
            _RECENT_MSGS.append(msg_key)
            if len(_RECENT_MSGS) > 2000:
                _RECENT_MSGS.pop(0)

    edit_routes = []
    new_routes = []

    for r in active_routes:
        r_id = r[0]
        # در زمان فراخوانی دستی، پیام باید مستقیماً برای ارسال برود
        if bypass_id_check:
            new_routes.append(r)
            continue

        mappings = await asyncio.to_thread(get_msg_mappings, r_id, chat_id_str, msg_id)
        if mappings:
            if edit_date is not None:
                edit_routes.append(r)
        else:
            current_max = get_last_processed_id(r_id, chat_id_str)
            if msg_id > current_max:
                new_routes.append(r)

    # ۱. اگر ویرایش واقعی برای پیام‌های قبلی است
    if edit_routes:
        await handle_edited_message(message, chat_username, edit_routes)

    # ۲. اگر پیام جدید است یا دستور فراخوانی دستی صادر شده است
    if not new_routes:
        return

    is_grouped = getattr(message, 'grouped_id', None) is not None
    
    if is_grouped:
        mg_id = message.grouped_id
        if mg_id in _PROCESSED_MEDIA_GROUPS and not bypass_id_check:
            return
        
        if mg_id not in media_groups_cache:
            media_groups_cache[mg_id] = []
            asyncio.create_task(process_media_group_delayed(mg_id, chat_username, message.chat_id, new_routes, target_platform, bypass_id_check=bypass_id_check))
        
        replaced = False
        for i, m in enumerate(media_groups_cache[mg_id]):
            if m.id == msg_id:
                media_groups_cache[mg_id][i] = message
                replaced = True
                break
        if not replaced:
            media_groups_cache[mg_id].append(message)
    else:
        await process_single_or_group([message], chat_username, message.chat_id, new_routes, target_platform, bypass_id_check=bypass_id_check)
        
async def run_historical_fetch(route_id, count, target_platform):
    routes = get_routes()
    target_route = next((r for r in routes if str(r[0]) == str(route_id)), None)
    if not target_route: 
        print(f"❌ خطای فراخوانی: مسیر با شناسه {route_id} یافت نشد.", flush=True)
        return
    
    bale_en, rubika_en = target_route[13], target_route[14]
    eitaa_en = target_route[18] if len(target_route) > 18 else True
    
    # بررسی وضعیت پلتفرم هدف
    if target_platform == 'bale' and not bale_en:
        print(f"⚠️ ارسال به بله در مسیر '{target_route[1]}' غیرفعال است. فراخوانی متوقف شد.", flush=True)
        return
    if target_platform == 'rubika' and not rubika_en:
        print(f"⚠️ ارسال به روبیکا در مسیر '{target_route[1]}' غیرفعال است. فراخوانی متوقف شد.", flush=True)
        return
    if target_platform == 'eitaa' and not eitaa_en:
        print(f"⚠️ ارسال به ایتا در مسیر '{target_route[1]}' غیرفعال است. فراخوانی متوقف شد.", flush=True)
        return
    if target_platform == 'all' and not bale_en and not rubika_en and not eitaa_en:
        print(f"⚠️ تمام مقاصد در مسیر '{target_route[1]}' غیرفعال هستند. فراخوانی متوقف شد.", flush=True)
        return
    
    raw_src = target_route[2] if target_route[2] else ""
    src_list = [x.strip().replace('@', '').replace('https://t.me/', '').replace('t.me/', '') for x in re.split(r'[,،\n\s]+', raw_src) if x.strip()]

    print(f"🚀 شروع فراخوانی دستی {count} پیام برای مسیر '{target_route[1]}' (مقصد: {target_platform})...", flush=True)

    for channel in src_list:
        messages = []
        try:
            # تبدیل به عدد اگر کانال به صورت آیدی عددی ثبت شده باشد
            ch_entity = int(channel) if (channel.isdigit() or (channel.startswith('-') and channel[1:].isdigit())) else channel
            
            try:
                async for msg in user_app.iter_messages(ch_entity, limit=count):
                    messages.append(msg)
            except FloodWaitError as e:
                print(f"⏳ محدودیت تلگرام در دریافت تاریخچه (FloodWait)! مکث برای {e.seconds} ثانیه...", flush=True)
                await asyncio.sleep(e.seconds)
                messages.clear()
                async for msg in user_app.iter_messages(ch_entity, limit=count):
                    messages.append(msg)
                
            messages.reverse()
            print(f"📥 تعداد {len(messages)} پیام از مبدا {channel} واکشی شد. شروع ارسال به مقصد...", flush=True)
            
            for msg in messages:
                chat = await msg.get_chat()
                chat_username = getattr(chat, 'username', None) or str(msg.chat_id)
                try:
                    await route_message(msg, chat_username, [target_route], bypass_id_check=True, target_platform=target_platform)
                except FloodWaitError as e:
                    print(f"⏳ خطای FloodWait! مکث برای {e.seconds} ثانیه...", flush=True)
                    await asyncio.sleep(e.seconds)
                    await route_message(msg, chat_username, [target_route], bypass_id_check=True, target_platform=target_platform)
                    
                await asyncio.sleep(1.5)
                
            print(f"✅ فراخوانی تاریخچه برای مبدا {channel} با موفقیت به پایان رسید.", flush=True)
            await asyncio.sleep(2)
        except Exception as e:
            print(f"❌ خطا در فراخوانی پیام‌های گذشته کانال {channel}: {e}", flush=True)

@user_app.on(events.NewMessage())
@user_app.on(events.MessageEdited())
async def incoming_telegram_message(event):
    message = event.message
    if not message.chat_id: return
    
    chat_id_str = str(message.chat_id)
    chat = await event.get_chat()
    chat_username = getattr(chat, 'username', None)
    
    def is_match(uname, cid, src_list):
        if cid in src_list: return True
        if uname and uname.lower() in src_list: return True
        return False
        
    needs_fetch = False
    if not chat_username and (event.is_channel or event.is_group):
        needs_fetch = True
        
    routes = get_routes()
    active_routes = []
    
    for r in routes:
        bale_enabled = r[13]
        rubika_enabled = r[14]
        eitaa_enabled = r[18] if len(r) > 18 else True
        if not bale_enabled and not rubika_enabled and not eitaa_enabled:
            continue
            
        raw_src = r[2] if r[2] else ""
        src_list = [x.strip().replace('@', '').replace('https://t.me/', '').replace('t.me/', '').lower() for x in re.split(r'[,،\n\s]+', raw_src) if x.strip()]
        if is_match(chat_username, chat_id_str, src_list):
            active_routes.append(r)
            
    if not active_routes and needs_fetch:
        try:
            if chat_username:
                for r in routes:
                    bale_enabled = r[13]
                    rubika_enabled = r[14]
                    eitaa_enabled = r[18] if len(r) > 18 else True
                    if not bale_enabled and not rubika_enabled and not eitaa_enabled:
                        continue
                        
                    raw_src = r[2] if r[2] else ""
                    src_list = [x.strip().replace('@', '').replace('https://t.me/', '').replace('t.me/', '').lower() for x in re.split(r'[,،\n\s]+', raw_src) if x.strip()]
                    if chat_username.lower() in src_list and r not in active_routes:
                        active_routes.append(r)
        except Exception: pass
        
    if not active_routes:
        return 

    # --- تغییرات ۴: مدیریت خطای FloodWaitError هنگام روت کردن پیام جدید ---
    try:
        await route_message(message, chat_username or chat_id_str, active_routes)
    except FloodWaitError as e:
        print(f"⏳ محدودیت تلگرام در پیام‌های ورودی (FloodWait)! مکث {e.seconds} ثانیه...", flush=True)
        await asyncio.sleep(e.seconds)
        await route_message(message, chat_username or chat_id_str, active_routes)

async def process_media_group_delayed(mg_id, chat_username, chat_id, active_routes, target_platform, bypass_id_check=False):
    start_time = time.time()
    last_count = len(media_groups_cache.get(mg_id, []))
    
    # صبر هوشمند تا زمان توقف ورود عکس‌های جدید به آلبوم
    while True:
        await asyncio.sleep(2)
        current_count = len(media_groups_cache.get(mg_id, []))
        if (current_count > 0 and current_count == last_count) or (time.time() - start_time > 12):
            break
        last_count = current_count

    messages = media_groups_cache.pop(mg_id, [])
    if messages:
        _PROCESSED_MEDIA_GROUPS.append(mg_id)
        if len(_PROCESSED_MEDIA_GROUPS) > 200:
            _PROCESSED_MEDIA_GROUPS.pop(0)
            
        messages.sort(key=lambda m: m.id)
        
        try:
            max_msg_id = messages[-1].id + 10
            min_msg_id = messages[0].id - 10
            
            try:
                history = await user_app.get_messages(chat_id, limit=20, max_id=max_msg_id, min_id=min_msg_id)
            except FloodWaitError as e:
                print(f"⏳ محدودیت تلگرام در خواندن گروه رسانه (FloodWait)! مکث {e.seconds} ثانیه...", flush=True)
                await asyncio.sleep(e.seconds)
                history = await user_app.get_messages(chat_id, limit=20, max_id=max_msg_id, min_id=min_msg_id)

            fresh_messages = sorted([m for m in history if m.grouped_id == mg_id], key=lambda x: x.id)
            if fresh_messages and len(fresh_messages) >= len(messages):
                messages = fresh_messages
        except Exception:
            pass
            
        await process_single_or_group(messages, chat_username, chat_id, active_routes, target_platform, bypass_id_check=bypass_id_check)

async def process_single_or_group(messages, chat_username, chat_id, active_routes, target_platform='all', lock_already_held=False, bypass_id_check=False):
    async with _PROCESSING_SEMAPHORE:
        main_msg_id = messages[0].id
        cid_clean = std_id(chat_id)
        
        class _NullLock:
            async def __aenter__(self): return None
            async def __aexit__(self, *args): pass

        msg_lock = None if lock_already_held else await get_msg_lock(chat_id, messages[0])
        lock_ctx = msg_lock if msg_lock is not None else _NullLock()
        
        async with lock_ctx:
            # 🛡 بررسی حفاظتی: اگر پیام حین انتظار در صف توسط تسک دیگری فرستاده شده، لغو شود
            if not lock_already_held and not bypass_id_check:
                all_done = True
                for r in active_routes:
                    r_id = r[0]
                    maps = await asyncio.to_thread(get_msg_mappings, r_id, cid_clean, main_msg_id)
                    if not maps:
                        all_done = False
                        break
                if all_done:
                    print(f"⏭ پیام {main_msg_id} از {chat_username} قبلاً منتقل شده است و نادیده گرفته شد.", flush=True)
                    return

            # علامت‌گذاری پیام به عنوان «در حال پردازش»
            flight_keys = [f"{cid_clean}_{m.id}" for m in messages]
            async with _IN_FLIGHT_GUARD:
                for fk in flight_keys:
                    _IN_FLIGHT_MSGS.add(fk)

            try:
                print(f"\n🔔 پردازش محتوا از {chat_username} آغاز شد!", flush=True)
                msg_link = f"https://t.me/c/{cid_clean}/{messages[0].id}" if messages else "نامشخص"
                
                caption_text = ""
                current_media_id = get_telegram_media_id(messages[0])
                
                for m in messages:
                    if m.text:
                        caption_text = m.text
                        break

                # اگر پیام متن نداشت، استخراج و تبدیل پیام‌های خاص (نظرسنجی، موقعیت مکانی، مخاطب)
                if not caption_text and messages:
                    m0 = messages[0]
                    poll_text = extract_poll_as_text(m0, msg_link)
                    if poll_text:
                        caption_text = poll_text
                    else:
                        geo_text = extract_geo_as_text(m0)
                        if geo_text:
                            caption_text = geo_text
                        else:
                            contact_text = extract_contact_as_text(m0)
                            if contact_text:
                                caption_text = contact_text

                # استخراج دکمه‌های شیشه‌ای لینکی و الحاق به انتهای متن یا کپشن
                if messages:
                    btn_links = extract_inline_button_links(messages[0])
                    if btn_links:
                        btn_suffix = "\n\n🔗 **لینک‌های پیوست:**\n" + "\n".join([f"• [{t}]({u})" for t, u in btn_links])
                        caption_text = (caption_text + btn_suffix) if caption_text else btn_suffix.strip()

                has_media = any(m.media is not None for m in messages)
                is_no_caption_media = has_media and not bool(caption_text and caption_text.strip())

                # اگر پست رسانه‌ای بدون کپشن است و هیچ مسیری اجازه انتقال آن را ندارد، پیام نادیده گرفته شده و شناسه ذخیره می‌شود
                if is_no_caption_media:
                    routes_allowing = [r for r in active_routes if (r[15] if len(r) > 15 else True)]
                    if not routes_allowing:
                        print(f"⏭ پیام رسانه‌ای بدون کپشن در تمامی مسیرهای فعال نادیده گرفته شد.", flush=True)
                        max_id_in_group = max(m.id for m in messages)
                        for r in active_routes:
                            route_id = r[0]
                            current_max = get_last_processed_id(route_id, cid_clean)
                            if max_id_in_group > current_max:
                                set_last_processed_id(route_id, cid_clean, max_id_in_group)
                                print(f"✅ دیتابیس مسیر '{r[1]}' برای مبدا ({chat_username}) آپدیت شد (شناسه {max_id_in_group}).", flush=True)
                        return

                downloaded_files = []
                files_to_cleanup = [] 

                for m in messages:
                    has_media_attr = m.media is not None
                    if has_media_attr:
                        try:
                            file_name = "unknown_file"
                            m_type = 'unknown'
                            
                            if m.photo: 
                                file_name = f"photo_{m.id}.jpg"; m_type = 'photo'
                            elif getattr(m, 'video', None): 
                                is_gif = bool(getattr(m, 'gif', False) or (m.document and any(getattr(attr, 'document_attribute_animated', False) for attr in getattr(m.document, 'attributes', []))))
                                if is_gif:
                                    file_name = f"gif_{m.id}.gif"; m_type = 'gif'
                                else:
                                    file_name = getattr(m.file, 'name', None) or f"video_{m.id}.mp4"; m_type = 'video'
                            elif getattr(m, 'document', None): 
                                doc = m.document
                                is_sticker = bool(getattr(m, 'sticker', None) or any(attr.__class__.__name__ == 'DocumentAttributeSticker' for attr in getattr(doc, 'attributes', [])))
                                is_anim = bool(getattr(m, 'gif', False) or any(attr.__class__.__name__ == 'DocumentAttributeAnimated' for attr in getattr(doc, 'attributes', [])))
                                
                                if is_sticker:
                                    file_name = getattr(m.file, 'name', None) or f"sticker_{m.id}{getattr(m.file, 'ext', '.webp')}"
                                    m_type = 'sticker'
                                elif is_anim:
                                    file_name = f"gif_{m.id}.gif"; m_type = 'gif'
                                else:
                                    file_name = getattr(m.file, 'name', None) or f"doc_{m.id}.dat"; m_type = 'document'
                            elif getattr(m, 'audio', None): 
                                file_name = getattr(m.file, 'name', None) or f"audio_{m.id}.mp3"; m_type = 'audio'
                            elif getattr(m, 'voice', None): 
                                file_name = f"voice_{m.id}.ogg"; m_type = 'voice'
                            
                            unique_download_name = f"{int(time.time())}_{m.id}_{os.path.basename(file_name)}"
                            
                            try:
                                path = await m.download_media(file=unique_download_name)
                            except FloodWaitError as e:
                                print(f"⏳ محدودیت دانلود مدیا (FloodWait)! مکث برای {e.seconds} ثانیه...", flush=True)
                                await asyncio.sleep(e.seconds)
                                path = await m.download_media(file=unique_download_name)

                            # تبدیل ویس (OGG به MP3) جهت پخش مستقیم در تمام کلاینت‌های ایتا
                            if path and os.path.exists(path) and (m_type == 'voice' or path.lower().endswith('.ogg')):
                                mp3_path = f"{os.path.splitext(path)[0]}_conv.mp3"
                                if await asyncio.to_thread(convert_ogg_to_mp3, path, mp3_path):
                                    files_to_cleanup.append(mp3_path)
                                    path = mp3_path
                                    file_name = f"voice_{m.id}.mp3"
                                    m_type = 'audio'

                            # تبدیل استیکر ویدیویی (WebM به GIF)
                            if path and os.path.exists(path) and m_type == 'sticker' and path.lower().endswith('.webm'):
                                gif_path = f"{os.path.splitext(path)[0]}_conv.gif"
                                if await asyncio.to_thread(convert_video_to_gif, path, gif_path):
                                    files_to_cleanup.append(gif_path)
                                    path = gif_path
                                    file_name = f"sticker_{m.id}.gif"
                                    m_type = 'gif'

                            if path and os.path.exists(path):
                                real_size_bytes = os.path.getsize(path)
                                real_size_mb = real_size_bytes / (1024 * 1024)
                                print(f"📥 فایل دانلود شد. نام: {file_name} | فرمت: {m_type} | حجم اصلی دیسک: {real_size_mb:.2f} MB", flush=True)
                                downloaded_files.append({
                                    'original_path': path, 
                                    'type': m_type, 
                                    'name': file_name,
                                    'original_size_mb': real_size_mb 
                                })
                                files_to_cleanup.append(path)
                        except Exception as e: print(f"❌ خطای دانلود: {e}", flush=True)
                
                successful_routes = []
                
                for route in active_routes:
                    r_id, r_name, r_src, r_bale, r_rubika, r_prompt, smart_filter, use_ai_media, raw_b_max, raw_r_max, ai_enabled, ai_hashtags, ai_translation, bale_enabled, rubika_enabled = route[:15]
                    allow_no_caption = route[15] if len(route) > 15 else True
                    r_eitaa = route[16] if len(route) > 16 else ""
                    raw_e_max = route[17] if len(route) > 17 else 50
                    eitaa_enabled = route[18] if len(route) > 18 else True

                    # بررسی مجاز بودن انتقال فایل و آلبوم بدون کپشن برای این مسیر
                    if is_no_caption_media and not allow_no_caption:
                        print(f"⏭ پست رسانه‌ای بدون کپشن در مسیر '{r_name}' طبق تنظیمات نادیده گرفته شد.", flush=True)
                        successful_routes.append(route)
                        continue
                    
                    bale_max_size = float(raw_b_max) if raw_b_max is not None else 50.0
                    rubika_max_size = float(raw_r_max) if raw_r_max is not None else 50.0
                    eitaa_max_size = float(raw_e_max) if raw_e_max is not None else 50.0

                    rubika_processed_files = []
                    bale_processed_files = []

                    for f_obj in downloaded_files:
                        orig_path = f_obj['original_path']
                        orig_size = f_obj['original_size_mb']
                        f_type = f_obj['type']
                        f_name = f_obj['name']
                        
                        ext = os.path.splitext(f_name)[1].lower()
                        is_media = f_type in ['video', 'audio', 'voice'] or ext in ['.mp4', '.mkv', '.avi', '.mov', '.mp3', '.m4a', '.ogg', '.wav', '.flac', '.aac', '.wma']

                        best_path = orig_path
                        best_size = orig_size

                        rubika_path, rubika_size = best_path, best_size
                        if rubika_size > rubika_max_size:
                            if is_media:
                                name_ext = os.path.splitext(f_name)[1].lower()
                                if f_type == 'video' and name_ext not in ['.mp4', '.mkv', '.mov', '.webm']: name_ext = '.mp4'
                                elif f_type in ['audio', 'voice'] and not name_ext: name_ext = '.ogg' if f_type == 'voice' else '.mp3'
                                
                                out_path = f"{orig_path}_rubika_comp{name_ext}"
                                print(f"🗜 حجم فعلی ({rubika_size:.2f}MB) بیش از سقف روبیکا است. فشرده‌سازی...", flush=True)
                                if await asyncio.to_thread(compress_media, best_path, out_path, rubika_max_size, f_type) and os.path.exists(out_path):
                                    act_size = os.path.getsize(out_path) / (1024 * 1024)
                                    files_to_cleanup.append(out_path)
                                    if act_size < best_size:
                                        rubika_path, rubika_size = out_path, act_size
                                        best_path, best_size = out_path, act_size

                        rubika_processed_files.append({'path': rubika_path, 'name': f_name, 'type': f_type, 'size_mb': rubika_size})

                        bale_path, bale_size = best_path, best_size
                        if bale_size > bale_max_size:
                            if is_media:
                                name_ext = os.path.splitext(f_name)[1].lower()
                                if f_type == 'video' and name_ext not in ['.mp4', '.mkv', '.mov', '.webm']: name_ext = '.mp4'
                                elif f_type in ['audio', 'voice'] and not name_ext: name_ext = '.ogg' if f_type == 'voice' else '.mp3'

                                out_path = f"{orig_path}_bale_comp{name_ext}"
                                print(f"🗜 حجم فعلی ({bale_size:.2f}MB) بیش از سقف بله است. فشرده‌سازی...", flush=True)
                                if await asyncio.to_thread(compress_media, best_path, out_path, bale_max_size, f_type) and os.path.exists(out_path):
                                    act_size = os.path.getsize(out_path) / (1024 * 1024)
                                    files_to_cleanup.append(out_path)
                                    if act_size < best_size:
                                        bale_path, bale_size = out_path, act_size
                                        best_path, best_size = out_path, act_size

                        bale_processed_files.append({'path': bale_path, 'name': f_name, 'type': f_type, 'size_mb': bale_size})

                    translated_caption = caption_text
                    if caption_text or downloaded_files:
                        ai_media_paths = []
                        if use_ai_media and downloaded_files:
                            for i in range(len(downloaded_files)):
                                f_name = downloaded_files[i]['name']
                                f_type = downloaded_files[i]['type']
                                orig_path = downloaded_files[i]['original_path']
                                
                                paths = [orig_path, rubika_processed_files[i]['path'], bale_processed_files[i]['path']]
                                valid_paths = [p for p in paths if os.path.exists(p)]
                                smallest_path = min(valid_paths, key=os.path.getsize)
                                smallest_size = os.path.getsize(smallest_path) / (1024 * 1024)
                                
                                if smallest_size > 19.0 and (f_type in ['video', 'audio', 'voice']):
                                    current_ai_path = smallest_path
                                    for attempt, target_mb in enumerate([18.0, 14.0], start=1):
                                        name_ext = os.path.splitext(f_name)[1].lower()
                                        if f_type == 'video' and name_ext not in ['.mp4', '.mkv', '.mov', '.webm']: name_ext = '.mp4'
                                        elif f_type in ['audio', 'voice'] and not name_ext: name_ext = '.ogg' if f_type == 'voice' else '.mp3'
                                        
                                        ai_comp_path = f"{orig_path}_ai_comp_{attempt}{name_ext}"
                                        if await asyncio.to_thread(compress_media, current_ai_path, ai_comp_path, target_mb, f_type) and os.path.exists(ai_comp_path):
                                            act_size = os.path.getsize(ai_comp_path) / (1024 * 1024)
                                            files_to_cleanup.append(ai_comp_path)
                                            if act_size < (os.path.getsize(current_ai_path) / (1024 * 1024)):
                                                current_ai_path = ai_comp_path
                                                if act_size <= 19.5: break
                                            else: break
                                    ai_media_paths.append(current_ai_path)
                                else:
                                    ai_media_paths.append(smallest_path)

                        print(f"⏳ تحلیل محتوا برای مسیر '{r_name}'...", flush=True)
                        translated_caption = await process_with_ai(
                            caption_text, r_prompt, smart_filter, ai_media_paths,
                            ai_enabled, ai_hashtags, ai_translation
                        )
                        
                        if translated_caption == "__API_ERROR__":
                            print(f"⚠️ خطای جمینی: پردازش مسیر '{r_name}' لغو شد تا در دور بعدی مجددا تلاش شود.", flush=True)
                            continue
                        
                        if translated_caption.strip().upper() == "FILTERED":
                            print(f"🚫 پست در مسیر '{r_name}' توسط فیلتر هوشمند مسدود شد!", flush=True)
                            successful_routes.append(route)
                            continue

                    route_all_succeeded = True
                    bale_delay = route[19] if len(route) > 19 else False
                    rubika_delay = route[20] if len(route) > 20 else False
                    eitaa_delay = route[21] if len(route) > 21 else True
                    delayed_platforms = []

                    # ۱. بررسی و ارسال به روبیکا
                    rubika_allowed_files = []
                    if target_platform in ['all', 'rubika'] and rubika_enabled and r_rubika.strip():
                        rubika_dests = [format_channel_id(x) for x in r_rubika.split(',') if x.strip()]
                        rubika_allowed_files = [f for f in rubika_processed_files if f['size_mb'] <= rubika_max_size]

                        if not rubika_delay or bypass_id_check:
                            for r_channel in rubika_dests:
                                if rubika_allowed_files:
                                    total_files = len(rubika_allowed_files)
                                    for idx, file_obj in enumerate(rubika_allowed_files):
                                        is_last = (idx == total_files - 1)
                                        cap = translated_caption if is_last else ""
                                        rubika_success, rubika_res = await asyncio.to_thread(process_rubika_media, cap, r_channel, file_obj['path'], file_obj['name'], file_obj['type'])
                                        if rubika_success:
                                            if rubika_res and is_last:
                                                for m in messages:
                                                    save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'rubika', r_channel, rubika_res, 'media', get_telegram_media_id(m) if hasattr(m, 'id') else "")
                                        else:
                                            await notify_admin(msg_link, f"روبیکا ({r_channel})", f"خطا:\n{rubika_res}")
                                            route_all_succeeded = False
                                        await asyncio.sleep(2)
                                elif caption_text:
                                    rubika_success, rubika_res = await asyncio.to_thread(send_text_to_rubika, translated_caption, r_channel)
                                    if rubika_success and rubika_res:
                                        for m in messages:
                                            save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'rubika', r_channel, rubika_res, 'text', "")
                                    elif not rubika_success:
                                        await notify_admin(msg_link, f"روبیکا ({r_channel})", f"خطا:\n{rubika_res}")
                                        route_all_succeeded = False
                                    await asyncio.sleep(2)
                        else:
                            delayed_platforms.append('rubika')

                    # ۲. بررسی و ارسال به بله
                    bale_allowed_files = []
                    if target_platform in ['all', 'bale'] and bale_enabled and r_bale.strip():
                        bale_dests = [format_channel_id(x) for x in r_bale.split(',') if x.strip()]
                        bale_allowed_files = [f for f in bale_processed_files if f['size_mb'] <= bale_max_size]
                        
                        if not bale_delay or bypass_id_check:
                            for b_channel in bale_dests:
                                bale_success = True
                                bale_res = None
                                if len(bale_allowed_files) > 1:
                                    bale_success, bale_res = await asyncio.to_thread(send_album_to_bale, translated_caption, b_channel, bale_allowed_files)
                                    if bale_success and bale_res:
                                        for m in messages:
                                            save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'bale', b_channel, bale_res, 'album', get_telegram_media_id(m) if hasattr(m, 'id') else "")
                                elif len(bale_allowed_files) == 1:
                                    f_obj = bale_allowed_files[0]
                                    bale_success, bale_res = await asyncio.to_thread(send_single_media_to_bale, translated_caption, b_channel, f_obj['path'], f_obj['name'], f_obj['type'])
                                    if bale_success and bale_res:
                                        for m in messages:
                                            save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'bale', b_channel, bale_res, 'media', get_telegram_media_id(m) if hasattr(m, 'id') else "")
                                elif caption_text:
                                    bale_success, bale_res = await asyncio.to_thread(send_text_to_bale, translated_caption, b_channel)
                                    if bale_success and bale_res:
                                        for m in messages:
                                            save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'bale', b_channel, bale_res, 'text', "")
                                
                                if not bale_success:
                                    await notify_admin(msg_link, f"بله ({b_channel})", f"خطا:\n{bale_res}")
                                    route_all_succeeded = False
                                await asyncio.sleep(3)
                        else:
                            delayed_platforms.append('bale')

                    # ۳. بررسی و ارسال به ایتا (همراه با مدیریت محدودیت ۱۰۲۴ کاراکتر کپشن)
                    eitaa_allowed_files = []
                    if target_platform in ['all', 'eitaa'] and eitaa_enabled and r_eitaa.strip():
                        eitaa_dests = [clean_eitaa_channel(x) for x in r_eitaa.split(',') if clean_eitaa_channel(x)]
                        eitaa_allowed_files = [f for f in rubika_processed_files if f['size_mb'] <= eitaa_max_size]
                        
                        eitaa_caption = format_text_for_eitaa(translated_caption)
                        is_long_caption = len(eitaa_caption) > 1024

                        if not eitaa_delay or bypass_id_check:
                            for e_channel in eitaa_dests:
                                if eitaa_allowed_files:
                                    total_e_files = len(eitaa_allowed_files)
                                    for e_idx, file_obj in enumerate(eitaa_allowed_files):
                                        e_is_last = (e_idx == total_e_files - 1)
                                        # در صورت طولانی بودن کپشن (>1024)، کپشن روی فایل الصاق نمی‌شود تا متن ناقص نشود
                                        e_cap = (eitaa_caption if not is_long_caption else "") if e_is_last else ""
                                        e_success, e_res = await asyncio.to_thread(process_eitaa_media, e_cap, e_channel, file_obj['path'], file_obj['name'], file_obj['type'])
                                        if e_success and e_res and e_is_last:
                                            for m in messages:
                                                save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'eitaa', e_channel, e_res, 'media', get_telegram_media_id(m) if hasattr(m, 'id') else "")
                                        elif not e_success:
                                            await notify_admin_all_platforms(f"⚠️ **خطا در ارسال به ایتا**\n\nکانال مبدا: {chat_username}\nمقصد ایتا: {e_channel}\nعلت: {e_res}\nلینک: {msg_link}")
                                            route_all_succeeded = False
                                        await asyncio.sleep(2)
                                        
                                    # اگر کپشن بیش از ۱۰۲۴ کاراکتر بود، کل متن بلافاصله پس از فایل‌ها به صورت پیام متنی ارسال می‌شود
                                    if is_long_caption and eitaa_caption:
                                        print(f"📄 کپشن طولانی ({len(eitaa_caption)} کاراکتر) به صورت پیام متنی مجزا به ایتا ارسال می‌شود...", flush=True)
                                        t_success, t_res = await asyncio.to_thread(send_text_to_eitaa, eitaa_caption, e_channel)
                                        if not t_success:
                                            await notify_admin_all_platforms(f"⚠️ **خطا در ارسال متن طولانی به ایتا**\n\nکانال مبدا: {chat_username}\nمقصد ایتا: {e_channel}\nعلت: {t_res}\nلینک: {msg_link}")
                                            route_all_succeeded = False
                                        await asyncio.sleep(2)
                                        
                                elif eitaa_caption:
                                    e_success, e_res = await asyncio.to_thread(send_text_to_eitaa, eitaa_caption, e_channel)
                                    if e_success and e_res:
                                        for m in messages:
                                            save_msg_mapping(r_id, cid_clean, getattr(m, 'id', main_msg_id), 'eitaa', e_channel, e_res, 'text', "")
                                    elif not e_success:
                                        await notify_admin_all_platforms(f"⚠️ **خطا در ارسال به ایتا**\n\nکانال مبدا: {chat_username}\nمقصد ایتا: {e_channel}\nعلت: {e_res}\nلینک: {msg_link}")
                                        route_all_succeeded = False
                                    await asyncio.sleep(2)
                        else:
                            delayed_platforms.append('eitaa')

                    # ۴. نگهداری و زمان‌بندی پیام در صف تاخیر ۱۰ دقیقه‌ای در صورت وجود مقاصد با تاخیر
                    if delayed_platforms:
                        pending_dir = f"downloads/delayed_pending/{r_id}_{cid_clean}_{main_msg_id}"
                        os.makedirs(pending_dir, exist_ok=True)
                        
                        preserved_rubika_files = []
                        if "rubika" in delayed_platforms and rubika_allowed_files:
                            for f_obj in rubika_allowed_files:
                                safe_dest = os.path.join(pending_dir, f"r_{f_obj['name']}")
                                try:
                                    shutil.copy2(f_obj['path'], safe_dest)
                                    preserved_rubika_files.append({
                                        'path': safe_dest,
                                        'name': f_obj['name'],
                                        'type': f_obj['type'],
                                        'size_mb': f_obj['size_mb']
                                    })
                                except Exception as cpy_err:
                                    print(f"⚠️ خطا در نگهداری فایل برای روبیکا: {cpy_err}", flush=True)

                        preserved_bale_files = []
                        if "bale" in delayed_platforms and bale_allowed_files:
                            for f_obj in bale_allowed_files:
                                safe_dest = os.path.join(pending_dir, f"b_{f_obj['name']}")
                                try:
                                    shutil.copy2(f_obj['path'], safe_dest)
                                    preserved_bale_files.append({
                                        'path': safe_dest,
                                        'name': f_obj['name'],
                                        'type': f_obj['type'],
                                        'size_mb': f_obj['size_mb']
                                    })
                                except Exception as cpy_err:
                                    print(f"⚠️ خطا در نگهداری فایل برای بله: {cpy_err}", flush=True)

                        preserved_eitaa_files = []
                        if "eitaa" in delayed_platforms and eitaa_allowed_files:
                            for f_obj in eitaa_allowed_files:
                                safe_dest = os.path.join(pending_dir, f"e_{f_obj['name']}")
                                try:
                                    shutil.copy2(f_obj['path'], safe_dest)
                                    preserved_eitaa_files.append({
                                        'path': safe_dest,
                                        'name': f_obj['name'],
                                        'type': f_obj['type'],
                                        'size_mb': f_obj['size_mb']
                                    })
                                except Exception as cpy_err:
                                    print(f"⚠️ خطا در نگهداری فایل برای ایتا: {cpy_err}", flush=True)

                        q_key = f"{r_id}_{cid_clean}_{main_msg_id}"
                        if q_key in _DELAY_QUEUE:
                            old_t = _DELAY_QUEUE[q_key].get("task")
                            if old_t and not old_t.done(): old_t.cancel()

                        del_task = asyncio.create_task(run_delayed_sender(q_key, 600))
                        _DELAY_QUEUE[q_key] = {
                            "task": del_task,
                            "route_id": r_id,
                            "cid_clean": cid_clean,
                            "main_msg_id": main_msg_id,
                            "caption": translated_caption,
                            "pending_dir": pending_dir,
                            "chat_username": chat_username,
                            "msg_link": msg_link,
                            "messages": messages,
                            "platforms": delayed_platforms,
                            "r_rubika": r_rubika,
                            "rubika_files": preserved_rubika_files,
                            "r_bale": r_bale,
                            "bale_files": preserved_bale_files,
                            "r_eitaa": r_eitaa,
                            "eitaa_files": preserved_eitaa_files,
                            "expire_at": time.time() + 600
                        }
                        plat_names = "، ".join({"rubika": "روبیکا", "bale": "بله", "eitaa": "ایتا"}.get(p, p) for p in delayed_platforms)
                        print(f"⏳ پیام {main_msg_id} برای ارسال به ({plat_names}) با تاخیر ۱۰ دقیقه‌ای در صف قرار گرفت.", flush=True)
                for path in set(files_to_cleanup):
                    if os.path.exists(path):
                        try: os.remove(path)
                        except: pass
                print("🗑 فایل‌های موقت پاک شدند.", flush=True)

                max_id_in_group = max(m.id for m in messages)
                for r in successful_routes:
                    route_id = r[0]
                    current_max = get_last_processed_id(route_id, cid_clean)
                    if max_id_in_group > current_max:
                        set_last_processed_id(route_id, cid_clean, max_id_in_group)
                        print(f"✅ دیتابیس مسیر '{r[1]}' برای مبدا ({chat_username}) آپدیت شد (شناسه {max_id_in_group}).", flush=True)

            finally:
                # آزادسازی پیام‌ها از وضعیت در حال پردازش
                async with _IN_FLIGHT_GUARD:
                    for fk in flight_keys:
                        _IN_FLIGHT_MSGS.discard(fk)

async def background_poller(client):
    print("🔄 سیستم رادار برای شکار پیام‌های گمشده (نسخه کاملا ایزوله‌شده مسیرها) فعال شد.", flush=True)
    while True:
        # افزایش فاصله بررسی رادار به ۶۰ ثانیه جهت جلوگیری از حساسیت تلگرام و خطای FloodWait
        await asyncio.sleep(60) 
        routes = get_routes() 
        channels_to_check = set()
        
        for r in routes:
            if str(r[0]) in _ROUTES_AWAITING_SYNC:
                continue
            bale_en, rubika_en = r[13], r[14]
            eitaa_en = r[18] if len(r) > 18 else True
            if not bale_en and not rubika_en and not eitaa_en: continue

            raw_src = r[2] if r[2] else ""
            src_list = [x.strip().replace('@', '').replace('https://t.me/', '').replace('t.me/', '').lower() for x in re.split(r'[,،\n\s]+', raw_src) if x.strip()]
            for ch in src_list: channels_to_check.add(ch)

        for channel in channels_to_check:
            try:
                # تبدیل شناسه‌های عددی کانال‌ها به int جهت سازگاری کامل با متد get_entity در تلتون
                target_peer = int(channel) if (channel.startswith("-") and channel.lstrip("-").isdigit()) or channel.isdigit() else channel
                chat_info = await client.get_entity(target_peer)
                chat_id_str = str(chat_info.id)
                cid_clean = std_id(chat_id_str)
                chat_username = getattr(chat_info, 'username', None) or chat_id_str
                
                for r in routes:
                    route_id = r[0]
                    eitaa_en = r[18] if len(r) > 18 else True
                    if not r[13] and not r[14] and not eitaa_en: continue
                    
                    r_src_list = [x.strip().replace('@', '').replace('https://t.me/', '').replace('t.me/', '').lower() for x in re.split(r'[,،\n\s]+', r[2] if r[2] else "") if x.strip()]
                    
                    if channel in r_src_list:
                        last_id = get_last_processed_id(route_id, cid_clean)
                        
                        if last_id == 0:
                            async for msg in client.iter_messages(channel, limit=1):
                                set_last_processed_id(route_id, cid_clean, msg.id)
                            continue
                        
                        raw_missed = []
                        async for msg in client.iter_messages(channel, min_id=last_id, limit=50):
                            raw_missed.append(msg)
                            
                        # فیلتر هوشمند پیام‌هایی که هم‌اکنون در حال ارسال هستند یا قبلاً ارسال شده‌اند
                        missed_msgs = []
                        for msg in raw_missed:
                            f_key = f"{cid_clean}_{msg.id}"
                            if f_key in _IN_FLIGHT_MSGS:
                                continue
                            existing_maps = await asyncio.to_thread(get_msg_mappings, route_id, cid_clean, msg.id)
                            if existing_maps:
                                continue
                            missed_msgs.append(msg)

                        if missed_msgs:
                            missed_msgs.reverse()
                            max_missed_id = max(m.id for m in missed_msgs)
                            print(f"\n⚡️ رادار {len(missed_msgs)} پیام گمشده در کانال {channel} را برای مسیر '{r[1]}' پیدا کرد!", flush=True)
                            
                            for idx_m, msg in enumerate(missed_msgs):
                                try:
                                    await route_message(msg, chat_username, [r])
                                except FloodWaitError as e:
                                    print(f"⏳ خطای FloodWait رادار! مکث برای {e.seconds} ثانیه...", flush=True)
                                    await asyncio.sleep(e.seconds + 2)
                                    await route_message(msg, chat_username, [r])
                                
                                next_msg = missed_msgs[idx_m + 1] if idx_m + 1 < len(missed_msgs) else None
                                is_same_album = bool(msg.grouped_id and next_msg and next_msg.grouped_id == msg.grouped_id)
                                if not is_same_album:
                                    await asyncio.sleep(2)
                            
                            if not any(getattr(m, 'grouped_id', None) is not None for m in missed_msgs):
                                current_max = get_last_processed_id(route_id, cid_clean)
                                if max_missed_id > current_max:
                                    set_last_processed_id(route_id, cid_clean, max_missed_id)
                                    
            except FloodWaitError as e:
                print(f"⏳ محدودیت خواندن تلگرام (رادار)! مکث {e.seconds} ثانیه...", flush=True)
                await asyncio.sleep(e.seconds + 2)
            except Exception as e:
                print(f"⚠️ خطای نامشخص رادار در کانال {channel}: {e}", flush=True)
            
            await asyncio.sleep(2)

# =======================================================================
# سیستم پیشرفته شبیه‌ساز (Mock) برای اتصال پنل مدیریت تلگرام به بله و روبیکا
# =======================================================================
def serialize_telethon_kb(kb):
    if not kb: return None
    try:
        if isinstance(kb, str):
            try: kb = json.loads(kb)
            except: pass
        if isinstance(kb, dict):
            if "inline_keyboard" in kb or "keyboard" in kb:
                return json.dumps(kb)
            return json.dumps({"inline_keyboard": kb})

        if hasattr(kb, 'rows'):
            out = []
            for r in kb.rows:
                out_row = []
                for b in getattr(r, 'buttons', []):
                    inner = getattr(b, 'button', b)
                    text = getattr(b, 'text', getattr(inner, 'text', ''))
                    data = getattr(b, 'data', getattr(inner, 'data', None))
                    url = getattr(b, 'url', getattr(inner, 'url', None))
                    btn_dict = {"text": str(text)}
                    if url:
                        btn_dict["url"] = str(url)
                    elif data is not None:
                        if isinstance(data, bytes):
                            data_str = data.decode('utf-8', errors='ignore')
                        else:
                            data_str = str(data)
                        btn_dict["callback_data"] = data_str
                    out_row.append(btn_dict)
                if out_row:
                    out.append(out_row)
            if out:
                return json.dumps({"inline_keyboard": out})

        if not isinstance(kb, (list, tuple)):
            kb = [kb]
            
        out = []
        for row in kb:
            if not isinstance(row, (list, tuple)):
                row = [row]
            out_row = []
            for btn in row:
                if isinstance(btn, dict):
                    out_row.append(btn)
                    continue
                inner = getattr(btn, 'button', btn)
                
                text = getattr(inner, 'text', None)
                if text is None or callable(text):
                    text = getattr(btn, 'text', '')
                if callable(text):
                    text = str(btn)
                    
                data = getattr(inner, 'data', None)
                if data is None:
                    data = getattr(btn, 'data', None)
                url = getattr(inner, 'url', None)
                if url is None:
                    url = getattr(btn, 'url', None)
                    
                btn_dict = {"text": str(text)}
                if url:
                    btn_dict["url"] = str(url)
                elif data is not None:
                    if isinstance(data, bytes):
                        data_str = data.decode('utf-8', errors='ignore')
                    else:
                        data_str = str(data)
                    btn_dict["callback_data"] = data_str
                else:
                    btn_dict["callback_data"] = str(text)
                    
                out_row.append(btn_dict)
            if out_row:
                out.append(out_row)
        if out:
            return json.dumps({"inline_keyboard": out})
    except Exception as e:
        print(f"⚠️ خطای تبدیل کیبورد برای پلتفرم: {e}", flush=True)
    return None

def send_to_platform(platform, chat_id, text, buttons):
    kb_json = serialize_telethon_kb(buttons)
    if platform == "bale":
        url = f"https://tapi.bale.ai/bot{BALE_TOKEN}/sendMessage"
        payload = {"chat_id": chat_id, "text": text}
        if kb_json: payload["reply_markup"] = json.loads(kb_json)
        try:
            res = _bale_eitaa_post(url, json=payload, proxies=DIRECT_PROXY, timeout=10)
            if res.status_code != 200:
                print(f"⚠️ خطای بله در ارسال پیام ({res.status_code}): {res.text}", flush=True)
        except Exception as e:
            print(f"⚠️ خطای استثنا ارسال به بله: {e}", flush=True)
    elif platform == "rubika":
        plain_text, metadata = parse_markdown_to_rubika(text)
        payload = {"chat_id": str(chat_id), "text": plain_text or text}
        if metadata: payload["metadata"] = metadata
        try:
            _rubika_post(
                f"https://botapi.rubika.ir/v3/{RUBIKA_TOKEN}/sendMessage",
                json=payload,
                headers={"User-Agent": "Mozilla/5.0"},
                proxies=DIRECT_PROXY,
                timeout=10
            )
        except: pass

def edit_on_platform(platform, chat_id, msg_id, text, buttons):
    if platform == "bale":
        cid = int(chat_id) if str(chat_id).lstrip('-').isdigit() else chat_id
        mid = int(msg_id) if msg_id and str(msg_id).isdigit() else None
        kb_json = serialize_telethon_kb(buttons)
        
        # ۱. ویرایش مستقیم پیام و دکمه‌ها درجا بدون حذف پیام (دقیقاً همانند تلگرام)
        if mid:
            url = f"https://tapi.bale.ai/bot{BALE_TOKEN}/editMessageText"
            payload = {"chat_id": cid, "message_id": mid, "text": text}
            if kb_json:
                payload["reply_markup"] = json.loads(kb_json)
            try:
                res = _bale_eitaa_post(url, json=payload, proxies=DIRECT_PROXY, timeout=10)
                if res.status_code == 200:
                    return
            except Exception:
                pass
                
        # ۲. اگر ویرایش درجا به هر دلیلی با خطا مواجه شد، پیام جدید ارسال می‌شود
        send_to_platform(platform, chat_id, text, buttons)
    elif platform == "rubika":
        send_to_platform(platform, chat_id, text, buttons)

class MockMessage:
    def __init__(self, chat_id, text, msg_id=None, platform="bale"):
        self.chat_id = int(chat_id) if str(chat_id).lstrip('-').isdigit() else chat_id
        self.text = text
        self.raw_text = text
        self.id = int(msg_id) if msg_id and str(msg_id).isdigit() else int(time.time())
        self.platform = platform
        
    async def reply(self, text, buttons=None):
        await asyncio.to_thread(send_to_platform, self.platform, self.chat_id, text, buttons)
        
    async def edit(self, text, buttons=None):
        await asyncio.to_thread(edit_on_platform, self.platform, self.chat_id, self.id, text, buttons)

class MockEvent:
    def __init__(self, message, client=None):
        self.message = message
        self.chat_id = message.chat_id
        self.sender_id = message.chat_id
        self.text = message.text
        self.raw_text = message.raw_text
        self.client = client
        self.is_private = True
        self.is_group = False
        self.is_channel = False

class MockCallbackQueryEvent:
    def __init__(self, chat_id, data, msg_id, platform="bale", sender_id=None):
        self.chat_id = int(chat_id) if str(chat_id).lstrip('-').isdigit() else chat_id
        self.sender_id = int(sender_id) if sender_id and str(sender_id).lstrip('-').isdigit() else self.chat_id
        self.data = data.encode('utf-8') if isinstance(data, str) else data
        self.msg_id = int(msg_id) if msg_id and str(msg_id).isdigit() else None
        self.platform = platform
        self.message = MockMessage(self.chat_id, "", self.msg_id, platform)
        self.is_private = True
        self.is_group = False
        self.is_channel = False
        
    async def edit(self, text, buttons=None):
        await asyncio.to_thread(edit_on_platform, self.platform, self.chat_id, self.msg_id, text, buttons)

    async def reply(self, text, buttons=None):
        await asyncio.to_thread(send_to_platform, self.platform, self.chat_id, text, buttons)

    async def respond(self, text, buttons=None):
        await asyncio.to_thread(send_to_platform, self.platform, self.chat_id, text, buttons)

    async def answer(self, text=None, alert=False):
        pass

async def bale_admin_poller():
    if not BALE_TOKEN: return
    offset = 0
    token_src = "BALE_TOKEN_ROUTER" if os.environ.get("BALE_TOKEN_ROUTER") else "BALE_TOKEN"
    print(f"🚀 رادار کنترل پنل 'بله' فعال شد (منبع توکن: {token_src}).", flush=True)
    if not os.environ.get("BALE_TOKEN_ROUTER"):
        print("⚠️ توجه: متغیر BALE_TOKEN_ROUTER در Secretها تعریف نشده است. اگر ربات دستیار دیگری همزمان در حال اجرا باشد، ممکن است کلیک دکمه‌ها بین دو ربات تداخل پیدا کند.", flush=True)
    while True:
        try:
            url = f"https://tapi.bale.ai/bot{BALE_TOKEN}/getUpdates?offset={offset}&timeout=20"
            res = await asyncio.to_thread(_bale_eitaa_get, url, proxies=DIRECT_PROXY, timeout=30)
            if res.status_code == 200:
                data = res.json()
                if data.get("ok"):
                    for update in data.get("result", []):
                        offset = update["update_id"] + 1
                        admins = get_all_admins()
                        
                        # بررسی با بالاترین اولویت برای رویداد کلیک دکمه‌های شیشه‌ای
                        if "callback_query" in update or "callbackQuery" in update:
                            cq = update.get("callback_query") or update.get("callbackQuery")
                            sender_id = str(cq.get("from", {}).get("id") or cq.get("from_user", {}).get("id") or cq.get("user", {}).get("id") or "")
                            msg_obj = cq.get("message") or {}
                            chat_obj = msg_obj.get("chat") if isinstance(msg_obj, dict) else None
                            if isinstance(chat_obj, dict):
                                chat_id = str(chat_obj.get("id", ""))
                            elif chat_obj is not None:
                                chat_id = str(chat_obj)
                            else:
                                chat_id = sender_id
                                
                            msg_id = msg_obj.get("message_id") if isinstance(msg_obj, dict) else None
                            cb_data = str(cq.get("data") or cq.get("callback_data") or cq.get("payload") or "")
                            cq_id = cq.get("id")
                            
                            
                            # پاسخ به callback_query به صورت ناهمگام در پس‌زمینه جهت توقف چرخش لودینگ
                            if cq_id:
                                def _ack(qid):
                                    try:
                                        _bale_eitaa_post(
                                            f"https://tapi.bale.ai/bot{BALE_TOKEN}/answerCallbackQuery",
                                            json={"callback_query_id": str(qid)},
                                            proxies=DIRECT_PROXY,
                                            timeout=5
                                        )
                                    except Exception: pass
                                asyncio.create_task(asyncio.to_thread(_ack, cq_id))
                                
                            if chat_id in admins or sender_id in admins:
                                mock_cq = MockCallbackQueryEvent(chat_id, cb_data, msg_id, "bale", sender_id)
                                asyncio.create_task(callback_handler(mock_cq))

                        elif "message" in update:
                            msg = update["message"]
                            sender_id = str(msg.get("from", {}).get("id", ""))
                            chat_id = str(msg.get("chat", {}).get("id", "")) or sender_id
                            text = msg.get("text") or msg.get("caption") or ""
                            if chat_id in admins or sender_id in admins:
                                mock_msg = MockMessage(chat_id, text, msg.get("message_id"), "bale")
                                asyncio.create_task(admin_handler(MockEvent(mock_msg, bot_app)))
        except Exception as e:
            print(f"⚠️ خطای حلقه رادار بله: {e}", flush=True)
        await asyncio.sleep(1)



async def rubika_admin_poller():
    if not RUBIKA_TOKEN: return
    print("🚀 زیرساخت کنترل پنل روبیکا آماده شد.", flush=True)
    while True:
        await asyncio.sleep(3600)
# =======================================================================

async def main():
    print("🚀 در حال راه‌اندازی...", flush=True)
    try: requests.get(f"https://api.telegram.org/bot{CONTROL_BOT_TOKEN}/deleteWebhook?drop_pending_updates=True", timeout=60)
    except: pass

    # --- تغییرات ۲: مدیریت خطای ابطال سشن (AuthKeyUnregisteredError) و توقف ایمن سیستم ---
    try:
        await user_app.start()
    except AuthKeyUnregisteredError:
        error_msg = "🚨 هشدار بحرانی: سشن تلگرام شما (SESSION_STRING) باطل شده است! برنامه برای جلوگیری از کرش متوقف شد."
        print(error_msg, flush=True)
        # ارسال پیغام بحرانی به ادمین در بله
        send_to_platform("bale", ADMIN_ID, error_msg, None)
        sys.exit(1) # خروج ایمن و جلوگیری از اجرای پروسه‌های بعدی

    await bot_app.start(bot_token=CONTROL_BOT_TOKEN)
    print("✅ سیستم مسیریاب با موفقیت فعال شد!", flush=True)
    
    print("\n🔄 در حال همگام‌سازی کانال‌ها و بارگذاری اطلاعات اولیه در رم...", flush=True)
    
    load_all_admins()
    load_all_states() 
    load_all_msg_mappings()
    routes = get_routes()
    
    synced_channels = set()
    for r in routes:
        route_id = r[0]
        eitaa_en = r[18] if len(r) > 18 else True
        if not r[13] and not r[14] and not eitaa_en: continue 
        src_list = [x.strip().replace('@', '').replace('https://t.me/', '').replace('t.me/', '').lower() for x in re.split(r'[,،\n\s]+', r[2] if r[2] else "") if x.strip()]
        for channel in src_list:
            # کلید همگام‌سازی ترکیبی از مسیر و کانال است تا برای مسیرهای مختلف مجزا عمل کند
            sync_key = f"{route_id}_{channel}"
            if sync_key not in synced_channels:
                synced_channels.add(sync_key)
                try:
                    chat_info = await user_app.get_entity(channel)
                    chat_id_str = str(chat_info.id)
                    async for msg in user_app.iter_messages(channel, limit=1):
                        # اعمال route_id برای جلوگیری از خطا
                        if get_last_processed_id(route_id, chat_id_str) == 0:
                            set_last_processed_id(route_id, chat_id_str, msg.id)
                        break
                    print(f"✅ کانال {channel} برای مسیر '{r[1]}' ثبت شد.", flush=True)
                except Exception: pass
                await asyncio.sleep(1.5)
                
    print("🏁 ربات آماده دریافت پیام‌های جدید است!\n", flush=True)
    
    asyncio.create_task(background_poller(user_app))
    asyncio.create_task(bale_admin_poller())
    asyncio.create_task(rubika_admin_poller())
    
    await custom_idle()
    
    print("🛑 سیگنال توقف دریافت شد. در حال ذخیره دیتا از رم به دیتابیس...", flush=True)
    flush_all_to_db()

if __name__ == "__main__":
    try: 
        loop = asyncio.get_event_loop()
    except RuntimeError:
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
    loop.run_until_complete(main())
# =======================================================================
# هندلر رویداد حذف پیام در تلگرام (حذف خودکار بله و روبیکا + مدیریت ایتا)
# =======================================================================
@user_app.on(events.MessageDeleted)
async def message_deleted_handler(event):
    chat_id = event.chat_id
    if not chat_id: return
    chat_id_str = str(chat_id)
    cid_clean = std_id(chat_id_str)
    
    active_routes = get_routes()
    
    for deleted_id in event.deleted_ids:
        # ۱. لغو از صف تاخیر ۱۰ دقیقه‌ای در صورت وجود
        for r in active_routes:
            r_id = r[0]
            q_key = f"{r_id}_{cid_clean}_{deleted_id}"
            if q_key in _DELAY_QUEUE:
                item = _DELAY_QUEUE.pop(q_key, None)
                if item:
                    t = item.get("task")
                    if t and not t.done(): t.cancel()
                    p_dir = item.get("pending_dir")
                    if p_dir and os.path.exists(p_dir):
                        shutil.rmtree(p_dir, ignore_errors=True)
                    print(f"🗑 پیام {deleted_id} در تلگرام حذف شد و از صف تاخیر مسیر '{r[1]}' لغو گردید.", flush=True)
        # ۲. بررسی پیام‌های قبلاً ارسال شده
        for r in active_routes:
            r_id = r[0]
            mappings = await asyncio.to_thread(get_msg_mappings, r_id, cid_clean, deleted_id)
            if not mappings:
                mappings = await asyncio.to_thread(get_msg_mappings, r_id, chat_id_str, deleted_id)
                
            for platform, dest_chat_id, dest_msg_id, _, _ in mappings:
                if platform == 'bale':
                    print(f"🗑 حذف خودکار پیام {dest_msg_id} از بله ({dest_chat_id})...", flush=True)
                    await asyncio.to_thread(delete_from_bale, dest_chat_id, dest_msg_id)
                elif platform == 'rubika':
                    print(f"🗑 حذف خودکار پیام {dest_msg_id} از روبیکا ({dest_chat_id})...", flush=True)
                    await asyncio.to_thread(delete_from_rubika, dest_chat_id, dest_msg_id)
                elif platform == 'eitaa':
                    warn_msg = (f"⚠️ **هشدار حذف پیام در ایتا**\n\n"
                                f"پیام شماره `{deleted_id}` در کانال مبدا تلگرام حذف شد.\n"
                                f"با توجه به اینکه این پیام قبلاً به کانال ایتا (`{dest_chat_id}`) ارسال شده و ایتا از حذف خودکار پشتیبانی نمی‌کند، لطفاً در صورت نیاز به صورت دستی از کانال ایتا حذف فرمایید.")
                    await notify_admin_all_platforms(warn_msg)


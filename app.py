"""우리집 재고실 | Python 3.11+ | streamlit run app.py

배포: app.py와 requirements.txt를 GitHub 저장소에 업로드한 뒤
Streamlit Community Cloud에서 app.py를 실행 파일로 선택하세요.
GitHub Pages에서는 Python/Streamlit 서버를 실행할 수 없습니다.

Streamlit 설정 > Secrets (선택, 실제 가족 사용 시 모두 권장):
APP_PASSWORD = "가족만 아는 긴 비밀번호"
APP_URL = "https://your-app.streamlit.app"
DATABASE_URL = "postgresql://USER:PASSWORD@HOST:5432/DB?sslmode=require"

DATABASE_URL: Supabase/Neon 등 PostgreSQL 연결 문자열(가급적 pooler).
연결 문자열과 비밀번호는 GitHub 코드에 쓰지 마세요.
미설정 시 SQLite 데모 모드: Cloud 재시작/재배포 시 데이터 유실 가능.
한 앱/DB는 한 가족용입니다. QR에는 위치만 담고 비밀번호는 담지 않습니다.
사진은 DB에 저장합니다(최대 2MB/장). QR로 로그인 인증을 대체하지 않습니다.
"""
from __future__ import annotations

import csv
import hashlib
import hmac
import html
import io
import json
import os
import sqlite3
import statistics
import uuid
from contextlib import contextmanager
from datetime import date, datetime, timedelta
from urllib.parse import urlencode, urlsplit, urlunsplit, parse_qsl
from zoneinfo import ZoneInfo

import pandas as pd
import qrcode
import streamlit as st

st.set_page_config(page_title="우리집 재고실", page_icon="🏠", layout="centered")
TZ = ZoneInfo("Asia/Seoul")
CATEGORIES = ["생필품", "식품", "생활물품", "가전·필터", "기타"]
STATUSES = ["구매 예정", "주문 완료", "도착"]


def today():
    return datetime.now(TZ).date()


def stamp():
    return datetime.now(TZ).isoformat(timespec="seconds")


def setting(key, default=""):
    try:
        return str(st.secrets.get(key, os.environ.get(key, default)))
    except (FileNotFoundError, st.errors.StreamlitSecretNotFoundError):
        return os.environ.get(key, default)


PG = bool(setting("DATABASE_URL"))


@contextmanager
def db():
    if PG:
        import psycopg
        from psycopg.rows import dict_row
        conn = psycopg.connect(setting("DATABASE_URL"), row_factory=dict_row, connect_timeout=12)
    else:
        conn = sqlite3.connect("home_inventory.sqlite3", timeout=20)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA foreign_keys=ON")
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def sql(conn, text, params=()):
    return conn.execute(text.replace("?", "%s") if PG else text, params)


def rows(text, params=()):
    with db() as conn:
        return [dict(r) for r in sql(conn, text, params).fetchall()]


def initialize():
    blob = "BYTEA" if PG else "BLOB"
    with db() as conn:
        for ddl in [
            "CREATE TABLE IF NOT EXISTS locations(id TEXT PRIMARY KEY, name TEXT NOT NULL UNIQUE)",
            f"""CREATE TABLE IF NOT EXISTS items(
                id TEXT PRIMARY KEY, name TEXT NOT NULL, aliases TEXT NOT NULL,
                category TEXT NOT NULL, location_id TEXT NOT NULL REFERENCES locations(id),
                qty INTEGER NOT NULL CHECK(qty>=0), minimum INTEGER NOT NULL CHECK(minimum>=0),
                unit TEXT NOT NULL, expiry TEXT, interval_days INTEGER NOT NULL,
                last_maintenance TEXT, memo TEXT NOT NULL, photo {blob}, created TEXT NOT NULL)""",
            """CREATE TABLE IF NOT EXISTS purchases(
                id TEXT PRIMARY KEY, item_id TEXT NOT NULL REFERENCES items(id),
                qty INTEGER NOT NULL CHECK(qty>0), status TEXT NOT NULL,
                buyer TEXT NOT NULL, created TEXT NOT NULL, arrived TEXT)""",
            """CREATE TABLE IF NOT EXISTS events(
                id TEXT PRIMARY KEY, item_id TEXT NOT NULL REFERENCES items(id),
                kind TEXT NOT NULL, qty INTEGER NOT NULL, occurred TEXT NOT NULL,
                actor TEXT NOT NULL, note TEXT NOT NULL)""",
        ]:
            sql(conn, ddl)
        for name in ["주방", "다용도실", "거실", "안방", "욕실"]:
            sql(conn, "INSERT INTO locations(id,name) VALUES(?,?) ON CONFLICT(name) DO NOTHING", (uuid.uuid4().hex, name))


def event(conn, item_id, kind, qty=0, note=""):
    sql(conn, "INSERT INTO events VALUES(?,?,?,?,?,?,?)", (uuid.uuid4().hex, item_id, kind, qty, stamp(), st.session_state.get("actor", "가족"), note))


def ensure_purchase(conn, item_id):
    # Item row must already be locked by the caller for concurrent writes.
    item = dict(sql(conn, "SELECT * FROM items WHERE id=?", (item_id,)).fetchone())
    if item["qty"] > item["minimum"]:
        return
    active = sql(conn, "SELECT id FROM purchases WHERE item_id=? AND status<>?", (item_id, "도착")).fetchone()
    if not active:
        sql(conn, "INSERT INTO purchases VALUES(?,?,?,?,?,?,?)", (uuid.uuid4().hex, item_id, max(1, item["minimum"] + 1 - item["qty"]), "구매 예정", "", stamp(), None))


def lock_item(conn, item_id):
    suffix = " FOR UPDATE" if PG else ""
    if not PG:
        sql(conn, "BEGIN IMMEDIATE")
    row = sql(conn, "SELECT * FROM items WHERE id=?" + suffix, (item_id,)).fetchone()
    if not row:
        raise ValueError("물건이 존재하지 않습니다.")
    return dict(row)


def change_stock(item_id, amount, kind):
    with db() as conn:
        item = lock_item(conn, item_id)
        if item["qty"] + amount < 0:
            raise ValueError("남은 수량보다 많이 처리할 수 없습니다.")
        sql(conn, "UPDATE items SET qty=qty+? WHERE id=?", (amount, item_id))
        event(conn, item_id, kind, abs(amount))
        ensure_purchase(conn, item_id)


def transition(purchase_id, target):
    with db() as conn:
        p = sql(conn, "SELECT * FROM purchases WHERE id=?", (purchase_id,)).fetchone()
        if not p:
            raise ValueError("구매 항목이 없습니다.")
        lock_item(conn, p["item_id"])
        p = dict(sql(conn, "SELECT * FROM purchases WHERE id=?", (purchase_id,)).fetchone())
        if target == "주문 완료" and p["status"] == "구매 예정":
            sql(conn, "UPDATE purchases SET status=?,buyer=? WHERE id=?", (target, st.session_state["actor"], purchase_id))
        elif target == "도착" and p["status"] == "주문 완료":
            sql(conn, "UPDATE purchases SET status=?,arrived=? WHERE id=?", (target, stamp(), purchase_id))
            sql(conn, "UPDATE items SET qty=qty+? WHERE id=?", (p["qty"], p["item_id"]))
            event(conn, p["item_id"], "입고", p["qty"], "구매 도착 확인")
        else:
            raise ValueError("이미 다른 가족이 처리했거나 올바른 순서가 아닙니다. 새로고침해 주세요.")


def forecast(item, events):
    # Complete start→finish cycles only. Unpaired or duplicate starts are not counted.
    start = None
    durations = []
    for e in sorted((e for e in events if e["item_id"] == item["id"]), key=lambda e: e["occurred"]):
        if e["kind"] == "사용 시작":
            start = datetime.fromisoformat(e["occurred"]).date()
        elif e["kind"] == "주기 취소":
            start = None
        elif e["kind"] == "다 씀" and start:
            days = (datetime.fromisoformat(e["occurred"]).date() - start).days
            if days > 0:
                durations.append(days)
            start = None
    if len(durations) < 2:
        return None, len(durations), start, None
    typical = statistics.median(durations[-6:])
    due = start + timedelta(days=round(typical)) if start else None
    return due, len(durations), start, typical


def make_qr_url(base, location_id):
    parts = urlsplit(base.strip())
    if parts.scheme != "https" or not parts.netloc or parts.username or parts.password:
        raise ValueError("https:// 로 시작하는 실제 배포 주소를 입력하세요.")
    query = dict(parse_qsl(parts.query, keep_blank_values=True))
    query["loc"] = location_id
    return urlunsplit((parts.scheme, parts.netloc, parts.path, urlencode(query), ""))


def refresh(message):
    st.session_state["notice"] = message
    st.rerun()


def action(call, message):
    try:
        call()
    except Exception as exc:
        st.error(str(exc) if isinstance(exc, ValueError) else "저장하지 못했습니다. 연결 상태를 확인하고 새로고침해 주세요.")
    else:
        refresh(message)


def parse_date(value):
    return date.fromisoformat(value) if value else None


def label(item, locations):
    return f'{item["name"]} · {locations.get(item["location_id"], "위치 없음")}'


def main():
    st.markdown("""<style>
    .stApp {background:#f5f7fb;}
    .block-container {max-width:820px;padding-top:1.4rem;padding-bottom:4rem;}
    h1,h2,h3 {color:#172b40;letter-spacing:-.035em;}
    div[data-testid="stVerticalBlockBorderWrapper"] {border-radius:18px;background:white;}
    .stButton button,.stDownloadButton button {min-height:46px;border-radius:12px;}
    div[data-testid="stMetric"] {background:white;border:1px solid #dfe5ed;border-radius:14px;padding:12px;}
    div[data-baseweb="input"] input {font-size:16px;}
    @media(max-width:600px){.block-container{padding-left:1rem;padding-right:1rem;}
    h1{font-size:1.8rem!important;} div[data-testid="stHorizontalBlock"]{gap:.5rem;}}
    </style>""", unsafe_allow_html=True)
    st.title("🏠 우리집 재고실")
    st.caption("어디에 있는지부터, 언제 사야 하는지까지.")
    password = setting("APP_PASSWORD")
    if password:
        if not st.session_state.get("authenticated"):
            with st.form("login"):
                st.subheader("가족 입장")
                entered = st.text_input("가족 비밀번호", type="password")
                submitted = st.form_submit_button("입장하기", use_container_width=True)
            if submitted:
                if hmac.compare_digest(entered.encode(), password.encode()):
                    st.session_state["authenticated"] = True
                    st.rerun()
                else:
                    st.error("비밀번호가 맞지 않습니다.")
            return
    else:
        st.warning("현재 공개 데모 모드입니다. 실제 가족 데이터는 설정에서 APP_PASSWORD를 지정한 후 등록하세요.")
    try:
        initialize()
        locations_raw = rows("SELECT * FROM locations ORDER BY name")
        items = rows("SELECT * FROM items ORDER BY name,created")
        events = rows("SELECT * FROM events ORDER BY occurred DESC")
        purchases = rows("SELECT * FROM purchases ORDER BY created DESC")
    except Exception:
        st.error("데이터베이스에 연결하지 못했습니다. DATABASE_URL과 DB 접속 허용 설정을 확인하세요. 비밀번호가 포함된 오류 내용은 공개하지 마세요.")
        return
    locations = {r["id"]: r["name"] for r in locations_raw}
    item_map = {i["id"]: i for i in items}
    if "actor" not in st.session_state:
        st.session_state["actor"] = "가족"
    with st.expander("👤 사용자 · 새로고침"):
        st.text_input("기록에 남길 이름 (실명 대신 별명 권장)", key="actor", max_chars=30)
        if st.button("최신 데이터 새로고침", use_container_width=True):
            st.rerun()
        if password and st.button("로그아웃", use_container_width=True):
            st.session_state.clear()
            st.rerun()
    if not st.session_state["actor"].strip():
        st.warning("기록에 남길 이름을 입력해 주세요.")
        return
    if not PG:
        st.caption("⚠️ SQLite 데모 저장 중 · Cloud 영구 보관은 PostgreSQL 연결 필요")
    if "notice" in st.session_state:
        st.success(st.session_state.pop("notice"))

    qr_loc = st.query_params.get("loc", "")
    if qr_loc and qr_loc not in locations:
        st.warning("이 QR의 보관 장소를 찾을 수 없습니다.")
        qr_loc = ""
    if qr_loc:
        st.info(f"📍 QR로 연 장소: {locations[qr_loc]}")
        if st.button("QR 장소 필터 해제"):
            st.query_params.clear()
            st.session_state.pop("location_filter", None)
            st.rerun()
    pages = ["오늘", "물건", "등록", "구매", "기록", "QR·설정"]
    if "page" not in st.session_state:
        st.session_state["page"] = "물건" if qr_loc else "오늘"
    # A selectbox avoids six overflowing tabs on small screens.
    page = st.selectbox("메뉴", pages, key="page", label_visibility="collapsed")

    if page == "오늘":
        st.subheader("오늘 챙길 것")
        active = [p for p in purchases if p["status"] != "도착"]
        low = [i for i in items if i["qty"] <= i["minimum"]]
        st.metric("등록한 물건", len(items))
        a, b = st.columns(2)
        a.metric("재고 확인", len(low))
        b.metric("진행 중 구매", len(active))
        alerts = []
        for i in items:
            name = label(i, locations)
            if i["qty"] and i["expiry"]:
                days = (parse_date(i["expiry"]) - today()).days
                if days <= 3:
                    alerts.append((days, "⚠️ " + name + (f" · 기한 {abs(days)}일 경과: 섭취 전 확인" if days < 0 else f" · 기한까지 {days}일")))
            if i["interval_days"] > 0 and i["last_maintenance"]:
                due = parse_date(i["last_maintenance"]) + timedelta(days=i["interval_days"])
                days = (due - today()).days
                if days <= 7:
                    alerts.append((days, f"🔧 {name} · 관리 예정 {due.isoformat()}"))
            due, count, start, median = forecast(i, events)
            if due and (due - today()).days <= 3:
                alerts.append(((due - today()).days, f"📉 {name} · 현재 사용 중인 1개 소진 예상 {due} (완료 주기 {count}회)"))
        for _, message in sorted(alerts):
            st.warning(message)
        if not alerts:
            st.success("임박한 기한·관리·소진 알림이 없어요.")
        for i in low:
            st.info(f'🛒 {label(i, locations)} · {i["qty"]}{i["unit"]} 남음 / 기준 {i["minimum"]}{i["unit"]}')
        st.caption("알림은 앱을 열었을 때 표시됩니다. 앱을 닫은 상태의 푸시 알림은 제공하지 않습니다.")
        if not items:
            st.info("‘등록’ 메뉴에서 생필품이나 자주 찾는 물건부터 추가해 보세요.")

    elif page == "물건":
        st.subheader("찾고, 바로 처리하기")
        search = st.text_input("이름 · 별칭 · 메모 검색", placeholder="예: 건전지, 배터리, 보증서")
        options = [""] + list(locations)
        if qr_loc and st.session_state.get("last_qr") != qr_loc:
            st.session_state["location_filter"] = qr_loc
            st.session_state["last_qr"] = qr_loc
        if st.session_state.get("location_filter", "") not in options:
            st.session_state["location_filter"] = ""
        loc = st.selectbox("보관 장소", options, format_func=lambda x: locations.get(x, "모든 장소"), key="location_filter")
        cat = st.selectbox("분류", ["전체"] + CATEGORIES)
        filtered = [i for i in items if (not loc or i["location_id"] == loc) and (cat == "전체" or i["category"] == cat) and (not search or search.casefold() in (i["name"] + " " + i["aliases"] + " " + i["memo"]).casefold())]
        st.caption(f"{len(filtered)}개 물건 · 사용 시작은 재고를 줄이지 않고, 다 쓸 때 차감합니다.")
        for i in filtered:
            iid = i["id"]
            with st.container(border=True):
                st.subheader(i["name"])
                st.caption(f'{locations[i["location_id"]]} · {i["category"]}')
                st.write(f'**{i["qty"]}{i["unit"]} 남음** · 최소 기준 {i["minimum"]}{i["unit"]}')
                if i["photo"]:
                    st.image(bytes(i["photo"]), width=160)
                if i["memo"]:
                    st.text(i["memo"])
                if i["expiry"]:
                    st.caption(f'소비·관리 기한: {i["expiry"]} (동일 기한 물량만 함께 관리)')
                due, n, start, typical = forecast(i, events)
                if typical:
                    st.caption(f'완료 주기 {n}회 · 최근 최대 6회 중앙값 {typical:g}일 · ' + (f'현재 1개 소진 예상 {due}' if due else '다음 사용 시작을 기록하면 예측합니다.'))
                else:
                    st.caption(f"소진 예측: 데이터 부족 ({n}/2회 완료). ‘사용 시작 → 다 씀’ 기록이 필요해요.")
                c1, c2 = st.columns(2)
                if c1.button("− 1개 사용", key="use" + iid, use_container_width=True, disabled=i["qty"] < 1 or bool(start)):
                    action(lambda: change_stock(iid, -1, "사용"), "1개 사용을 기록했어요.")
                if c2.button("+ 1개 보충", key="add" + iid, use_container_width=True):
                    action(lambda: change_stock(iid, 1, "입고"), "1개를 보충했어요.")
                with st.expander("사용 주기 · 폐기 · 구매 · 수정"):
                    st.caption("세제처럼 오래 쓰는 물건은 ‘사용 시작 → 다 씀’. 일회성 소모는 위 ‘1개 사용’을 이용하세요. 한 품목당 동시에 한 개만 주기를 기록합니다.")
                    if st.button("사용 시작", key="start" + iid, disabled=bool(start) or i["qty"] < 1, use_container_width=True):
                        def begin(iid=iid):
                            with db() as conn:
                                current = lock_item(conn, iid)
                                ev = [dict(r) for r in sql(conn, "SELECT * FROM events WHERE item_id=?", (iid,)).fetchall()]
                                if current["qty"] < 1 or forecast(current, ev)[2]:
                                    raise ValueError("이미 사용 중이거나 재고가 없습니다.")
                                event(conn, iid, "사용 시작")
                        action(begin, "사용 시작을 기록했어요.")
                    if st.button("다 씀 (재고 −1)", key="finish" + iid, disabled=not start or i["qty"] < 1, use_container_width=True):
                        def finish(iid=iid):
                            with db() as conn:
                                current = lock_item(conn, iid)
                                ev = [dict(r) for r in sql(conn, "SELECT * FROM events WHERE item_id=?", (iid,)).fetchall()]
                                if not forecast(current, ev)[2] or current["qty"] < 1:
                                    raise ValueError("이미 완료했거나 재고가 없습니다.")
                                sql(conn, "UPDATE items SET qty=qty-1 WHERE id=?", (iid,))
                                event(conn, iid, "다 씀", 1)
                                ensure_purchase(conn, iid)
                        action(finish, "완료 주기와 재고를 기록했어요.")
                    waste = st.number_input("폐기 수량", min_value=1, max_value=max(1, i["qty"]), step=1, key="wq" + iid)
                    if st.button("폐기 기록", key="waste" + iid, disabled=i["qty"] < 1 or bool(start), use_container_width=True):
                        action(lambda: change_stock(iid, -waste, "폐기"), "폐기를 기록했어요.")
                    if start:
                        st.caption("사용 중인 주기가 있으면 일반 사용·폐기를 막습니다. 잘못 시작했다면 취소하세요.")
                        if st.button("사용 시작 취소", key="cancelcycle" + iid):
                            def cancel_cycle(iid=iid):
                                with db() as conn:
                                    lock_item(conn, iid)
                                    # Close the open cycle without stock change or a training sample.
                                    event(conn, iid, "주기 취소")
                            action(cancel_cycle, "사용 주기를 취소했어요.")
                    buy_qty = st.number_input("구매할 수량", min_value=1, max_value=999, key="bq" + iid)
                    if st.button("구매 목록에 넣기", key="buy" + iid, use_container_width=True):
                        def buy(iid=iid, quantity=buy_qty):
                            with db() as conn:
                                current = lock_item(conn, iid)
                                active = sql(conn, "SELECT id FROM purchases WHERE item_id=? AND status<>?", (iid, "도착")).fetchone()
                                if active:
                                    raise ValueError("이미 구매 예정/주문 항목이 있어요. 구매 메뉴를 확인하세요.")
                                sql(conn, "INSERT INTO purchases VALUES(?,?,?,?,?,?,?)", (uuid.uuid4().hex, iid, quantity, "구매 예정", "", stamp(), None))
                        action(buy, "구매 목록에 추가했어요.")
                    st.caption(f'구매 전 확인: 현재 {i["qty"]}{i["unit"]} · 위치 {locations[i["location_id"]]}')
                    if i["interval_days"] > 0 and st.button("오늘 관리·교체 완료", key="maint" + iid, use_container_width=True):
                        def maintenance(iid=iid):
                            with db() as conn:
                                lock_item(conn, iid)
                                sql(conn, "UPDATE items SET last_maintenance=? WHERE id=?", (today().isoformat(), iid))
                                event(conn, iid, "관리 완료")
                        action(maintenance, "관리 날짜를 갱신했어요.")
                    with st.form("edit" + iid):
                        new_name = st.text_input("물건 이름", value=i["name"], max_chars=80)
                        new_loc = st.selectbox("위치 변경", list(locations), index=list(locations).index(i["location_id"]), format_func=locations.get)
                        new_aliases = st.text_input("별칭", value=i["aliases"], max_chars=200)
                        new_min = st.number_input("최소 수량", min_value=0, max_value=999, value=i["minimum"])
                        new_memo = st.text_area("메모 (모델명·업체 연락처·비용·보관 설명 등)", value=i["memo"], max_chars=2000)
                        new_expiry = st.date_input("소비·관리 기한 (선택)", value=parse_date(i["expiry"]), key="ed" + iid)
                        new_interval = st.number_input("관리 주기 (일, 0은 미사용)", min_value=0, max_value=3650, value=i["interval_days"])
                        new_last = st.date_input("최근 관리일 (선택)", value=parse_date(i["last_maintenance"]), key="el" + iid)
                        if st.form_submit_button("수정 저장", use_container_width=True):
                            def edit(iid=iid):
                                if not new_name.strip():
                                    raise ValueError("물건 이름을 입력하세요.")
                                if new_interval and not new_last:
                                    raise ValueError("관리 주기를 쓰려면 최근 관리일도 입력하세요.")
                                with db() as conn:
                                    lock_item(conn, iid)
                                    sql(conn, "UPDATE items SET name=?,location_id=?,aliases=?,minimum=?,memo=?,expiry=?,interval_days=?,last_maintenance=? WHERE id=?", (new_name.strip(), new_loc, new_aliases, new_min, new_memo, new_expiry.isoformat() if new_expiry else None, new_interval, new_last.isoformat() if new_last else None, iid))
                                    event(conn, iid, "정보 수정")
                                    ensure_purchase(conn, iid)
                            action(edit, "물건 정보를 수정했어요.")
        if not filtered:
            st.info("해당 물건이 없어요. 검색어나 장소를 바꾸거나 등록해 주세요.")

    elif page == "등록":
        st.subheader("물건 등록")
        st.caption("서로 다른 소비기한의 식품은 이름에 날짜를 붙여 따로 등록하세요. 예: 우유 11/20")
        with st.form("create", clear_on_submit=True):
            name = st.text_input("물건 이름 *", max_chars=80)
            aliases = st.text_input("별칭", placeholder="예: 건전지, 배터리, AA", max_chars=200)
            category = st.selectbox("분류", CATEGORIES)
            location = st.selectbox("보관 장소", list(locations), index=list(locations).index(qr_loc) if qr_loc else 0, format_func=locations.get)
            qty = st.number_input("현재 수량", 0, 9999, 1)
            unit = st.selectbox("단위", ["개", "팩", "병", "봉", "상자", "롤"])
            minimum = st.number_input("최소 수량 (이하이면 구매 목록 자동 추가)", 0, 999, 0)
            expiry = st.date_input("소비·관리 기한 (선택)", value=None)
            interval = st.number_input("교체·관리 주기 (일, 0은 미사용)", 0, 3650, 0)
            last = st.date_input("최근 교체·관리일 (선택)", value=None)
            memo = st.text_area("메모", max_chars=2000, placeholder="모델명, 수리 연락처, 비용, 상세 위치 등")
            photo = st.file_uploader("사진 (선택 · 2MB 이하)", type=["jpg", "jpeg", "png"])
            submitted = st.form_submit_button("등록하기", use_container_width=True)
        if submitted:
            def create():
                if not name.strip():
                    raise ValueError("물건 이름을 입력하세요.")
                if interval and not last:
                    raise ValueError("관리 주기를 쓰려면 최근 관리일도 입력하세요.")
                if photo and photo.size > 2 * 1024 * 1024:
                    raise ValueError("사진은 2MB 이하로 올려 주세요.")
                data = None
                if photo:
                    from PIL import Image, ImageOps
                    image = Image.open(photo)
                    image = ImageOps.exif_transpose(image)
                    image.thumbnail((1000, 1000))
                    buf = io.BytesIO()
                    image.convert("RGB").save(buf, format="JPEG", quality=80)
                    data = buf.getvalue()
                with db() as conn:
                    if not PG:
                        sql(conn, "BEGIN IMMEDIATE")
                    duplicates = sql(conn, "SELECT id FROM items WHERE LOWER(name)=LOWER(?) AND location_id=?", (name.strip(), location)).fetchone()
                    if duplicates:
                        raise ValueError("같은 장소에 같은 이름이 있어요. 기존 재고를 보충하거나 이름에 구분을 추가하세요.")
                    iid = uuid.uuid4().hex
                    sql(conn, "INSERT INTO items VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)", (iid, name.strip(), aliases.strip(), category, location, qty, minimum, unit, expiry.isoformat() if expiry else None, interval, last.isoformat() if last else None, memo, data, stamp()))
                    event(conn, iid, "등록", qty)
                    ensure_purchase(conn, iid)
            action(create, "새 물건을 등록했어요.")

    elif page == "구매":
        st.subheader("함께 쓰는 구매 목록")
        st.caption("도착 버튼을 눌러야 재고에 반영됩니다. 열린 화면은 자동 갱신되지 않으므로 구매 직전 새로고침해 주세요.")
        show_done = st.checkbox("도착 완료도 보기")
        visible = [p for p in purchases if show_done or p["status"] != "도착"]
        if not visible:
            st.success("진행 중인 구매가 없어요.")
        for p in visible:
            i = item_map[p["item_id"]]
            with st.container(border=True):
                st.write(f'**{i["name"]} · {p["qty"]}{i["unit"]}**')
                st.write(f'{p["status"]} · 담당: {p["buyer"] or "미정"}')
                st.caption(f'현재 재고 {i["qty"]}{i["unit"]} · {locations[i["location_id"]]}')
                if i["qty"] > 0 and p["status"] == "구매 예정":
                    st.info("집에 남은 재고가 있어요. 구매가 필요한지 확인하세요.")
                if p["status"] == "구매 예정":
                    if st.button("내가 주문했어요", key="ordered" + p["id"], use_container_width=True):
                        action(lambda pid=p["id"]: transition(pid, "주문 완료"), "주문 상태를 공유했어요.")
                    new_q = st.number_input("구매 수량 변경", 1, 999, min(999, p["qty"]), key="pq" + p["id"])
                    if st.button("수량 저장", key="ps" + p["id"]):
                        def update_purchase(p=p, new_q=new_q):
                            with db() as conn:
                                lock_item(conn, p["item_id"])
                                cur = sql(conn, "UPDATE purchases SET qty=? WHERE id=? AND status=?", (new_q, p["id"], "구매 예정"))
                                if cur.rowcount != 1:
                                    raise ValueError("이미 주문된 항목입니다. 새로고침하세요.")
                        action(update_purchase, "구매 수량을 변경했어요.")
                    if st.button("구매 예정 취소", key="pc" + p["id"]):
                        def cancel(p=p):
                            with db() as conn:
                                lock_item(conn, p["item_id"])
                                cur = sql(conn, "DELETE FROM purchases WHERE id=? AND status=?", (p["id"], "구매 예정"))
                                if cur.rowcount != 1:
                                    raise ValueError("이미 주문된 항목입니다. 새로고침하세요.")
                        action(cancel, "구매 예정을 취소했어요. 재고가 다시 변하면 최소 수량 조건에 따라 재등록될 수 있어요.")
                elif p["status"] == "주문 완료":
                    if st.button("도착 확인 · 재고 반영", key="arrived" + p["id"], use_container_width=True):
                        action(lambda pid=p["id"]: transition(pid, "도착"), "도착 수량을 재고에 반영했어요.")

    elif page == "기록":
        st.subheader("기록과 사용 패턴")
        st.caption("단위가 다른 물건의 수량을 합산하지 않고, 품목별로 표시합니다.")
        summary = []
        for i in items:
            ev = [e for e in events if e["item_id"] == i["id"]]
            waste = sum(e["qty"] for e in ev if e["kind"] == "폐기")
            used = sum(e["qty"] for e in ev if e["kind"] in ["사용", "다 씀"])
            arrivals = sorted(datetime.fromisoformat(p["arrived"]).date() for p in purchases if p["item_id"] == i["id"] and p["arrived"])
            gaps = [(b - a).days for a, b in zip(arrivals, arrivals[1:]) if (b - a).days > 0]
            due, n, start, typical = forecast(i, events)
            summary.append({"물건": label(i, locations), "단위": i["unit"], "사용": used, "폐기": waste, "재고": i["qty"], "구매 간격 중앙값(일)": statistics.median(gaps) if gaps else None, "현재 1개 소진 예상": str(due) if due else "데이터 부족/미사용"})
        if summary:
            st.dataframe(pd.DataFrame(summary), hide_index=True, use_container_width=True)
        event_view = [{"날짜": e["occurred"][:16].replace("T", " "), "물건": item_map[e["item_id"]]["name"], "처리": e["kind"], "수량": e["qty"], "작성자": e["actor"], "메모": e["note"]} for e in events]
        st.subheader("최근 활동")
        if event_view:
            st.dataframe(pd.DataFrame(event_view[:200]), hide_index=True, use_container_width=True)
            st.download_button("전체 기록 CSV 받기", pd.DataFrame(event_view).to_csv(index=False).encode("utf-8-sig"), "home_events.csv", "text/csv", use_container_width=True)
        st.caption("예측은 최근 최대 6개의 완료 사용 주기 중앙값을 이용합니다. 같은 날 시작·완료한 주기는 예측에서 제외합니다. 재고 전체의 소진일이나 식품 안전을 보장하지 않습니다.")
        st.subheader("생기부 탐구에 활용하기")
        st.write("앱 사용 전후에 물건 탐색 시간, 중복 구매 횟수, 입력 시간을 같은 기준으로 직접 측정해 비교하세요. 이 앱이 그 효과를 자동 측정하거나 검증하지는 않습니다.")

    else:
        st.subheader("보관함 QR 만들기")
        st.write("보관함에 붙인 QR을 휴대폰 기본 카메라로 스캔하면 그 장소의 물건 목록이 열려요.")
        base = st.text_input("실제 Streamlit 배포 주소", value=setting("APP_URL"), placeholder="https://your-app.streamlit.app")
        qr_location = st.selectbox("QR을 만들 보관 장소", list(locations), format_func=locations.get)
        if base:
            try:
                link = make_qr_url(base, qr_location)
                image = qrcode.make(link)
                buf = io.BytesIO()
                image.save(buf, format="PNG")
                st.image(buf.getvalue(), caption=locations[qr_location] + " 보관함 QR", width=240)
                st.link_button("QR 링크 열기", link, use_container_width=True)
                st.download_button("QR 이미지 받기", buf.getvalue(), "location_qr.png", "image/png", use_container_width=True)
                st.caption("같은 데이터베이스를 유지하면 QR은 계속 사용할 수 있습니다. 다른 DB로 바꾸면 장소 ID가 달라져 다시 발급해야 합니다.")
            except ValueError as exc:
                st.error(str(exc))
        with st.form("location_add", clear_on_submit=True):
            new_location = st.text_input("새 보관 장소 이름", max_chars=60, placeholder="예: 주방 오른쪽 두 번째 서랍")
            if st.form_submit_button("보관 장소 추가", use_container_width=True):
                def add_location():
                    if not new_location.strip():
                        raise ValueError("장소 이름을 입력하세요.")
                    with db() as conn:
                        if sql(conn, "SELECT id FROM locations WHERE name=?", (new_location.strip(),)).fetchone():
                            raise ValueError("이미 등록된 장소입니다.")
                        sql(conn, "INSERT INTO locations VALUES(?,?)", (uuid.uuid4().hex, new_location.strip()))
                action(add_location, "보관 장소를 추가했어요.")
        st.subheader("백업")
        export_items = [{k: v for k, v in i.items() if k != "photo"} for i in items]
        payload = {"version": 1, "exported": stamp(), "locations": locations_raw, "items": export_items, "purchases": purchases, "events": events}
        st.download_button("전체 데이터 JSON 내보내기 (사진 제외)", json.dumps(payload, ensure_ascii=False, indent=2).encode(), "home_backup.json", "application/json", use_container_width=True)
        st.caption("JSON은 데이터 확인·이관용입니다. 앱 내 자동 복원 기능은 없습니다. 사진까지 보존하려면 외부 DB 서비스의 백업을 사용하세요.")
        with st.expander("GitHub · Streamlit 배포 안내"):
            st.markdown('''1. GitHub 저장소에 **app.py**, **requirements.txt** 두 파일을 올립니다.
2. Streamlit Community Cloud에서 해당 저장소를 연결하고 실행 파일을 **app.py**로 설정합니다.
3. 설정의 **Secrets**에 가족 비밀번호, 앱 주소, PostgreSQL 연결 문자열을 입력합니다.
4. 배포 주소로 접속해 장소와 물건을 등록하고 QR을 내려받아 붙입니다.

**GitHub Pages는 지원하지 않습니다.** 외부 DB가 없으면 데모만 권장합니다.
가족 구성원은 같은 앱을 이용해야 합니다. 별도 가족별 계정 분리는 없습니다.
공유 비밀번호는 간단한 접근 제한이며, 민감한 개인정보·금융정보는 저장하지 마세요.''')
            st.code('APP_PASSWORD = "가족만 아는 긴 비밀번호"\nAPP_URL = "https://your-app.streamlit.app"\nDATABASE_URL = "postgresql://USER:PASSWORD@HOST:5432/DB?sslmode=require"', language="toml")
        st.caption("화면 디자인: 모바일 단일 열 · 큰 버튼 · 흰색 카드 · 장소별 QR. 예측과 기한 안내는 참고용입니다.")


if __name__ == "__main__":
    main()

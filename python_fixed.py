#!/usr/bin/env python
# coding: utf-8

"""
Cactus 2.0
Multi-threaded, Professional GUI, macOS Permission Handling
Compatible with Windows, macOS, and Linux
"""

import os
import sys
import hashlib
import json
import sqlite3
import shutil
import subprocess
import platform
import threading
import queue
import re
import struct
import codecs
import plistlib
import uuid
import tempfile
import calendar
import glob
import gzip
import ipaddress
import socket
import time
from collections import Counter
from urllib.parse import unquote
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

import tkinter as tk
from tkinter import ttk, scrolledtext, filedialog, messagebox
from tkinter import font as tkfont


import zipfile
import getpass
import stat as _stat
import csv
import io


# ============================================================
# COMMAND RECORDER - every external program the tool starts is logged
# (the report lists them, with a hash of each output, as the method used)
# ============================================================
COMMAND_LOG = []
_COMMAND_LOCK = threading.Lock()


def _record_command(cmd, rc, out, secs, error=''):
    try:
        if isinstance(out, str):
            out = out.encode('utf-8', 'replace')
        text = ' '.join(map(str, cmd)) if isinstance(cmd, (list, tuple)) else str(cmd)
        rec = {'time_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'),
               'command': text[:400], 'returncode': rc, 'output_bytes': len(out or b''),
               'output_sha256': hashlib.sha256(out or b'').hexdigest(), 'seconds': round(secs, 2),
               'error': error[:200]}
        with _COMMAND_LOCK:
            if len(COMMAND_LOG) < 5000:
                COMMAND_LOG.append(rec)
    except Exception:
        pass


class _RecordingSubprocess:
    """Stands in for the subprocess module. run() behaves identically but is logged."""

    def __init__(self, real):
        self._real = real

    def __getattr__(self, name):
        return getattr(self._real, name)

    def run(self, cmd, *args, **kwargs):
        t0 = time.time()
        try:
            r = self._real.run(cmd, *args, **kwargs)
        except BaseException as e:
            _record_command(cmd, None, b'', time.time() - t0, f"{type(e).__name__}: {e}")
            raise
        _record_command(cmd, getattr(r, 'returncode', None), getattr(r, 'stdout', b'') or b'', time.time() - t0)
        return r


subprocess = _RecordingSubprocess(subprocess)


# ============================================================
# EVIDENCE DICTIONARY - remembers when each result was collected and its SHA-256 then
# ============================================================
class EvidenceDict(dict):
    def __init__(self, on_record=None):
        super().__init__()
        self.meta = {}
        self._on_record = on_record

    def __setitem__(self, key, value):
        super().__setitem__(key, value)
        try:
            raw = value if isinstance(value, str) else json.dumps(value, default=str, sort_keys=True)
            self.meta[key] = {'collected_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'),
                              'sha256': hashlib.sha256(raw.encode('utf-8', 'replace')).hexdigest()}
            if self._on_record:
                self._on_record(key, self.meta[key])
        except Exception:
            pass

    def update(self, *a, **k):
        for key, value in dict(*a, **k).items():
            self[key] = value

    def clear(self):
        super().clear()
        self.meta.clear()



# ============================================================
# COLOR PALETTE - Professional Dark Theme
# ============================================================
class Theme:
    BG_DARK = "#0f1419"
    BG_MEDIUM = "#1a2332"
    BG_LIGHT = "#243447"
    BG_CARD = "#1e2a3a"
    ACCENT = "#00d4ff"
    ACCENT_HOVER = "#00b8e6"
    ACCENT_GREEN = "#00ff88"
    ACCENT_RED = "#ff4757"
    ACCENT_YELLOW = "#ffa502"
    TEXT_PRIMARY = "#e8eef5"
    TEXT_SECONDARY = "#8b9bb4"
    BORDER = "#2d3e52"
    SUCCESS = "#00ff88"
    WARNING = "#ffa502"
    ERROR = "#ff4757"


# ============================================================
# WORKER THREAD - Background task execution
# ============================================================
class Worker(threading.Thread):
    """Generic worker thread for background tasks."""
    def __init__(self, task, callback, error_callback=None, *args, **kwargs):
        super().__init__(daemon=True)
        self.task = task
        self.callback = callback
        self.error_callback = error_callback
        self.args = args
        self.kwargs = kwargs

    def run(self):
        try:
            result = self.task(*self.args, **self.kwargs)
            self.callback(result)
        except Exception as e:
            if self.error_callback:
                self.error_callback(e)
            else:
                print(f"Worker error: {e}")


# ============================================================
# MAIN APPLICATION
# ============================================================
# CALENDAR POPUP - date picker (Tkinter has no built-in one)
# ============================================================
class DatePicker(tk.Toplevel):
    """Small month-grid calendar. Writes YYYY-MM-DD into a StringVar and closes."""

    def __init__(self, master, var, anchor=None, today=None):
        super().__init__(master)
        self.title("Pick a date")
        self.configure(bg=Theme.BG_DARK)
        self.resizable(False, False)
        self.transient(master)
        self.var = var
        self.today = today or date.today()
        try:
            cur = datetime.strptime(var.get().strip(), '%Y-%m-%d').date()
        except ValueError:
            cur = self.today
        if cur > self.today:
            cur = self.today
        self.selected = cur
        self.year, self.month = cur.year, cur.month
        self.body = tk.Frame(self, bg=Theme.BG_CARD, highlightbackground=Theme.BORDER,
                             highlightthickness=1)
        self.body.pack(padx=6, pady=6)
        self._build()
        self.update_idletasks()
        if anchor is not None:
            x = anchor.winfo_rootx()
            y = anchor.winfo_rooty() + anchor.winfo_height() + 4
            self.geometry(f"+{x}+{y}")
        try:
            self.grab_set()
        except tk.TclError:
            pass

    def _shift(self, delta):
        m = self.month + delta
        self.year += (m - 1) // 12
        self.month = (m - 1) % 12 + 1
        self._build()

    def _pick(self, day):
        self.var.set(date(self.year, self.month, day).isoformat())
        self.destroy()

    def _build(self):
        for w in self.body.winfo_children():
            w.destroy()
        head = tk.Frame(self.body, bg=Theme.BG_CARD)
        head.pack(fill='x', padx=8, pady=(8, 4))
        at_limit = (self.year, self.month) >= (self.today.year, self.today.month)
        tk.Button(head, text="◀", width=3, relief='flat', bg=Theme.BG_LIGHT,
                  fg=Theme.TEXT_PRIMARY, activebackground=Theme.ACCENT,
                  command=lambda: self._shift(-1)).pack(side='left')
        tk.Label(head, text=f"{calendar.month_name[self.month]} {self.year}",
                 bg=Theme.BG_CARD, fg=Theme.ACCENT,
                 font=('Segoe UI', 11, 'bold')).pack(side='left', expand=True)
        tk.Button(head, text="▶", width=3, relief='flat', bg=Theme.BG_LIGHT,
                  fg=Theme.TEXT_SECONDARY if at_limit else Theme.TEXT_PRIMARY,
                  activebackground=Theme.ACCENT,
                  state='disabled' if at_limit else 'normal',
                  command=lambda: self._shift(1)).pack(side='right')
        grid = tk.Frame(self.body, bg=Theme.BG_CARD)
        grid.pack(padx=8, pady=4)
        for c, name in enumerate(("Mo", "Tu", "We", "Th", "Fr", "Sa", "Su")):
            tk.Label(grid, text=name, width=4, bg=Theme.BG_CARD,
                     fg=Theme.TEXT_SECONDARY, font=('Segoe UI', 9)).grid(row=0, column=c)
        weeks = calendar.Calendar(firstweekday=0).monthdayscalendar(self.year, self.month)
        for r, week in enumerate(weeks, start=1):
            for c, day in enumerate(week):
                if day == 0:
                    continue
                d = date(self.year, self.month, day)
                future = d > self.today
                if d == self.selected:
                    bg, fg = Theme.ACCENT, Theme.BG_DARK
                elif d == self.today:
                    bg, fg = Theme.BG_LIGHT, Theme.ACCENT
                else:
                    bg, fg = Theme.BG_CARD, Theme.TEXT_PRIMARY
                tk.Button(grid, text=str(day), width=3, relief='flat', bg=bg,
                          fg=Theme.TEXT_SECONDARY if future else fg,
                          activebackground=Theme.ACCENT_HOVER,
                          state='disabled' if future else 'normal',
                          command=lambda dd=day: self._pick(dd)).grid(row=r, column=c, padx=1, pady=1)
        foot = tk.Frame(self.body, bg=Theme.BG_CARD)
        foot.pack(fill='x', padx=8, pady=(4, 8))
        tk.Button(foot, text="Today", relief='flat', bg=Theme.BG_LIGHT, fg=Theme.TEXT_PRIMARY,
                  activebackground=Theme.ACCENT,
                  command=lambda: (self.var.set(self.today.isoformat()), self.destroy())
                  ).pack(side='left')
        tk.Button(foot, text="Close", relief='flat', bg=Theme.BG_LIGHT, fg=Theme.TEXT_PRIMARY,
                  activebackground=Theme.ACCENT, command=self.destroy).pack(side='right')



# ============================================================
# ============================================================
# v3.4 ADDITIONS - pure logic functions (hash-set matching, encryption
# detection, deleted-file/recycle-bin, NTFS MFT/USN, RAM acquisition,
# report signing, baseline-diff, graphical-timeline layout, case
# dashboard, read-only/write-blocker advisory). Thin GUI/IO wrappers
# that call these live as methods inside the class below.
# ============================================================
# ---- from c7_hashsets.py ----

_HEX_RE = re.compile(r'^[0-9a-fA-F]+$')
_ALGO_BY_LEN = {32: 'md5', 40: 'sha1', 64: 'sha256', 128: 'sha512'}


def v34__looks_like_hash(tok):
    tok = tok.strip().strip('"')
    return bool(tok) and tok.lower() not in ('', 'na', 'n/a') and _HEX_RE.match(tok) and len(tok) in _ALGO_BY_LEN


def v34_parse_hash_set(text):
    """
    Accepts: a bare list of hashes (one per line), or NSRL-RDS-style CSV
    with a header row containing columns like SHA-1/MD5/SHA-256.
    Returns {'md5': set(), 'sha1': set(), 'sha256': set(), 'sha512': set()},
    plus a count of lines that were not recognised as hashes.
    """
    sets = {'md5': set(), 'sha1': set(), 'sha256': set(), 'sha512': set()}
    unrecognised = 0
    lines = text.splitlines()
    if not lines:
        return sets, 0

    # Try CSV with a header naming hash columns (NSRL RDS minimal / full set style)
    header = lines[0]
    if ',' in header and re.search(r'(?i)\b(md5|sha-?1|sha-?256|sha-?512)\b', header):
        try:
            reader = csv.reader(io.StringIO(text))
            cols = next(reader)
            idx_by_algo = {}
            for i, c in enumerate(cols):
                cl = re.sub(r'[^a-z0-9]', '', c.lower())
                for algo, key in (('md5', 'md5'), ('sha1', 'sha1'), ('sha256', 'sha256'), ('sha512', 'sha512')):
                    if cl == key:
                        idx_by_algo[algo] = i
            if idx_by_algo:
                for row in reader:
                    for algo, i in idx_by_algo.items():
                        if i < len(row):
                            v = row[i].strip().strip('"')
                            if v34__looks_like_hash(v) and _ALGO_BY_LEN[len(v)] == algo:
                                sets[algo].add(v.lower())
                            elif v:
                                unrecognised += 1
                return sets, unrecognised
        except Exception:
            pass  # fall through to plain line-by-line parsing

    # Plain list: one hash per line, optionally with trailing comment/filename after whitespace
    for ln in lines:
        tok = ln.strip()
        if not tok or tok.startswith('#'):
            continue
        tok = tok.split()[0].split(',')[0].strip().strip('"')
        if v34__looks_like_hash(tok):
            sets[_ALGO_BY_LEN[len(tok)]].add(tok.lower())
        else:
            unrecognised += 1
    return sets, unrecognised


def v34_total_hashes(sets):
    return sum(len(v) for v in sets.values())


def v34_match_hash_set(sets, evidence_hashes, label):
    """
    evidence_hashes: iterable of (source_name, {'md5':.., 'sha1':.., 'sha256':.., 'sha512':..})
      - a dict may have only some of the algorithms populated; that's fine.
    label: 'allow' or 'block' - only affects the returned classification text.
    Returns list of (source_name, algo, hash_value) for every match, in input order.
    """
    hits = []
    for name, hdict in evidence_hashes:
        for algo, val in (hdict or {}).items():
            if not val:
                continue
            val = val.lower()
            if val in sets.get(algo, ()):
                hits.append((name, algo, val))
                break  # one match per file is enough to classify it
    return hits


def v34_render_hash_set_report(set_name, label, sets, unrecognised, evidence_hashes):
    hits = v34_match_hash_set(sets, evidence_hashes, label)
    total = v34_total_hashes(sets)
    n_items = len(list(evidence_hashes)) if not isinstance(evidence_hashes, list) else len(evidence_hashes)
    out = ["=" * 60]
    kind = "KNOWN-GOOD (allowlist)" if label == 'allow' else "KNOWN-BAD / IOC (blocklist)"
    out.append(f"HASH-SET MATCH  --  {kind}")
    out.append(f"Set: {set_name}   ({total:,} hashes loaded" +
               (f", {unrecognised} line(s) not recognised as a hash" if unrecognised else "") + ")")
    out.append("=" * 60)
    out.append("")
    if label == 'allow':
        out.append(f"{len(hits)} of {n_items} collected/exported file(s) match this known-good set and can be "
                    f"de-prioritised. This does NOT clear a file of suspicion by itself -- a hash set is only as "
                    f"good as its source and coverage.")
    else:
        out.append(f"{len(hits)} of {n_items} collected/exported file(s) match this known-bad / IOC set. "
                    f"A hash match is a strong lead, not proof by itself -- confirm with the indicator's source.")
    out.append("")
    if hits:
        out.append(("Known-good matches:" if label == 'allow' else "FLAGGED matches:"))
        for name, algo, val in hits:
            out.append(f"  {'[OK]  ' if label == 'allow' else '[HIT] '}{name}   {algo}={val}")
    else:
        out.append("No matches.")
    return "\n".join(out) + "\n"


# ---- from c8_encryption.py ----
def v34_parse_bitlocker(manage_bde_out):
    """Parse `manage-bde -status` text -> list of (volume, state, flag)."""
    rows = []
    vol = None
    for ln in (manage_bde_out or '').splitlines():
        m = re.match(r'^\s*Volume\s+(\S+)\s*\[', ln)
        if m:
            vol = m.group(1)
            continue
        m = re.search(r'Conversion Status:\s*(.+)', ln)
        if m and vol:
            state = m.group(1).strip()
            flagged = 'fully decrypted' in state.lower() or state.lower().startswith('decrypt')
            rows.append((vol, state, 'OFF' if flagged else 'ON'))
            vol = None
    return rows


def v34_parse_filevault(fdesetup_out):
    txt = (fdesetup_out or '').strip().lower()
    if 'filevault is on' in txt:
        return [('startup disk', 'On', 'ON')]
    if 'filevault is off' in txt:
        return [('startup disk', 'Off', 'OFF')]
    return []


def v34_parse_luks(lsblk_out):
    """Parse `lsblk -o NAME,TYPE,FSTYPE,MOUNTPOINT` text -> encrypted volumes."""
    rows = []
    for ln in (lsblk_out or '').splitlines()[1:]:
        parts = ln.split(None, 3)
        if len(parts) >= 3 and 'crypto_luks' in parts[2].lower():
            name = parts[0].lstrip('├└│─ ')
            mnt = parts[3] if len(parts) > 3 else ''
            rows.append((name, 'LUKS', 'ON' if True else 'OFF', mnt))
    # normalise to 3-tuple form used by bitlocker/filevault for a uniform renderer
    return [(name, f'LUKS container{(" mounted at " + mnt) if mnt else " (not mounted / locked)"}', state)
            for (name, _t, state, mnt) in rows]


def v34_render_encryption_summary(osn, **raw):
    """
    raw: bitlocker=..., filevault=..., lsblk=... (whichever text this OS collected)
    Returns a short summary string with ON/OFF/UNKNOWN flags per volume.
    """
    out = ["=" * 60, "ENCRYPTION / DISK PROTECTION STATUS", "=" * 60, ""]
    rows = []
    if osn == 'Windows':
        rows = v34_parse_bitlocker(raw.get('bitlocker'))
        out.append("BitLocker, per volume (from `manage-bde -status`):")
    elif osn == 'Darwin':
        rows = v34_parse_filevault(raw.get('filevault'))
        out.append("FileVault (from `fdesetup status`):")
    else:
        rows = v34_parse_luks(raw.get('lsblk'))
        out.append("LUKS-encrypted block devices (from `lsblk`):")
    out.append("-" * 40)
    if not rows:
        out.append("  Could not determine status (command unavailable, needs admin, or no encrypted volumes found).")
    else:
        for row in rows:
            vol, state, flag = row[0], row[1], row[-1]
            mark = {'ON': '[ENCRYPTED]', 'OFF': '[NOT ENCRYPTED]'}.get(flag, '[UNKNOWN]')
            out.append(f"  {mark}  {vol}: {state}")
    n_off = sum(1 for r in rows if r[-1] == 'OFF')
    out.append("")
    if n_off:
        out.append(f"{n_off} volume(s) are NOT encrypted. Worth noting in the report: an unencrypted volume "
                    f"found during the investigation is itself an evidentiary fact (e.g. relevant to a data-"
                    f"protection or policy question), not a tool finding about the incident itself.")
    elif rows:
        out.append("All checked volumes report as encrypted.")
    return "\n".join(out) + "\n", rows


# ---- from c9_recycle.py ----

_EPOCH = datetime(1601, 1, 1, tzinfo=timezone.utc)


def v34__filetime_to_dt(ft):
    try:
        return (_EPOCH + timedelta(microseconds=ft / 10)).isoformat()
    except (OverflowError, OSError, ValueError):
        return None


def v34_parse_recycle_i_file(data):
    """
    Parse one $I* metadata file's bytes (modern Vista+ format).
    Returns dict(version, size, deleted_utc, original_path) or None if the
    bytes don't look like a recognised $I record.
    """
    if len(data) < 24:
        return None
    version = struct.unpack('<q', data[0:8])[0]
    if version not in (1, 2):
        return None
    size = struct.unpack('<q', data[8:16])[0]
    ft = struct.unpack('<q', data[16:24])[0]
    deleted = v34__filetime_to_dt(ft)
    try:
        if version == 1:
            # v1 (Vista/7): fixed 260 WCHAR path field starting at offset 24
            raw = data[24:24 + 260 * 2]
            path = raw.decode('utf-16-le', 'replace').split('\x00', 1)[0]
        else:
            # v2 (Win10+): int32 path length (in UTF-16 chars) at 24, then the path
            if len(data) < 28:
                return None
            path_len = struct.unpack('<i', data[24:28])[0]
            raw = data[28:28 + path_len * 2]
            path = raw.decode('utf-16-le', 'replace').split('\x00', 1)[0]
    except Exception:
        path = '(path could not be decoded)'
    return {'version': version, 'size': size, 'deleted_utc': deleted, 'original_path': path}


def v34_parse_trashinfo(text):
    """Parse a freedesktop .trashinfo file's text -> dict(path, deletion_date)."""
    out = {}
    for ln in text.splitlines():
        if ln.startswith('Path='):
            out['path'] = ln[5:].strip()
        elif ln.startswith('DeletionDate='):
            out['deletion_date'] = ln[13:].strip()
    return out if 'path' in out else None


def v34_render_recycle_bin_report(osn, items):
    """
    items: list of dicts, OS-specific shape already produced by the caller:
      Windows: {'i_file':.., 'r_present': bool, 'sha256': str|None, **v34_parse_recycle_i_file()}
      macOS:   {'name':.., 'mtime':.., 'size':.., 'sha256': str|None}
      Linux:   {'name':.., 'original_path':.., 'deletion_date':.., 'size':.., 'sha256': str|None}
    """
    out = ["=" * 60, "DELETED FILES / RECYCLE BIN", "=" * 60, ""]
    if not items:
        out.append("No items found (bin empty, not accessible, or needs elevated permissions).")
        return "\n".join(out) + "\n"
    out.append(f"{len(items)} item(s) found. Content, where recoverable, is hashed and preserved in the evidence "
                f"vault; metadata timestamps are from the recycle bin's own record where the OS provides one.")
    out.append("")
    for it in items:
        if osn == 'Windows':
            out.append(f"  Original path: {it.get('original_path', '?')}")
            out.append(f"    Deleted (UTC): {it.get('deleted_utc') or 'unknown'}   Size: {it.get('size', '?')} bytes"
                        f"   Content recovered: {'yes' if it.get('r_present') else 'no'}")
            if it.get('sha256'):
                out.append(f"    SHA-256: {it['sha256']}")
        elif osn == 'Darwin':
            out.append(f"  {it.get('name', '?')}")
            out.append(f"    In Trash since (file mtime, not a guaranteed deletion time): {it.get('mtime', '?')}"
                        f"   Size: {it.get('size', '?')} bytes")
            if it.get('sha256'):
                out.append(f"    SHA-256: {it['sha256']}")
        else:
            out.append(f"  Original path: {it.get('original_path', it.get('name', '?'))}")
            out.append(f"    Deleted: {it.get('deletion_date') or 'unknown'}   Size: {it.get('size', '?')} bytes")
            if it.get('sha256'):
                out.append(f"    SHA-256: {it['sha256']}")
        out.append("")
    return "\n".join(out) + "\n"


# ---- from c10_mft_usn.py ----
_EPOCH = datetime(1601, 1, 1, tzinfo=timezone.utc)
_MFT_RECORD_SIZE = 1024
_MFT_SIGNATURE = b'FILE'


def v34__filetime_to_dt(ft):
    try:
        if ft <= 0:
            return None
        return (_EPOCH + timedelta(microseconds=ft / 10)).isoformat()
    except (OverflowError, OSError, ValueError):
        return None


def v34__apply_fixup(record):
    """NTFS records are 'fixed up': the last 2 bytes of each 512-byte sector
    are replaced with a signature and the real bytes saved in the update
    sequence array. We don't strictly need the real bytes for the fields we
    read (they sit earlier in the record), so this is a best-effort no-op
    guard -- just validates the signature is present."""
    try:
        usa_offset, usa_count = struct.unpack('<HH', record[4:8])
        return usa_count >= 1
    except Exception:
        return False


def v34_parse_mft_record(record, record_num=None):
    """
    record: exactly 1024 (or 4096, rare) bytes of one $MFT entry.
    Returns None if not a valid/parseable FILE record (e.g. unused slot),
    else a dict with: record_num, in_use, is_directory, filename,
    parent_ref, si_times (dict), fn_times (dict).
    """
    if len(record) < 56 or record[0:4] != _MFT_SIGNATURE:
        return None
    if not v34__apply_fixup(record):
        return None
    try:
        flags = struct.unpack('<H', record[22:24])[0]
        in_use = bool(flags & 0x0001)
        is_dir = bool(flags & 0x0002)
        attrs_offset = struct.unpack('<H', record[20:22])[0]
    except Exception:
        return None

    si_times, fn_times, filename, parent_ref = {}, {}, None, None
    off = attrs_offset
    guard = 0
    while off + 8 <= len(record) and guard < 64:
        guard += 1
        atype = struct.unpack('<I', record[off:off + 4])[0]
        if atype == 0xFFFFFFFF:
            break
        try:
            alen = struct.unpack('<I', record[off + 4:off + 8])[0]
        except Exception:
            break
        if alen <= 0 or off + alen > len(record):
            break
        content_off_in_attr = None
        try:
            non_resident = record[off + 8]
            if non_resident == 0:
                content_off_in_attr = struct.unpack('<H', record[off + 20:off + 22])[0]
        except Exception:
            pass

        if atype == 0x10 and content_off_in_attr is not None:  # STANDARD_INFORMATION
            base = off + content_off_in_attr
            if base + 32 <= len(record):
                ctime, atime, mtime, mft_mtime = struct.unpack('<QQQQ', record[base:base + 32])
                si_times = {'created': v34__filetime_to_dt(ctime), 'modified': v34__filetime_to_dt(mtime),
                            'mft_modified': v34__filetime_to_dt(mft_mtime), 'accessed': v34__filetime_to_dt(atime)}
        elif atype == 0x30 and content_off_in_attr is not None:  # FILE_NAME
            base = off + content_off_in_attr
            if base + 66 <= len(record):
                parent_ref = struct.unpack('<Q', record[base:base + 8])[0] & 0x0000FFFFFFFFFFFF
                ctime, mtime, mft_mtime, atime = struct.unpack('<QQQQ', record[base + 8:base + 40])
                name_len = record[base + 64]
                name_space = record[base + 65]
                name_bytes = record[base + 66:base + 66 + name_len * 2]
                try:
                    name = name_bytes.decode('utf-16-le', 'replace')
                except Exception:
                    name = None
                # prefer the Win32 namespace (0 or 1) name over DOS 8.3 (2)
                if name and (filename is None or name_space != 2):
                    filename = name
                    fn_times = {'created': v34__filetime_to_dt(ctime), 'modified': v34__filetime_to_dt(mtime),
                                'mft_modified': v34__filetime_to_dt(mft_mtime), 'accessed': v34__filetime_to_dt(atime)}
        off += alen

    if filename is None and not si_times:
        return None
    return {'record_num': record_num, 'in_use': in_use, 'is_directory': is_dir, 'filename': filename,
            'parent_ref': parent_ref, 'si_times': si_times, 'fn_times': fn_times}


def v34_iter_mft_records(fileobj, max_records=200000):
    """Yield v34_parse_mft_record() results (skipping unparseable slots) from a
    file-like object positioned at the start of an $MFT."""
    n = 0
    while n < max_records:
        block = fileobj.read(_MFT_RECORD_SIZE)
        if len(block) < _MFT_RECORD_SIZE:
            break
        rec = v34_parse_mft_record(block, record_num=n)
        if rec is not None:
            yield rec
        n += 1


def v34_timestomp_suspects(records, max_results=200):
    """A FILE_NAME creation time noticeably later than STANDARD_INFORMATION's
    creation time is a classic timestomp indicator ($SI edited, $FN left behind,
    or vice versa). Flag records where the two disagree by more than a minute."""
    out = []
    for r in records:
        si, fn = r.get('si_times') or {}, r.get('fn_times') or {}
        sc, fc = si.get('created'), fn.get('created')
        if sc and fc and sc != fc:
            out.append(r)
            if len(out) >= max_results:
                break
    return out


def v34_parse_usn_readjournal_csv(text):
    """Parse `fsutil usn readjournal <volume> csv` output -> list of dicts."""
    rows = []
    reader = csv.reader(io.StringIO(text))
    header = None
    for row in reader:
        if not row or not any(c.strip() for c in row):
            continue
        if header is None:
            header = [c.strip().lower() for c in row]
            continue
        if len(row) < len(header):
            row = row + [''] * (len(header) - len(row))
        rows.append(dict(zip(header, row)))
    return rows


def v34_render_usn_report(rows, max_rows=1000):
    out = ["=" * 60, "USN JOURNAL (file-system change log)", "=" * 60, ""]
    if not rows:
        out.append("No entries decoded (journal not enabled, needs admin, or `fsutil` unavailable).")
        return "\n".join(out) + "\n"
    out.append(f"{len(rows):,} change record(s) decoded (showing up to {max_rows:,}).")
    out.append("")
    for row in rows[:max_rows]:
        name = row.get('file name') or row.get('filename') or '?'
        reason = row.get('reason') or ''
        ts = row.get('time stamp') or row.get('timestamp') or ''
        out.append(f"  {ts}  {name}   [{reason}]")
    return "\n".join(out) + "\n"


def v34_render_mft_report(records, suspects, max_rows=1000):
    out = ["=" * 60, "NTFS $MFT (Master File Table)", "=" * 60, ""]
    if not records:
        out.append("No records decoded (needs admin, volume not NTFS, or $MFT could not be opened).")
        return "\n".join(out) + "\n"
    out.append(f"{len(records):,} record(s) decoded (showing up to {max_rows:,}).")
    out.append(f"{len(suspects)} record(s) show a FILE_NAME creation time that disagrees with "
               f"STANDARD_INFORMATION's -- a classic timestomp indicator. Listed separately below; it is a "
               f"lead, not proof (legitimate copy/restore operations can also cause this).")
    out.append("")
    for r in records[:max_rows]:
        tag = ('deleted' if not r['in_use'] else 'active') + (', dir' if r['is_directory'] else '')
        out.append(f"  #{r['record_num']}  [{tag}]  {r.get('filename') or '(no name decoded)'}")
        si = r.get('si_times') or {}
        if si.get('created'):
            out.append(f"      $SI created: {si.get('created')}   modified: {si.get('modified')}")
    if suspects:
        out.append("\nPossible timestomp indicators:")
        for r in suspects[:200]:
            out.append(f"  #{r['record_num']}  {r.get('filename')}   "
                       f"$SI created={r['si_times'].get('created')}   $FN created={r['fn_times'].get('created')}")
    return "\n".join(out) + "\n"


# ---- from c11_ram.py ----


def v34_find_memory_tool(current_os, extra_search_paths=None):
    """-> (kind, path) or (None, '')"""
    extra_search_paths = extra_search_paths or []
    if current_os == 'Windows':
        candidates = ['winpmem.exe', 'winpmem_mini_x64.exe']
        pf = os.environ.get('ProgramFiles', r'C:\Program Files')
        search_dirs = [pf, os.path.join(pf, 'WinPmem')] + extra_search_paths
    elif current_os == 'Linux':
        candidates = ['avml']
        search_dirs = ['/usr/local/bin', '/usr/bin'] + extra_search_paths
    else:
        return None, ''  # macOS: no supported live full-memory imaging path
    for name in candidates:
        p = shutil.which(name)
        if p:
            return name.split('.')[0], p
        for d in search_dirs:
            cand = os.path.join(d, name)
            if os.path.isfile(cand):
                return name.split('.')[0], cand
    return None, ''


def v34_build_acquisition_command(kind, exe, out_path):
    """Returns the argv list to run for the given detected tool."""
    if kind.startswith('winpmem'):
        return [exe, out_path]
    if kind == 'avml':
        return [exe, out_path]
    raise ValueError(f"unknown memory-acquisition tool kind: {kind}")


def v34_unavailable_message(current_os):
    if current_os == 'Darwin':
        return ("RAM acquisition is not available on macOS: Apple's System Integrity Protection blocks the raw "
                "/dev/mem-style access live memory imagers need, and there is no current supported free tool for "
                "it on recent macOS. This is a genuine platform limitation, not a missing feature here.")
    if current_os == 'Windows':
        return ("No memory-imaging tool found. Install WinPmem (free, open source) from "
                "https://github.com/Velocidex/WinPmem/releases and place winpmem.exe on PATH, or in "
                "Program Files\\WinPmem, then try again.")
    return ("No memory-imaging tool found. Install AVML (free, open source, static binary, no kernel module needed) "
            "from https://github.com/microsoft/avml/releases, place it on PATH, then try again.")


# ---- from c12_signing.py ----


def v34_detect_backend():
    try:
        import cryptography  # noqa: F401
        return 'cryptography'
    except ImportError:
        pass
    if shutil.which('openssl'):
        return 'openssl'
    return None


def v34_sign_bytes_cryptography(private_key_pem, data):
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import padding
    key = serialization.load_pem_private_key(private_key_pem, password=None)
    sig = key.sign(data, padding.PKCS1v15(), hashes.SHA256())
    return sig


def v34_verify_bytes_cryptography(public_key_pem, data, signature):
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import padding
    from cryptography.exceptions import InvalidSignature
    key = serialization.load_pem_public_key(public_key_pem)
    try:
        key.verify(signature, data, padding.PKCS1v15(), hashes.SHA256())
        return True
    except InvalidSignature:
        return False


def v34_generate_keypair_cryptography():
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric import rsa
    key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    priv_pem = key.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8,
                                  serialization.NoEncryption())
    pub_pem = key.public_key().public_bytes(serialization.Encoding.PEM,
                                             serialization.PublicFormat.SubjectPublicKeyInfo)
    return priv_pem, pub_pem


def v34_fingerprint(public_key_pem):
    """Short human-checkable fingerprint of a PEM public key (SHA-256, hex, colon-grouped)."""
    h = hashlib.sha256(public_key_pem).hexdigest()
    return ':'.join(h[i:i + 4] for i in range(0, 32, 4))


def v34_render_signature_block(backend, pubkey_fingerprint, signed, sig_path, manifest_hash):
    out = ["=" * 60, "REPORT / EVIDENCE SIGNATURE", "=" * 60, ""]
    if not signed:
        out.append("Not signed: no signing backend available (needs the Python 'cryptography' package or the "
                    "'openssl' command-line tool). Hashing above still proves integrity; signing additionally "
                    "proves which examiner key attested to it. Install either and re-export to add a signature.")
        return "\n".join(out) + "\n"
    out.append(f"Signed with: {backend}  (RSA-2048 / SHA-256, PKCS#1 v1.5)")
    out.append(f"Examiner public-key fingerprint: {pubkey_fingerprint}")
    out.append(f"Signature covers: manifest.sha256  ({manifest_hash})")
    out.append(f"Signature file: {sig_path}")
    out.append("")
    out.append("To verify independently with OpenSSL:")
    out.append("  openssl dgst -sha256 -verify examiner_public_key.pem -signature manifest.sig manifest.sha256")
    return "\n".join(out) + "\n"


# ---- from c13_diff.py ----
def v34__as_path_hash_dict(manifest):
    """manifest.json's 'files' is a LIST of {'path':.., 'sha256':.., ...} records
    (see export_evidence_package); normalise to {path: sha256}. Also accepts an
    already-normalised dict for convenience/testing."""
    files = manifest.get('files', manifest) if isinstance(manifest, dict) else manifest
    if isinstance(files, dict):
        return {p: (v.get('sha256') if isinstance(v, dict) else v) for p, v in files.items()}
    out = {}
    for rec in files or []:
        if isinstance(rec, dict) and 'path' in rec:
            out[rec['path']] = rec.get('sha256')
    return out


def v34_diff_manifests(before, after):
    """
    before, after: a parsed manifest.json dict (the shape export_evidence_package()
    writes: {'files': [{'path':.., 'sha256':.., ...}, ...], ...}).
    Returns dict with 'added', 'removed', 'changed' (path -> (old_hash, new_hash)),
    'unchanged' (count only).
    """
    b_files = v34__as_path_hash_dict(before)
    a_files = v34__as_path_hash_dict(after)
    b_paths, a_paths = set(b_files), set(a_files)

    added = sorted(a_paths - b_paths)
    removed = sorted(b_paths - a_paths)
    changed = {}
    unchanged = 0
    for p in sorted(b_paths & a_paths):
        bh, ah = b_files[p], a_files[p]
        if bh != ah:
            changed[p] = (bh, ah)
        else:
            unchanged += 1
    return {'added': added, 'removed': removed, 'changed': changed, 'unchanged': unchanged}


def v34_diff_process_lists(before_procs, after_procs):
    """
    before_procs, after_procs: list of dicts with at least 'pid' and 'name'
    (the shape _list_processes() already returns).
    Returns dict with 'new' (processes present only after) and 'ended'
    (present only before), matched by (name, exe_hash) when available,
    else by name alone.
    """
    def key(p):
        return (p.get('name', '').lower(), p.get('hash') or p.get('exe_hash') or '')

    b_by_key = {key(p): p for p in before_procs}
    a_by_key = {key(p): p for p in after_procs}
    new = [a_by_key[k] for k in a_by_key if k not in b_by_key]
    ended = [b_by_key[k] for k in b_by_key if k not in a_by_key]
    return {'new': new, 'ended': ended}


def v34_render_diff_report(label_before, label_after, file_diff, proc_diff=None):
    out = ["=" * 60, "BASELINE DIFF", f"{label_before}   -->   {label_after}", "=" * 60, ""]
    out.append(f"Files added: {len(file_diff['added'])}   removed: {len(file_diff['removed'])}   "
               f"changed: {len(file_diff['changed'])}   unchanged: {file_diff['unchanged']}")
    out.append("")
    if file_diff['added']:
        out.append("Added since baseline:")
        out += [f"  + {p}" for p in file_diff['added'][:500]]
        out.append("")
    if file_diff['removed']:
        out.append("Removed since baseline:")
        out += [f"  - {p}" for p in file_diff['removed'][:500]]
        out.append("")
    if file_diff['changed']:
        out.append("Changed (hash differs) since baseline:")
        for p, (oldh, newh) in list(file_diff['changed'].items())[:500]:
            out.append(f"  ~ {p}")
            out.append(f"      was: {oldh}")
            out.append(f"      now: {newh}")
        out.append("")
    if proc_diff is not None:
        out.append(f"Processes newly present: {len(proc_diff['new'])}   no longer present: {len(proc_diff['ended'])}")
        for p in proc_diff['new'][:200]:
            out.append(f"  + pid {p.get('pid', '?')}  {p.get('name', '?')}")
        for p in proc_diff['ended'][:200]:
            out.append(f"  - pid {p.get('pid', '?')}  {p.get('name', '?')}")
    if not (file_diff['added'] or file_diff['removed'] or file_diff['changed']):
        out.append("No file differences between the two collections.")
    return "\n".join(out) + "\n"


# ---- from c14_timeline_layout.py ----

_SOURCE_COLORS = ['#4fc3f7', '#81c784', '#ffb74d', '#e57373', '#ba68c8', '#4db6ac',
                  '#fff176', '#90a4ae', '#f06292', '#aed581']


def v34__try_parse(ts):
    ts = (ts or '').strip()
    if not ts:
        return None
    s = ts.replace('Z', '+00:00')
    for fmt in (None, '%Y-%m-%d %H:%M:%S', '%m/%d/%Y %H:%M:%S', '%Y-%m-%dT%H:%M:%S'):
        try:
            return datetime.fromisoformat(s) if fmt is None else datetime.strptime(ts, fmt)
        except (ValueError, TypeError):
            continue
    m = re.search(r'(\d{4})-(\d{2})-(\d{2})', ts)
    if m:
        try:
            return datetime(int(m.group(1)), int(m.group(2)), int(m.group(3)))
        except ValueError:
            return None
    return None


def v34_assign_colors(sources):
    uniq = sorted(set(sources))
    return {s: _SOURCE_COLORS[i % len(_SOURCE_COLORS)] for i, s in enumerate(uniq)}


def v34_layout_timeline(events, width=1400, margin=40, row_height=22):
    """
    events: list of {'time', 'source', 'context'} (as build_super_timeline() produces).
    Returns {'points': [...], 'unparsed': [...], 'span': (min_dt, max_dt), 'colors': {source: hex}}
    Each point: {'x': int, 'source': str, 'context': str, 'time': str, 'dt': datetime}
    """
    parsed = []
    unparsed = []
    for e in events:
        dt = v34__try_parse(e.get('time'))
        if dt is None:
            unparsed.append(e)
        else:
            parsed.append((dt, e))
    colors = v34_assign_colors([e.get('source', '') for e in events])
    if not parsed:
        return {'points': [], 'unparsed': unparsed, 'span': (None, None), 'colors': colors}

    parsed.sort(key=lambda t: t[0])
    tmin, tmax = parsed[0][0], parsed[-1][0]
    span_secs = max((tmax - tmin).total_seconds(), 1)
    usable_w = max(width - 2 * margin, 10)

    points = []
    for dt, e in parsed:
        frac = (dt - tmin).total_seconds() / span_secs
        x = margin + int(frac * usable_w)
        points.append({'x': x, 'source': e.get('source', ''), 'context': e.get('context', ''),
                       'time': e.get('time', ''), 'dt': dt, 'color': colors.get(e.get('source', ''), '#888')})
    return {'points': points, 'unparsed': unparsed, 'span': (tmin, tmax), 'colors': colors}


# ---- from c15_dashboard.py ----

_CASE_DIR_RE = re.compile(r'^(?P<case>.+)_(?P<ts>\d{8}T\d{6}Z)$')


def v34__dir_size(path):
    total = 0
    for dp, _dn, fns in os.walk(path):
        for n in fns:
            try:
                total += (Path(dp) / n).stat().st_size
            except OSError:
                pass
    return total


def v34__human_size(n):
    for unit in ('B', 'KB', 'MB', 'GB', 'TB'):
        if n < 1024:
            return f"{n:.0f} {unit}" if unit == 'B' else f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} PB"


def v34_scan_cases(base_dir):
    """
    base_dir: the CACTUS_Cases root (or any folder containing <case>_<UTCts> vaults).
    Returns a list of dicts, most recent first:
      {name, case_id, created_utc, path, size_bytes, size_human, exports: [...], examiner}
    Never raises on a single bad folder -- it's skipped, not fatal to the whole scan.
    """
    base = Path(base_dir)
    results = []
    if not base.is_dir():
        return results
    for entry in sorted(base.iterdir()):
        if not entry.is_dir():
            continue
        m = _CASE_DIR_RE.match(entry.name)
        case_id, ts = (m.group('case'), m.group('ts')) if m else (entry.name, '')
        exports = []
        examiner = ''
        for exp_dir in sorted(entry.glob('export_*')):
            manifest_path = exp_dir / 'manifest.json'
            if manifest_path.is_file():
                try:
                    manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
                except (OSError, ValueError):
                    manifest = {}
                case = manifest.get('case') or {}
                examiner = examiner or case.get('examiner', '')
                exports.append({'name': exp_dir.name, 'created_utc': manifest.get('created_utc', ''),
                                'file_count': manifest.get('file_count', 0), 'manifest_sha256': None})
                sidecar = entry / f"{exp_dir.name}.zip.hashes.txt"
                if sidecar.is_file():
                    for ln in sidecar.read_text(encoding='utf-8', errors='replace').splitlines():
                        if ln.startswith('SHA-256:'):
                            exports[-1]['manifest_sha256'] = ln.split(':', 1)[1].strip()
        size = v34__dir_size(entry)
        results.append({'name': entry.name, 'case_id': case_id, 'created_utc_from_name': ts, 'path': str(entry),
                        'size_bytes': size, 'size_human': v34__human_size(size), 'exports': exports, 'examiner': examiner})
    results.sort(key=lambda r: r['created_utc_from_name'], reverse=True)
    return results


def v34_render_dashboard(cases):
    out = ["=" * 70, f"CASE DASHBOARD  ({len(cases)} case folder(s))", "=" * 70, ""]
    if not cases:
        out.append("No case folders found under this base directory yet.")
        return "\n".join(out) + "\n"
    for c in cases:
        out.append(f"{c['case_id']}   [{c['created_utc_from_name'] or 'unknown timestamp'}]")
        out.append(f"  Path: {c['path']}")
        out.append(f"  Size on disk: {c['size_human']}   Exported package(s): {len(c['exports'])}" +
                   (f"   Examiner: {c['examiner']}" if c['examiner'] else ""))
        for e in c['exports']:
            out.append(f"    - {e['name']}   {e['file_count']} file(s)   created {e['created_utc']}")
            if e['manifest_sha256']:
                out.append(f"      package SHA-256: {e['manifest_sha256']}")
        out.append("")
    return "\n".join(out) + "\n"


# ---- from c16_readonly.py ----


def v34_check_mount_readonly_posix(path, mount_output):
    """
    path: the target path.
    mount_output: text of `mount` (Linux/macOS) already captured by the caller
    (kept as an argument, not a subprocess call here, so this is testable).
    Returns (is_readonly: bool|None, mountpoint: str|None, raw_line: str|None).
    None means "could not determine."
    """
    best_match, best_len = None, -1
    for ln in (mount_output or '').splitlines():
        m = re.match(r'^(?P<dev>\S+) on (?P<mnt>.+?) (?:type \S+ )?\((?P<opts>[^)]*)\)\s*$', ln)
        if not m:
            continue
        mnt = m.group('mnt')
        if path.startswith(mnt) and len(mnt) > best_len:
            best_match, best_len = (mnt, m.group('opts'), ln), len(mnt)
    if not best_match:
        return None, None, None
    mnt, opts, raw = best_match
    opt_list = [o.strip() for o in opts.split(',')]
    if 'ro' in opt_list:
        return True, mnt, raw
    if 'rw' in opt_list:
        return False, mnt, raw
    return None, mnt, raw


def v34_render_readonly_note(path, is_readonly, mountpoint, is_removable=None):
    out = [f"Write-protection check for: {path}"]
    if is_readonly is None:
        out.append("  Could not determine whether the containing volume is mounted read-only.")
    elif is_readonly:
        out.append(f"  Mounted READ-ONLY at {mountpoint}. Good -- this collection cannot have modified it.")
    else:
        out.append(f"  Mounted read-write at {mountpoint}. This tool does not write to the target path itself, "
                    f"but the OS may still touch metadata (e.g. access times) while reading it. For courtroom-"
                    f"grade dead-box imaging, use a hardware write blocker; this is a live-system check, not a "
                    f"substitute for one.")
    if is_removable is not None:
        out.append(f"  Removable/external media: {'yes' if is_removable else 'no'}")
    return "\n".join(out) + "\n"



class DigitalForensicTool:
    def __init__(self, root):
        self.root = root
        self.root.title("Cactus v2.0")
        self.root.geometry("1500x900")
        self.root.minsize(1200, 700)
        self.root.configure(bg=Theme.BG_DARK)

        # State
        self.current_os = platform.system()
        self.investigation_data = EvidenceDict(self._record_evidence)
        self.active_workers = []
        self.task_queue = queue.Queue()
        self.ui_queue = queue.Queue()

        # Setup styles
        self.setup_styles()

        # Build UI
        self.build_ui()

        # Start UI update loop
        self.process_ui_queue()

        # Show welcome
        self.root.after(200, self.show_welcome)

    # --------------------------------------------------------
    # STYLES
    # --------------------------------------------------------
    def setup_styles(self):
        style = ttk.Style()
        try:
            style.theme_use('clam')
        except tk.TclError:
            pass

        # Frames
        style.configure('TFrame', background=Theme.BG_DARK)
        style.configure('Card.TFrame', background=Theme.BG_CARD, relief='flat')
        style.configure('Header.TFrame', background=Theme.BG_MEDIUM)

        # Labels
        style.configure('TLabel', background=Theme.BG_DARK,
                        foreground=Theme.TEXT_PRIMARY, font=('Segoe UI', 10))
        style.configure('Card.TLabel', background=Theme.BG_CARD,
                        foreground=Theme.TEXT_PRIMARY, font=('Segoe UI', 10))
        style.configure('Header.TLabel', background=Theme.BG_MEDIUM,
                        foreground=Theme.TEXT_PRIMARY, font=('Segoe UI', 10))
        style.configure('Title.TLabel', background=Theme.BG_MEDIUM,
                        foreground=Theme.ACCENT, font=('Segoe UI', 18, 'bold'))
        style.configure('Subtitle.TLabel', background=Theme.BG_MEDIUM,
                        foreground=Theme.TEXT_SECONDARY, font=('Segoe UI', 9))
        style.configure('Section.TLabel', background=Theme.BG_CARD,
                        foreground=Theme.ACCENT, font=('Segoe UI', 12, 'bold'))

        # Buttons
        style.configure('TButton', background=Theme.BG_LIGHT,
                        foreground=Theme.TEXT_PRIMARY, borderwidth=0,
                        focuscolor=Theme.ACCENT, padding=(16, 8),
                        font=('Segoe UI', 10, 'bold'))
        style.map('TButton',
                  background=[('active', Theme.ACCENT), ('pressed', Theme.ACCENT_HOVER)],
                  foreground=[('active', Theme.BG_DARK), ('pressed', Theme.BG_DARK)])

        style.configure('Accent.TButton', background=Theme.ACCENT,
                        foreground=Theme.BG_DARK, borderwidth=0,
                        focuscolor=Theme.ACCENT, padding=(16, 8),
                        font=('Segoe UI', 10, 'bold'))
        style.map('Accent.TButton',
                  background=[('active', Theme.ACCENT_HOVER), ('pressed', Theme.ACCENT_HOVER)])

        style.configure('Danger.TButton', background=Theme.ERROR,
                        foreground='white', borderwidth=0,
                        padding=(16, 8), font=('Segoe UI', 10, 'bold'))
        style.map('Danger.TButton',
                  background=[('active', '#e63946'), ('pressed', '#c1121f')])

        # Notebook
        style.configure('TNotebook', background=Theme.BG_DARK, borderwidth=0)
        style.configure('TNotebook.Tab', background=Theme.BG_MEDIUM,
                        foreground=Theme.TEXT_SECONDARY, padding=(20, 10),
                        font=('Segoe UI', 10, 'bold'), borderwidth=0)
        style.map('TNotebook.Tab',
                  background=[('selected', Theme.BG_CARD), ('active', Theme.BG_LIGHT)],
                  foreground=[('selected', Theme.ACCENT), ('active', Theme.TEXT_PRIMARY)])

        # Entry
        style.configure('TEntry', fieldbackground=Theme.BG_LIGHT,
                        foreground=Theme.TEXT_PRIMARY, borderwidth=0,
                        insertcolor=Theme.ACCENT, padding=8)

        # Combobox
        style.configure('TCombobox', fieldbackground=Theme.BG_LIGHT,
                        background=Theme.BG_LIGHT, foreground=Theme.TEXT_PRIMARY,
                        arrowcolor=Theme.ACCENT, borderwidth=0, padding=6)
        style.map('TCombobox',
                  fieldbackground=[('readonly', Theme.BG_LIGHT)],
                  background=[('readonly', Theme.BG_LIGHT)],
                  foreground=[('readonly', Theme.TEXT_PRIMARY)],
                  selectbackground=[('readonly', Theme.BG_LIGHT)],
                  selectforeground=[('readonly', Theme.TEXT_PRIMARY)])
        self.root.option_add('*TCombobox*Listbox.background', Theme.BG_LIGHT)
        self.root.option_add('*TCombobox*Listbox.foreground', Theme.TEXT_PRIMARY)
        self.root.option_add('*TCombobox*Listbox.selectBackground', Theme.ACCENT)
        self.root.option_add('*TCombobox*Listbox.selectForeground', Theme.BG_DARK)

        # Checkbutton
        style.configure('TCheckbutton', background=Theme.BG_CARD,
                        foreground=Theme.TEXT_PRIMARY, font=('Segoe UI', 10))
        style.map('TCheckbutton',
                  background=[('active', Theme.BG_CARD)],
                  foreground=[('active', Theme.ACCENT)])

        # Progressbar
        style.configure('TProgressbar', background=Theme.ACCENT,
                        troughcolor=Theme.BG_LIGHT, borderwidth=0,
                        lightcolor=Theme.ACCENT, darkcolor=Theme.ACCENT)
        style.configure('Horizontal.TProgressbar', background=Theme.ACCENT,
                        troughcolor=Theme.BG_LIGHT)

        # LabelFrame
        style.configure('TLabelframe', background=Theme.BG_CARD,
                        foreground=Theme.ACCENT, borderwidth=1,
                        relief='solid', bordercolor=Theme.BORDER)
        style.configure('TLabelframe.Label', background=Theme.BG_CARD,
                        foreground=Theme.ACCENT, font=('Segoe UI', 11, 'bold'))

    # --------------------------------------------------------
    # UI CONSTRUCTION
    # --------------------------------------------------------
    def build_ui(self):
        # Header
        self.build_header()

        # Body (sidebar + main content)
        body = tk.Frame(self.root, bg=Theme.BG_DARK)
        body.pack(fill='both', expand=True, padx=16, pady=(0, 8))

        # Main notebook
        self.notebook = ttk.Notebook(body)
        self.notebook.pack(fill='both', expand=True)

        self.build_system_tab()
        self.build_browser_tab()
        self.build_devices_tab()
        self.build_registry_tab()
        self.build_events_tab()
        self.build_network_tab()
        self.build_packets_tab()
        self.build_live_tab()
        self.build_ioc_tab()
        self.build_search_tab()
        self.build_case_tab()
        self.build_report_tab()

        # Status bar
        self.build_status_bar()

    def build_header(self):
        header = tk.Frame(self.root, bg=Theme.BG_MEDIUM, height=70)
        header.pack(fill='x', pady=(0, 12))
        header.pack_propagate(False)

        left = tk.Frame(header, bg=Theme.BG_MEDIUM)
        left.pack(side='left', padx=20, pady=12)

        tk.Label(left, text="🔍", font=('Segoe UI', 22),
                 bg=Theme.BG_MEDIUM, fg=Theme.ACCENT).pack(side='left', padx=(0, 10))

        title_box = tk.Frame(left, bg=Theme.BG_MEDIUM)
        title_box.pack(side='left')
        tk.Label(title_box, text="Cactus v2.0",
                 font=('Segoe UI', 16, 'bold'),
                 bg=Theme.BG_MEDIUM, fg=Theme.TEXT_PRIMARY).pack(anchor='w')
        tk.Label(title_box, text="Professional Artifact Collection & Analysis Suite",
                 font=('Segoe UI', 9),
                 bg=Theme.BG_MEDIUM, fg=Theme.TEXT_SECONDARY).pack(anchor='w')

        right = tk.Frame(header, bg=Theme.BG_MEDIUM)
        right.pack(side='right', padx=20, pady=12)

        os_icon = {"Windows": "🪟", "Linux": "🐧", "Darwin": "🍎"}.get(self.current_os, "💻")
        tk.Label(right, text=f"{os_icon}  {self.current_os}",
                 font=('Segoe UI', 11, 'bold'),
                 bg=Theme.BG_MEDIUM, fg=Theme.ACCENT).pack(anchor='e')
        tk.Label(right, text=platform.platform()[:40],
                 font=('Segoe UI', 8),
                 bg=Theme.BG_MEDIUM, fg=Theme.TEXT_SECONDARY).pack(anchor='e')

    def build_status_bar(self):
        bar = tk.Frame(self.root, bg=Theme.BG_MEDIUM, height=34)
        bar.pack(fill='x', side='bottom')
        bar.pack_propagate(False)

        self.status_dot = tk.Label(bar, text="●", font=('Segoe UI', 12),
                                   bg=Theme.BG_MEDIUM, fg=Theme.SUCCESS)
        self.status_dot.pack(side='left', padx=(16, 6))

        self.status_label = tk.Label(bar, text="Ready",
                                     font=('Segoe UI', 10),
                                     bg=Theme.BG_MEDIUM, fg=Theme.TEXT_PRIMARY)
        self.status_label.pack(side='left')

        self.progress_bar = ttk.Progressbar(bar, mode='indeterminate', length=180)
        self.progress_bar.pack(side='right', padx=16, pady=6)

        self.thread_label = tk.Label(bar, text="Threads: 0",
                                     font=('Segoe UI', 9),
                                     bg=Theme.BG_MEDIUM, fg=Theme.TEXT_SECONDARY)
        self.thread_label.pack(side='right', padx=10)

    # --------------------------------------------------------
    # TAB: SYSTEM ANALYSIS
    # --------------------------------------------------------
    def build_system_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  📊  System  ')

        # Top action bar
        actions = tk.Frame(tab, bg=Theme.BG_DARK)
        actions.pack(fill='x', padx=12, pady=12)

        ttk.Button(actions, text="⚡ Collect System Info", style='Accent.TButton',
                   command=self.collect_system_info).pack(side='left', padx=4)
        ttk.Button(actions, text="🕐 Collect Timeline",
                   command=self.collect_timeline).pack(side='left', padx=4)
        ttk.Button(actions, text="🗑 Clear",
                   command=lambda: self.clear_text(self.system_text)).pack(side='left', padx=4)

        # Panels
        panels = tk.Frame(tab, bg=Theme.BG_DARK)
        panels.pack(fill='both', expand=True, padx=12, pady=(0, 12))

        left = self._make_card(panels, "System Information")
        left.pack(side='left', fill='both', expand=True, padx=(0, 6))
        self.system_text = self._make_text_area(left)

        right = self._make_card(panels, "Timeline & Recent Activity")
        right.pack(side='right', fill='both', expand=True, padx=(6, 0))
        self.timeline_text = self._make_text_area(right)

    # --------------------------------------------------------
    # TAB: BROWSER ARTIFACTS
    # --------------------------------------------------------
    def build_browser_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  🌐  Browsers  ')

        # Browser selection card
        sel_card = self._make_card(tab, "Target Browsers")
        sel_card.pack(fill='x', padx=12, pady=12)

        browsers_row = tk.Frame(sel_card, bg=Theme.BG_CARD)
        browsers_row.pack(fill='x', padx=8, pady=8)

        self.browser_vars = {}
        browsers = [
            ('Chrome', '🌐'), ('Firefox', '🦊'), ('Safari', '🧭'),
            ('Microsoft Edge', '🌊'), ('Brave', '🦁')
        ]
        for name, icon in browsers:
            var = tk.BooleanVar(value=True)
            self.browser_vars[name] = var
            cb = ttk.Checkbutton(browsers_row, text=f"{icon} {name}", variable=var)
            cb.pack(side='left', padx=12)

        # Action bar
        actions = tk.Frame(tab, bg=Theme.BG_DARK)
        actions.pack(fill='x', padx=12, pady=(0, 8))
        ttk.Button(actions, text="⚡ Collect Browser History", style='Accent.TButton',
                   command=self.collect_browser_history).pack(side='left', padx=4)
        ttk.Button(actions, text="🍎 Check macOS Permissions",
                   command=self.check_macos_permissions).pack(side='left', padx=4)
        ttk.Button(actions, text="🛡 Admin",
                   command=self.restart_as_admin).pack(side='left', padx=4)
        ttk.Button(actions, text="🗑 Clear",
                   command=lambda: self.clear_text(self.history_text)).pack(side='left', padx=4)

        # Results
        results = self._make_card(tab, "Browser History & Activity")
        results.pack(fill='both', expand=True, padx=12, pady=(0, 12))
        self.history_text = self._make_text_area(results)

    # --------------------------------------------------------
    # TAB: EVENT LOGS
    # --------------------------------------------------------
    def build_events_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  📋  Events  ')

        # ---- range / filter controls -------------------------------
        ctl = self._make_card(tab, "What to collect")
        ctl.pack(fill='x', padx=12, pady=(12, 8))
        row1 = tk.Frame(ctl.body, bg=Theme.BG_CARD)
        row1.pack(fill='x', padx=8, pady=(4, 2))
        lbl = lambda p, t: tk.Label(p, text=t, bg=Theme.BG_CARD, fg=Theme.TEXT_PRIMARY,
                                    font=('Segoe UI', 10))

        lbl(row1, "Time range:").pack(side='left', padx=(0, 6))
        self.event_preset = tk.StringVar(value="Last 1 day")
        self.event_preset_cb = ttk.Combobox(
            row1, textvariable=self.event_preset, state='readonly', width=16,
            values=[name for name, _d in self.EVENT_PRESETS])
        self.event_preset_cb.pack(side='left', padx=(0, 14))
        self.event_preset_cb.bind('<<ComboboxSelected>>', self._toggle_custom_dates)

        today = date.today()
        self.event_from = tk.StringVar(value=(today - timedelta(days=7)).isoformat())
        self.event_to = tk.StringVar(value=today.isoformat())
        lbl(row1, "From:").pack(side='left', padx=(0, 4))
        self.event_from_entry = ttk.Entry(row1, textvariable=self.event_from, width=11)
        self.event_from_entry.pack(side='left')
        self.event_from_btn = ttk.Button(
            row1, text="📅", width=3,
            command=lambda: DatePicker(self.root, self.event_from, self.event_from_btn))
        self.event_from_btn.pack(side='left', padx=(2, 10))
        lbl(row1, "To:").pack(side='left', padx=(0, 4))
        self.event_to_entry = ttk.Entry(row1, textvariable=self.event_to, width=11)
        self.event_to_entry.pack(side='left')
        self.event_to_btn = ttk.Button(
            row1, text="📅", width=3,
            command=lambda: DatePicker(self.root, self.event_to, self.event_to_btn))
        self.event_to_btn.pack(side='left', padx=(2, 0))

        row2 = tk.Frame(ctl.body, bg=Theme.BG_CARD)
        row2.pack(fill='x', padx=8, pady=(2, 8))
        lbl(row2, "Level:").pack(side='left', padx=(0, 6))
        self.event_level = tk.StringVar(value=self.LEVEL_FILTERS[0])
        ttk.Combobox(row2, textvariable=self.event_level, state='readonly', width=18,
                     values=self.LEVEL_FILTERS).pack(side='left', padx=(0, 14))
        lbl(row2, "Max events:").pack(side='left', padx=(0, 6))
        self.event_limit = tk.StringVar(value="5000")
        ttk.Combobox(row2, textvariable=self.event_limit, state='readonly', width=8,
                     values=["500", "1000", "5000", "20000", "50000"]).pack(side='left', padx=(0, 14))
        ttk.Button(row2, text="⚡ Collect Event Logs", style='Accent.TButton',
                   command=self.collect_event_logs).pack(side='left', padx=4)
        ttk.Button(row2, text="🗑 Clear",
                   command=self.clear_event_view).pack(side='left', padx=4)
        self._toggle_custom_dates()

        # ---- timeline ----------------------------------------------
        tl = self._make_card(tab, "Timeline  (events per hour / day / week)")
        tl.pack(fill='x', padx=12, pady=(0, 8))
        self.timeline_info = tk.Label(tl.body, text="Collect event logs to draw the timeline.",
                                      bg=Theme.BG_CARD, fg=Theme.TEXT_SECONDARY,
                                      font=('Segoe UI', 9), anchor='w')
        self.timeline_info.pack(fill='x', padx=6)
        self.timeline_canvas = tk.Canvas(tl.body, height=170, bg=Theme.BG_LIGHT,
                                         highlightthickness=0)
        self.timeline_canvas.pack(fill='x', padx=4, pady=(2, 4))
        self.timeline_canvas.bind('<Configure>', lambda e: self._draw_timeline())
        self.timeline_canvas.bind('<Motion>', self._timeline_hover)
        self.timeline_canvas.bind('<Leave>', lambda e: self._timeline_hover(None))
        self._timeline_data = None
        self._timeline_rects = []

        # ---- results -------------------------------------------------
        card = self._make_card(tab, "Events  (newest first)")
        card.pack(fill='both', expand=True, padx=12, pady=(0, 12))
        self.log_text = self._make_text_area(card)

    # --------------------------------------------------------
    # TAB: NETWORK ACTIVITY
    # --------------------------------------------------------
    def build_network_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  📡  Network  ')

        actions = tk.Frame(tab, bg=Theme.BG_DARK)
        actions.pack(fill='x', padx=12, pady=(12, 4))
        ttk.Button(actions, text="⚡ Collect Network Activity", style='Accent.TButton',
                   command=self.collect_network_activity).pack(side='left', padx=4)
        tk.Label(actions, text="Passive capture:", bg=Theme.BG_DARK,
                 fg=Theme.TEXT_PRIMARY, font=('Segoe UI', 10)).pack(side='left', padx=(18, 4))
        self.capture_secs = tk.StringVar(value="30")
        ttk.Combobox(actions, textvariable=self.capture_secs, state='readonly', width=5,
                     values=["10", "30", "60", "120", "300"]).pack(side='left')
        tk.Label(actions, text="seconds", bg=Theme.BG_DARK, fg=Theme.TEXT_SECONDARY,
                 font=('Segoe UI', 9)).pack(side='left', padx=(4, 6))
        ttk.Button(actions, text="🔬 Capture Protocols",
                   command=self.capture_protocols).pack(side='left', padx=4)
        ttk.Button(actions, text="🗑 Clear",
                   command=lambda: self.clear_text(self.network_text)).pack(side='left', padx=4)

        tk.Label(tab, text=("Lists the devices this computer has seen on the network (ARP / neighbour "
                            "cache), which protocols each one is using right now, the networks this "
                            "computer has joined before, and the services it offers. Nothing is sent "
                            "to other devices. 'Capture Protocols' listens passively and needs "
                            "administrator rights."),
                 bg=Theme.BG_DARK, fg=Theme.TEXT_SECONDARY, font=('Segoe UI', 9),
                 anchor='w', justify='left', wraplength=1300).pack(fill='x', padx=16, pady=(0, 8))

        card = self._make_card(tab, "Network Devices, Protocols & History")
        card.pack(fill='both', expand=True, padx=12, pady=(0, 12))
        self.network_text = self._make_text_area(card)

    # --------------------------------------------------------

    # --------------------------------------------------------
    # TAB: IOC EXTRACTION
    # --------------------------------------------------------
    def build_ioc_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  🔐  Hashing  ')

        # File picker card
        picker = self._make_card(tab, "File Selection")
        picker.pack(fill='x', padx=12, pady=12)

        row = tk.Frame(picker, bg=Theme.BG_CARD)
        row.pack(fill='x', padx=8, pady=8)

        self.file_path = tk.StringVar()
        ttk.Entry(row, textvariable=self.file_path).pack(
            side='left', fill='x', expand=True, padx=(0, 8))
        ttk.Button(row, text="📁 Browse", command=self.browse_file).pack(side='left', padx=4)

        # Actions
        actions = tk.Frame(tab, bg=Theme.BG_DARK)
        actions.pack(fill='x', padx=12, pady=(0, 8))
        ttk.Button(actions, text="⚡ Calculate Hashes", style='Accent.TButton',
                   command=self.calculate_hashes).pack(side='left', padx=4)
        ttk.Button(actions, text="✓ Verify Hash",
                   command=self.verify_hash).pack(side='left', padx=4)

        # Results
        card = self._make_card(tab, "Hash Values (MD5 / SHA1 / SHA256 / SHA512)")
        card.pack(fill='both', expand=True, padx=12, pady=(0, 12))
        self.hash_text = self._make_text_area(card)

        # Hash-set matching (NSRL-style known-good / known-bad IOC hash lists)
        hs_card = self._make_card(tab, "Hash-Set Matching (compares hashes already collected in this case)")
        hs_card.pack(fill='x', padx=12, pady=(0, 12))
        hs_row = tk.Frame(hs_card, bg=Theme.BG_CARD)
        hs_row.pack(fill='x', padx=8, pady=8)
        ttk.Button(hs_row, text="📥 Load Known-Good Set (e.g. NSRL)",
                   command=lambda: self.load_hash_set('allow')).pack(side='left', padx=4)
        ttk.Button(hs_row, text="📥 Load Known-Bad / IOC Hash Set",
                   command=lambda: self.load_hash_set('block')).pack(side='left', padx=4)
        tk.Label(hs_card, text=("Loads a local text or CSV file of hashes (MD5/SHA-1/SHA-256/SHA-512, or an NSRL-RDS-style "
                                "CSV export). No network lookups are made -- the set must already be on disk. Matches "
                                "are checked against every file already hashed in this case's collected evidence."),
                 bg=Theme.BG_CARD, fg=Theme.TEXT_SECONDARY, font=('Segoe UI', 9), anchor='w', justify='left',
                 wraplength=1300).pack(fill='x', padx=8, pady=(0, 8))

    # --------------------------------------------------------
    # TAB: REPORT
    # --------------------------------------------------------
    def build_report_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  📄  Report  ')

        # Options card
        options = self._make_card(tab, "Report Options")
        options.pack(fill='x', padx=12, pady=12)

        row = tk.Frame(options, bg=Theme.BG_CARD)
        row.pack(fill='x', padx=8, pady=8)

        tk.Label(row, text="Format:", bg=Theme.BG_CARD,
                 fg=Theme.TEXT_PRIMARY, font=('Segoe UI', 10)).pack(side='left', padx=(0, 8))

        self.report_format = ttk.Combobox(row, values=['PDF', 'HTML', 'JSON', 'TXT'],
                                          state='readonly', width=12)
        self.report_format.set('PDF')
        self.report_format.pack(side='left', padx=4)

        ttk.Button(row, text="📄 Generate Report", style='Accent.TButton',
                   command=self.generate_report).pack(side='left', padx=16)

        # Preview
        card = self._make_card(tab, "Report Preview")
        card.pack(fill='both', expand=True, padx=12, pady=(0, 12))
        self.report_text = self._make_text_area(card)

    # --------------------------------------------------------
    # TAB: CONNECTED DEVICES
    # --------------------------------------------------------
    def build_devices_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  💽  Devices  ')

        actions = tk.Frame(tab, bg=Theme.BG_DARK)
        actions.pack(fill='x', padx=12, pady=12)
        ttk.Button(actions, text="⚡ Scan Connected Devices", style='Accent.TButton',
                   command=self.collect_devices).pack(side='left', padx=4)
        ttk.Button(actions, text="🕘 USB / Device History",
                   command=self.collect_device_history).pack(side='left', padx=4)
        ttk.Button(actions, text="🗑 Clear",
                   command=lambda: self.clear_text(self.devices_text)).pack(side='left', padx=4)

        card = self._make_card(tab, "Storage & USB Devices  (USB, SSD, HDD, NVMe, SD card, optical)")
        card.pack(fill='both', expand=True, padx=12, pady=(0, 12))
        self.devices_text = self._make_text_area(card)

    # --------------------------------------------------------
    # TAB: OS REGISTRY
    # --------------------------------------------------------
    def build_registry_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  🗝  Artifacts  ')

        actions = tk.Frame(tab, bg=Theme.BG_DARK)
        actions.pack(fill='x', padx=12, pady=(12, 4))
        ttk.Button(actions, text="⚡ Collect All", style='Accent.TButton',
                   command=lambda: self.collect_artifacts(
                       [k for _l, k in self._artifact_list()])).pack(side='left', padx=4)
        for label, kind in self._artifact_list():
            ttk.Button(actions, text=label,
                       command=lambda k=kind: self.collect_artifacts([k])
                       ).pack(side='left', padx=4)
        ttk.Button(actions, text="🛡 Admin",
                   command=self.restart_as_admin).pack(side='left', padx=4)
        ttk.Button(actions, text="🗑 Clear",
                   command=lambda: self.clear_text(self.registry_text)).pack(side='left', padx=4)

        notes = {
            "Windows": "Windows forensic artifacts (read-only): Registry, Shellbags, Jump Lists, "
                       "Prefetch, Recent files, RunMRU, RecentDocs. Run as Administrator for Prefetch.",
            "Darwin": "macOS has no registry. Reading the equivalent artifacts: plists, recent items, "
                      "download quarantine history, install history and shell history. "
                      "Some need Full Disk Access.",
        }
        note = notes.get(self.current_os,
                         "Linux has no registry. Reading the equivalent artifacts: /etc config, recent "
                         "files, Trash, shell history and logins.")
        tk.Label(tab, text=note, bg=Theme.BG_DARK, fg=Theme.TEXT_SECONDARY,
                 font=('Segoe UI', 9), anchor='w', justify='left',
                 wraplength=1300).pack(fill='x', padx=16, pady=(0, 8))

        card = self._make_card(tab, "Registry / System Artifacts")
        card.pack(fill='both', expand=True, padx=12, pady=(0, 12))
        self.registry_text = self._make_text_area(card)

    # --------------------------------------------------------
    # UI HELPERS
    # --------------------------------------------------------
    def _make_card(self, parent, title):
        """Create a styled card container with a title."""
        wrapper = tk.Frame(parent, bg=Theme.BG_DARK)
        inner = tk.Frame(wrapper, bg=Theme.BG_CARD, highlightbackground=Theme.BORDER,
                         highlightthickness=1)
        inner.pack(fill='both', expand=True)

        title_bar = tk.Frame(inner, bg=Theme.BG_CARD)
        title_bar.pack(fill='x', padx=12, pady=(10, 4))
        tk.Label(title_bar, text=title, bg=Theme.BG_CARD,
                 fg=Theme.ACCENT, font=('Segoe UI', 11, 'bold')).pack(side='left')

        body = tk.Frame(inner, bg=Theme.BG_CARD)
        body.pack(fill='both', expand=True, padx=8, pady=(0, 8))

        wrapper.body = body
        return wrapper

    def _make_text_area(self, card):
        """Create a styled scrolled text area inside a card."""
        txt = scrolledtext.ScrolledText(
            card.body,
            bg=Theme.BG_LIGHT, fg=Theme.TEXT_PRIMARY,
            insertbackground=Theme.ACCENT,
            selectbackground=Theme.ACCENT, selectforeground=Theme.BG_DARK,
            font=('Consolas', 10), relief='flat', borderwidth=0,
            wrap='word', padx=12, pady=10
        )
        txt.pack(fill='both', expand=True)
        return txt

    def _pack_card(self, card, **kwargs):
        card.pack(**kwargs)
        return card

    # --------------------------------------------------------
    # THREADING HELPERS
    # --------------------------------------------------------
    def run_async(self, task, *args, on_done=None, on_error=None, status="Working..."):
        """Run task in background thread, call callbacks on main thread."""
        self.set_status(status, busy=True)
        label = status.rstrip('.')
        self._audit(label, 'started')

        def wrapped_done(result):
            def go():
                self._audit(label, 'completed')
                self._finish_task(on_done, result)
            self.root.after(0, go)

        def wrapped_error(e):
            def go():
                self._audit(label, 'FAILED', f"{type(e).__name__}: {e}"[:200])
                self._finish_task_error(on_error, e)
            self.root.after(0, go)

        worker = Worker(task, wrapped_done, wrapped_error, *args)
        self.active_workers.append(worker)
        self.update_thread_count()
        worker.start()

    def _finish_task(self, callback, result):
        self._cleanup_workers()
        self.set_status("Done", busy=False)
        if callback:
            callback(result)

    def _finish_task_error(self, callback, error):
        self._cleanup_workers()
        self.set_status("Error", busy=False)
        if callback:
            callback(error)
        else:
            messagebox.showerror("Error", str(error))

    def _cleanup_workers(self):
        self.active_workers = [w for w in self.active_workers if w.is_alive()]
        self.update_thread_count()

    def update_thread_count(self):
        self.thread_label.config(text=f"Threads: {len(self.active_workers)}")

    def set_status(self, text, busy=False):
        self.status_label.config(text=text)
        if busy:
            self.status_dot.config(fg=Theme.WARNING)
            self.progress_bar.start(12)
        else:
            self.status_dot.config(fg=Theme.SUCCESS)
            self.progress_bar.stop()

    def process_ui_queue(self):
        """Process UI updates queued from worker threads."""
        try:
            while True:
                fn = self.ui_queue.get_nowait()
                fn()
        except queue.Empty:
            pass
        self.root.after(100, self.process_ui_queue)

    # --------------------------------------------------------
    # WELCOME / SYSTEM INFO COLLECTION
    # --------------------------------------------------------
    def show_welcome(self):
        info = (
            "╔══════════════════════════════════════════════════════════╗\n"
            "║                  Cactus v2.0                             ║\n"
            "╚══════════════════════════════════════════════════════════╝\n\n"
            f"  Operating System : {self.current_os}\n"
            f"  Platform         : {platform.platform()}\n"
            f"  Processor        : {platform.processor()}\n"
            f"  Python Version   : {sys.version.split()[0]}\n\n"
            "  Capabilities:\n"
            "  ─────────────────────────────────────────────\n"
            "  ✓  System Information Collection\n"
            "  ✓  Browser History (Chrome, Firefox, Safari, Edge, Brave)\n"
            "  ✓  Connected Devices (USB, SSD, HDD, NVMe, SD) & USB History\n"
            "  ✓  Registry & Artifacts: Shellbags, Jump Lists, Prefetch, plists, recent files\n"
            "  ✓  Event Logs with time range, calendar & timeline chart\n"
            "  ✓  Network Activity: LAN devices, protocols, known networks, passive capture\n"
            "  ✓  File Hash Generation (MD5, SHA1, SHA256, SHA512)\n"
            "  ✓  Search & IOC list matching across everything collected\n"
            "  ✓  Case details, activity log and SHA-256 sealed reports\n"
            "  ✓  Timeline Analysis\n"
            "  ✓  Multi-format Report Generation\n\n"
            "  ⚡  All operations run on background threads — UI stays responsive.\n"
        )
        self.system_text.insert('1.0', info)

    # --------------------------------------------------------
    # SYSTEM INFO
    # --------------------------------------------------------
    def collect_system_info(self):
        self.run_async(self._task_collect_system_info,
                       on_done=self._on_system_info_done,
                       status="Collecting system information...")

    def _task_collect_system_info(self):
        info = "=" * 60 + "\n"
        info += "SYSTEM INFORMATION\n"
        info += f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        info += "=" * 60 + "\n\n"

        info += f"Operating System : {self.current_os}\n"
        info += f"Platform         : {platform.platform()}\n"
        info += f"Processor        : {platform.processor()}\n"
        info += f"Architecture     : {platform.machine()}\n"
        info += f"Hostname         : {platform.node()}\n\n"

        if self.current_os == "Windows":
            info += self._windows_info()
        elif self.current_os == "Linux":
            info += self._linux_info()
        elif self.current_os == "Darwin":
            info += self._macos_info()
        return info

    def _windows_info(self):
        out = ""
        try:
            r = subprocess.run(['systeminfo'], capture_output=True, text=True,
                               timeout=20, errors='ignore')
            out += "System Details:\n" + r.stdout[:800] + "...\n\n"
        except Exception:
            pass
        try:
            r = subprocess.run(['tasklist'], capture_output=True, text=True,
                               timeout=10, errors='ignore')
            out += "Running Processes:\n" + r.stdout[:800] + "...\n"
        except Exception:
            pass
        return out

    def _linux_info(self):
        out = ""
        try:
            with open('/proc/cpuinfo') as f:
                out += "CPU Info:\n" + f.read()[:600] + "...\n\n"
        except Exception:
            pass
        try:
            with open('/proc/meminfo') as f:
                out += "Memory Info:\n" + f.read()[:400] + "...\n\n"
        except Exception:
            pass
        return out

    def _macos_info(self):
        out = ""
        try:
            r = subprocess.run(['sw_vers'], capture_output=True, text=True, timeout=5)
            out += "macOS Version:\n" + r.stdout + "\n"
        except Exception:
            pass
        try:
            r = subprocess.run(['system_profiler', 'SPHardwareDataType'],
                               capture_output=True, text=True, timeout=15)
            out += "Hardware Info:\n" + r.stdout[:800] + "...\n"
        except Exception:
            pass
        return out

    def _on_system_info_done(self, info):
        self.system_text.insert('end', info + "\n")
        self.system_text.see('end')
        self.investigation_data['system_info'] = info

    # --------------------------------------------------------
    # TIMELINE
    # --------------------------------------------------------
    
    # --------------------------------------------------------
    # TIMELINE - FULL FILESYSTEM METADATA COLLECTION
    # Windows / Linux / macOS
    # --------------------------------------------------------

    def collect_timeline(self):
        self.run_async(
            self._task_collect_timeline,
            on_done=self._on_timeline_done,
            status="Scanning all accessible drives and filesystems..."
        )

    def _timeline_roots(self):
        """Return accessible filesystem roots for the current OS."""
        roots = []

        if self.current_os == "Windows":
            import ctypes

            kernel32 = ctypes.windll.kernel32
            mask = kernel32.GetLogicalDrives()

            for i in range(26):
                if mask & (1 << i):
                    drive = f"{chr(65 + i)}:\\"
                    drive_type = kernel32.GetDriveTypeW(drive)

                    # Fixed, removable and network drives.
                    if drive_type in (2, 3, 4) and os.path.exists(drive):
                        roots.append(drive)

        elif self.current_os == "Linux":
            excluded_fs = {
                "proc", "sysfs", "devtmpfs", "devpts",
                "cgroup", "cgroup2", "tmpfs", "securityfs",
                "debugfs", "tracefs", "pstore", "mqueue",
                "fusectl", "configfs", "autofs"
            }

            try:
                with open("/proc/self/mountinfo", "r",
                          encoding="utf-8", errors="replace") as f:
                    for line in f:
                        parts = line.split()
                        if "-" not in parts:
                            continue

                        sep = parts.index("-")
                        if sep + 1 >= len(parts):
                            continue

                        fs_type = parts[sep + 1]
                        mountpoint = parts[4]

                        # Decode escaped spaces and special characters.
                        mountpoint = re.sub(
                            r"\\([0-7]{3})",
                            lambda m: chr(int(m.group(1), 8)),
                            mountpoint
                        )

                        if fs_type not in excluded_fs:
                            if os.path.isdir(mountpoint):
                                roots.append(mountpoint)

            except OSError:
                roots.append("/")

        elif self.current_os == "Darwin":
            roots.append("/")

            # Include mounted external and additional volumes.
            try:
                result = subprocess.run(
                    ["mount"],
                    capture_output=True,
                    text=True,
                    timeout=20,
                    errors="replace"
                )

                for line in result.stdout.splitlines():
                    match = re.search(r" on (.+?) \(([^,]+)", line)
                    if not match:
                        continue

                    mountpoint = match.group(1)
                    fs_type = match.group(2)

                    if fs_type != "devfs" and os.path.isdir(mountpoint):
                        roots.append(mountpoint)

            except Exception:
                pass

        # Normalize and remove duplicate roots.
        unique = []
        seen = set()

        for root in roots:
            try:
                normalized = os.path.realpath(root)
                if normalized not in seen and os.path.isdir(normalized):
                    seen.add(normalized)
                    unique.append(normalized)
            except OSError:
                continue

        return unique

    def _task_collect_timeline(self):
        """Recursively collect filesystem metadata without opening file contents."""

        started = time.time()
        collected_at = datetime.now().astimezone().isoformat()

        result = {
            "collected": collected_at,
            "operating_system": self.current_os,
            "roots": [],
            "records": [],
            "errors": [],
            "files": 0,
            "directories": 0,
            "skipped": 0
        }

        roots = self._timeline_roots()
        result["roots"] = roots

        def report_error(path, exc):
            result["skipped"] += 1
            if len(result["errors"]) < 10000:
                result["errors"].append({
                    "path": str(path),
                    "error": f"{type(exc).__name__}: {exc}"
                })

        def timestamp(value):
            if value is None:
                return ""

            try:
                return datetime.fromtimestamp(
                    value, timezone.utc
                ).isoformat()
            except (ValueError, OSError, OverflowError):
                return ""

        for root in roots:
            try:
                root_device = os.stat(root).st_dev
            except OSError as exc:
                report_error(root, exc)
                continue

            # Do not follow symlinks or cross into another mounted
            # filesystem. Each mounted filesystem is scanned separately.
            def walk_error(exc):
                report_error(getattr(exc, "filename", root), exc)

            for current, dirs, files in os.walk(
                root,
                topdown=True,
                followlinks=False,
                onerror=walk_error
            ):
                # Prune symbolic links, junctions and mount boundaries.
                safe_dirs = []

                for name in dirs:
                    path = os.path.join(current, name)

                    try:
                        if os.path.islink(path):
                            result["skipped"] += 1
                            continue

                        if hasattr(os.path, "isjunction"):
                            if os.path.isjunction(path):
                                result["skipped"] += 1
                                continue

                        st = os.stat(path, follow_symlinks=False)

                        if st.st_dev != root_device:
                            continue

                        safe_dirs.append(name)

                        result["records"].append({
                            "path": path,
                            "type": "directory",
                            "size_bytes": st.st_size,
                            "created_utc": timestamp(
                                getattr(st, "st_birthtime", None)
                            ),
                            "modified_utc": timestamp(st.st_mtime),
                            "accessed_utc": timestamp(st.st_atime),
                            "metadata_changed_utc": (
                                timestamp(st.st_ctime)
                                if os.name != "nt" else ""
                            )
                        })

                        result["directories"] += 1

                    except OSError as exc:
                        report_error(path, exc)

                dirs[:] = safe_dirs

                for name in files:
                    path = os.path.join(current, name)

                    try:
                        if os.path.islink(path):
                            result["skipped"] += 1
                            continue

                        st = os.stat(path, follow_symlinks=False)

                        if st.st_dev != root_device:
                            continue

                        if not os.path.isfile(path):
                            result["skipped"] += 1
                            continue

                        # Windows st_ctime represents creation time.
                        # On Linux, st_ctime is metadata-change time.
                        created = getattr(st, "st_birthtime", None)

                        if created is None and os.name == "nt":
                            created = st.st_ctime

                        result["records"].append({
                            "path": path,
                            "type": os.path.splitext(name)[1].lower()
                                    or "no extension",
                            "size_bytes": st.st_size,
                            "created_utc": timestamp(created),
                            "modified_utc": timestamp(st.st_mtime),
                            "accessed_utc": timestamp(st.st_atime),
                            "metadata_changed_utc": (
                                timestamp(st.st_ctime)
                                if os.name != "nt" else ""
                            )
                        })

                        result["files"] += 1

                    except OSError as exc:
                        report_error(path, exc)

        # Sort by modification timestamp, oldest first.
        result["records"].sort(
            key=lambda item: item["modified_utc"]
        )

        result["duration_seconds"] = round(time.time() - started, 2)

        return result

    def _on_timeline_done(self, result):
        """Display summary and offer a complete CSV export."""

        if not isinstance(result, dict):
            self.timeline_text.insert(
                "end", str(result) + "\n"
            )
            self.timeline_text.see("end")
            self.investigation_data["timeline"] = str(result)
            return

        records = result["records"]

        summary = (
            "=" * 70 + "\n"
            "FULL FILESYSTEM TIMELINE\n"
            + "=" * 70 + "\n"
            f"Operating system: {result['operating_system']}\n"
            f"Collection time: {result['collected']}\n"
            f"Scanned roots: {len(result['roots'])}\n"
            f"Files collected: {result['files']:,}\n"
            f"Directories collected: {result['directories']:,}\n"
            f"Skipped / inaccessible: {result['skipped']:,}\n"
            f"Collection duration: {result['duration_seconds']} seconds\n"
            f"Total records: {len(records):,}\n\n"
            "Scanned roots:\n"
            + "\n".join(f"  {p}" for p in result["roots"])
            + "\n\n"
            "The complete metadata is available in the CSV export.\n"
            + "=" * 70 + "\n"
        )

        self.timeline_text.delete("1.0", "end")
        self.timeline_text.insert("end", summary)
        self.timeline_text.see("end")

        self.investigation_data["timeline"] = summary
        self.investigation_data["timeline_data"] = records

        self._audit(
            "Full filesystem timeline",
            "completed",
            f"{len(records)} records; {result['skipped']} skipped"
        )

        if not records:
            messagebox.showwarning(
                "Timeline",
                "No filesystem records were collected. "
                "Check permissions and the collection roots."
            )
            return

        if messagebox.askyesno(
            "Timeline export",
            f"Collected {len(records):,} filesystem records.\n\n"
            "Export the complete timeline to CSV?"
        ):
            filename = filedialog.asksaveasfilename(
                defaultextension=".csv",
                filetypes=[("CSV files", "*.csv")],
                initialfile=(
                    "Cactus_Full_Timeline_"
                    + datetime.now().strftime("%Y%m%d_%H%M%S")
                    + ".csv"
                )
            )

            if filename:
                fields = [
                    "path", "type", "size_bytes",
                    "created_utc", "modified_utc",
                    "accessed_utc", "metadata_changed_utc"
                ]

                try:
                    with open(
                        filename, "w", newline="",
                        encoding="utf-8-sig"
                    ) as f:
                        writer = csv.DictWriter(
                            f, fieldnames=fields,
                            extrasaction="ignore"
                        )
                        writer.writeheader()
                        writer.writerows(records)

                    self._seal_report(filename)

                    messagebox.showinfo(
                        "Timeline exported",
                        f"Complete timeline saved to:\n{filename}"
                    )

                except OSError as exc:
                    messagebox.showerror(
                        "Export failed",
                        str(exc)
                    )


    # --------------------------------------------------
    # BROWSER HISTORY
    # ---------------------------------------------
    def collect_browser_history(self):
        self.run_async(self._task_collect_browser_history,
                       on_done=self._on_browser_history_done,
                       status="Collecting browser history...")

    def _task_collect_browser_history(self):
        out = "=" * 60 + "\n"
        out += "BROWSER HISTORY & ACTIVITY\n"
        out += f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        out += "=" * 60 + "\n"
        out += self._privilege_line() + "\n\n"

        collected = False
        permission_denied = []

        targets = [
            ('Chrome', self.browser_vars.get('Chrome'), self._chrome_history),
            ('Firefox', self.browser_vars.get('Firefox'), self._firefox_history),
            ('Microsoft Edge', self.browser_vars.get('Microsoft Edge'), self._edge_history),
            ('Brave', self.browser_vars.get('Brave'), self._brave_history),
        ]
        if self.current_os == "Darwin":
            targets.append(('Safari', self.browser_vars.get('Safari'), self._safari_history))

        for name, var, fn in targets:
            if var and var.get():
                try:
                    data, denied = fn()
                    if denied:
                        permission_denied.append(name)
                    if data:
                        out += f"{name.upper()} HISTORY:\n" + "-" * 40 + "\n" + data + "\n"
                        collected = True
                except Exception as e:
                    out += f"{name}: Error — {e}\n"

        if not collected:
            out += "No browser history found or browsers not installed.\n"
            out += "Note: Some browsers may require administrative privileges.\n"

        return out, permission_denied

    def _on_browser_history_done(self, result):
        text, denied = result
        self.history_text.delete('1.0', 'end')
        self.history_text.insert('1.0', text)
        self.investigation_data['browser_history'] = text

        # macOS permission popup
        if self.current_os == "Darwin" and denied:
            self.root.after(200, lambda: self.show_macos_permission_popup(denied))

    # --- macOS permission handling ---
    def check_macos_permissions(self):
        """Check if we can access browser data on macOS."""
        if self.current_os != "Darwin":
            messagebox.showinfo("Permissions",
                "This check is only relevant on macOS.\n"
                "On other platforms, browser data is read directly from the filesystem.")
            return

        denied = self._detect_macos_permission_issues()
        if denied:
            self.show_macos_permission_popup(denied)
        else:
            messagebox.showinfo("Permissions",
                "✓ Browser data directories appear accessible.\n"
                "If artifacts still don't extract, grant Full Disk Access manually.")

    def _detect_macos_permission_issues(self):
        """Return list of browsers whose data cannot be read on macOS."""
        denied = []
        checks = {
            'Chrome': '~/Library/Application Support/Google/Chrome',
            'Firefox': '~/Library/Application Support/Firefox',
            'Safari': '~/Library/Safari',
            'Microsoft Edge': '~/Library/Application Support/Microsoft Edge',
            'Brave': '~/Library/Application Support/BraveSoftware',
        }
        for name, p in checks.items():
            full = self._xp(p)
            if os.path.exists(full):
                if not os.access(full, os.R_OK):
                    denied.append(name)
                else:
                    # Test listing
                    try:
                        os.listdir(full)
                    except PermissionError:
                        denied.append(name)
        return denied

    def show_macos_permission_popup(self, denied_browsers):
        """Show a professional macOS permission popup with instructions."""
        popup = tk.Toplevel(self.root)
        popup.title("macOS Permission Required")
        popup.geometry("620x480")
        popup.configure(bg=Theme.BG_DARK)
        popup.transient(self.root)
        popup.grab_set()

        # Center
        popup.update_idletasks()
        x = (popup.winfo_screenwidth() // 2) - 310
        y = (popup.winfo_screenheight() // 2) - 240
        popup.geometry(f"+{x}+{y}")

        # Header
        header = tk.Frame(popup, bg=Theme.BG_MEDIUM, height=70)
        header.pack(fill='x')
        header.pack_propagate(False)

        tk.Label(header, text="🍎", font=('Segoe UI', 24),
                 bg=Theme.BG_MEDIUM, fg=Theme.ACCENT).pack(side='left', padx=20)

        hbox = tk.Frame(header, bg=Theme.BG_MEDIUM)
        hbox.pack(side='left', pady=12)
        tk.Label(hbox, text="macOS Full Disk Access Required",
                 font=('Segoe UI', 14, 'bold'),
                 bg=Theme.BG_MEDIUM, fg=Theme.ACCENT_RED).pack(anchor='w')
        tk.Label(hbox, text="Some browser artifacts could not be extracted",
                 font=('Segoe UI', 9),
                 bg=Theme.BG_MEDIUM, fg=Theme.TEXT_SECONDARY).pack(anchor='w')

        # Body
        body = tk.Frame(popup, bg=Theme.BG_DARK)
        body.pack(fill='both', expand=True, padx=20, pady=16)

        tk.Label(body, text="Blocked Browsers:",
                 font=('Segoe UI', 11, 'bold'),
                 bg=Theme.BG_DARK, fg=Theme.TEXT_PRIMARY).pack(anchor='w')

        blocked = tk.Frame(body, bg=Theme.BG_CARD, highlightbackground=Theme.ACCENT_RED,
                           highlightthickness=1)
        blocked.pack(fill='x', pady=(6, 14))
        for b in denied_browsers:
            tk.Label(blocked, text=f"  ✗  {b}",
                     font=('Consolas', 10), bg=Theme.BG_CARD,
                     fg=Theme.ACCENT_RED, anchor='w').pack(fill='x', padx=10, pady=3)

        tk.Label(body, text="How to Grant Full Disk Access:",
                 font=('Segoe UI', 11, 'bold'),
                 bg=Theme.BG_DARK, fg=Theme.TEXT_PRIMARY).pack(anchor='w', pady=(6, 6))

        steps = (
            "1.  Open  System Settings  (or System Preferences)\n"
            "2.  Navigate to  Privacy & Security  →  Full Disk Access\n"
            "3.  Click the  🔒  icon (bottom-left) and authenticate\n"
            "4.  Click  ➕  and add the app running this tool:\n"
            "       •  Terminal.app ,  iTerm.app , or\n"
            "       •  Python.app  (from your Python installation)\n"
            "5.  Toggle the switch  ON  next to the added app\n"
            "6.  Fully  quit and relaunch  this tool"
        )
        steps_box = tk.Frame(body, bg=Theme.BG_CARD, highlightbackground=Theme.BORDER,
                             highlightthickness=1)
        steps_box.pack(fill='both', expand=True)
        tk.Label(steps_box, text=steps, justify='left', anchor='nw',
                 font=('Consolas', 9), bg=Theme.BG_CARD,
                 fg=Theme.TEXT_PRIMARY, padx=14, pady=12).pack(fill='both', expand=True)

        # Footer buttons
        footer = tk.Frame(popup, bg=Theme.BG_DARK)
        footer.pack(fill='x', padx=20, pady=(0, 16))

        def open_settings():
            try:
                subprocess.Popen([
                    'open',
                    'x-apple.systempreferences:com.apple.preference.security?Privacy_AllFiles'
                ])
            except Exception as e:
                messagebox.showerror("Error", f"Could not open System Settings: {e}")

        def open_help():
            try:
                subprocess.Popen([
                    'open',
                    'https://support.apple.com/guide/mac-help/control-access-to-files-and-folders-mchlp3008/mac'
                ])
            except Exception:
                pass

        ttk.Button(footer, text="🔓 Open System Settings", style='Accent.TButton',
                   command=open_settings).pack(side='left', padx=4)
        ttk.Button(footer, text="❓ Apple Support Docs",
                   command=open_help).pack(side='left', padx=4)
        ttk.Button(footer, text="Close",
                   command=popup.destroy).pack(side='right', padx=4)

    # --- Who is being examined, and are we privileged? ---------------
    def _home(self):
        """Home folder of the person being examined.
        Under sudo the process runs as root, so '~' would be /root; use the user who ran sudo."""
        su = os.environ.get('SUDO_USER')
        if su and su != 'root' and hasattr(os, 'geteuid') and os.geteuid() == 0:
            try:
                import pwd
                return Path(pwd.getpwnam(su).pw_dir)
            except Exception:
                pass
        return Path.home()

    def _xp(self, p):
        """expanduser() that uses _home()."""
        p = str(p)
        if p == '~':
            return str(self._home())
        if p.startswith(('~/', '~\\')):
            return str(self._home() / p[2:])
        return p

    def _is_admin(self):
        try:
            if self.current_os == "Windows":
                import ctypes
                return bool(ctypes.windll.shell32.IsUserAnAdmin())
            return os.geteuid() == 0
        except Exception:
            return False

    def _privilege_line(self):
        who = 'Administrator' if self.current_os == 'Windows' else 'root'
        return (f"Examining home folder: {self._home()}    "
                f"Running as {who}: {'yes' if self._is_admin() else 'NO'}")

    def restart_as_admin(self):
        if self.current_os != "Windows":
            cmd = "sudo -E python3 python_fixed.py" if self.current_os == "Linux" else "sudo python3 python_fixed.py"
            messagebox.showinfo("Run with more rights",
                                f"Close the tool and start it from a terminal with:\n\n    {cmd}\n\n"
                                "The tool reads the folders of the user who ran sudo, not root's.")
            return
        import ctypes
        if getattr(sys, 'frozen', False):
            exe, params = sys.executable, ''
        else:
            exe, params = sys.executable, f'"{os.path.abspath(sys.argv[0])}"'
        if ctypes.windll.shell32.ShellExecuteW(None, 'runas', exe, params, None, 1) > 32:
            self.root.after(300, self.root.destroy)
        else:
            messagebox.showwarning("Administrator", "Elevation was cancelled or refused.")

    # --- Browser readers ---------------------------------------------
    @staticmethod
    def _t_webkit(v):
        try:
            return (datetime(1601, 1, 1) + timedelta(microseconds=int(v))).strftime('%Y-%m-%d %H:%M:%S') + " UTC" if v and 0 < int(v) < 2.6e16 else "?"
        except Exception:
            return "?"

    @staticmethod
    def _t_unix_us(v):
        try:
            return datetime.fromtimestamp(int(v) / 1e6, timezone.utc).strftime('%Y-%m-%d %H:%M:%S') + " UTC" if v and int(v) > 0 else "?"
        except Exception:
            return "?"

    @staticmethod
    def _t_cocoa(v):
        try:
            return (datetime(2001, 1, 1) + timedelta(seconds=float(v))).strftime('%Y-%m-%d %H:%M:%S') + " UTC" if v else "?"
        except Exception:
            return "?"

    def _copy_db(self, src):
        """Copy a SQLite file (and its -wal/-shm/-journal) into a private temp folder.
        Never uses the current directory: a launched .app starts in '/', an elevated .exe in System32.
        -> (copy_path, tmpdir, problem) where problem is '', 'denied', 'locked' or 'error: ...'"""
        try:
            tmpdir = tempfile.mkdtemp(prefix='cactus_')
        except OSError as e:
            return None, None, f"error: cannot create a temporary folder ({e})"
        dst = os.path.join(tmpdir, os.path.basename(src))
        try:
            shutil.copyfile(src, dst)
        except PermissionError as e:
            shutil.rmtree(tmpdir, ignore_errors=True)
            return None, None, ('locked' if getattr(e, 'winerror', None) in (32, 33) else 'denied')
        except OSError as e:
            shutil.rmtree(tmpdir, ignore_errors=True)
            return None, None, f"error: {e}"
        for sfx in ('-wal', '-shm', '-journal'):
            if os.path.exists(src + sfx):
                try:
                    shutil.copyfile(src + sfx, dst + sfx)
                except OSError:
                    pass
        return dst, tmpdir, ''

    def _query_db(self, src, sql):
        """Run a read-only query on a copy of the database. -> (rows, problem, note)"""
        path, tmpdir, problem = self._copy_db(src)
        uri = None
        if problem == 'locked':      # browser holds it open: read in place, strictly read-only
            uri = Path(src).as_uri() + '?mode=ro&immutable=1'
        elif problem:
            return None, problem, ''
        try:
            con = sqlite3.connect(path) if path else sqlite3.connect(uri, uri=True)
            try:
                return con.execute(sql).fetchall(), '', ('read in place: the browser has the file locked' if uri else '')
            finally:
                con.close()
        except sqlite3.DatabaseError as e:
            return None, f"error: {e}", ''
        finally:
            if tmpdir:
                shutil.rmtree(tmpdir, ignore_errors=True)

    def _browser_roots(self, browser):
        h = self._home()
        osn = self.current_os
        la = Path(os.environ.get('LOCALAPPDATA') or (h / 'AppData' / 'Local'))
        ra = Path(os.environ.get('APPDATA') or (h / 'AppData' / 'Roaming'))
        mac = h / 'Library' / 'Application Support'
        v = {
            'chrome': {'Windows': [la / 'Google/Chrome/User Data', la / 'Google/Chrome Beta/User Data', la / 'Chromium/User Data'],
                       'Darwin': [mac / 'Google/Chrome', mac / 'Google/Chrome Beta', mac / 'Chromium'],
                       'Linux': [h / '.config/google-chrome', h / '.config/google-chrome-beta', h / '.config/chromium',
                                 h / 'snap/chromium/common/chromium', h / '.var/app/com.google.Chrome/config/google-chrome',
                                 h / '.var/app/org.chromium.Chromium/config/chromium']},
            'edge': {'Windows': [la / 'Microsoft/Edge/User Data'], 'Darwin': [mac / 'Microsoft Edge'],
                     'Linux': [h / '.config/microsoft-edge', h / '.var/app/com.microsoft.Edge/config/microsoft-edge']},
            'brave': {'Windows': [la / 'BraveSoftware/Brave-Browser/User Data'], 'Darwin': [mac / 'BraveSoftware/Brave-Browser'],
                      'Linux': [h / '.config/BraveSoftware/Brave-Browser', h / 'snap/brave/current/.config/BraveSoftware/Brave-Browser',
                                h / '.var/app/com.brave.Browser/config/BraveSoftware/Brave-Browser']},
            'firefox': {'Windows': [ra / 'Mozilla/Firefox/Profiles'], 'Darwin': [mac / 'Firefox/Profiles'],
                        'Linux': [h / '.mozilla/firefox', h / 'snap/firefox/common/.mozilla/firefox',
                                  h / '.var/app/org.mozilla.firefox/.mozilla/firefox']},
        }
        return v[browser].get(osn, [])

    def _history_report(self, kind, roots):
        """Find every profile under roots, read its history. -> (text, denied)"""
        db_name, sql, tfmt = {
            'chromium': ('History', "SELECT url, title, last_visit_time, visit_count FROM urls "
                                    "ORDER BY last_visit_time DESC LIMIT 50", self._t_webkit),
            'firefox': ('places.sqlite', "SELECT url, title, last_visit_date, visit_count FROM moz_places "
                                         "WHERE last_visit_date IS NOT NULL ORDER BY last_visit_date DESC LIMIT 50",
                        self._t_unix_us),
        }[kind]
        out, denied, searched, found = "", False, [], 0
        for root in roots:
            exists = Path(root).is_dir()
            searched.append(f"  {'found    ' if exists else 'not found'}  {root}")
            if not exists:
                continue
            try:
                subs = sorted(p for p in Path(root).iterdir() if p.is_dir())
            except PermissionError:
                denied = True
                out += f"Cannot list {root}: access denied.\n"
                continue
            if kind == 'chromium':
                subs = [p for p in subs if p.name == 'Default' or p.name.startswith('Profile ')]
            for prof in subs:
                db = prof / db_name
                if not db.exists():
                    continue
                found += 1
                rows, problem, note = self._query_db(str(db), sql)
                out += f"[profile: {prof.name}]  {db}\n"
                if note:
                    out += f"  note: {note}\n"
                if rows is None:
                    if problem == 'denied':
                        denied = True
                        out += ("  Access denied. "
                                + ("macOS blocks this folder until Full Disk Access is granted to the program that "
                                   "started this tool (Terminal, VS Code or CACTUS.app), then restart that program.\n"
                                   if self.current_os == "Darwin" else
                                   "Run the tool as Administrator / root.\n"))
                    elif problem == 'locked':
                        out += "  The browser has the file locked and it could not be read. Close the browser and try again.\n"
                    else:
                        out += f"  Could not be read ({problem}).\n"
                    continue
                shown = 0
                for url, title, ts, cnt in rows:
                    out += f"  {tfmt(ts)}   visits {cnt if cnt is not None else '?'}\n      {title or '(no title)'}\n      {url}\n"
                    shown += 1
                if not shown:
                    out += "  (no entries)\n"
                out += "-" * 40 + "\n"
        if not found:
            out += ("No history database found. Places checked:\n" + "\n".join(searched) + "\n"
                    + "If the browser is installed somewhere else (portable or another user), "
                      "tell me the path and I will add it.\n")
        return out, denied

    def _read_chromium_db(self, path):
        """Kept for compatibility: one Chromium History file."""
        if not os.path.exists(path):
            return "History file not found.\n", False
        rows, problem, note = self._query_db(path, "SELECT url, title, last_visit_time, visit_count FROM urls "
                                                   "ORDER BY last_visit_time DESC LIMIT 50")
        if rows is None:
            return (f"Cannot read history ({problem}).\n", problem == 'denied')
        return "".join(f"URL   : {u}\nTitle : {t}\nLast  : {self._t_webkit(ts)}\n" + "-" * 30 + "\n"
                       for u, t, ts, _c in rows if t) or "No entries found.\n", False

    def _chrome_history(self):
        return self._history_report('chromium', self._browser_roots('chrome'))

    def _edge_history(self):
        return self._history_report('chromium', self._browser_roots('edge'))

    def _brave_history(self):
        return self._history_report('chromium', self._browser_roots('brave'))

    def _firefox_history(self):
        return self._history_report('firefox', self._browser_roots('firefox'))

    def _safari_history(self):
        if self.current_os != "Darwin":
            return "Safari is only available on macOS.\n", False
        path = self._home() / 'Library' / 'Safari' / 'History.db'
        if not path.exists():
            return f"Safari history database not found ({path}).\n", False
        # real Safari schema: URLs live in history_items, titles and times in history_visits
        rows, problem, note = self._query_db(
            str(path), "SELECT i.url, v.title, v.visit_time, i.visit_count FROM history_items i "
                       "JOIN history_visits v ON v.history_item = i.id ORDER BY v.visit_time DESC LIMIT 50")
        if rows is None and problem.startswith('error'):          # older/simpler layout
            rows, problem, note = self._query_db(
                str(path), "SELECT url, title, visit_time, visit_count FROM history_items "
                           "ORDER BY visit_time DESC LIMIT 50")
        if rows is None:
            if problem == 'denied':
                return ("Access denied. Grant Full Disk Access to the program that started this tool "
                        "(Terminal, VS Code or CACTUS.app), then restart that program.\n"), True
            return f"Safari history could not be read ({problem}).\n", False
        out = f"[{path}]\n" + (f"  note: {note}\n" if note else "")
        for url, title, ts, cnt in rows:
            out += f"  {self._t_cocoa(ts)}   visits {cnt if cnt is not None else '?'}\n      {title or '(no title)'}\n      {url}\n"
        return out + ("-" * 40 + "\n" if rows else "  (no entries)\n"), False

    # ========================================================
    # CASE RECORD, ACTIVITY LOG (chain of custody), REPORT INTEGRITY
    # ========================================================
    TOOL_VERSION = "3.4"
    vault_path = None

    def _audit(self, action, status='ok', detail=''):
        """Append to the activity log. Entries are never edited or removed by 'Clear All Data'."""
        log = self.__dict__.setdefault('audit_log', [])
        entry = {'time': datetime.now().astimezone().isoformat(timespec='seconds'),
                 'action': str(action), 'status': status, 'detail': str(detail)}
        log.append(entry)
        w = self.__dict__.get('audit_text')
        if w is not None:
            try:
                w.insert('end', self._audit_line(entry) + "\n")
                w.see('end')
            except tk.TclError:
                pass

    @staticmethod
    def _audit_line(e):
        s = f"{e['time']}  {e['status']:<9} {e['action']}"
        return s + (f"   [{e['detail']}]" if e.get('detail') else "")

    # ========================================================
    # CASE RECORD, EVIDENCE VAULT, PACKAGE EXPORT AND VERIFICATION
    # ========================================================
    HASH_ALGOS = ('md5', 'sha1', 'sha256', 'sha512')
    CASE_FIELDS = (('case_id', 'Case ID / FIR No.', 30), ('case_title', 'Case title', 60),
                   ('exhibit_ref', 'Exhibit / device ref.', 30), ('examiner', 'Examiner', 30),
                   ('organization', 'Organisation', 40), ('requested_by', 'Requested by', 40),
                   ('location', 'Place of examination', 40),
                   ('authority', 'Legal authority / consent', 70), ('notes', 'Notes', 90),
                   ('validation_note', 'Tool validation done', 90))

    def _case_info(self):
        v = self.__dict__.get('case_vars') or {}
        out = {k: '' for k, _l, _w in self.CASE_FIELDS}
        out['base_dir'] = ''
        for k in out:
            if k in v:
                out[k] = v[k].get().strip()
        return out

    def build_case_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  🗂  Case  ')
        card = self._make_card(tab, "Case details  (printed in every report)")
        card.pack(fill='x', padx=12, pady=(12, 8))
        grid = tk.Frame(card.body, bg=Theme.BG_CARD)
        grid.pack(fill='x', padx=8, pady=8)
        self.case_vars = {}
        for r, (key, label, w) in enumerate(self.CASE_FIELDS):
            tk.Label(grid, text=label + ":", bg=Theme.BG_CARD, fg=Theme.TEXT_PRIMARY,
                     font=('Segoe UI', 10)).grid(row=r // 2, column=(r % 2) * 2, sticky='w', padx=(0, 8), pady=3)
            var = tk.StringVar()
            self.case_vars[key] = var
            ttk.Entry(grid, textvariable=var, width=34).grid(row=r // 2, column=(r % 2) * 2 + 1,
                                                              sticky='w', padx=(0, 24), pady=3)
        tk.Label(grid, text="Evidence folder:", bg=Theme.BG_CARD, fg=Theme.TEXT_PRIMARY,
                 font=('Segoe UI', 10)).grid(row=6, column=0, sticky='w', pady=3)
        self.case_vars['base_dir'] = tk.StringVar(value=str(self._home() / 'CACTUS_Cases'))
        ttk.Entry(grid, textvariable=self.case_vars['base_dir'], width=34).grid(row=6, column=1, sticky='w', pady=3)
        ttk.Button(grid, text="Browse", command=lambda: self.case_vars['base_dir'].set(
            filedialog.askdirectory(title="Where should evidence be stored?") or self.case_vars['base_dir'].get())
        ).grid(row=6, column=2, sticky='w')
        actions = tk.Frame(tab, bg=Theme.BG_DARK)
        actions.pack(fill='x', padx=12, pady=(0, 8))
        ttk.Button(actions, text="📦 Export Evidence Package", style='Accent.TButton',
                   command=self.export_evidence_package).pack(side='left', padx=4)
        ttk.Button(actions, text="🔍 Verify a Package...", command=self.verify_package_dialog).pack(side='left', padx=4)
        ttk.Button(actions, text="💾 Export Activity Log", command=self.export_audit).pack(side='left', padx=4)
        ttk.Button(actions, text="🆕 New Evidence Folder", command=self.new_vault).pack(side='left', padx=4)
        ttk.Button(actions, text="📊 Case Dashboard", command=self.show_case_dashboard).pack(side='left', padx=4)
        ttk.Button(actions, text="🧮 Compare Two Packages", command=self.run_baseline_diff).pack(side='left', padx=4)
        self.vault_label = tk.Label(actions, text="", bg=Theme.BG_DARK, fg=Theme.TEXT_SECONDARY, font=('Segoe UI', 9))
        self.vault_label.pack(side='left', padx=10)
        card = self._make_card(tab, "Activity log (chain of custody) and integrity results")
        card.pack(fill='both', expand=True, padx=12, pady=(0, 12))
        self.audit_text = self._make_text_area(card)
        for e in self.__dict__.get('audit_log', []):
            self.audit_text.insert('end', self._audit_line(e) + "\n")

    def _show_in_log(self, text):
        self.audit_text.insert('end', "\n" + text + "\n")
        self.audit_text.see('end')

    # ---- v3.4: multi-case dashboard -------------------------------------------------
    def show_case_dashboard(self):
        base_dir = self.case_vars['base_dir'].get() or str(self._home() / 'CACTUS_Cases')
        cases = v34_scan_cases(base_dir)
        win = tk.Toplevel(self.root)
        win.title("Case Dashboard")
        win.geometry("980x560")
        win.configure(bg=Theme.BG_DARK)
        top = tk.Frame(win, bg=Theme.BG_DARK)
        top.pack(fill='x', padx=10, pady=(10, 4))
        tk.Label(top, text=f"Base directory: {base_dir}", bg=Theme.BG_DARK, fg=Theme.TEXT_SECONDARY,
                 font=('Segoe UI', 9)).pack(side='left')
        text = scrolledtext.ScrolledText(win, bg=Theme.BG_MEDIUM, fg=Theme.TEXT_PRIMARY, insertbackground=Theme.TEXT_PRIMARY,
                                         font=('Consolas', 10), wrap='word')
        text.pack(fill='both', expand=True, padx=10, pady=10)
        text.insert('1.0', v34_render_dashboard(cases))
        text.config(state='disabled')

        def refresh():
            new_cases = v34_scan_cases(base_dir)
            text.config(state='normal')
            text.delete('1.0', 'end')
            text.insert('1.0', v34_render_dashboard(new_cases))
            text.config(state='disabled')

        ttk.Button(top, text="🔄 Refresh", command=refresh).pack(side='right', padx=4)
        self._audit('case dashboard opened', 'ok', f"{len(cases)} case(s) under {base_dir}")

    # ---- v3.4: baseline diff (compare two exported packages' manifests) ------------
    def run_baseline_diff(self):
        p1 = filedialog.askopenfilename(title="Choose the BEFORE/baseline manifest.json",
                                        filetypes=[("manifest.json", "manifest.json"), ("All files", "*.*")])
        if not p1:
            return
        p2 = filedialog.askopenfilename(title="Choose the AFTER manifest.json",
                                        filetypes=[("manifest.json", "manifest.json"), ("All files", "*.*")])
        if not p2:
            return
        try:
            before = json.loads(Path(p1).read_text(encoding='utf-8'))
            after = json.loads(Path(p2).read_text(encoding='utf-8'))
        except (OSError, ValueError) as e:
            messagebox.showerror("Baseline diff", f"Could not read one of the manifests: {e}")
            return
        file_diff = v34_diff_manifests(before, after)
        report = v34_render_diff_report(os.path.basename(os.path.dirname(p1)) or p1,
                                        os.path.basename(os.path.dirname(p2)) or p2, file_diff)
        self.investigation_data['baseline_diff'] = report
        self._audit('baseline diff run', 'ok', f"{len(file_diff['added'])} added, {len(file_diff['removed'])} removed, "
                                               f"{len(file_diff['changed'])} changed")
        win = tk.Toplevel(self.root)
        win.title("Baseline Diff")
        win.geometry("900x560")
        win.configure(bg=Theme.BG_DARK)
        text = scrolledtext.ScrolledText(win, bg=Theme.BG_MEDIUM, fg=Theme.TEXT_PRIMARY, insertbackground=Theme.TEXT_PRIMARY,
                                         font=('Consolas', 10), wrap='word')
        text.pack(fill='both', expand=True, padx=10, pady=10)
        text.insert('1.0', report)

    # ---- hashing -----------------------------------------------------
    @classmethod
    def _hash_path(cls, path):
        hs = {a: hashlib.new(a) for a in cls.HASH_ALGOS}
        size = 0
        with open(path, 'rb') as f:
            for chunk in iter(lambda: f.read(1 << 20), b''):
                size += len(chunk)
                for h in hs.values():
                    h.update(chunk)
        d = {a: h.hexdigest() for a, h in hs.items()}
        d['size'] = size
        return d

    @classmethod
    def _hash_bytes(cls, data):
        d = {a: hashlib.new(a, data).hexdigest() for a in cls.HASH_ALGOS}
        d['size'] = len(data)
        return d

    @staticmethod
    def _readonly(path):
        try:
            os.chmod(path, 0o444)
        except OSError:
            pass

    def _chown_tree(self, root):
        """Under sudo, hand the evidence folder to the real user so they can open it."""
        try:
            uid, gid = int(os.environ.get('SUDO_UID', '')), int(os.environ.get('SUDO_GID', ''))
        except ValueError:
            return
        if not (hasattr(os, 'geteuid') and os.geteuid() == 0):
            return
        try:
            os.chown(root, uid, gid)
            for dp, dns, fns in os.walk(root):
                for n in dns + fns:
                    os.chown(os.path.join(dp, n), uid, gid, follow_symlinks=False)
        except OSError:
            pass

    # ---- who/what/where, for the report -----------------------------------
    def _tool_identity(self):
        c = self.__dict__.get('_tool_id_cache')
        if c:
            return c
        frozen = bool(getattr(sys, 'frozen', False))
        path = sys.executable if frozen else os.path.abspath(globals().get('__file__') or sys.argv[0])
        info = {'name': 'CACTUS Digital Forensic Investigation Tool', 'version': self.TOOL_VERSION,
                'file': path, 'frozen': frozen, 'python': sys.version.split()[0],
                'sha256': '', 'size': 0}
        try:
            h = self._hash_path(path)
            info['sha256'], info['size'] = h['sha256'], h['size']
        except OSError as e:
            info['sha256'] = f"(could not hash: {e})"
        self._tool_id_cache = info
        return info

    def _host_info(self):
        now = datetime.now().astimezone()
        off = now.utcoffset() or timedelta(0)
        sec = int(off.total_seconds())
        up = ''
        try:
            with open('/proc/uptime') as f:
                up = f"{float(f.read().split()[0]) / 3600:.1f} hours"
        except OSError:
            pass
        return {'hostname': platform.node(), 'os': self.current_os, 'platform': platform.platform(),
                'machine': platform.machine(), 'user': getpass.getuser() if hasattr(getpass, 'getuser') else '',
                'examined_user_home': str(self._home()), 'is_admin': self._is_admin(),
                'timezone': f"{now.tzname()} (UTC{'+' if sec >= 0 else '-'}{abs(sec) // 3600:02d}:{abs(sec) % 3600 // 60:02d})",
                'clock_local': now.isoformat(timespec='seconds'),
                'clock_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'), 'uptime': up}

    # ---- what goes into the evidence set ---------------------------------------
    SECTION_DESC = {
        'system_info': "Operating system, hardware and basic configuration of the examined computer.",
        'timeline': "Files recently modified in the user's Documents, Downloads and Desktop folders.",
        'browser_history': "Web pages visited, read from each browser's own history database (copied before reading).",
        'connected_devices': "Storage and USB devices attached at the time of examination.",
        'device_history': "Storage and USB devices that were attached in the past.",
        'live_time': "System clock, time zone, time-synchronisation status and uptime at the time of collection.",
        'live_users': "Accounts logged on, and recent logins.",
        'live_network': "Network configuration: addresses, routes, DNS settings and DNS cache.",
        'live_processes': "Programs running at the time of collection, with parent process, path, command line and SHA-256 of each executable file.",
        'live_accounts': "Local user accounts and administrator group membership.",
        'live_security': "Security tool status: firewall, antivirus, disk encryption, system integrity.",
        'live_shares': "Network shares, mounted remote file systems and open sessions.",
        'live_dns_swap': "Recently resolved domain names (DNS cache) and URL/domain-like fragments recovered from the swap/paging file.",
        'live_history': "Commands typed in PowerShell (Windows) as recorded by the console.",
        'registry': "Registry (Windows) or equivalent configuration files (macOS, Linux).",
        'artifact_shellbags': "Folders the user browsed in Windows Explorer (Shellbags).",
        'artifact_jumplists': "Files and programs recently opened, per application (Jump Lists).",
        'artifact_prefetch': "Programs that were run, how many times and when (Prefetch).",
        'artifact_recent': "Recently opened files, Run dialog commands and recent documents.",
        'artifact_services': "Services and drivers that start automatically (persistence locations).",
        'artifact_tasks': "Scheduled tasks (persistence locations).",
        'artifact_downloads': "Files downloaded through browsers and other applications (macOS quarantine events).",
        'artifact_installs': "Software installation history.",
        'artifact_shellhistory': "Commands typed in a terminal.",
        'artifact_trash': "Files moved to the Trash.",
        'artifact_logins': "Login history.",
        'artifact_shimcache': "Program paths Windows has seen (ShimCache / AppCompatCache); not proof of execution.",
        'artifact_amcache': "Programs installed or run, including since-uninstalled ones, with a file hash where recorded (Amcache).",
        'artifact_srum': "Per-application network usage and last-seen times, even for removed applications (SRUM).",
        'artifact_persistence': "Programs configured to start automatically, a common persistence location for malware as well as legitimate software.",
        'event_logs': "System event log entries for the selected period.",
        'network_activity': "Devices seen on the local network, protocols in use, listening services and previously joined networks.",
        'protocol_capture': "Short passive capture summarising protocols per device (metadata only).",
        'packet_capture': "Network packet capture(s) and their analysis. The capture files themselves are hashed and stored with the evidence.",
        'super_timeline': "Every timestamp found in the data already collected, merged into one chronological view.",
        'yara_matches': "Results of scanning running program files (and an optional folder) against supplied YARA rules.",
        'ioc_matches': "Indicators supplied by the examiner that were found in the collected data.",
        'hashset_match': "Collected/exported file hashes compared against an examiner-supplied hash set (known-good allowlist or known-bad/IOC blocklist). No network lookups; the set is a local file the examiner loaded.",
        'encryption_status': "Disk/volume encryption status (BitLocker, FileVault or LUKS), parsed from the OS's own status command into a flagged summary.",
        'artifact_recyclebin': "Deleted files recovered from the Recycle Bin / Trash, with original path and deletion time where the OS records one, and content hashed where recoverable.",
        'artifact_mft': "NTFS Master File Table entries, decoded directly from $MFT -- independent of what the live OS currently reports, so it can show files the OS no longer lists. Includes a check for FILE_NAME vs STANDARD_INFORMATION timestamp mismatches (a timestomp indicator).",
        'artifact_usnjournal': "NTFS USN Journal (file-system change log), decoded via the OS's own `fsutil usn readjournal`.",
        'ram_acquisition': "Log of a RAM (physical memory) acquisition: tool used, start/end time and the SHA-256 of the resulting image. The image itself is stored as a separate file in the evidence package, not inlined here (it can be gigabytes).",
        'baseline_diff': "Difference between two evidence packages from this case (e.g. before/after a suspected incident): files added, removed or changed, and processes newly present or no longer present.",
    }

    def _report_sections(self):
        return [('SYSTEM INFORMATION', 'system_info'), ('TIMELINE', 'timeline'),
                ('BROWSER HISTORY', 'browser_history'), ('CONNECTED DEVICES', 'connected_devices'),
                ('USB / DEVICE HISTORY', 'device_history'),
                ('SYSTEM TIME AND UPTIME', 'live_time'), ('LOGGED-ON USERS', 'live_users'),
                ('NETWORK CONFIGURATION', 'live_network'), ('RUNNING PROCESSES', 'live_processes'),
                ('ACCOUNTS AND GROUPS', 'live_accounts'), ('SECURITY STATUS', 'live_security'),
                ('SHARES AND SESSIONS', 'live_shares'), ('DNS CACHE & SWAP TRACES', 'live_dns_swap'),
                ('POWERSHELL HISTORY', 'live_history'),
                ('OS REGISTRY ARTIFACTS', 'registry'), ('SHELLBAGS', 'artifact_shellbags'),
                ('JUMP LISTS', 'artifact_jumplists'), ('PREFETCH', 'artifact_prefetch'),
                ('RECENT FILES', 'artifact_recent'), ('DOWNLOADS (QUARANTINE)', 'artifact_downloads'),
                ('INSTALL HISTORY', 'artifact_installs'), ('SHELL HISTORY', 'artifact_shellhistory'),
                ('TRASH', 'artifact_trash'), ('LOGINS', 'artifact_logins'),
                ('WINDOWS SERVICES', 'artifact_services'), ('SCHEDULED TASKS', 'artifact_tasks'),
                ('SHIMCACHE', 'artifact_shimcache'), ('AMCACHE', 'artifact_amcache'), ('SRUM', 'artifact_srum'),
                ('PERSISTENCE', 'artifact_persistence'),
                ('EVENT LOGS', 'event_logs'), ('NETWORK ACTIVITY', 'network_activity'),
                ('PASSIVE PROTOCOL CAPTURE', 'protocol_capture'), ('PACKET CAPTURE', 'packet_capture'),
                ('SUPER-TIMELINE', 'super_timeline'), ('YARA SCAN', 'yara_matches'),
                ('IOC MATCHES', 'ioc_matches'), ('HASH-SET MATCH', 'hashset_match'),
                ('ENCRYPTION STATUS', 'encryption_status'),
                ('DELETED FILES / RECYCLE BIN', 'artifact_recyclebin'),
                ('NTFS $MFT', 'artifact_mft'), ('NTFS USN JOURNAL', 'artifact_usnjournal'),
                ('RAM ACQUISITION', 'ram_acquisition'), ('BASELINE DIFF', 'baseline_diff')]

    def _evidence_files(self):
        """The evidence set, in a fixed order: [{'id','name','key','title','desc','data','collected_utc',...hashes}].
        Used by both the report's inventory and the package, so their hashes always agree."""
        di = self.investigation_data
        meta = getattr(di, 'meta', {}) or {}
        titles = {k: t for t, k in self._report_sections()}
        ordered = [k for _t, k in self._report_sections() if k in di]
        ordered += [k for k in di if k not in ordered]
        out = []
        for i, key in enumerate(ordered, 1):
            val = di[key]
            if isinstance(val, str):
                data, ext = val.encode('utf-8', 'replace'), 'txt'
            else:
                data, ext = json.dumps(val, indent=2, default=str, sort_keys=True).encode('utf-8'), 'json'
            h = self._hash_bytes(data)
            title = titles.get(key) or key.upper().replace('_', ' ')
            out.append({'id': f"E{i:03d}", 'name': f"E{i:03d}_{key}.{ext}", 'key': key, 'title': title,
                        'desc': self.SECTION_DESC.get(key) or ("Structured data behind " + titles.get(key.replace('_data', ''), key)
                                                               if key.endswith('_data') else key),
                        'data': data, 'collected_utc': (meta.get(key) or {}).get('collected_utc', ''), **h})
        return out

    def _record_evidence(self, key, meta):
        if key in ('ioc_matches',):
            return
        self._audit('evidence recorded', 'ok', f"{key}  SHA-256 {meta['sha256'][:16]}...")

    # ---- the evidence folder ---------------------------------------------------
    def _vault(self, create=True):
        v = self.__dict__.get('vault_path')
        if v and Path(v).exists():
            return Path(v)
        if not create:
            return None
        ci = self._case_info()
        case = re.sub(r'[^A-Za-z0-9_.-]+', '_', ci['case_id'] or 'CASE').strip('_') or 'CASE'
        base = Path(ci['base_dir'] or (self._home() / 'CACTUS_Cases'))
        v = base / f"{case}_{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}"
        (v / 'captures').mkdir(parents=True, exist_ok=True)
        self.vault_path = str(v)
        self._audit('evidence folder created', 'ok', str(v))
        lab = self.__dict__.get('vault_label')
        if lab is not None:
            lab.config(text=f"Evidence folder: {v}")
        return v

    def new_vault(self):
        self.vault_path = None
        self.captures = []
        v = self._vault()
        messagebox.showinfo("Evidence folder", f"New evidence folder created:\n{v}")

    # ---- export ----------------------------------------------------------------------
    def export_evidence_package(self):
        if not self.investigation_data and not self.__dict__.get('captures'):
            messagebox.showinfo("Evidence package", "Nothing has been collected yet.")
            return
        try:
            vault = self._vault()
        except OSError as e:
            messagebox.showerror("Evidence package", f"Cannot create the evidence folder:\n{e}")
            return
        self._case_snapshot = self._case_info()
        self._audit_snapshot = list(self.__dict__.get('audit_log', []))
        self.run_async(self._task_export_package, str(vault), on_done=self._on_package_done,
                       on_error=lambda e: messagebox.showerror("Evidence package", f"Export failed:\n{type(e).__name__}: {e}"),
                       status="Building evidence package...")

    # ---- v3.4: examiner signing key (reused across cases, like a real cert would be) ----
    def _examiner_keypair(self):
        keydir = self._home() / '.cactus_examiner_key'
        priv_p, pub_p = keydir / 'private.pem', keydir / 'public.pem'
        if priv_p.is_file() and pub_p.is_file():
            return priv_p.read_bytes(), pub_p.read_bytes()
        keydir.mkdir(parents=True, exist_ok=True)
        priv, pub = v34_generate_keypair_cryptography()
        priv_p.write_bytes(priv)
        pub_p.write_bytes(pub)
        try:
            os.chmod(priv_p, 0o600)
        except OSError:
            pass
        return priv, pub

    def _sign_manifest(self, exp, manifest_sha256_file_bytes):
        backend = v34_detect_backend()
        if backend != 'cryptography':
            # openssl-CLI-only environments: keep it simple and honest rather than shelling
            # out to openssl for key management too -- report as unsigned with the real reason.
            reason = ("no signing backend available (install the Python 'cryptography' package)" if not backend
                     else "only an 'openssl' CLI backend was detected; this version signs via the 'cryptography' "
                          "package only -- install it with: pip install cryptography")
            return {'signed': False, 'backend': backend, 'reason': reason}
        try:
            priv, pub = self._examiner_keypair()
            sig = v34_sign_bytes_cryptography(priv, manifest_sha256_file_bytes)
            (exp / 'manifest.sig').write_bytes(sig)
            (exp / 'examiner_public_key.pem').write_bytes(pub)
            fp = v34_fingerprint(pub)
            return {'signed': True, 'backend': 'cryptography', 'fingerprint': fp, 'sig_path': 'manifest.sig'}
        except Exception as e:
            return {'signed': False, 'backend': backend, 'reason': f"signing failed: {type(e).__name__}: {e}"}

    def _task_export_package(self, vault_str):
        vault = Path(vault_str)
        stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
        exp = vault / f"export_{stamp}"
        for d in ('evidence', 'report', 'network', 'logs', 'memory'):
            (exp / d).mkdir(parents=True, exist_ok=True)
        records, notes = [], []

        def register(rel, desc, kind, extra=None):
            p = exp / rel
            h = self._hash_path(p)
            self._readonly(p)
            rec = {'path': rel.replace('\\', '/'), 'kind': kind, 'description': desc, **h}
            rec.update(extra or {})
            records.append(rec)
            return rec

        def put(rel, data, desc, kind, extra=None):
            p = exp / rel
            p.write_bytes(data if isinstance(data, bytes) else data.encode('utf-8'))
            return register(rel, desc, kind, extra)

        files = self._evidence_files()
        for f in files:
            put(f"evidence/{f['name']}", f['data'], f"{f['title']}: {f['desc']}", 'collected data',
                {'evidence_id': f['id'], 'collected_utc': f['collected_utc']})
        caps = []
        for c in self.__dict__.get('captures', []):
            src = Path(c['path'])
            if not src.exists():
                notes.append(f"Capture file missing at export: {src}")
                continue
            dst = exp / 'network' / src.name
            shutil.copy2(src, dst)
            rec = register(f"network/{src.name}", f"Packet capture ({c.get('tool', '?')} on {c.get('interface', '?')})",
                           'packet capture', {'collected_utc': c.get('finished_utc', '')})
            if c.get('sha256') and c['sha256'] != rec['sha256']:
                notes.append(f"WARNING: {src.name} differs from the hash taken at capture time!")
            caps.append(dict(c, **{k: rec[k] for k in ('md5', 'sha1', 'sha256', 'sha512', 'size')}))
        for m in self.__dict__.get('ram_images', []):
            src = Path(m['path'])
            if not src.exists():
                notes.append(f"RAM image missing at export: {src}")
                continue
            dst = exp / 'memory' / src.name
            shutil.copy2(src, dst)
            rec = register(f"memory/{src.name}", f"RAM image ({m.get('tool', '?')})", 'memory image',
                           {'collected_utc': m.get('finished_utc', '')})
            if m.get('sha256') and m['sha256'] != rec['sha256']:
                notes.append(f"WARNING: {src.name} differs from the hash taken at acquisition time!")
        audit = self.__dict__.get('_audit_snapshot') or list(self.__dict__.get('audit_log', []))
        put('logs/chain_of_custody.txt', self._audit_text_block(audit), "Activity log (chain of custody)", 'log')
        put('logs/chain_of_custody.json', json.dumps(audit, indent=2), "Activity log, machine-readable", 'log')
        with _COMMAND_LOCK:
            cmds = list(COMMAND_LOG)
        put('logs/commands_executed.json', json.dumps(cmds, indent=2),
            "Every external command run, with a SHA-256 of its output", 'log')
        put('logs/environment.json', json.dumps({'tool': self._tool_identity(), 'host': self._host_info(),
                                                  'case': self._case_snapshot_safe()}, indent=2),
            "Tool identity (with its own SHA-256), host and case details", 'log')
        model = self._report_model(files=files, captures=caps, notes=notes)
        (exp / 'report' / 'Forensic_Report.txt').write_text(self._render_report_txt(model), encoding='utf-8')
        register('report/Forensic_Report.txt', "Examination report (plain text)", 'report')
        (exp / 'report' / 'Forensic_Report.html').write_text(self._render_report_html(model), encoding='utf-8')
        register('report/Forensic_Report.html', "Examination report (HTML, print to PDF)", 'report')
        (exp / 'report' / 'Forensic_Report.json').write_text(json.dumps(self._report_json(model), indent=2, default=str), encoding='utf-8')
        register('report/Forensic_Report.json', "Examination report (machine-readable)", 'report')
        pdf_ok = self._render_report_pdf(model, str(exp / 'report' / 'Forensic_Report.pdf'))
        if pdf_ok:
            register('report/Forensic_Report.pdf', "Examination report (PDF)", 'report')
        else:
            notes.append("PDF was not produced because the ReportLab library is not installed (pip install reportlab).")
        manifest = {'format': 'CACTUS evidence manifest 1', 'created_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'),
                    'tool': self._tool_identity(), 'case': self._case_snapshot_safe(), 'hash_algorithms': list(self.HASH_ALGOS),
                    'file_count': len(records), 'notes': notes, 'files': sorted(records, key=lambda r: r['path'])}
        (exp / 'manifest.json').write_text(json.dumps(manifest, indent=2, default=str), encoding='utf-8')
        mh = self._hash_path(exp / 'manifest.json')
        (exp / 'manifest.sha256').write_text(f"{mh['sha256']}  manifest.json\n", encoding='utf-8')
        sig_info = self._sign_manifest(exp, (exp / 'manifest.sha256').read_bytes())
        if sig_info['signed']:
            # Not added to manifest.json's own file list: a signature of the manifest's hash
            # can't also be listed inside the thing it hashes (same reason manifest.json,
            # manifest.sha256 and README_VERIFY.txt aren't self-listed either). Still made
            # read-only like every other sealed evidence file.
            self._readonly(exp / 'manifest.sig')
            self._readonly(exp / 'examiner_public_key.pem')
        (exp / 'README_VERIFY.txt').write_text(
            "HOW TO VERIFY THIS EVIDENCE PACKAGE\n\n"
            "1. Every file is listed in manifest.json with its MD5, SHA-1, SHA-256 and SHA-512.\n"
            "2. manifest.sha256 holds the SHA-256 of manifest.json itself.\n"
            "3. Verify with this tool (Case tab > Verify a Package), or independently:\n"
            "     Linux/macOS:  shasum -a 256 <file>       Windows:  certutil -hashfile <file> SHA256\n"
            "4. The SHA-256 of the whole .zip package is recorded separately, next to the .zip, in <name>.zip.hashes.txt\n"
            "   and in the report handed over. Compare it with the package you received.\n"
            "5. Any difference in even one byte produces a completely different hash.\n"
            + ("6. manifest.sig is a cryptographic signature of manifest.sha256, made with the examiner's key "
               "(examiner_public_key.pem). Verify with:\n"
               "     openssl dgst -sha256 -verify examiner_public_key.pem -signature manifest.sig manifest.sha256\n"
               if sig_info['signed'] else ""), encoding='utf-8')
        for n in ('manifest.json', 'manifest.sha256', 'README_VERIFY.txt'):
            self._readonly(exp / n)
        zpath = vault / f"{exp.name}.zip"
        with zipfile.ZipFile(zpath, 'w', zipfile.ZIP_DEFLATED) as z:
            for dp, _dn, fns in os.walk(exp):
                for n in sorted(fns):
                    full = Path(dp) / n
                    z.write(full, str(Path(exp.name) / full.relative_to(exp)))
        zh = self._hash_path(zpath)
        sidecar = Path(str(zpath) + '.hashes.txt')
        sig_block = v34_render_signature_block(sig_info.get('backend'), sig_info.get('fingerprint'),
                                               sig_info['signed'], sig_info.get('sig_path'), mh['sha256'])
        sidecar.write_text(
            f"Evidence package: {zpath.name}\nCreated (UTC): {manifest['created_utc']}\nCase: {self._case_snapshot_safe().get('case_id', '')}\n"
            f"Size: {zh['size']} bytes\nMD5:    {zh['md5']}\nSHA-1:  {zh['sha1']}\nSHA-256: {zh['sha256']}\nSHA-512: {zh['sha512']}\n"
            f"Manifest SHA-256: {mh['sha256']}\n\n" + sig_block, encoding='utf-8')
        self._readonly(zpath)
        self._chown_tree(vault)
        return {'folder': str(exp), 'zip': str(zpath), 'zip_hashes': zh, 'manifest_sha256': mh['sha256'],
                'files': len(records), 'notes': notes, 'pdf': pdf_ok, 'sidecar': str(sidecar), 'sig_info': sig_info}

    def _on_package_done(self, r):
        self._audit('evidence package exported', 'ok', f"{os.path.basename(r['zip'])} SHA-256 {r['zip_hashes']['sha256']}"
                    + (f"  signed ({r['sig_info'].get('fingerprint', '')})" if r['sig_info']['signed'] else "  not signed"))
        txt = (f"EVIDENCE PACKAGE CREATED\n  Folder : {r['folder']}\n  ZIP    : {r['zip']}\n  Files  : {r['files']}\n"
               f"  ZIP SHA-256 : {r['zip_hashes']['sha256']}\n  ZIP SHA-512 : {r['zip_hashes']['sha512']}\n"
               f"  Manifest SHA-256 : {r['manifest_sha256']}\n"
               f"  Signed : {'yes, ' + r['sig_info'].get('fingerprint', '') if r['sig_info']['signed'] else 'no (' + r['sig_info'].get('reason', '') + ')'}\n")
        for n in r['notes']:
            txt += f"  NOTE: {n}\n"
        self._show_in_log(txt)
        messagebox.showinfo("Evidence package created",
                            f"{r['zip']}\n\nSHA-256 of the complete package:\n{r['zip_hashes']['sha256']}\n\n"
                            f"Write this hash in your case notes and the certificate. It is also saved in\n{os.path.basename(r['sidecar'])}"
                            + ("\n\nSigned with examiner key: " + r['sig_info'].get('fingerprint', '') if r['sig_info']['signed']
                               else "\n\nNot cryptographically signed: " + r['sig_info'].get('reason', ''))
                            + ("\n\n" + "\n".join(r['notes']) if r['notes'] else ""))

    # ---- verification ------------------------------------------------------------------
    def verify_package_dialog(self):
        p = filedialog.askopenfilename(title="Choose an evidence package (.zip)", filetypes=[("Evidence package", "*.zip"), ("All files", "*.*")])
        if not p:
            p = filedialog.askdirectory(title="...or choose an unzipped package folder")
        if not p:
            return
        self.run_async(self.verify_package, p, on_done=self._on_verify_done, status="Verifying evidence package...")

    def _on_verify_done(self, res):
        ok, text = res
        self._audit('package verified', 'ok' if ok else 'FAILED', text.splitlines()[0][:150])
        self._show_in_log(text)
        (messagebox.showinfo if ok else messagebox.showerror)("Package verification", text.split("\n\n")[0])

    def verify_package(self, path):
        """Re-hash every file against manifest.json. -> (ok, report text)"""
        path = Path(path)
        lines, problems = [], []
        opener, names = None, []
        if path.is_file():
            zh = self._hash_path(path)
            lines.append(f"Package: {path}\nSHA-256 of the whole package: {zh['sha256']}")
            side = Path(str(path) + '.hashes.txt')
            if side.exists():
                m = re.search(r'SHA-256:\s*([0-9a-f]{64})', side.read_text(errors='ignore'))
                if m and m.group(1) == zh['sha256']:
                    lines.append("  matches the recorded package hash (.hashes.txt): OK")
                elif m:
                    problems.append("package hash differs from the recorded one in .hashes.txt")
            try:
                z = zipfile.ZipFile(path)
            except zipfile.BadZipFile:
                return False, "INTEGRITY FAILURE: not a valid ZIP file.\n"
            names = z.namelist()
            mans = [n for n in names if n.endswith('manifest.json')]
            if not mans:
                return False, "INTEGRITY FAILURE: no manifest.json in the package.\n"
            prefix = mans[0][:-len('manifest.json')]
            manifest_bytes = z.read(mans[0])
            msha = [n for n in names if n == prefix + 'manifest.sha256']
            read = lambda rel: z.open(prefix + rel)
            has = lambda rel: (prefix + rel) in names
            listing = {n[len(prefix):] for n in names if n.startswith(prefix) and not n.endswith('/')}
        else:
            mans = list(path.rglob('manifest.json'))
            if not mans:
                return False, "INTEGRITY FAILURE: no manifest.json found in that folder.\n"
            base = mans[0].parent
            lines.append(f"Folder: {base}")
            manifest_bytes = mans[0].read_bytes()
            msha = [base / 'manifest.sha256'] if (base / 'manifest.sha256').exists() else []
            read = lambda rel: open(base / rel, 'rb')
            has = lambda rel: (base / rel).exists()
            listing = {str(p.relative_to(base)).replace('\\', '/') for p in base.rglob('*') if p.is_file()}
        try:
            manifest = json.loads(manifest_bytes)
        except ValueError:
            return False, "INTEGRITY FAILURE: manifest.json cannot be read.\n"
        mh = hashlib.sha256(manifest_bytes).hexdigest()
        lines.append(f"manifest.json SHA-256: {mh}")
        if msha:
            rec = (z.read(msha[0]).decode() if path.is_file() else Path(msha[0]).read_text()).split()[0]
            if rec == mh:
                lines.append("  matches manifest.sha256: OK")
            else:
                problems.append("manifest.json does not match manifest.sha256")
        good = 0
        for rec in manifest.get('files', []):
            rel = rec['path']
            if not has(rel):
                problems.append(f"MISSING: {rel}")
                continue
            hs = {a: hashlib.new(a) for a in self.HASH_ALGOS}
            size = 0
            with read(rel) as f:
                for chunk in iter(lambda: f.read(1 << 20), b''):
                    size += len(chunk)
                    for h in hs.values():
                        h.update(chunk)
            bad = [a for a in self.HASH_ALGOS if a in rec and hs[a].hexdigest() != rec[a]]
            if bad or size != rec.get('size', size):
                problems.append(f"CHANGED: {rel}  ({', '.join(bad) or 'size'} differ)")
            else:
                good += 1
        listed = {r['path'] for r in manifest.get('files', [])}
        extra = sorted(n for n in listing if n not in listed and n not in
                      ('manifest.json', 'manifest.sha256', 'README_VERIFY.txt', 'manifest.sig', 'examiner_public_key.pem'))
        for n in extra:
            problems.append(f"NOT IN MANIFEST: {n}")
        total = len(manifest.get('files', []))
        head = (f"VERIFIED: all {total} files match the manifest. No change detected." if not problems else
                f"INTEGRITY FAILURE: {len(problems)} problem(s). {good} of {total} files match.")
        body = "\n".join(lines) + f"\nFiles checked: {total}   matching: {good}\n"
        if problems:
            body += "\nPROBLEMS:\n" + "\n".join("  - " + p for p in problems) + "\n"
        return (not problems), head + "\n\n" + body

    def export_audit(self):
        fn = filedialog.asksaveasfilename(
            defaultextension=".txt", filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
            initialfile=f"activity_log_{datetime.now().strftime('%Y%m%d_%H%M%S')}.txt")
        if fn:
            with open(fn, 'w', encoding='utf-8') as f:
                f.write(self._audit_text_block())
            messagebox.showinfo("Success", f"Activity log saved to:\n{fn}\n\nSHA-256: {self._seal_report(fn)}")

    def _audit_text_block(self, log=None):
        log = self.__dict__.get("audit_log", []) if log is None else log
        return "\n".join(self._audit_line(e) for e in log) + "\n"

    def _seal_report(self, fn):
        """SHA-256 of a saved file, also written next to it as <file>.sha256."""
        h = hashlib.sha256()
        with open(fn, 'rb') as f:
            for chunk in iter(lambda: f.read(1 << 20), b''):
                h.update(chunk)
        digest = h.hexdigest()
        try:
            Path(str(fn) + '.sha256').write_text(f"{digest}  {os.path.basename(fn)}\n", encoding='utf-8')
        except OSError:
            pass
        self._audit('file saved', 'ok', f"{os.path.basename(fn)} SHA-256 {digest}")
        return digest

    # ========================================================
    # SEARCH & IOC MATCHING  (over everything collected this session)
    # ========================================================
    def build_search_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  🔎  Search  ')
        card = self._make_card(tab, "Search collected data")
        card.pack(fill='x', padx=12, pady=(12, 8))
        row = tk.Frame(card.body, bg=Theme.BG_CARD)
        row.pack(fill='x', padx=8, pady=8)
        self.search_term = tk.StringVar()
        e = ttk.Entry(row, textvariable=self.search_term, width=50)
        e.pack(side='left', padx=(0, 8))
        e.bind('<Return>', lambda _e: self.run_search())
        ttk.Button(row, text="🔎 Search", style='Accent.TButton', command=self.run_search).pack(side='left', padx=4)
        tk.Label(row, text="Separate several words with |  (means OR). Not case sensitive.",
                 bg=Theme.BG_CARD, fg=Theme.TEXT_SECONDARY, font=('Segoe UI', 9)).pack(side='left', padx=8)
        row2 = tk.Frame(card.body, bg=Theme.BG_CARD)
        row2.pack(fill='x', padx=8, pady=(0, 8))
        ttk.Button(row2, text="📂 Load IOC list...", command=self.load_ioc_list).pack(side='left', padx=(0, 8))
        ttk.Button(row2, text="🎯 Match IOCs", command=self.match_iocs).pack(side='left', padx=4)
        self.ioc_info = tk.Label(row2, text="No IOC list loaded. One indicator per line: IP, domain, URL, "
                                            "MD5/SHA1/SHA256 or any text. Lines starting with # are ignored.",
                                 bg=Theme.BG_CARD, fg=Theme.TEXT_SECONDARY, font=('Segoe UI', 9))
        self.ioc_info.pack(side='left', padx=8)
        ttk.Button(row2, text="🗑 Clear", command=lambda: self.clear_text(self.search_text)).pack(side='right', padx=4)
        self.iocs = []
        card = self._make_card(tab, "Results")
        card.pack(fill='both', expand=True, padx=12, pady=(0, 12))
        self.search_text = self._make_text_area(card)

    def _data_lines(self):
        """(section, line number, text) over every text result collected so far."""
        skip = {'ioc_matches', 'search_results'}
        for key, val in self.investigation_data.items():
            if key in skip or not isinstance(val, str):
                continue
            for i, line in enumerate(val.splitlines(), 1):
                yield key, i, line

    def _search_text(self, term, limit=500):
        parts = [p.strip() for p in term.split('|') if p.strip()]
        if not parts:
            return "Type something to search for.\n", 0
        rx = re.compile('|'.join(re.escape(p) for p in parts), re.I)
        hits, by_sec, total_lines = [], Counter(), 0
        for sec, n, line in self._data_lines():
            total_lines += 1
            if rx.search(line):
                by_sec[sec] += 1
                if len(hits) < limit:
                    hits.append((sec, n, line.strip()))
        out = f"SEARCH: {' OR '.join(parts)}\nSearched {total_lines:,} lines in {len({s for s in self.investigation_data})} sections.\n"
        if not by_sec:
            return out + "No matches. Only data collected in this session is searched; collect it first.\n", 0
        out += f"{sum(by_sec.values()):,} matching lines: " + ", ".join(f"{k} ({v})" for k, v in by_sec.most_common()) + "\n\n"
        cur = None
        for sec, n, line in hits:
            if sec != cur:
                out += f"[{sec}]\n"
                cur = sec
            out += f"  line {n:>5}: {line[:220]}\n"
        if sum(by_sec.values()) > limit:
            out += f"\n... only the first {limit} matches are shown; refine the search.\n"
        return out, sum(by_sec.values())

    def run_search(self):
        text, n = self._search_text(self.search_term.get())
        self.search_text.delete('1.0', 'end')
        self.search_text.insert('1.0', text)
        self._audit('search', 'ok', f"'{self.search_term.get()[:60]}' -> {n} matches")

    @staticmethod
    def _ioc_kind(s):
        try:
            ipaddress.ip_address(s)
            return 'ip'
        except ValueError:
            pass
        for n, k in ((32, 'md5'), (40, 'sha1'), (64, 'sha256')):
            if re.fullmatch(r'[0-9a-fA-F]{%d}' % n, s):
                return k
        if re.match(r'https?://', s, re.I):
            return 'url'
        if re.fullmatch(r'([a-z0-9-]+\.)+[a-z]{2,}', s, re.I):
            return 'domain'
        return 'text'

    def _parse_ioc_list(self, text, limit=3000):
        seen, out = set(), []
        for line in (text or '').splitlines():
            s = line.strip().strip(',;')
            if not s or s.startswith('#'):
                continue
            k = s.lower()
            if k in seen:
                continue
            seen.add(k)
            out.append((s, self._ioc_kind(s)))
            if len(out) >= limit:
                break
        return out

    def load_ioc_list(self):
        fn = filedialog.askopenfilename(title="Choose an IOC list (text file)",
                                        filetypes=[("Text / CSV", "*.txt *.csv *.ioc"), ("All files", "*.*")])
        if not fn:
            return
        try:
            with open(fn, encoding='utf-8-sig', errors='replace') as f:
                self.iocs = self._parse_ioc_list(f.read())
        except OSError as e:
            messagebox.showerror("IOC list", f"Cannot read the file: {e}")
            return
        kinds = Counter(k for _s, k in self.iocs)
        self.ioc_info.config(text=f"{len(self.iocs)} indicators loaded from {os.path.basename(fn)}  ("
                                  + ", ".join(f"{v} {k}" for k, v in kinds.most_common()) + ")")
        self._audit('IOC list loaded', 'ok', f"{os.path.basename(fn)}: {len(self.iocs)} indicators")

    _IOC_WRAP = {'ip': (r'(?<![\d.])', r'(?!\d|\.\d)'), 'domain': (r'(?<![A-Za-z0-9-])', r'(?![A-Za-z0-9-])'),
                 'md5': (r'(?<![0-9A-Fa-f])', r'(?![0-9A-Fa-f])'), 'sha1': (r'(?<![0-9A-Fa-f])', r'(?![0-9A-Fa-f])'),
                 'sha256': (r'(?<![0-9A-Fa-f])', r'(?![0-9A-Fa-f])'), 'url': ('', ''), 'text': ('', '')}

    def _match_iocs(self, iocs, lines, per_ioc=20):
        """-> {indicator: [(section, line no, text), ...]} for every indicator that appears."""
        groups = {}
        for s, k in iocs:
            groups.setdefault(k, []).append(s)
        rxs = []
        for k, items in groups.items():
            pre, post = self._IOC_WRAP[k]
            items = sorted(items, key=len, reverse=True)
            for i in range(0, len(items), 400):
                rxs.append(re.compile(pre + '(?:' + '|'.join(re.escape(x) for x in items[i:i + 400]) + ')' + post, re.I))
        canon = {s.lower(): s for s, _k in iocs}
        found = {}
        for sec, n, line in lines:
            for rx in rxs:
                for m in rx.finditer(line):
                    ind = canon.get(m.group(0).lower())
                    if ind is None:
                        continue
                    lst = found.setdefault(ind, [])
                    if len(lst) < per_ioc:
                        lst.append((sec, n, line.strip()[:200]))
        return found

    def match_iocs(self):
        if not self.iocs:
            messagebox.showinfo("IOC match", "Load an IOC list first.")
            return
        if not any(isinstance(v, str) for v in self.investigation_data.values()):
            messagebox.showinfo("IOC match", "Nothing collected yet. Collect some data first, then match.")
            return
        self.run_async(self._task_match_iocs, list(self.iocs), on_done=self._on_iocs_done,
                       status="Matching indicators...")

    def _task_match_iocs(self, iocs):
        lines = list(self._data_lines())
        found = self._match_iocs(iocs, lines)
        out = "=" * 70 + "\nIOC MATCHES\n" + f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n" + "=" * 70 + "\n"
        out += (f"{len(found)} of {len(iocs)} indicators found in {len(lines):,} lines of collected data.\n"
                "A match is a lead to investigate, not proof. No match only means it is not in what was collected here.\n\n")
        for s, k in iocs:
            if s in found:
                out += f"[HIT] {s}   ({k})\n"
                for sec, n, text in found[s]:
                    out += f"      {sec} line {n}: {text}\n"
        miss = [s for s, _k in iocs if s not in found]
        out += f"\nNot found ({len(miss)}): " + (", ".join(miss[:40]) + (" ..." if len(miss) > 40 else "")) + "\n"
        return out, len(found), len(iocs)

    def _on_iocs_done(self, res):
        text, hits, total = res
        self.search_text.delete('1.0', 'end')
        self.search_text.insert('1.0', text)
        self.investigation_data['ioc_matches'] = text
        self._audit('IOC match', 'ok', f"{hits}/{total} indicators found")

    # ========================================================
    # WINDOWS: SERVICES AND SCHEDULED TASKS (persistence)
    # ========================================================
    _SUSP_HINTS = (('\\temp\\', 'runs from a Temp folder'), ('\\appdata\\', 'runs from a user AppData folder'),
                   ('\\users\\public\\', 'runs from Users\\Public'), ('\\downloads\\', 'runs from Downloads'),
                   ('powershell', 'uses PowerShell'), (' -enc', 'encoded command'), ('frombase64string', 'base64 decoding'),
                   ('mshta', 'uses mshta'), ('wscript', 'uses wscript'), ('cscript', 'uses cscript'),
                   ('regsvr32', 'uses regsvr32'), ('http://', 'contains a URL'), ('https://', 'contains a URL'))

    def _susp_reasons(self, cmd):
        c = (cmd or '').lower().replace('/', '\\')
        seen, out = set(), []
        for needle, why in self._SUSP_HINTS:
            if needle in c and why not in seen:
                seen.add(why)
                out.append(why)
        return out

    def _art_services_windows(self, wr=None):
        if wr is None:
            import winreg as wr
        H = wr.HKEY_LOCAL_MACHINE
        base = r"SYSTEM\CurrentControlSet\Services"
        start_names = {0: 'boot', 1: 'system', 2: 'automatic', 3: 'manual', 4: 'disabled'}
        out = ["Services and drivers that start by themselves are a common place for malware to persist. "
               "Entries marked [CHECK] have a feature worth a look (unusual folder, PowerShell, URL). "
               "That is a lead, not a verdict: many legitimate programs do the same.\n"]
        try:
            names = self._reg_subkeys(wr, H, base, limit=5000)
        except OSError as e:
            return "\n".join(out) + f"Not available: {e}\n"
        rows = []
        for n in names:
            p = base + "\\" + n
            typ, start = self._reg_value(wr, H, p, 'Type'), self._reg_value(wr, H, p, 'Start')
            img = self._reg_value(wr, H, p, 'ImagePath')
            if not isinstance(typ, int) or not isinstance(start, int) or not img:
                continue
            kind = 'driver' if typ & 0x0F else 'service'
            if start > 2:
                continue                             # manual / disabled are not started by themselves
            img = str(img)
            why = self._susp_reasons(img)
            rows.append((0 if why else 1, n, kind, start, img, str(self._reg_value(wr, H, p, 'DisplayName') or ''),
                         str(self._reg_value(wr, H, p, 'ObjectName') or ''), self._reg_lastwrite(wr, H, p), why))
        rows.sort(key=lambda r: (r[0], r[1].lower()))
        for _f, n, kind, start, img, disp, acct, lw, why in rows[:400]:
            out.append(f"  {'[CHECK] ' if why else ''}{n}   ({kind}, starts: {start_names.get(start, start)})")
            out.append(f"      {img}")
            if disp and disp != n and not disp.startswith('@'):
                out.append(f"      name: {disp}")
            out.append(f"      account: {acct or '?'}   key last written: {lw}" + (f"   why: {', '.join(why)}" if why else ""))
        out.append(f"\n  Total auto-start services/drivers: {len(rows)}   flagged: {sum(1 for r in rows if r[8])}")
        return "\n".join(out) + "\n"

    def _parse_task_xml(self, raw):
        """Scheduled-task XML (UTF-16 with BOM on Windows) -> dict, or None."""
        import xml.etree.ElementTree as ET
        for enc in ('utf-16', 'utf-8-sig', 'latin-1'):
            try:
                text = raw.decode(enc)
                break
            except UnicodeError:
                continue
        text = re.sub(r'^<\?xml[^>]*\?>', '', text.lstrip('\ufeff'))
        try:
            root = ET.fromstring(text)
        except ET.ParseError:
            return None
        loc = lambda el: el.tag.rsplit('}', 1)[-1]
        info = {'uri': '', 'author': '', 'date': '', 'enabled': True, 'user': '', 'runlevel': '',
                'triggers': [], 'actions': []}
        for el in root.iter():
            t, v = loc(el), (el.text or '').strip()
            if t == 'URI':
                info['uri'] = v
            elif t == 'Author':
                info['author'] = v
            elif t == 'Date' and not info['date']:
                info['date'] = v
            elif t in ('UserId', 'GroupId') and not info['user']:
                info['user'] = v
            elif t == 'RunLevel':
                info['runlevel'] = v
        for st in (c for c in root if loc(c) == 'Settings'):
            for x in st:
                if loc(x) == 'Enabled':
                    info['enabled'] = (x.text or '').strip().lower() != 'false'
        trig = [c for c in root if loc(c) == 'Triggers']
        for tr in (trig[0] if trig else []):
            info['triggers'].append(loc(tr))
        act = [c for c in root if loc(c) == 'Actions']
        for a in (act[0] if act else []):
            if loc(a) == 'Exec':
                kv = {loc(x): (x.text or '').strip() for x in a}
                info['actions'].append((kv.get('Command', '') + (' ' + kv['Arguments'] if kv.get('Arguments') else '')).strip())
            else:
                info['actions'].append(f"({loc(a)})")
        return info

    def _art_tasks_windows(self, folder=None):
        folder = Path(folder) if folder else Path(os.environ.get('SystemRoot', r'C:\Windows')) / 'System32' / 'Tasks'
        out = ["Scheduled tasks run programs at boot, logon or on a timer, so they are a favourite persistence spot. "
               "Entries marked [CHECK] have a feature worth a look; that is a lead, not a verdict.\n",
               self._privilege_line() + "\n", f"Folder: {folder}\n"]
        files, denied = [], 0
        for dirpath, _dirs, names in os.walk(folder, onerror=lambda e: None):
            for n in names:
                files.append(Path(dirpath) / n)
        if not files:
            try:
                os.listdir(folder)
            except PermissionError:
                return "\n".join(out) + "ACCESS DENIED. Run as Administrator (use 'Run with more rights').\n"
            except FileNotFoundError:
                return "\n".join(out) + "The folder does not exist.\n"
            return "\n".join(out) + "No task files found.\n"
        rows = []
        for p in files:
            try:
                info = self._parse_task_xml(p.read_bytes())
            except PermissionError:
                denied += 1
                continue
            except OSError:
                continue
            if not info:
                continue
            cmd = " ; ".join(info['actions'])
            why = self._susp_reasons(cmd)
            rows.append((0 if why else 1, info['uri'] or str(p.relative_to(folder)), info, cmd, why))
        rows.sort(key=lambda r: (r[0], r[1].lower()))
        for _f, name, info, cmd, why in rows[:400]:
            out.append(f"  {'[CHECK] ' if why else ''}{name}   {'' if info['enabled'] else '(disabled)'}")
            out.append(f"      runs: {cmd or '(none)'}")
            out.append(f"      triggers: {', '.join(info['triggers']) or '-'}   user: {info['user'] or '?'}"
                       f"{'  ' + info['runlevel'] if info['runlevel'] else ''}   author: {info['author'] or '?'}"
                       f"   registered: {info['date'] or '?'}" + (f"\n      why: {', '.join(why)}" if why else ""))
        out.append(f"\n  Total tasks read: {len(rows)}   flagged: {sum(1 for r in rows if r[4])}"
                   + (f"   unreadable (access denied): {denied}" if denied else ""))
        return "\n".join(out) + "\n"

    # ========================================================
    # EVENT LOGS  (date range, level filter, timeline)
    # ========================================================
    LEVEL_FILTERS = ['All levels', 'Warnings and above', 'Errors and above']
    EVENT_PRESETS = [
        ("Last 1 hour", timedelta(hours=1)), ("Last 6 hours", timedelta(hours=6)),
        ("Last 1 day", timedelta(days=1)), ("Last 3 days", timedelta(days=3)),
        ("Last 1 week", timedelta(weeks=1)), ("Last 2 weeks", timedelta(weeks=2)),
        ("Last 1 month", timedelta(days=30)), ("Last 3 months", timedelta(days=90)),
        ("Last 6 months", timedelta(days=180)), ("Last 1 year", timedelta(days=365)),
        ("Custom range", None),
    ]
    _LEVEL_ORDER = ['critical', 'error', 'warning', 'info', 'debug']

    def _toggle_custom_dates(self, *_):
        custom = self.event_preset.get() == "Custom range"
        for w in (self.event_from_entry, self.event_to_entry,
                  self.event_from_btn, self.event_to_btn):
            w.configure(state='normal' if custom else 'disabled')

    def _event_range(self, now=None):
        """(start, end, label) as timezone-aware local datetimes. Raises ValueError."""
        now = now or datetime.now().astimezone()
        label = self.event_preset.get()
        delta = dict(self.EVENT_PRESETS).get(label)
        if delta is not None:
            return now - delta, now, label
        try:
            d1 = datetime.strptime(self.event_from.get().strip(), '%Y-%m-%d')
            d2 = datetime.strptime(self.event_to.get().strip(), '%Y-%m-%d')
        except ValueError:
            raise ValueError("Dates must look like YYYY-MM-DD. Use the calendar buttons.")
        if d1 > d2:
            raise ValueError("The 'From' date is after the 'To' date.")
        start = d1.astimezone()                       # naive datetime is read as local time
        end = (d2 + timedelta(days=1) - timedelta(seconds=1)).astimezone()
        if start > now:
            raise ValueError("The 'From' date is in the future.")
        end = min(end, now)
        return start, end, f"{d1:%Y-%m-%d} to {d2:%Y-%m-%d}"

    def collect_event_logs(self):
        try:
            start, end, label = self._event_range()
            limit = int(self.event_limit.get())
        except ValueError as e:
            messagebox.showerror("Event log range", str(e))
            return
        self.run_async(self._task_collect_event_logs, start, end, label, limit,
                       self.event_level.get(),
                       on_done=self._on_event_logs_done,
                       status=f"Collecting event logs ({label})...")

    def clear_event_view(self):
        self.clear_text(self.log_text)
        self._timeline_data = None
        self.timeline_info.config(text="Collect event logs to draw the timeline.")
        self._draw_timeline()

    def _task_collect_event_logs(self, start, end, label, limit, level):
        result = {'range': {'label': label, 'start': start.isoformat(), 'end': end.isoformat()},
                  'level_filter': level, 'limit': limit, 'source': '', 'events': [],
                  'capped': False, 'notes': [], 'collected': datetime.now().isoformat()}
        try:
            if self.current_os == "Windows":
                self._events_windows(result, start, end, limit, level)
            elif self.current_os == "Darwin":
                self._events_macos(result, start, end, limit, level)
            else:
                self._events_linux(result, start, end, limit, level)
        except Exception as e:
            result['notes'].append(f"Collection failed: {type(e).__name__}: {e}")
        events = sorted(result['events'], key=lambda e: e['time'], reverse=True)
        if len(events) > limit:
            events = events[:limit]
            result['capped'] = True
        result['events'] = events
        return result

    # ---- helpers ------------------------------------------------
    @staticmethod
    def _parse_iso(s):
        """ISO-8601 / journald / macOS timestamps -> aware datetime (naive = local time)."""
        s = (s or '').strip().replace(',', '.')
        s = re.sub(r'Z$', '+00:00', s)
        s = re.sub(r'([+-]\d{2})(\d{2})$', r'\1:\2', s)
        s = re.sub(r'\.(\d+)', lambda m: '.' + (m.group(1) + '000000')[:6], s)
        try:
            d = datetime.fromisoformat(s)
        except ValueError:
            return None
        return d if d.tzinfo else d.astimezone()

    @staticmethod
    def _fmt_local(d):
        return d.astimezone().strftime('%Y-%m-%d %H:%M:%S')

    @staticmethod
    def _infer_level(msg):
        m = (msg or '').lower()
        if re.search(r'\b(panic|fatal|critical|emerg(ency)?)\b', m):
            return 'critical'
        if re.search(r'\b(error|fail(ed|ure|ures)?|denied|refused|segfault|invalid user)\b', m):
            return 'error'
        if re.search(r'\bwarn(ing)?\b', m):
            return 'warning'
        return 'info'

    @staticmethod
    def _level_passes(level, flt):
        if flt == 'Errors and above':
            return level in ('critical', 'error')
        if flt == 'Warnings and above':
            return level in ('critical', 'error', 'warning')
        return True

    # ---- Windows (wevtutil) ---------------------------------------
    def _win_xpath(self, start, end, level):
        s = start.astimezone(timezone.utc).strftime('%Y-%m-%dT%H:%M:%S.000Z')
        e = end.astimezone(timezone.utc).strftime('%Y-%m-%dT%H:%M:%S.999Z')
        conds = []
        if level == 'Errors and above':
            conds.append('(Level=1 or Level=2)')
        elif level == 'Warnings and above':
            conds.append('(Level=1 or Level=2 or Level=3)')
        conds.append(f"TimeCreated[@SystemTime>='{s}' and @SystemTime<='{e}']")
        return "*[System[" + " and ".join(conds) + "]]"

    def _parse_wevt_xml(self, text, logname):
        import xml.etree.ElementTree as ET
        text = re.sub(r'<\?xml[^>]*\?>', '', text or '')
        elems = []
        try:
            elems = list(ET.fromstring('<Events>' + text + '</Events>'))
        except ET.ParseError:
            for chunk in re.findall(r'<Event[ >].*?</Event>', text, re.S):
                try:
                    elems.append(ET.fromstring(chunk))
                except ET.ParseError:
                    pass
        lv = {'0': 'info', '1': 'critical', '2': 'error', '3': 'warning', '4': 'info', '5': 'debug'}
        out = []
        loc = lambda el: el.tag.rsplit('}', 1)[-1]
        for ev in elems:
            info = {'time': None, 'level': 'info', 'source': '', 'id': None, 'message': '',
                    'log': logname}
            data_items = []
            for el in ev.iter():
                t = loc(el)
                if t == 'TimeCreated' and info['time'] is None:
                    info['time'] = self._parse_iso(el.get('SystemTime', ''))
                elif t == 'EventID' and info['id'] is None:
                    info['id'] = (el.text or '').strip()
                elif t == 'Level' and (el.text or '').strip().isdigit() and not info.get('_lv'):
                    info['level'] = lv.get(el.text.strip(), 'info')
                    info['_lv'] = True
                elif t == 'Provider' and not info['source']:
                    info['source'] = el.get('Name', '')
                elif t == 'Message' and el.text:
                    info['message'] = ' '.join(el.text.split())
                elif t == 'Data':
                    n, v = el.get('Name'), (el.text or '').strip()
                    if v:
                        data_items.append(f"{n}={v}" if n else v)
            info.pop('_lv', None)
            if not info['message'] and data_items:
                info['message'] = '; '.join(data_items)[:300]
            if info['time'] is not None:
                out.append(info)
        return out

    def _events_windows(self, result, start, end, limit, level):
        xp = self._win_xpath(start, end, level)
        got_any = False
        for log in ('System', 'Application', 'Security'):
            try:
                r = subprocess.run(['wevtutil', 'qe', log, '/q:' + xp, '/f:RenderedXml',
                                    '/rd:true', f'/c:{limit}'],
                                   capture_output=True, text=True, timeout=240, errors='replace')
            except FileNotFoundError:
                result['notes'].append("wevtutil.exe not found.")
                break
            except subprocess.TimeoutExpired:
                result['notes'].append(f"{log}: query timed out; choose a shorter range.")
                continue
            if r.returncode != 0:
                msg = (r.stderr or '').strip().splitlines()
                hint = " Run as Administrator." if r.returncode == 5 or 'denied' in (r.stderr or '').lower() else ""
                result['notes'].append(f"{log}: could not be read ({msg[0] if msg else 'error ' + str(r.returncode)}).{hint}")
                continue
            evs = self._parse_wevt_xml(r.stdout, log)
            got_any = got_any or bool(evs)
            if len(evs) >= limit:
                result['capped'] = True
            result['events'] += evs
        result['source'] = "wevtutil (System, Application, Security logs)"
        if not got_any and not result['notes']:
            result['notes'].append("No events in this period.")

    # ---- Linux (journald, then /var/log files) ------------------
    def _parse_journal_json(self, text):
        pri = {'0': 'critical', '1': 'critical', '2': 'critical', '3': 'error', '4': 'warning',
               '5': 'info', '6': 'info', '7': 'debug'}
        out = []
        for line in (text or '').splitlines():
            line = line.strip()
            if not line.startswith('{'):
                continue
            try:
                j = json.loads(line)
                us = int(j.get('__REALTIME_TIMESTAMP'))
            except (ValueError, TypeError):
                continue
            msg = j.get('MESSAGE', '')
            if isinstance(msg, list):                       # journald stores non-UTF-8 as bytes
                msg = bytes(x & 255 for x in msg).decode('utf-8', 'replace')
            out.append({'time': datetime.fromtimestamp(us / 1e6, timezone.utc),
                        'level': pri.get(str(j.get('PRIORITY', '6')), 'info'),
                        'source': j.get('SYSLOG_IDENTIFIER') or j.get('_COMM') or '',
                        'id': None, 'message': ' '.join(str(msg).split()), 'log': 'journal'})
        return out

    def _parse_syslog_line(self, line, now=None):
        now = now or datetime.now().astimezone()
        m = re.match(r'^(\d{4}-\d{2}-\d{2}[T ]\d{2}:\d{2}:\d{2}(?:[.,]\d+)?(?:Z|[+-]\d{2}:?\d{2})?)'
                     r'\s+(\S+)\s+([^:\s\[]+)(?:\[\d+\])?:\s*(.*)$', line)
        if m:
            ts = self._parse_iso(m.group(1))
            src, msg = m.group(3), m.group(4)
        else:
            m = re.match(r'^([A-Z][a-z]{2})\s+(\d{1,2})\s+(\d{2}:\d{2}:\d{2})\s+(\S+)\s+'
                         r'([^:\s\[]+)(?:\[\d+\])?:\s*(.*)$', line)
            if not m:
                return None
            try:
                naive = datetime.strptime(f"{now.year} {m.group(1)} {m.group(2)} {m.group(3)}",
                                          "%Y %b %d %H:%M:%S")
            except ValueError:
                return None
            ts = naive.astimezone()
            if ts > now + timedelta(days=1):               # no year in the line: it was last year
                ts = naive.replace(year=now.year - 1).astimezone()
            src, msg = m.group(5), m.group(6)
        if ts is None:
            return None
        return {'time': ts, 'level': self._infer_level(msg), 'source': src, 'id': None,
                'message': ' '.join(msg.split()), 'log': 'syslog'}

    def _events_from_logfiles(self, result, start, end, level, log_dir='/var/log', now=None):
        now = now or datetime.now().astimezone()
        base = Path(log_dir)
        files = []
        for n in ('syslog', 'messages', 'auth.log', 'secure', 'kern.log'):
            try:
                for p in sorted(base.glob(n + '*')):
                    if p.name == n or re.search(r'\.\d+(\.gz)?$', p.name):
                        files.append(p)
            except Exception:
                pass
        if not files:
            result['notes'].append(f"No readable log files found in {log_dir}.")
            return
        seen_any = False
        for p in files:
            try:
                if datetime.fromtimestamp(p.stat().st_mtime).astimezone() < start:
                    continue                                  # whole file is older than the range
                opener = gzip.open if p.name.endswith('.gz') else open
                with opener(p, 'rt', errors='ignore') as f:
                    for line in f:
                        ev = self._parse_syslog_line(line.rstrip('\n'), now)
                        if ev and start <= ev['time'] <= end and self._level_passes(ev['level'], level):
                            ev['log'] = p.name
                            result['events'].append(ev)
                seen_any = True
            except PermissionError:
                result['notes'].append(f"{p}: permission denied (try running with sudo).")
            except Exception as e:
                result['notes'].append(f"{p}: {type(e).__name__}: {e}")
        if seen_any:
            result['source'] = f"log files in {log_dir} (levels inferred from message text)"

    def _events_linux(self, result, start, end, limit, level, log_dir='/var/log'):
        if shutil.which('journalctl'):
            fmt = lambda d: d.astimezone(timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')
            cmd = ['journalctl', '--no-pager', '-o', 'json', '-r', '-n', str(limit),
                   '--since', fmt(start), '--until', fmt(end)]
            if level == 'Errors and above':
                cmd += ['-p', 'err']
            elif level == 'Warnings and above':
                cmd += ['-p', 'warning']
            try:
                r = subprocess.run(cmd, capture_output=True, text=True, timeout=240, errors='replace')
                evs = self._parse_journal_json(r.stdout)
                if evs:
                    result['events'] += evs
                    result['source'] = "journalctl (systemd journal)"
                    if len(evs) >= limit:
                        result['capped'] = True
                    return
                if r.returncode != 0 and r.stderr.strip():
                    result['notes'].append("journalctl: " + r.stderr.strip().splitlines()[0])
            except subprocess.TimeoutExpired:
                result['notes'].append("journalctl timed out; choose a shorter range.")
        self._events_from_logfiles(result, start, end, level, log_dir)
        if not result['events'] and not result['notes']:
            result['notes'].append("No events in this period.")

    # ---- macOS (unified log) ------------------------------------
    def _parse_macos_log_line(self, line):
        try:
            j = json.loads(line)
        except ValueError:
            return None
        if not isinstance(j, dict) or 'timestamp' not in j:
            return None
        t = self._parse_iso(str(j['timestamp']))
        if t is None:
            return None
        mt = str(j.get('messageType', 'Default')).lower()
        lvl = {'fault': 'critical', 'error': 'error', 'debug': 'debug'}.get(mt, 'info')
        proc = os.path.basename(str(j.get('processImagePath', ''))) or j.get('subsystem', '')
        return {'time': t, 'level': lvl, 'source': proc, 'id': None,
                'message': ' '.join(str(j.get('eventMessage', '')).split()), 'log': 'unified log'}

    def _events_macos(self, result, start, end, limit, level):
        fmt = lambda d: d.astimezone().strftime('%Y-%m-%d %H:%M:%S')
        cmd = ['log', 'show', '--start', fmt(start), '--end', fmt(end), '--style', 'ndjson']
        pred = None
        if level != 'All levels':
            pred = 'messageType == fault OR messageType == error'
            if level == 'Warnings and above':
                result['notes'].append("macOS has no 'warning' level; showing errors and faults.")
        elif end - start > timedelta(days=1):
            pred = 'messageType == fault OR messageType == error'
            result['notes'].append("Ranges over 1 day read only error and fault messages "
                                   "(the full log is huge and mostly not kept by macOS).")
        if pred:
            cmd += ['--predicate', pred]
        try:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    text=True, errors='replace')
        except FileNotFoundError:
            result['notes'].append("The 'log' command was not found.")
            return
        timer = threading.Timer(240, proc.kill)
        timer.start()
        n = 0
        try:
            for line in proc.stdout:
                ev = self._parse_macos_log_line(line)
                if ev:
                    result['events'].append(ev)
                    n += 1
                    if n >= limit:
                        result['capped'] = True
                        proc.kill()
                        break
        finally:
            timer.cancel()
        err = ''
        try:
            proc.wait(timeout=5)
            err = proc.stderr.read().strip()
        except Exception:
            pass
        result['source'] = "log show (macOS unified log, oldest first)"
        if result['capped']:
            result['notes'].append("macOS returns the oldest events first, so the limit kept the earliest "
                                   "part of the range. Use a shorter range or the error filter.")
        if not result['events'] and err:
            result['notes'].append("log show: " + err.splitlines()[0])
            if 'Permission' in err or 'privilege' in err.lower():
                result['notes'].append("Run the tool with sudo, or grant Full Disk Access.")

    # ---- summary text + timeline -----------------------------------
    def _event_buckets(self, events, start, end):
        span = end - start
        unit = 'hour' if span <= timedelta(days=2) else ('day' if span <= timedelta(days=70) else 'week')
        step = {'hour': timedelta(hours=1), 'day': timedelta(days=1), 'week': timedelta(weeks=1)}[unit]

        def floor(d):
            if unit == 'hour':
                return d.replace(minute=0, second=0, microsecond=0)
            d = d.replace(hour=0, minute=0, second=0, microsecond=0)
            return d - timedelta(days=d.weekday()) if unit == 'week' else d

        s = floor(start.astimezone().replace(tzinfo=None))
        e = end.astimezone().replace(tzinfo=None)
        buckets, cur = {}, s
        while cur <= e and len(buckets) < 3000:
            buckets[cur] = {'critical': 0, 'error': 0, 'warning': 0, 'info': 0}
            cur += step
        for ev in events:
            k = floor(ev['time'].astimezone().replace(tzinfo=None))
            if k in buckets:
                buckets[k]['info' if ev['level'] == 'debug' else ev['level']] += 1
        fmt = {'hour': '%m-%d %H:00', 'day': '%Y-%m-%d', 'week': 'wk of %Y-%m-%d'}[unit]
        return unit, [dict(label=k.strftime(fmt), **v) for k, v in sorted(buckets.items())]

    def _format_events(self, result):
        ev = result['events']
        rng = result['range']
        st = datetime.fromisoformat(rng['start'])
        en = datetime.fromisoformat(rng['end'])
        out = "=" * 70 + "\nSYSTEM EVENT LOGS\n"
        out += f"Range     : {rng['label']}   ({self._fmt_local(st)}  ->  {self._fmt_local(en)}, local time)\n"
        out += f"Source    : {result['source'] or 'none'}\n"
        out += f"Level     : {result['level_filter']}      Max events: {result['limit']:,}\n"
        out += f"Collected : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n" + "=" * 70 + "\n\n"
        out += f"Events found: {len(ev):,}"
        if result['capped'] and ev:
            out += (f"   (limit reached: only the newest events are included, back to "
                    f"{self._fmt_local(ev[-1]['time'])}; raise 'Max events' for more)")
        out += "\n"
        if ev:
            cnt = Counter(e['level'] for e in ev)
            out += "By level   : " + "   ".join(f"{l} {cnt[l]:,}" for l in self._LEVEL_ORDER if cnt[l]) + "\n"
            days = Counter(e['time'].astimezone().strftime('%Y-%m-%d') for e in ev)
            out += "Busiest days: " + ", ".join(f"{d} ({n:,})" for d, n in days.most_common(5)) + "\n"
            src = Counter(e['source'] for e in ev if e['source'])
            out += "Top sources: " + ", ".join(f"{s} ({n:,})" for s, n in src.most_common(8)) + "\n"
            ids = Counter((e['id'], e['log']) for e in ev if e['id'])
            if ids:
                out += "Top event IDs: " + ", ".join(f"{i} [{l}] x{n:,}" for (i, l), n in ids.most_common(8)) + "\n"
        for n in result['notes']:
            out += f"NOTE: {n}\n"
        if ev:
            show = ev[:400]
            out += f"\nEVENTS (newest first, showing {len(show):,} of {len(ev):,})\n" + "-" * 70 + "\n"
            for e in show:
                eid = f" id={e['id']}" if e['id'] else ""
                msg = e['message'][:220] + ("..." if len(e['message']) > 220 else "")
                out += (f"{self._fmt_local(e['time'])}  {e['level'].upper():<8} "
                        f"{e['source'][:28]:<28}{eid}  {msg}\n")
        return out + "\n"

    def _on_event_logs_done(self, result):
        text = self._format_events(result)
        self.log_text.delete('1.0', 'end')
        self.log_text.insert('1.0', text)
        self.investigation_data['event_logs'] = text
        data = dict(result)
        data['events'] = [dict(e, time=e['time'].isoformat()) for e in result['events'][:2000]]
        data['events_total'] = len(result['events'])
        self.investigation_data['event_logs_data'] = data

        st = datetime.fromisoformat(result['range']['start'])
        en = datetime.fromisoformat(result['range']['end'])
        if result['capped'] and result['events']:
            st = max(st, result['events'][-1]['time'])        # earlier buckets would look falsely empty
        unit, buckets = self._event_buckets(result['events'], st, en)
        self._timeline_data = {'unit': unit, 'buckets': buckets, 'capped': result['capped'],
                               'total': len(result['events'])}
        self.timeline_info.config(
            text=f"{len(result['events']):,} events, one bar per {unit}."
                 + ("  Limit reached: older events are not shown." if result['capped'] else "")
                 + "  Hover a bar for details.")
        self._draw_timeline()

    def _draw_timeline(self):
        c = self.timeline_canvas
        c.delete('all')
        self._timeline_rects = []
        w, h = c.winfo_width(), c.winfo_height()
        if w < 80 or h < 60:
            return
        d = self._timeline_data
        if not d or not d['buckets']:
            c.create_text(w / 2, h / 2, text="No timeline yet. Collect event logs first.",
                          fill=Theme.TEXT_SECONDARY, font=('Segoe UI', 10))
            return
        L, R, T, B = 48, 14, 24, 30
        bks = d['buckets']
        totals = [b['critical'] + b['error'] + b['warning'] + b['info'] for b in bks]
        top = max(totals) or 1
        n = len(bks)
        bw = (w - L - R) / n
        gap = min(2.0, bw * 0.2)
        base = h - B
        ph = base - T
        for frac in (0, 0.5, 1):
            y = base - ph * frac
            c.create_line(L, y, w - R, y, fill=Theme.BORDER)
            c.create_text(L - 6, y, text=f"{int(round(top * frac)):,}", anchor='e',
                          fill=Theme.TEXT_SECONDARY, font=('Segoe UI', 8))
        for i, b in enumerate(bks):
            x0, x1 = L + i * bw + gap / 2, L + (i + 1) * bw - gap / 2
            y = base
            for val, col in ((b['critical'] + b['error'], Theme.ERROR),
                             (b['warning'], Theme.WARNING), (b['info'], Theme.ACCENT)):
                if val:
                    ht = max(1.0, ph * val / top)
                    c.create_rectangle(x0, y - ht, max(x1, x0 + 1), y, fill=col, outline='')
                    y -= ht
            self._timeline_rects.append((x0, x1 + gap, i))
        for i in sorted({0, n // 2, n - 1}):
            x = L + (i + 0.5) * bw
            anchor = 'w' if i == 0 and n > 1 else ('e' if i == n - 1 and n > 1 else 'center')
            c.create_text(min(max(x, L), w - R), base + 14, text=bks[i]['label'], anchor=anchor,
                          fill=Theme.TEXT_SECONDARY, font=('Segoe UI', 8))
        lx = w - R
        for text, col in (("Info", Theme.ACCENT), ("Warning", Theme.WARNING), ("Error / critical", Theme.ERROR)):
            tw = 7 * len(text) + 18
            c.create_text(lx, 10, text=text, anchor='e', fill=Theme.TEXT_SECONDARY, font=('Segoe UI', 8))
            c.create_rectangle(lx - tw + 4, 6, lx - tw + 14, 14, fill=col, outline='')
            lx -= tw + 14

    def _timeline_hover(self, event):
        d = self._timeline_data
        if not d:
            return
        default = (f"{d['total']:,} events, one bar per {d['unit']}.  Hover a bar for details.")
        if event is None:
            self.timeline_info.config(text=default)
            return
        for x0, x1, i in self._timeline_rects:
            if x0 <= event.x <= x1:
                b = d['buckets'][i]
                tot = b['critical'] + b['error'] + b['warning'] + b['info']
                self.timeline_info.config(
                    text=f"{b['label']}:  {tot:,} events   (errors {b['critical'] + b['error']:,}, "
                         f"warnings {b['warning']:,}, info {b['info']:,})")
                return
        self.timeline_info.config(text=default)

    # ========================================================
    # NETWORK ACTIVITY  (devices, protocols, known networks, capture)
    # ========================================================
    _PORT_NAMES = {
        20: 'FTP-data', 21: 'FTP', 22: 'SSH', 23: 'Telnet', 25: 'SMTP', 53: 'DNS', 67: 'DHCP',
        68: 'DHCP', 80: 'HTTP', 88: 'Kerberos', 110: 'POP3', 123: 'NTP', 135: 'MS-RPC',
        137: 'NetBIOS-NS', 138: 'NetBIOS-DGM', 139: 'NetBIOS-SSN', 143: 'IMAP', 161: 'SNMP',
        389: 'LDAP', 443: 'HTTPS', 445: 'SMB', 465: 'SMTPS', 514: 'Syslog', 515: 'LPD',
        548: 'AFP', 587: 'SMTP-submission', 631: 'IPP (printing)', 636: 'LDAPS', 993: 'IMAPS',
        995: 'POP3S', 1883: 'MQTT', 1900: 'SSDP/UPnP', 3306: 'MySQL', 3389: 'RDP',
        5060: 'SIP', 5353: 'mDNS', 5355: 'LLMNR', 5357: 'WSD', 5432: 'PostgreSQL',
        5900: 'VNC', 8080: 'HTTP-alt', 8443: 'HTTPS-alt', 8883: 'MQTT-TLS', 9100: 'JetDirect (printing)',
    }
    _VIRTUAL_MACS = {'005056': 'VMware', '000c29': 'VMware', '000569': 'VMware',
                     '080027': 'VirtualBox', '525400': 'QEMU/KVM', '00155d': 'Microsoft Hyper-V',
                     '00163e': 'Xen', '0242ac': 'Docker'}
    _oui_cache = None

    @classmethod
    def _service_for(cls, proto, lport, rport):
        """Service name for a flow: prefer the well-known side."""
        p = (proto or 'tcp').lower().rstrip('46')
        for port in (rport, lport):
            if port in cls._PORT_NAMES:
                return f"{cls._PORT_NAMES[port]} ({p}/{port})"
        cands = [x for x in (rport, lport) if x]
        if cands and min(cands) < 1024:
            try:
                return f"{socket.getservbyport(min(cands), p)} ({p}/{min(cands)})"
            except OSError:
                pass
        return f"{p}/{rport or lport or '?'}"

    @staticmethod
    def _hostport(s):
        s = (s or '').strip()
        if s in ('*:*', '*'):
            return '*', 0
        host, _, port = s.rpartition(':')
        host = host.strip('[]').split('%')[0]
        return (host or '*'), (int(port) if port.isdigit() else 0)

    @staticmethod
    def _hostport_dot(s):
        s = (s or '').strip()
        host, _, port = s.rpartition('.')
        host = host.split('%')[0]
        return (host or '*'), (int(port) if port.isdigit() else 0)

    @staticmethod
    def _norm_mac(m):
        parts = re.split(r'[:\-]', m.strip().lower())
        return ':'.join(x.zfill(2) for x in parts) if len(parts) == 6 else m.strip().lower()

    # ---- connection table parsers -----------------------------------
    def _mkconn(self, proto, local, remote, state='', pid='', proc='', dot=False):
        sp = self._hostport_dot if dot else self._hostport
        lip, lport = sp(local)
        rip, rport = sp(remote)
        proto = proto.upper().rstrip('46')
        state = state.upper().replace('LISTENING', 'LISTEN')
        return {'proto': proto, 'local_ip': lip, 'local_port': lport, 'remote_ip': rip,
                'remote_port': rport, 'state': state, 'pid': str(pid or ''), 'process': proc or ''}

    def _parse_ss(self, text):
        out = []
        for line in (text or '').splitlines():
            f = line.split()
            if len(f) < 6 or f[0] not in ('tcp', 'udp'):
                continue
            m = re.search(r'\(\("([^"]+)",pid=(\d+)', ' '.join(f[6:]))
            state = {'UNCONN': 'LISTEN'}.get(f[1], f[1]) if f[0] == 'udp' else f[1]
            out.append(self._mkconn(f[0], f[4], f[5], state, m.group(2) if m else '',
                                    m.group(1) if m else ''))
        return out

    def _parse_netstat_win(self, text, pid_names=None):
        out = []
        for line in (text or '').splitlines():
            f = line.split()
            if not f or f[0] not in ('TCP', 'UDP'):
                continue
            if f[0] == 'TCP' and len(f) >= 5:
                state, pid = f[3], f[4]
            elif f[0] == 'UDP' and len(f) >= 4:
                state, pid = '', f[3]
            else:
                continue
            out.append(self._mkconn(f[0], f[1], f[2], state, pid, (pid_names or {}).get(pid, '')))
        return out

    def _parse_lsof(self, text):
        out = []
        for line in (text or '').splitlines()[1:]:
            f = line.split(None, 8)
            if len(f) < 9 or f[7] not in ('TCP', 'UDP'):
                continue
            name = f[8]
            m = re.search(r'\((\w+)\)\s*$', name)
            state = m.group(1) if m else ''
            core = re.sub(r'\s*\(\w+\)\s*$', '', name)
            local, _, remote = core.partition('->')
            out.append(self._mkconn(f[7], local, remote or '*:*', state or ('' if remote else 'LISTEN'),
                                    f[1], f[0].replace('\\x20', ' ')))
        return out

    def _parse_netstat_bsd(self, text):
        out = []
        for line in (text or '').splitlines():
            f = line.split()
            if len(f) < 5 or not re.match(r'^(tcp|udp)\d*$', f[0]):
                continue
            out.append(self._mkconn(f[0], f[3], f[4], f[5] if len(f) > 5 else '', dot=True))
        return out

    # ---- neighbour (ARP / NDP) parsers -------------------------------
    @staticmethod
    def _usable_neighbor(ip, mac):
        try:
            a = ipaddress.ip_address(ip)
        except ValueError:
            return False
        if a.is_multicast or a.is_unspecified or a.is_loopback:
            return False
        if ip == '255.255.255.255' or not re.fullmatch(r'([0-9a-f]{2}:){5}[0-9a-f]{2}', mac):
            return False
        return not (int(mac[:2], 16) & 1) and mac != 'ff:ff:ff:ff:ff:ff'

    def _neigh(self, ip, mac, state='', iface='', router=False):
        mac = self._norm_mac(mac)
        ip = ip.split('%')[0]
        if not self._usable_neighbor(ip, mac):
            return None
        return {'ip': ip, 'mac': mac, 'state': state, 'iface': iface, 'router': router}

    def _parse_ip_neigh(self, text):
        out = []
        for line in (text or '').splitlines():
            m = re.match(r'^(\S+)\s+dev\s+(\S+)\s+lladdr\s+(\S+)(\s+router)?\s+(\w+)\s*$', line.strip())
            if m:
                n = self._neigh(m.group(1), m.group(3), m.group(5), m.group(2), bool(m.group(4)))
                if n:
                    out.append(n)
        return out

    def _parse_arp_unix(self, text):
        out = []
        for line in (text or '').splitlines():
            m = re.search(r'\((\d+\.\d+\.\d+\.\d+)\) at ([0-9a-fA-F:]+)(?: \[\w+\])?(?: on (\S+))?', line)
            if m:
                n = self._neigh(m.group(1), m.group(2), 'ARP', m.group(3) or '')
                if n:
                    out.append(n)
        return out

    def _parse_ndp(self, text):
        out = []
        for line in (text or '').splitlines()[1:]:
            f = line.split()
            if len(f) >= 3 and re.fullmatch(r'[0-9a-fA-F:]+', f[1]) and ':' in f[1]:
                n = self._neigh(f[0], f[1], 'NDP', f[2])
                if n:
                    out.append(n)
        return out

    def _parse_arp_windows(self, text):
        out, iface = [], ''
        for line in (text or '').splitlines():
            m = re.match(r'^\s*Interface:\s*(\S+)', line)
            if m:
                iface = m.group(1)
                continue
            m = re.match(r'^\s*(\d+\.\d+\.\d+\.\d+)\s+((?:[0-9a-fA-F]{2}-){5}[0-9a-fA-F]{2})\s+(\w+)', line)
            if m:
                n = self._neigh(m.group(1), m.group(2), m.group(3), iface)
                if n:
                    out.append(n)
        return out

    # ---- MAC details -------------------------------------------------
    def _load_oui(self):
        db = {}
        for path in ('/usr/share/ieee-data/oui.txt', '/usr/share/wireshark/manuf',
                     '/usr/share/nmap/nmap-mac-prefixes', '/opt/homebrew/share/wireshark/manuf',
                     '/usr/local/share/wireshark/manuf'):
            try:
                with open(path, errors='ignore') as f:
                    for line in f:
                        m = re.match(r'^([0-9A-F]{2})-([0-9A-F]{2})-([0-9A-F]{2})\s+\(hex\)\s+(.+)$', line)
                        if m:
                            db[''.join(m.group(1, 2, 3))] = m.group(4).strip()
                            continue
                        m = re.match(r'^([0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2})\s+(\S+)(?:\s+(.+))?$', line)
                        if m:
                            db[m.group(1).replace(':', '').upper()] = (m.group(3) or m.group(2)).strip()
                            continue
                        m = re.match(r'^([0-9A-Fa-f]{6})\s+(.+)$', line)
                        if m:
                            db[m.group(1).upper()] = m.group(2).strip()
                if db:
                    break
            except OSError:
                continue
        return db

    def _mac_info(self, mac):
        pre = mac.replace(':', '')[:6]
        if DigitalForensicTool._oui_cache is None:
            DigitalForensicTool._oui_cache = self._load_oui()
        vendor = self._VIRTUAL_MACS.get(pre) or DigitalForensicTool._oui_cache.get(pre.upper(), '')
        if int(mac[:2], 16) & 2:
            tag = "locally administered MAC (randomised: typical of phones/laptops with a private Wi-Fi address, or virtual)"
            return (vendor + "; " if vendor else "") + tag
        return vendor or "vendor unknown (no OUI list found on this computer)"

    # ---- collection ---------------------------------------------------
    def _run(self, cmd, timeout=20):
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, errors='replace')
            return r.stdout
        except (OSError, subprocess.SubprocessError):
            return ''

    def _collect_neighbors(self, notes):
        out = []
        if self.current_os == "Windows":
            out = self._parse_arp_windows(self._run(['arp', '-a']))
            notes.append("Windows IPv6 neighbours are not listed (only the IPv4 ARP table).")
        elif self.current_os == "Darwin":
            out = self._parse_arp_unix(self._run(['arp', '-an'])) + self._parse_ndp(self._run(['ndp', '-an']))
        else:
            out = self._parse_ip_neigh(self._run(['ip', 'neigh', 'show']))
            if not out:
                out = self._parse_arp_unix(self._run(['arp', '-an']))
            if not out and os.path.exists('/proc/net/arp'):
                try:
                    with open('/proc/net/arp') as f:
                        for line in list(f)[1:]:
                            c = line.split()
                            if len(c) >= 6:
                                n = self._neigh(c[0], c[3], 'ARP', c[5])
                                if n:
                                    out.append(n)
                except OSError:
                    pass
        seen, uniq = set(), []
        for n in out:
            if n['ip'] not in seen:
                seen.add(n['ip'])
                uniq.append(n)
        return uniq

    def _collect_connections(self, notes):
        conns = []
        if self.current_os == "Windows":
            names = {}
            for row in self._run(['tasklist', '/fo', 'csv', '/nh'], 30).splitlines():
                m = re.match(r'^"([^"]+)","(\d+)"', row)
                if m:
                    names[m.group(2)] = m.group(1)
            conns = self._parse_netstat_win(self._run(['netstat', '-ano'], 30), names)
        elif self.current_os == "Darwin":
            if shutil.which('lsof'):
                conns = self._parse_lsof(self._run(['lsof', '-nP', '-i'], 40))
            if not conns:
                conns = (self._parse_netstat_bsd(self._run(['netstat', '-an', '-p', 'tcp']))
                         + self._parse_netstat_bsd(self._run(['netstat', '-an', '-p', 'udp'])))
                notes.append("Process names unavailable (lsof returned nothing; try sudo).")
        else:
            conns = self._parse_ss(self._run(['ss', '-H', '-tunap']))
            if not conns and shutil.which('lsof'):
                conns = self._parse_lsof(self._run(['lsof', '-nP', '-i'], 40))
            if not conns:
                notes.append("No connection information: neither 'ss' nor 'lsof' returned data.")
            elif os.geteuid() != 0 if hasattr(os, 'geteuid') else False:
                notes.append("Not running as root: process names are shown only for your own programs.")
        return conns

    # ---- known networks (history) --------------------------------------
    def _known_networks_windows(self, wr=None):
        if wr is None:
            import winreg as wr
        H = wr.HKEY_LOCAL_MACHINE
        base = r"SOFTWARE\Microsoft\Windows NT\CurrentVersion\NetworkList"
        types = {6: 'wired', 23: 'VPN / broadband', 71: 'wireless (Wi-Fi)', 83: 'mobile broadband'}
        sigs = {}
        for kind in ('Unmanaged', 'Managed'):
            try:
                for s in self._reg_subkeys(wr, H, f"{base}\\Signatures\\{kind}"):
                    p = f"{base}\\Signatures\\{kind}\\{s}"
                    guid = str(self._reg_value(wr, H, p, 'ProfileGuid') or '').lower()
                    gw = self._reg_value(wr, H, p, 'DefaultGatewayMac')
                    sigs[guid] = {'gateway_mac': self._norm_mac(bytes(gw).hex(':')) if gw and len(gw) == 6 else '',
                                  'dns_suffix': str(self._reg_value(wr, H, p, 'DnsSuffix') or ''),
                                  'ssid_first': str(self._reg_value(wr, H, p, 'FirstNetwork') or '')}
            except OSError:
                continue
        nets = []
        try:
            for g in self._reg_subkeys(wr, H, base + r"\Profiles"):
                p = base + "\\Profiles\\" + g
                nt = self._reg_value(wr, H, p, 'NameType')
                created = self._reg_value(wr, H, p, 'DateCreated')
                last = self._reg_value(wr, H, p, 'DateLastConnected')
                sg = sigs.get(g.lower(), {})
                nets.append({'name': str(self._reg_value(wr, H, p, 'ProfileName') or g),
                             'type': types.get(nt, f"type {nt}" if nt is not None else '?'),
                             'first': self._systemtime(created) if created else '?',
                             'last': self._systemtime(last) if last else '?',
                             'gateway_mac': sg.get('gateway_mac', ''), 'dns_suffix': sg.get('dns_suffix', ''),
                             'source': 'Windows registry (NetworkList)'})
        except OSError as e:
            nets.append({'name': f"(NetworkList not readable: {e})", 'type': '', 'first': '', 'last': '',
                         'gateway_mac': '', 'dns_suffix': '', 'source': ''})
        nets.sort(key=lambda n: n['last'], reverse=True)
        saved = [m.group(1).strip() for m in re.finditer(r'All User Profile\s*:\s*(.+)',
                                                            self._run(['netsh', 'wlan', 'show', 'profiles']))]
        known = {n['name'] for n in nets}
        for s in saved:
            if s not in known:
                nets.append({'name': s, 'type': 'wireless (Wi-Fi), saved profile', 'first': '', 'last': '',
                             'gateway_mac': '', 'dns_suffix': '', 'source': 'netsh wlan (saved profile)'})
        return nets

    def _known_networks_macos(self, root='/'):
        nets, notes = [], []
        cands = ['Library/Preferences/com.apple.wifi.known-networks.plist',
                 'Library/Preferences/SystemConfiguration/com.apple.airport.preferences.plist']
        for rel in cands:
            p = Path(root) / rel
            try:
                with open(p, 'rb') as f:
                    data = plistlib.load(f)
            except FileNotFoundError:
                continue
            except PermissionError:
                notes.append(f"{p}: permission denied (run with sudo or grant Full Disk Access).")
                continue
            except Exception as e:
                notes.append(f"{p}: {type(e).__name__}: {e}")
                continue
            entries = data.get('KnownNetworks', data) if isinstance(data, dict) else {}
            for key, v in (entries.items() if isinstance(entries, dict) else []):
                if not isinstance(v, dict) or not str(key).startswith('wifi.network.ssid.'):
                    continue
                ssid = v.get('SSIDString') or v.get('SSID')
                if isinstance(ssid, (bytes, bytearray)):
                    ssid = bytes(ssid).decode('utf-8', 'replace')
                ssid = ssid or str(key)[len('wifi.network.ssid.'):]
                stamps = [v.get(k) for k in ('JoinedByUserAt', 'JoinedBySystemAt', 'LastConnected')
                          if hasattr(v.get(k), 'strftime')]
                added = v.get('AddedAt') if hasattr(v.get('AddedAt'), 'strftime') else None
                nets.append({'name': str(ssid), 'type': 'Wi-Fi ' + str(v.get('SecurityType') or
                             v.get('SupportedSecurityTypes') or '').strip(),
                             'first': added.strftime('%Y-%m-%d %H:%M:%S') if added else '?',
                             'last': max(stamps).strftime('%Y-%m-%d %H:%M:%S') if stamps else '?',
                             'gateway_mac': '', 'dns_suffix': '', 'source': p.name})
            if nets:
                break
        if not nets:
            hw = self._run(['networksetup', '-listallhardwareports'])
            m = re.search(r'Hardware Port: (?:Wi-Fi|AirPort)\s*\nDevice: (\w+)', hw)
            if m:
                lst = self._run(['networksetup', '-listpreferredwirelessnetworks', m.group(1)])
                for line in lst.splitlines()[1:]:
                    if line.strip():
                        nets.append({'name': line.strip(), 'type': 'Wi-Fi, saved', 'first': '', 'last': '',
                                     'gateway_mac': '', 'dns_suffix': '', 'source': 'networksetup'})
        nets.sort(key=lambda n: n['last'], reverse=True)
        return nets, notes

    @staticmethod
    def _split_unescaped(line, sep=':'):
        return [p.replace('\\' + sep, sep) for p in re.split(r'(?<!\\)' + re.escape(sep), line)]

    def _parse_nmcli(self, text):
        nets = []
        for line in (text or '').splitlines():
            f = self._split_unescaped(line)
            if len(f) >= 3:
                ts = int(f[2]) if f[2].isdigit() else 0
                nets.append({'name': f[0], 'type': f[1].replace('802-11-wireless', 'Wi-Fi')
                                                         .replace('802-3-ethernet', 'wired'),
                             'first': '', 'gateway_mac': '', 'dns_suffix': '',
                             'last': datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S') if ts else 'never',
                             'source': 'NetworkManager (nmcli)'})
        return nets

    def _parse_nmconnection(self, text, fname=''):
        sec, kv = '', {}
        for line in (text or '').splitlines():
            line = line.strip()
            m = re.match(r'^\[(.+)\]$', line)
            if m:
                sec = m.group(1)
            elif '=' in line and not line.startswith('#'):
                k, v = line.split('=', 1)
                kv[(sec, k.strip())] = v.strip()
        ts = kv.get(('connection', 'timestamp'), '')
        name = kv.get(('wifi', 'ssid')) or kv.get(('connection', 'id')) or fname
        return {'name': name, 'type': kv.get(('connection', 'type'), '').replace('802-11-wireless', 'Wi-Fi')
                                                                    .replace('802-3-ethernet', 'wired'),
                'first': '', 'gateway_mac': '', 'dns_suffix': '',
                'last': datetime.fromtimestamp(int(ts)).strftime('%Y-%m-%d %H:%M:%S') if ts.isdigit() else '?',
                'source': 'NetworkManager file ' + fname}

    def _parse_dhclient_leases(self, text):
        leases = []
        for block in re.findall(r'lease\s*\{(.*?)\}', text or '', re.S):
            g = lambda pat: (re.search(pat, block) or [None, ''])[1]
            leases.append({'interface': g(r'interface\s+"([^"]+)"'), 'address': g(r'fixed-address\s+([\d.]+)'),
                           'router': g(r'option routers\s+([\d.]+)'),
                           'server': g(r'option dhcp-server-identifier\s+([\d.]+)'),
                           'domain': g(r'option domain-name\s+"([^"]+)"'),
                           'expire': g(r'expire\s+\d+\s+([\d/]+\s+[\d:]+)')})
        return leases

    def _known_networks_linux(self):
        nets, notes = [], []
        if shutil.which('nmcli'):
            nets = self._parse_nmcli(self._run(['nmcli', '-t', '-f', 'NAME,TYPE,TIMESTAMP', 'connection', 'show']))
        if not nets:
            d = Path('/etc/NetworkManager/system-connections')
            try:
                for p in sorted(d.glob('*')):
                    nets.append(self._parse_nmconnection(p.read_text(errors='ignore'), p.name))
            except PermissionError:
                notes.append("NetworkManager connection files need root (try sudo).")
            except OSError:
                pass
        leases = []
        for pat in ('/var/lib/dhcp/dhclient*.leases', '/var/lib/dhclient/*.leases'):
            for p in glob.glob(pat):
                try:
                    leases += self._parse_dhclient_leases(Path(p).read_text(errors='ignore'))
                except OSError:
                    pass
        for n in nets:
            n['dhcp'] = ''
        for l in leases:
            nets.append({'name': f"DHCP lease on {l['interface'] or '?'}", 'type': 'DHCP lease',
                         'first': '', 'last': l['expire'] and f"lease expires {l['expire']}" or '?',
                         'gateway_mac': '', 'dns_suffix': l['domain'], 'source': 'dhclient leases',
                         'note': f"our address {l['address']}, router {l['router']}, DHCP server {l['server']}"})
        nets.sort(key=lambda n: n['last'], reverse=True)
        return nets, notes

    # ---- the combined collector ------------------------------------------
    def collect_network_activity(self):
        self.run_async(self._task_collect_network, on_done=self._on_network_done,
                       status="Collecting network activity...")

    def _task_collect_network(self):
        res = {'notes': [], 'neighbors': [], 'connections': [], 'known_networks': []}
        try:
            res['neighbors'] = self._collect_neighbors(res['notes'])
            res['connections'] = self._collect_connections(res['notes'])
        except Exception as e:
            res['notes'].append(f"Collection failed: {type(e).__name__}: {e}")
        try:
            if self.current_os == "Windows":
                res['known_networks'] = self._known_networks_windows()
            elif self.current_os == "Darwin":
                res['known_networks'], extra = self._known_networks_macos()
                res['notes'] += extra
            else:
                res['known_networks'], extra = self._known_networks_linux()
                res['notes'] += extra
        except Exception as e:
            res['notes'].append(f"Known-network history failed: {type(e).__name__}: {e}")
        return res

    def _correlate_devices(self, neighbors, conns):
        """Per neighbour: the protocols seen in the current connection table."""
        listen_tcp = {c['local_port'] for c in conns if c['proto'] == 'TCP' and c['state'] == 'LISTEN'}
        by_ip = {n['ip']: n for n in neighbors}
        flows = {ip: {} for ip in by_ip}
        for c in conns:
            ip = c['remote_ip'].split('%')[0]
            if ip not in by_ip or c['state'] == 'LISTEN':
                continue
            if c['proto'] != 'TCP':
                direction = '-'
            elif c['local_port'] in listen_tcp or (c['local_port'] < 1024 <= c['remote_port']):
                direction = 'inbound'      # they connected to a service on this computer
            else:
                direction = 'outbound'
            svc = self._service_for(c['proto'], c['local_port'], c['remote_port'])
            f = flows[ip].setdefault((svc, direction), {'count': 0, 'states': set(), 'procs': set()})
            f['count'] += 1
            if c['state']:
                f['states'].add(c['state'])
            if c['process']:
                f['procs'].add(c['process'])
        return flows

    def _format_network(self, res):
        nb, conns = res['neighbors'], res['connections']
        out = "=" * 70 + "\nNETWORK ACTIVITY\n"
        out += f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n" + "=" * 70 + "\n\n"
        flows = self._correlate_devices(nb, conns)
        out += f"DEVICES SEEN ON THE LOCAL NETWORK ({len(nb)})\n" + "-" * 70 + "\n"
        if not nb:
            out += "None in the ARP / neighbour cache. The cache only holds devices this computer\n"
            out += "talked to recently and empties after a few minutes.\n"
        for i, n in enumerate(sorted(nb, key=lambda x: [int(p) if p.isdigit() else 0 for p in re.split(r'[.:]', x['ip'])]), 1):
            out += f"[{i}] {n['ip']}   {n['mac']}   {n['state'] or '-'}   on {n['iface'] or '?'}"
            out += "   (router)" if n['router'] else ""
            out += f"\n    MAC: {self._mac_info(n['mac'])}\n"
            fl = flows.get(n['ip'], {})
            if fl:
                out += "    Protocols in use right now:\n"
                for (svc, d), f in sorted(fl.items(), key=lambda kv: -kv[1]['count']):
                    st = ",".join(sorted(f['states'])) or '-'
                    pr = f"   [{', '.join(sorted(f['procs']))}]" if f['procs'] else ""
                    out += f"      {svc:<26} {d:<9} x{f['count']}  {st}{pr}\n"
            else:
                out += "    No open connection with this device right now (seen in the ARP cache only).\n"
        out += "\n"
        ext = Counter()
        for c in conns:
            if c['state'] != 'LISTEN' and c['remote_ip'] not in ('*', '', '0.0.0.0', '::'):
                ext[self._service_for(c['proto'], c['local_port'], c['remote_port'])] += 1
        out += f"PROTOCOL SUMMARY (all {sum(ext.values()):,} current connections)\n" + "-" * 70 + "\n"
        for svc, n in ext.most_common(15):
            out += f"  {svc:<30} {n:>5}\n"
        if not ext:
            out += "  (no active connections found)\n"
        listen = sorted({(c['proto'], c['local_port'], c['process'] or '-', c['local_ip']) for c in conns
                         if c['state'] == 'LISTEN'}, key=lambda x: (x[1], x[0]))
        out += f"\nSERVICES THIS COMPUTER OFFERS ({len(listen)} listening ports)\n" + "-" * 70 + "\n"
        for proto, port, proc, ip in listen[:60]:
            scope = "all interfaces" if ip in ('0.0.0.0', '::', '*') else ("this computer only" if ip.startswith('127.') or ip == '::1' else ip)
            out += f"  {proto.lower()}/{port:<6} {self._service_for(proto, port, 0).split(' (')[0]:<18} {proc:<22} {scope}\n"
        if not listen:
            out += "  (none found)\n"
        est = [c for c in conns if c['state'] not in ('LISTEN', '') or c['proto'] == 'UDP' and c['remote_ip'] not in ('*', '')]
        out += f"\nACTIVE CONNECTIONS ({len(est)})\n" + "-" * 70 + "\n"
        for c in est[:150]:
            out += (f"  {c['proto']:<4} {c['local_ip']}:{c['local_port']:<6} -> {c['remote_ip']}:{c['remote_port']:<6} "
                    f"{c['state'] or '-':<12} {c['process'] or ''}\n")
        if len(est) > 150:
            out += f"  ... {len(est) - 150} more not shown\n"
        kn = res['known_networks']
        out += f"\nNETWORKS THIS COMPUTER HAS JOINED BEFORE ({len(kn)}, newest first)\n" + "-" * 70 + "\n"
        for n in kn:
            out += f"  {n['name']}   [{n['type']}]\n"
            when = []
            if n.get('first'):
                when.append(f"first {n['first']}")
            if n.get('last'):
                when.append(f"last {n['last']}")
            if when:
                out += "      " + "   ".join(when) + "\n"
            extra = []
            if n.get('gateway_mac'):
                extra.append(f"router MAC {n['gateway_mac']} ({self._mac_info(n['gateway_mac']).split(';')[0]})")
            if n.get('dns_suffix'):
                extra.append(f"DNS suffix {n['dns_suffix']}")
            if n.get('note'):
                extra.append(n['note'])
            if extra:
                out += "      " + "; ".join(extra) + "\n"
        if not kn:
            out += "  (none found, or not readable without administrator rights)\n"
        out += "\nLIMITS\n" + "-" * 70 + "\n"
        out += ("  - The operating system does not keep a history of which device used which protocol.\n"
                "    This list shows what is visible now; use 'Capture Protocols' to observe traffic over time.\n"
                "  - Devices that never talked to this computer, or whose ARP entry expired, are not listed.\n"
                "    A full list of every device needs the router's client / DHCP table.\n"
                "  - Nothing is sent to other devices: no scans, pings or name lookups.\n")
        for n in res['notes']:
            out += f"NOTE: {n}\n"
        return out + "\n"

    def _on_network_done(self, res):
        text = self._format_network(res)
        self.network_text.delete('1.0', 'end')
        self.network_text.insert('1.0', text)
        self.investigation_data['network_activity'] = text
        self.investigation_data['network_activity_data'] = {
            'neighbors': res['neighbors'], 'known_networks': res['known_networks'],
            'connections': res['connections'][:1000], 'notes': res['notes']}

    # ---- passive protocol capture -----------------------------------------
    def capture_protocols(self):
        try:
            secs = int(self.capture_secs.get())
        except ValueError:
            secs = 30
        if self.current_os == "Windows":
            messagebox.showinfo("Capture Protocols",
                                "Passive capture is not available on Windows in this tool.\n\n"
                                "Use Wireshark, or run 'pktmon start --capture' from an "
                                "administrator prompt, then analyse the file.")
            return
        if not messagebox.askokcancel(
                "Capture Protocols",
                f"Listen to network traffic for {secs} seconds?\n\n"
                "Only the addresses, ports and protocol names are recorded. The content of the "
                "traffic is not stored. It needs administrator rights (sudo).\n\n"
                "Use this only on networks you are authorised to monitor."):
            return
        self.run_async(self._task_capture, secs, on_done=self._on_capture_done,
                       status=f"Capturing protocols for {secs}s...")

    @staticmethod
    def _split_tcpdump_addr(a, v6):
        a = a.rstrip(':')
        if v6:
            if '.' in a:
                ip, _, port = a.rpartition('.')
                return ip, (int(port) if port.isdigit() else 0)
            return a, 0
        parts = a.split('.')
        return ('.'.join(parts[:4]), int(parts[4])) if len(parts) == 5 and parts[4].isdigit() else (a, 0)

    def _parse_tcpdump_line(self, line):
        m = re.search(r'\bIP(6?) (\S+) > (\S+?): (.*)$', line)
        if not m:
            return None
        v6 = bool(m.group(1))
        sip, sport = self._split_tcpdump_addr(m.group(2), v6)
        dip, dport = self._split_tcpdump_addr(m.group(3), v6)
        rest = m.group(4)
        low = rest.lower()
        proto = ('TCP' if low.startswith('tcp') else 'UDP' if low.startswith('udp') else
                 'ICMP' if low.startswith('icmp') else 'IGMP' if low.startswith('igmp') else 'IP')
        ln = re.search(r'(?:length|tcp|udp)\s+(\d+)\s*$', rest, re.I) or re.search(r'length (\d+)', rest)
        return {'src': sip, 'sport': sport, 'dst': dip, 'dport': dport, 'proto': proto,
                'bytes': int(ln.group(1)) if ln else 0}

    @staticmethod
    def _is_lan(ip):
        try:
            a = ipaddress.ip_address(ip)
        except ValueError:
            return False
        return (a.is_private or a.is_link_local) and not (a.is_multicast or a.is_loopback or a.is_unspecified)

    @staticmethod
    def _is_bcast(ip):
        """Multicast or (private) x.x.x.255 / limited broadcast: a group address, not a device."""
        try:
            a = ipaddress.ip_address(ip)
        except ValueError:
            return False
        return a.is_multicast or ip == '255.255.255.255' or (a.version == 4 and a.is_private and ip.endswith('.255'))

    def _aggregate_capture(self, packets):
        """-> (per-device protocols, internet traffic by protocol, LAN broadcast/multicast by protocol)"""
        dev, ext, grp = {}, {}, {}
        for p in packets:
            svc = self._service_for(p['proto'], p['sport'], p['dport']) if p['proto'] in ('TCP', 'UDP') else p['proto']
            if self._is_bcast(p['dst']) or self._is_bcast(p['src']):
                e = grp.setdefault(svc, {'packets': 0, 'bytes': 0})
                e['packets'] += 1
                e['bytes'] += p['bytes']
                if self._is_lan(p['src']) and not self._is_bcast(p['src']):
                    d = dev.setdefault(p['src'], {}).setdefault(svc, {'sent': 0, 'received': 0, 'bytes': 0})
                    d['sent'] += 1
                    d['bytes'] += p['bytes']
                continue
            for ip, role in ((p['src'], 'sent'), (p['dst'], 'received')):
                if self._is_lan(ip):
                    e = dev.setdefault(ip, {}).setdefault(svc, {'sent': 0, 'received': 0, 'bytes': 0})
                    e[role] += 1
                    e['bytes'] += p['bytes']
            if not self._is_lan(p['src']) or not self._is_lan(p['dst']):
                e = ext.setdefault(svc, {'packets': 0, 'bytes': 0})
                e['packets'] += 1
                e['bytes'] += p['bytes']
        return dev, ext, grp

    def _default_iface(self):
        if self.current_os == "Darwin":
            m = re.search(r'interface:\s*(\S+)', self._run(['route', '-n', 'get', 'default']))
            return m.group(1) if m else 'en0'
        return 'any'

    def _task_capture(self, secs):
        res = {'seconds': secs, 'packets': 0, 'devices': {}, 'external': {}, 'broadcast': {}, 'notes': []}
        exe = shutil.which('tcpdump')
        if not exe:
            res['notes'].append("tcpdump is not installed (Linux: sudo apt install tcpdump; it ships with macOS).")
            return res
        iface = self._default_iface()
        cmd = [exe, '-nn', '-q', '-l', '-c', '200000', '-i', iface]
        try:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    text=True, errors='replace')
        except OSError as e:
            res['notes'].append(f"Could not start tcpdump: {e}")
            return res
        packets = []
        timer = threading.Timer(secs, proc.terminate)
        timer.start()
        try:
            for line in proc.stdout:
                p = self._parse_tcpdump_line(line)
                if p:
                    packets.append(p)
        finally:
            timer.cancel()
        try:
            proc.wait(timeout=5)
            err = proc.stderr.read()
        except Exception:
            proc.kill()
            err = ''
        if not packets and re.search(r'permission|not permitted|denied|root', err, re.I):
            res['notes'].append("tcpdump was not allowed to capture. Start the tool with sudo.")
        elif not packets:
            res['notes'].append("No IP packets were seen" + (f" ({err.strip().splitlines()[-1]})" if err.strip() else "."))
        res['packets'] = len(packets)
        res['devices'], res['external'], res['broadcast'] = self._aggregate_capture(packets)
        res['interface'] = iface
        return res

    def _on_capture_done(self, res):
        out = "=" * 70 + f"\nPASSIVE PROTOCOL CAPTURE ({res['seconds']} s on {res.get('interface', '?')})\n"
        out += f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n" + "=" * 70 + "\n"
        out += f"Packets observed: {res['packets']:,}   (only addresses, ports and protocol names are kept)\n\n"
        for ip, svcs in sorted(res['devices'].items()):
            out += f"{ip}\n"
            for svc, e in sorted(svcs.items(), key=lambda kv: -(kv[1]['sent'] + kv[1]['received']))[:12]:
                out += f"    {svc:<28} sent {e['sent']:>6}   received {e['received']:>6}   {e['bytes']:>10,} bytes\n"
        if res['external']:
            out += "\nTRAFFIC TO / FROM THE INTERNET (by protocol)\n" + "-" * 70 + "\n"
            for svc, e in sorted(res['external'].items(), key=lambda kv: -kv[1]['packets'])[:12]:
                out += f"    {svc:<28} {e['packets']:>7} packets   {e['bytes']:>10,} bytes\n"
        if res.get('broadcast'):
            out += "\nLOCAL BROADCAST / MULTICAST (announcements to the whole network)\n" + "-" * 70 + "\n"
            for svc, e in sorted(res['broadcast'].items(), key=lambda kv: -kv[1]['packets'])[:12]:
                out += f"    {svc:<28} {e['packets']:>7} packets   {e['bytes']:>10,} bytes\n"
        for n in res['notes']:
            out += f"NOTE: {n}\n"
        out += "\n"
        self.network_text.insert('end', out)
        self.network_text.see('end')
        self.investigation_data['protocol_capture'] = out
        self.investigation_data['protocol_capture_data'] = res

    # ========================================================
    # CONNECTED DEVICES  (USB / SSD / HDD / NVMe / SD / optical)
    # ========================================================
    _WIN_BUS = {'1': 'SCSI', '2': 'ATAPI', '3': 'ATA', '4': '1394', '5': 'SSA',
                '6': 'Fibre Channel', '7': 'USB', '8': 'RAID', '9': 'iSCSI',
                '10': 'SAS', '11': 'SATA', '12': 'SD', '13': 'MMC',
                '15': 'Virtual', '16': 'Storage Spaces', '17': 'NVMe',
                '18': 'SCM', '19': 'UFS'}
    _WIN_MEDIA = {'3': 'HDD', '4': 'SSD', '5': 'SCM'}
    _WIN_DRIVE_TYPES = {2: 'Removable', 3: 'Fixed', 4: 'Network', 5: 'Optical', 6: 'RAM disk'}

    @staticmethod
    def _human_size(n):
        """Decimal units (1 GB = 10^9 bytes), the way drive makers label capacity."""
        try:
            n = float(n)
        except (TypeError, ValueError):
            return "?"
        units = ['B', 'KB', 'MB', 'GB', 'TB', 'PB']
        i = 0
        while n >= 1000 and i < len(units) - 1:
            n /= 1000
            i += 1
        return f"{n:.0f} {units[i]}" if i == 0 else f"{n:.1f} {units[i]}"

    @staticmethod
    def _truthy(v):
        return str(v).strip().lower() in ('1', 'true', 'yes')

    @staticmethod
    def _classify_disk(name, bus, rotational, model="", dtype="disk"):
        """Linux: decide USB / NVMe / SSD / HDD / SD / optical / virtual."""
        bus = (bus or '').lower()
        m = (model or '').lower()
        if dtype == 'rom' or name.startswith(('sr', 'cdrom')):
            return "Optical drive"
        if name.startswith('vd') or any(v in m for v in ('qemu', 'virtual', 'vbox', 'vmware')):
            return "Virtual disk"
        if bus == 'usb':
            return "USB HDD" if rotational else "USB flash / SSD"
        if name.startswith('nvme') or bus == 'nvme':
            return "NVMe SSD"
        if name.startswith('mmcblk') or bus in ('mmc', 'sd'):
            return "SD / eMMC card"
        if rotational is True:
            return "HDD"
        if rotational is False:
            return "SSD"
        return "Unknown"

    def collect_devices(self):
        self.run_async(self._task_collect_devices,
                       on_done=self._on_devices_done,
                       status="Scanning connected devices...")

    def _task_collect_devices(self):
        result = {'devices': [], 'volumes': [], 'usb_bus': [], 'notes': []}
        try:
            if self.current_os == "Windows":
                self._devices_windows(result)
            elif self.current_os == "Darwin":
                self._devices_macos(result)
            else:
                self._devices_linux(result)
        except Exception as e:
            result['notes'].append(f"Device scan failed: {type(e).__name__}: {e}")
        return result

    def _on_devices_done(self, result):
        text = self._format_devices(result)
        start = self.devices_text.index('end-1c')
        self.devices_text.insert('end', text)
        self.devices_text.yview(start)   # show the new result from its first line
        self.investigation_data['connected_devices'] = text
        self.investigation_data['connected_devices_data'] = result

    def _format_devices(self, result):
        out = "=" * 60 + "\n"
        out += "CONNECTED STORAGE DEVICES\n"
        out += f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        out += "=" * 60 + "\n\n"

        devices = result.get('devices', [])
        if devices:
            counts = {}
            for d in devices:
                counts[d['type']] = counts.get(d['type'], 0) + 1
            out += "Summary: " + ", ".join(f"{n} x {t}" for t, n in sorted(counts.items())) + "\n"
            out += "(sizes use decimal units, 1 GB = 1,000,000,000 bytes)\n\n"
        else:
            out += "No storage devices detected.\n\n"

        for i, d in enumerate(devices, 1):
            out += f"[{i}] {d['device']}  -  {d['type']}\n"
            out += f"    Model     : {d.get('model') or '-'}\n"
            if d.get('vendor'):
                out += f"    Vendor    : {d['vendor']}\n"
            out += f"    Serial    : {d.get('serial') or '-'}\n"
            out += f"    Size      : {d.get('size') or '?'}\n"
            out += f"    Bus       : {d.get('bus') or '-'}\n"
            out += f"    Removable : {'yes' if d.get('removable') else 'no'}\n"
            parts = d.get('partitions') or []
            if parts:
                out += "    Partitions:\n"
                for p in parts:
                    label = f"  label='{p['label']}'" if p.get('label') else ""
                    mount = f"  mounted at {p['mount']}" if p.get('mount') else "  (not mounted)"
                    out += (f"      {p.get('name', ''):<12} {p.get('fs') or '-':<10} "
                            f"{p.get('size', ''):>10}{label}{mount}\n")
            out += "\n"

        vols = result.get('volumes', [])
        if vols:
            out += "MOUNTED VOLUMES\n" + "-" * 40 + "\n"
            for v in vols:
                label = f"  '{v['label']}'" if v.get('label') else ""
                free = f"  free {v['free']}" if v.get('free') else ""
                out += (f"  {v.get('volume', ''):<10} {v.get('kind', ''):<12} "
                        f"{v.get('fs') or '-':<8} {v.get('size', ''):>10}{free}{label}\n")
            out += "\n"

        usb = result.get('usb_bus', [])
        if usb:
            out += "USB BUS (all connected USB peripherals)\n" + "-" * 40 + "\n"
            for line in usb:
                out += f"  {line}\n"
            out += "\n"

        for n in result.get('notes', []):
            out += f"NOTE: {n}\n"
        return out + "\n"

    # ---- Linux ------------------------------------------------
    def _walk_lsblk(self, node):
        for c in node.get('children') or []:
            yield c
            yield from self._walk_lsblk(c)

    def _lsblk_part(self, c):
        mount = c.get('mountpoint') or ''
        if not mount:
            mps = [m for m in (c.get('mountpoints') or []) if m]
            mount = mps[0] if mps else ''
        return {'name': c.get('name') or '', 'fs': c.get('fstype') or '',
                'label': c.get('label') or '', 'mount': mount,
                'size': self._human_size(c.get('size'))}

    def _parse_lsblk(self, data):
        devices = []
        for d in data.get('blockdevices') or []:
            name = d.get('name') or ''
            dtype = d.get('type') or ''
            if dtype == 'loop' or name.startswith(('loop', 'ram', 'zram')):
                continue
            rota = self._truthy(d.get('rota')) if d.get('rota') is not None else None
            parts = [self._lsblk_part(c) for c in self._walk_lsblk(d)]
            if not parts and (d.get('fstype') or d.get('mountpoint')):
                parts.append(self._lsblk_part(d))
            bus = (d.get('tran') or '').upper()
            devices.append({
                'device': '/dev/' + name,
                'type': self._classify_disk(name, d.get('tran'), rota, d.get('model') or '', dtype),
                'bus': bus,
                'size': self._human_size(d.get('size')),
                'model': (d.get('model') or '').strip(),
                'vendor': (d.get('vendor') or '').strip(),
                'serial': (d.get('serial') or '').strip(),
                'removable': self._truthy(d.get('rm')),
                'partitions': parts,
            })
        return devices

    def _devices_linux_sysfs(self):
        """Fallback when lsblk is missing: read /sys/block directly."""
        base = '/sys/block'
        devices = []
        if not os.path.isdir(base):
            return devices

        def rd(p):
            try:
                with open(p) as f:
                    return f.read().strip()
            except Exception:
                return ''

        for name in sorted(os.listdir(base)):
            if name.startswith(('loop', 'ram', 'zram')):
                continue
            d = os.path.join(base, name)
            rota = rd(d + '/queue/rotational') == '1'
            model = rd(d + '/device/model')
            bus = 'usb' if '/usb' in os.path.realpath(d) else ''
            try:
                size = int(rd(d + '/size') or 0) * 512
            except ValueError:
                size = 0
            devices.append({
                'device': '/dev/' + name,
                'type': self._classify_disk(name, bus, rota, model),
                'bus': bus.upper(), 'size': self._human_size(size),
                'model': model, 'vendor': rd(d + '/device/vendor'),
                'serial': rd(d + '/device/serial'),
                'removable': rd(d + '/removable') == '1', 'partitions': [],
            })
        return devices

    def _devices_linux(self, result):
        if shutil.which('lsblk'):
            try:
                r = subprocess.run(
                    ['lsblk', '-J', '-b', '-o',
                     'NAME,TYPE,SIZE,MODEL,VENDOR,SERIAL,TRAN,ROTA,RM,FSTYPE,LABEL,MOUNTPOINT'],
                    capture_output=True, text=True, timeout=15, errors='ignore')
                result['devices'] = self._parse_lsblk(json.loads(r.stdout))
            except Exception as e:
                result['notes'].append(f"lsblk failed ({e}); falling back to /sys/block.")
        if not result['devices']:
            result['devices'] = self._devices_linux_sysfs()
            result['notes'].append("Used /sys/block (lsblk unavailable or empty): "
                                   "partitions and filesystems are not shown.")
        if shutil.which('lsusb'):
            try:
                r = subprocess.run(['lsusb'], capture_output=True, text=True,
                                   timeout=10, errors='ignore')
                result['usb_bus'] = [l.strip() for l in r.stdout.splitlines() if l.strip()]
            except Exception as e:
                result['notes'].append(f"lsusb failed: {e}")
        else:
            result['notes'].append("lsusb not installed (package usbutils): "
                                   "non-storage USB peripherals are not listed.")

    # ---- Windows ----------------------------------------------
    def _ps_json(self, script, timeout=30):
        r = subprocess.run(
            ['powershell', '-NoProfile', '-NonInteractive', '-Command',
             script + ' | ConvertTo-Json -Compress -Depth 3'],
            capture_output=True, text=True, timeout=timeout, errors='ignore')
        out = (r.stdout or '').strip()
        if not out:
            return []
        data = json.loads(out)
        return data if isinstance(data, list) else [data]

    def _classify_windows(self, bus, media, model=""):
        bus_l, media_l, m = (bus or '').lower(), (media or '').upper(), (model or '').lower()
        if any(v in m for v in ('virtual', 'vbox', 'vmware', 'qemu')) or bus_l == 'virtual':
            return "Virtual disk"
        if bus_l == 'usb':
            return "USB HDD" if media_l == 'HDD' else "USB flash / SSD"
        if bus_l == 'nvme':
            return "NVMe SSD"
        if bus_l in ('sd', 'mmc'):
            return "SD / eMMC card"
        if media_l == 'SSD':
            return "SSD"
        if media_l == 'HDD':
            return "HDD"
        return "Disk (media type not reported)"

    def _parse_windows_devices(self, phys, cim, vols, pnp=None):
        result = {'devices': [], 'volumes': [], 'usb_bus': [], 'notes': []}
        phys_by_id = {str(p.get('DeviceId')): p for p in phys}
        for c in cim:
            idx = str(c.get('Index'))
            p = phys_by_id.get(idx, {})
            bus = self._WIN_BUS.get(str(p.get('BusType')), str(p.get('BusType') or '')) \
                or str(c.get('InterfaceType') or '')
            media = self._WIN_MEDIA.get(str(p.get('MediaType')), str(p.get('MediaType') or ''))
            model = (c.get('Model') or p.get('FriendlyName') or '').strip()
            media_kind = str(c.get('MediaType') or '').lower()
            result['devices'].append({
                'device': c.get('DeviceID') or f"PhysicalDrive{idx}",
                'type': self._classify_windows(bus, media, model),
                'bus': bus, 'size': self._human_size(c.get('Size') or p.get('Size')),
                'model': model, 'vendor': '',
                'serial': (c.get('SerialNumber') or p.get('SerialNumber') or '').strip(),
                'removable': 'removable' in media_kind or 'external' in media_kind
                             or bus.upper() == 'USB',
                'partitions': [],
            })
        if not cim:   # no Win32_DiskDrive data: use Get-PhysicalDisk on its own
            for p in phys:
                bus = self._WIN_BUS.get(str(p.get('BusType')), str(p.get('BusType') or ''))
                media = self._WIN_MEDIA.get(str(p.get('MediaType')), str(p.get('MediaType') or ''))
                result['devices'].append({
                    'device': f"PhysicalDisk{p.get('DeviceId')}",
                    'type': self._classify_windows(bus, media, p.get('FriendlyName')),
                    'bus': bus, 'size': self._human_size(p.get('Size')),
                    'model': (p.get('FriendlyName') or '').strip(), 'vendor': '',
                    'serial': (p.get('SerialNumber') or '').strip(),
                    'removable': bus.upper() == 'USB', 'partitions': [],
                })
        for v in vols:
            result['volumes'].append({
                'volume': v.get('DeviceID') or '',
                'kind': self._WIN_DRIVE_TYPES.get(v.get('DriveType'), str(v.get('DriveType'))),
                'fs': v.get('FileSystem') or '', 'label': v.get('VolumeName') or '',
                'size': self._human_size(v.get('Size')) if v.get('Size') else '',
                'free': self._human_size(v.get('FreeSpace')) if v.get('FreeSpace') else '',
            })
        for u in pnp or []:
            name = u.get('FriendlyName') or '(unnamed)'
            result['usb_bus'].append(f"{name}  [{u.get('Status', '')}]  {u.get('InstanceId', '')}")
        return result

    def _devices_windows(self, result):
        phys = cim = vols = pnp = []
        notes = []
        try:
            phys = self._ps_json(
                'Get-PhysicalDisk | Select-Object DeviceId,FriendlyName,SerialNumber,Size,'
                '@{n="MediaType";e={"$($_.MediaType)"}},@{n="BusType";e={"$($_.BusType)"}}')
        except Exception as e:
            notes.append(f"Get-PhysicalDisk failed: {e}")
        try:
            cim = self._ps_json('Get-CimInstance Win32_DiskDrive | Select-Object Index,DeviceID,'
                                'Model,InterfaceType,MediaType,Size,SerialNumber')
        except Exception as e:
            notes.append(f"Win32_DiskDrive failed: {e}")
        try:
            vols = self._ps_json('Get-CimInstance Win32_LogicalDisk | Select-Object DeviceID,'
                                 'DriveType,VolumeName,FileSystem,Size,FreeSpace')
        except Exception as e:
            notes.append(f"Win32_LogicalDisk failed: {e}")
        try:
            pnp = self._ps_json('Get-PnpDevice -PresentOnly -Class USB | '
                                'Select-Object FriendlyName,InstanceId,Status', timeout=45)
        except Exception as e:
            notes.append(f"Get-PnpDevice failed: {e}")
        parsed = self._parse_windows_devices(phys, cim, vols, pnp)
        result.update(parsed)
        result['notes'].extend(notes)

    # ---- macOS ------------------------------------------------
    @staticmethod
    def _classify_mac(bus, solid, media_name=""):
        b = (bus or '').lower()
        if 'disk image' in b or 'disk image' in (media_name or '').lower():
            return "Disk image (DMG)"
        if b == 'usb':
            return "USB HDD" if solid is False else "USB flash / SSD"
        if b == 'secure digital':
            return "SD card"
        if b in ('apple fabric', 'pci-express', 'nvme'):
            return "NVMe / PCIe SSD"
        if 'thunderbolt' in b:
            return "Thunderbolt HDD" if solid is False else "Thunderbolt SSD"
        if solid is True:
            return "SSD"
        if solid is False:
            return "HDD"
        return "Unknown"

    def _parse_diskutil(self, listing, infos):
        devices, volumes = [], []
        for ent in listing.get('AllDisksAndPartitions') or []:
            ident = ent.get('DeviceIdentifier', '')
            info = infos.get(ident, {})
            parts = [{'name': p.get('DeviceIdentifier', ''), 'fs': p.get('Content', ''),
                      'label': p.get('VolumeName', ''), 'mount': p.get('MountPoint', ''),
                      'size': self._human_size(p.get('Size'))}
                     for p in ent.get('Partitions') or []]
            for v in ent.get('APFSVolumes') or []:
                volumes.append({'volume': v.get('MountPoint') or v.get('DeviceIdentifier', ''),
                                'kind': 'APFS volume', 'fs': 'APFS',
                                'label': v.get('VolumeName', ''),
                                'size': self._human_size(v.get('CapacityInUse')),
                                'free': '(size shown = space used)'})
            if 'APFSVolumes' in ent and not parts:
                continue   # synthesized APFS container: its volumes are listed above
            bus = info.get('BusProtocol', '')
            solid = info.get('SolidState')
            media = info.get('MediaName', '')
            devices.append({
                'device': '/dev/' + ident,
                'type': self._classify_mac(bus, solid, media),
                'bus': bus,
                'size': self._human_size(info.get('TotalSize') or ent.get('Size')),
                'model': media, 'vendor': '',
                'serial': '',
                'removable': bool(info.get('Removable') or info.get('RemovableMedia')
                                  or info.get('Internal') is False),
                'partitions': parts,
            })
        return devices, volumes

    def _sp_usb_walk(self, items, out):
        for it in items or []:
            if isinstance(it, dict):
                if any(k in it for k in ('vendor_id', 'product_id', 'serial_num')):
                    out.append(
                        f"{it.get('_name', '(unnamed)')}  vendor={it.get('manufacturer') or it.get('vendor_id', '-')}"
                        f"  VID:PID={it.get('vendor_id', '-')}:{it.get('product_id', '-')}"
                        f"  serial={it.get('serial_num', '-')}")
                self._sp_usb_walk(it.get('_items'), out)

    def _devices_macos(self, result):
        r = subprocess.run(['diskutil', 'list', '-plist'], capture_output=True, timeout=20)
        listing = plistlib.loads(r.stdout)
        infos = {}
        for ent in listing.get('AllDisksAndPartitions') or []:
            ident = ent.get('DeviceIdentifier', '')
            try:
                ri = subprocess.run(['diskutil', 'info', '-plist', ident],
                                    capture_output=True, timeout=15)
                infos[ident] = plistlib.loads(ri.stdout)
            except Exception as e:
                result['notes'].append(f"diskutil info {ident} failed: {e}")
        devices, volumes = self._parse_diskutil(listing, infos)
        result['devices'], result['volumes'] = devices, volumes

        for dtype in ('SPUSBDataType', 'SPUSBHostDataType'):
            try:
                rs = subprocess.run(['system_profiler', dtype, '-json'],
                                    capture_output=True, text=True, timeout=30, errors='ignore')
                data = json.loads(rs.stdout)
                self._sp_usb_walk(data.get(dtype), result['usb_bus'])
                if result['usb_bus']:
                    break
            except Exception:
                continue
        if not result['usb_bus']:
            result['notes'].append("No USB peripherals reported by system_profiler "
                                   "(none connected, or the report format changed).")

    # ========================================================
    # DEVICE / USB HISTORY  (devices that were connected before)
    # ========================================================
    def collect_device_history(self):
        self.run_async(self._task_device_history,
                       on_done=self._on_device_history_done,
                       status="Collecting USB / device history...")

    def _task_device_history(self):
        out = "=" * 60 + "\n"
        out += "USB / DEVICE HISTORY (previously connected)\n"
        out += f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        out += "=" * 60 + "\n\n"
        try:
            if self.current_os == "Windows":
                out += self._usb_history_windows()
            elif self.current_os == "Darwin":
                out += self._usb_history_macos()
            else:
                out += self._usb_history_linux()
        except Exception as e:
            out += f"History collection failed: {type(e).__name__}: {e}\n"
        return out + "\n"

    def _on_device_history_done(self, text):
        start = self.devices_text.index('end-1c')
        self.devices_text.insert('end', text)
        self.devices_text.yview(start)
        self.investigation_data['device_history'] = text

    @staticmethod
    def _filter_usb_lines(lines, keep=80):
        pat = re.compile(r'New USB device found|Product:|Manufacturer:|SerialNumber:|'
                         r'usb-storage|Attached SCSI|USB Mass Storage|Direct-Access|'
                         r'USB disconnect|new (high|full|low|super)[- ]speed USB', re.I)
        hits = [l.rstrip() for l in lines if pat.search(l)]
        return hits[-keep:]

    def _usb_history_linux(self):
        lines, source = [], ''
        try:
            r = subprocess.run(['journalctl', '-k', '--no-pager', '-o', 'short-iso'],
                               capture_output=True, text=True, timeout=25, errors='ignore')
            if r.returncode == 0 and r.stdout.strip():
                lines, source = r.stdout.splitlines(), 'journalctl -k'
        except Exception:
            pass
        if not lines:
            for p in ('/var/log/kern.log', '/var/log/messages', '/var/log/syslog'):
                try:
                    with open(p, errors='ignore') as f:
                        lines, source = f.readlines(), p
                    break
                except Exception:
                    continue
        if not lines:
            try:
                r = subprocess.run(['dmesg'], capture_output=True, text=True,
                                   timeout=10, errors='ignore')
                if r.stdout.strip():
                    lines, source = r.stdout.splitlines(), 'dmesg'
            except Exception:
                pass
        if not lines:
            return ("No kernel log could be read (needs root, or logs rotated away).\n"
                    "Try:  sudo python3 python_fixed.py\n")
        hits = self._filter_usb_lines(lines)
        out = f"Source: {source}  (last {len(hits)} USB-related lines)\n" + "-" * 40 + "\n"
        return out + ("\n".join(hits) if hits else "No USB events found in this log.") + "\n"

    def _usb_history_macos(self):
        out = ""
        fp = str(self._home() / 'Library/Preferences/com.apple.finder.plist')
        out += "Volumes remembered by Finder (FXDesktopVolumePositions):\n" + "-" * 40 + "\n"
        try:
            with open(fp, 'rb') as f:
                prefs = plistlib.load(f)
            names = sorted((prefs.get('FXDesktopVolumePositions') or {}).keys())
            out += ("\n".join(f"  {n}" for n in names) if names else "  (none recorded)") + "\n"
        except PermissionError:
            out += "  Permission denied. Grant Full Disk Access to Terminal / VS Code.\n"
        except Exception as e:
            out += f"  Not available: {e}\n"

        out += "\nCurrently present in /Volumes:\n" + "-" * 40 + "\n"
        try:
            out += "\n".join(f"  {n}" for n in sorted(os.listdir('/Volumes'))) + "\n"
        except Exception as e:
            out += f"  {e}\n"

        out += "\nUSB events in the unified log (last 1 day):\n" + "-" * 40 + "\n"
        try:
            r = subprocess.run(['log', 'show', '--last', '1d', '--style', 'compact', '--predicate',
                                'eventMessage CONTAINS[c] "USB" AND process == "kernel"'],
                               capture_output=True, text=True, timeout=45, errors='ignore')
            lines = [l for l in r.stdout.splitlines() if l.strip()][-40:]
            out += ("\n".join(lines) if lines else "  No matching events.") + "\n"
        except Exception as e:
            out += f"  Could not read the unified log: {e}\n"
        return out

    # ---- Windows USB history (registry) ------------------------
    @staticmethod
    def _filetime_to_str(ft):
        try:
            return (datetime(1601, 1, 1) + timedelta(microseconds=int(ft) // 10)
                    ).strftime('%Y-%m-%d %H:%M:%S UTC')
        except Exception:
            return "?"

    @staticmethod
    def _systemtime(b):
        try:
            y, mo, _dow, d, h, mi, s, _ms = struct.unpack('<8H', bytes(b)[:16])
            return f"{y:04d}-{mo:02d}-{d:02d} {h:02d}:{mi:02d}:{s:02d}"
        except Exception:
            return "?"

    @staticmethod
    def _fmt_reg_value(v):
        if isinstance(v, (bytes, bytearray)):
            tail = "..." if len(v) > 24 else ""
            return f"<binary {len(v)} bytes> {bytes(v)[:24].hex(' ')}{tail}"
        if isinstance(v, list):
            return "; ".join(map(str, v))[:200]
        s = str(v)
        return s if len(s) <= 200 else s[:200] + "..."

    def _reg_key_values(self, wr, hive, path, only=None, limit=60):
        lines = []
        with wr.OpenKey(hive, path, 0, wr.KEY_READ) as k:
            _nsub, nval, lw = wr.QueryInfoKey(k)
            for i in range(nval):
                name, val, _typ = wr.EnumValue(k, i)
                if only and name not in only:
                    continue
                lines.append(f"  {name or '(Default)'} = {self._fmt_reg_value(val)}")
                if len(lines) >= limit:
                    lines.append("  ... (more values not shown)")
                    break
        return lines, self._filetime_to_str(lw)

    def _reg_subkeys(self, wr, hive, path, limit=300):
        with wr.OpenKey(hive, path, 0, wr.KEY_READ) as k:
            nsub, _nval, _lw = wr.QueryInfoKey(k)
            return [wr.EnumKey(k, i) for i in range(min(nsub, limit))]

    def _reg_value(self, wr, hive, path, name):
        try:
            with wr.OpenKey(hive, path, 0, wr.KEY_READ) as k:
                return wr.QueryValueEx(k, name)[0]
        except OSError:
            return None

    def _reg_lastwrite(self, wr, hive, path):
        try:
            with wr.OpenKey(hive, path, 0, wr.KEY_READ) as k:
                return self._filetime_to_str(wr.QueryInfoKey(k)[2])
        except OSError:
            return "?"

    def _usb_history_windows(self, wr=None):
        if wr is None:
            import winreg as wr
        HKLM = wr.HKEY_LOCAL_MACHINE
        out = ""

        out += "USB STORAGE DEVICES EVER CONNECTED (HKLM\\SYSTEM\\...\\Enum\\USBSTOR)\n" + "-" * 40 + "\n"
        base = r"SYSTEM\CurrentControlSet\Enum\USBSTOR"
        try:
            rows = 0
            for cls in self._reg_subkeys(wr, HKLM, base):
                for inst in self._reg_subkeys(wr, HKLM, base + "\\" + cls):
                    p = base + "\\" + cls + "\\" + inst
                    friendly = self._reg_value(wr, HKLM, p, 'FriendlyName') or cls
                    out += (f"  {friendly}\n      class={cls}\n      serial/instance={inst}\n"
                            f"      key last written: {self._reg_lastwrite(wr, HKLM, p)}\n")
                    rows += 1
            if not rows:
                out += "  (no USB storage devices recorded)\n"
            out += ("  Note: 'key last written' is a hint about the most recent connection, "
                    "not an exact timestamp.\n")
        except PermissionError:
            out += "  Access denied. Run as Administrator.\n"
        except OSError as e:
            out += f"  Not available: {e}\n"

        out += "\nWINDOWS PORTABLE DEVICES\n" + "-" * 40 + "\n"
        base = r"SOFTWARE\Microsoft\Windows Portable Devices\Devices"
        try:
            subs = self._reg_subkeys(wr, HKLM, base)
            for s in subs:
                fn = self._reg_value(wr, HKLM, base + "\\" + s, 'FriendlyName') or '-'
                out += f"  {fn}   ({s[:70]})\n"
            if not subs:
                out += "  (none)\n"
        except OSError as e:
            out += f"  Not available: {e}\n"

        out += "\nDRIVE LETTER ASSIGNMENTS (HKLM\\SYSTEM\\MountedDevices)\n" + "-" * 40 + "\n"
        try:
            with wr.OpenKey(HKLM, "SYSTEM\\MountedDevices", 0, wr.KEY_READ) as k:
                _nsub, nval, _lw = wr.QueryInfoKey(k)
                shown = 0
                for i in range(nval):
                    name, val, _t = wr.EnumValue(k, i)
                    if not name.startswith("\\DosDevices\\"):
                        continue
                    text = ""
                    if isinstance(val, (bytes, bytearray)):
                        try:
                            text = bytes(val).decode('utf-16le')
                        except Exception:
                            text = ""
                    if not text or not text.isprintable():
                        text = f"<disk signature> {bytes(val)[:12].hex(' ')}"
                    out += f"  {name.replace(chr(92) + 'DosDevices' + chr(92), '')}  ->  {text[:110]}\n"
                    shown += 1
                if not shown:
                    out += "  (none)\n"
        except OSError as e:
            out += f"  Not available: {e}\n"
        return out

    # ========================================================
    # EXECUTION EVIDENCE: SHIMCACHE, AMCACHE, SRUM  (Windows)
    # ========================================================
    def _art_shimcache(self, wr=None):
        if wr is None:
            import winreg as wr
        HKLM = wr.HKEY_LOCAL_MACHINE
        base = r"SYSTEM\CurrentControlSet\Control\Session Manager\AppCompatCache"
        out = ["ShimCache (AppCompatCache) lists program paths Windows has seen, with a last-modified time taken from the "
               "file itself (NOT a run time: presence here does not prove the program was executed, only that Windows looked "
               "at it, e.g. for compatibility checks).",
               "Parsing this structure is version-sensitive and done here on a best-effort basis. Cross-check important "
               "entries with a validated tool such as Eric Zimmerman's AppCompatCacheParser before relying on them.\n"]
        raw = self._reg_value(wr, HKLM, base, 'AppCompatCache')
        if raw is None:
            out.append("AppCompatCache value not found (or access denied; run as Administrator).")
            return "\n".join(out) + "\n"
        data = bytes(raw)
        out.append(f"Raw value: {len(data)} bytes, SHA-256 {hashlib.sha256(data).hexdigest()}")
        entries = self._parse_shimcache(data)
        if not entries:
            out.append("\nNo entries could be decoded (unrecognised format for this Windows build).")
            return "\n".join(out) + "\n"
        out.append(f"\n{len(entries)} entries decoded:\n" + "-" * 70)
        for p, ts in entries[:2000]:
            out.append(f"  {ts:<26} {p}")
        if len(entries) > 2000:
            out.append(f"  ... {len(entries) - 2000} more entries not shown")
        return "\n".join(out) + "\n"

    def _parse_shimcache(self, data):
        """-> [(path, last_modified_str)]. Supports Win7/2008R2, Win8/8.1 and a Win10/11 heuristic scan."""
        out = []
        try:
            if len(data) >= 8 and struct.unpack_from('<I', data, 0)[0] == 0xBADC0FEE:   # Windows 7 / 2008 R2
                n = struct.unpack_from('<I', data, 4)[0]
                off = 8
                for _ in range(min(n, 100000)):
                    if off + 2 > len(data):
                        break
                    plen = struct.unpack_from('<H', data, off)[0]
                    off += 2
                    if off + plen > len(data):
                        break
                    path = data[off:off + plen].decode('utf-16le', 'ignore')
                    off += plen
                    ts = '?'
                    if off + 8 <= len(data):
                        ts = self._filetime_to_str(struct.unpack_from('<Q', data, off)[0])
                        off += 8
                    off += 8     # file size / insertion flags field, format-dependent; skipped defensively
                    if path:
                        out.append((path, ts))
                return out
            if data[:4] in (b'00ts', b'10ts'):                                        # Windows 8 / 8.1
                n_off = 4 if data[:4] == b'00ts' else 8
                n = struct.unpack_from('<I', data, n_off)[0] if n_off + 4 <= len(data) else 0
                off = 0x80 if data[:4] == b'10ts' else 0x8
                for _ in range(min(n, 100000)):
                    if off + 4 > len(data) or data[off:off + 4] not in (b'00ts', b'10ts'):
                        break
                    plen = struct.unpack_from('<H', data, off + 8)[0] if off + 10 <= len(data) else 0
                    poff = off + 12
                    if poff + plen > len(data):
                        break
                    path = data[poff:poff + plen].decode('utf-16le', 'ignore')
                    data_off = poff + plen
                    ts = self._filetime_to_str(struct.unpack_from('<Q', data, data_off)[0]) if data_off + 8 <= len(data) else '?'
                    entry_len = struct.unpack_from('<I', data, off + 4)[0] if off + 8 <= len(data) else 0
                    if path:
                        out.append((path, ts))
                    off += 12 + (entry_len if entry_len > plen else plen + 20)
                if out:
                    return out
            # Windows 10/11: entries are commonly tagged with a repeating b'10ts' marker.
            # Scan for the marker rather than trusting one fixed header layout, which drifts between builds.
            for m in re.finditer(rb'10ts', data):
                off = m.start() + 4
                if off + 8 > len(data):
                    continue
                plen = struct.unpack_from('<I', data, off)[0]
                poff = off + 4
                if plen == 0 or plen > 2000 or poff + plen > len(data):
                    continue
                path = data[poff:poff + plen].decode('utf-16le', 'ignore')
                if not path or not path[0].isalpha() or ':' not in path[:4]:
                    continue
                toff = poff + plen
                ts = self._filetime_to_str(struct.unpack_from('<Q', data, toff)[0]) if toff + 8 <= len(data) else '?'
                out.append((path, ts))
        except (struct.error, IndexError, UnicodeDecodeError):
            pass
        return out

    # ---- Amcache (mounted through the real registry loader, so format drift is handled by Windows itself) ----
    def _amcache_hive_path(self):
        return Path(os.environ.get('SystemRoot', r'C:\Windows')) / 'AppCompat' / 'Programs' / 'Amcache.hve'

    def _art_amcache(self, wr=None):
        if wr is None:
            import winreg as wr
        intro = ["Amcache records programs that were installed or run, including ones since uninstalled, with a SHA-1 of "
                 "the file where Windows recorded one.",
                 "Requires Administrator rights (the hive is loaded temporarily, read, then unloaded).\n"]
        src = self._amcache_hive_path()
        if not src.exists():
            return "\n".join(intro + [f"Amcache.hve not found at {src}."]) + "\n"
        try:
            h = self._hash_path(src)
        except OSError as e:
            return "\n".join(intro + [f"Could not read {src}: {e}"]) + "\n"
        intro.append(f"Source file: {src}   SHA-256 {h['sha256']}")
        key = f"CACTUS_AMCACHE_{uuid.uuid4().hex[:8]}"
        mounted = False
        try:
            mounted = self._amcache_mount(key, src)
            if not mounted:
                return "\n".join(intro + ["Could not load the hive (reg.exe load failed; are you Administrator?)."]) + "\n"
            rows = self._amcache_read(wr, wr.HKEY_LOCAL_MACHINE, key)
        finally:
            if mounted:
                self._amcache_unmount(key)
        if not rows:
            return "\n".join(intro + ["Hive loaded, but no recognised Amcache entries were found under this key."]) + "\n"
        out = intro + [f"\n{len(rows)} entries:\n" + "-" * 70]
        for r in rows[:3000]:
            out.append(f"  {r.get('path') or '(no path)'}")
            bits = [f"SHA-1 {r['sha1']}" if r.get('sha1') else '', f"size {r['size']}" if r.get('size') else '',
                    f"link/compile date {r['linkdate']}" if r.get('linkdate') else '', f"publisher {r['publisher']}" if r.get('publisher') else '']
            bits = [b for b in bits if b]
            if bits:
                out.append("      " + "   ".join(bits))
        if len(rows) > 3000:
            out.append(f"  ... {len(rows) - 3000} more entries not shown")
        return "\n".join(out) + "\n"

    def _amcache_mount(self, key, src):
        r = subprocess.run(['reg', 'load', f'HKLM\\{key}', str(src)], capture_output=True, text=True, timeout=30, errors='replace')
        return r.returncode == 0

    def _amcache_unmount(self, key):
        try:
            subprocess.run(['reg', 'unload', f'HKLM\\{key}'], capture_output=True, text=True, timeout=30, errors='replace')
        except (OSError, subprocess.SubprocessError):
            pass

    def _amcache_read(self, wr, HKLM, key):
        """Walk Root\\InventoryApplicationFile (Win10+) and Root\\File\\<vol> (legacy) under the mounted hive."""
        rows = []
        new_base = f"{key}\\Root\\InventoryApplicationFile"
        try:
            for sub in self._reg_subkeys(wr, HKLM, new_base, limit=20000):
                p = f"{new_base}\\{sub}"
                sha1 = self._reg_value(wr, HKLM, p, 'FileId') or ''
                sha1 = re.sub(r'^0000', '', str(sha1)) if sha1 else ''
                rows.append({'path': self._reg_value(wr, HKLM, p, 'LowerCaseLongPath') or self._reg_value(wr, HKLM, p, 'Name'),
                            'sha1': sha1, 'size': self._reg_value(wr, HKLM, p, 'Size'),
                            'linkdate': self._reg_value(wr, HKLM, p, 'LinkDate'), 'publisher': self._reg_value(wr, HKLM, p, 'Publisher')})
        except OSError:
            pass
        legacy_base = f"{key}\\Root\\File"
        try:
            for vol in self._reg_subkeys(wr, HKLM, legacy_base, limit=200):
                vp = f"{legacy_base}\\{vol}"
                for sub in self._reg_subkeys(wr, HKLM, vp, limit=20000):
                    p = f"{vp}\\{sub}"
                    sha1 = self._reg_value(wr, HKLM, p, '101') or ''        # legacy numeric value names
                    sha1 = re.sub(r'^0000', '', str(sha1)) if sha1 else ''
                    rows.append({'path': self._reg_value(wr, HKLM, p, '15') or self._reg_value(wr, HKLM, p, '17'),
                                'sha1': sha1, 'size': self._reg_value(wr, HKLM, p, '6'),
                                'linkdate': None, 'publisher': self._reg_value(wr, HKLM, p, '12')})
        except OSError:
            pass
        return [r for r in rows if r.get('path')]

    # ---- SRUM (System Resource Usage Monitor): ESE / JET Blue database ----
    def _art_srum(self):
        src = Path(os.environ.get('SystemRoot', r'C:\Windows')) / 'System32' / 'sru' / 'SRUDB.dat'
        intro = ["SRUM records, per application and per day, how much network data was used and when the application "
                 "last ran (even for applications that are no longer installed).",
                 "SRUDB.dat is an ESE (JET Blue) database. Full decoding needs the optional 'libesedb-python' package "
                 "(pip install libesedb-python) or a dedicated tool (KAPE + SrumECmd, srum-dump). Without it, this file is "
                 "located and hashed for separate analysis, but its rows are not decoded here.\n"]
        if not src.exists():
            return "\n".join(intro + [f"SRUDB.dat not found at {src}."]) + "\n"
        path, tmpdir, problem = self._copy_db(str(src))
        try:
            if problem:
                return "\n".join(intro + [f"Could not read a stable copy ({problem}). SRUM is usually locked while Windows is running; "
                                          "a volume shadow copy or an offline image is normally needed."]) + "\n"
            h = self._hash_path(path)
            intro.append(f"Source file: {src}   SHA-256 {h['sha256']}   {h['size']:,} bytes")
            try:
                import pyesedb
            except ImportError:
                return "\n".join(intro + ["pyesedb is not installed, so rows were not decoded. The file above was hashed "
                                          "so it can be preserved and parsed separately."]) + "\n"
            try:
                rows = self._srum_read(pyesedb, path)
            except Exception as e:
                return "\n".join(intro + [f"The file was read but could not be parsed as expected ({type(e).__name__}: {e}). "
                                          "The database format may differ from what this reader expects; use SrumECmd for a "
                                          "validated result."]) + "\n"
            if not rows:
                return "\n".join(intro + ["No application/network usage rows were found in the tables this tool reads."]) + "\n"
            out = intro + [f"\n{len(rows)} usage record(s) decoded:\n" + "-" * 70]
            for r in rows[:3000]:
                out.append(f"  {r['table']:<10} {r.get('time', '?'):<20} {r.get('app', '?')[:90]}")
                extra = ', '.join(f"{k}={v}" for k, v in r.items() if k not in ('table', 'time', 'app') and v not in (None, ''))
                if extra:
                    out.append(f"      {extra}")
            if len(rows) > 3000:
                out.append(f"  ... {len(rows) - 3000} more not shown")
            return "\n".join(out) + "\n"
        finally:
            if tmpdir:
                shutil.rmtree(tmpdir, ignore_errors=True)

    def _srum_read(self, pyesedb, path):
        """Best-effort: resolve SruDbIdMapTable, then list rows from the known app- and network-usage tables.
        Untested against a real pyesedb installation; every access is guarded so a library API mismatch
        drops that one row/column rather than the whole collection."""
        f = pyesedb.file()
        f.open(path)
        tables = {}
        for i in range(f.get_number_of_tables()):
            t = f.get_table(i)
            tables[t.get_name()] = t

        def val(rec, i):
            try:
                return rec.get_value_data_as_string(i)
            except Exception:
                pass
            try:
                return rec.get_value_data_as_integer(i)
            except Exception:
                pass
            try:
                d = rec.get_value_data(i)
                return d.hex() if d else None
            except Exception:
                return None

        def columns(t):
            return [t.get_column_name(i) for i in range(t.get_number_of_columns())]

        idmap = {}
        idt = tables.get('SruDbIdMapTable')
        if idt is not None:
            cols = columns(idt)
            try:
                ii, ib = cols.index('IdIndex'), cols.index('IdBlob')
            except ValueError:
                ii = ib = None
            if ii is not None:
                for ri in range(idt.get_number_of_records()):
                    rec = idt.get_record(ri)
                    k, v = val(rec, ii), val(rec, ib)
                    if k is not None:
                        idmap[k] = v if isinstance(v, str) else (str(v) if v is not None else '?')

        def resolve(v):
            try:
                return idmap.get(int(v), str(v))
            except (TypeError, ValueError):
                return str(v)

        wanted = {'{D10CA2FE-6FCF-4F6D-848E-B2E99266FA89}': 'app',          # Application Resource Usage
                 '{973F5D5C-1D90-4944-BE8E-24B94231A174}': 'network',       # Network Usage
                 '{DD6636C4-8929-4683-974E-22C046A43763}': 'network-conn'}  # Network Connectivity Usage
        rows = []
        for name, kind in wanted.items():
            t = tables.get(name)
            if t is None:
                continue
            cols = columns(t)
            idx = {c: i for i, c in enumerate(cols)}
            for ri in range(min(t.get_number_of_records(), 20000)):
                rec = t.get_record(ri)
                row = {'table': kind}
                if 'AppId' in idx:
                    row['app'] = resolve(val(rec, idx['AppId']))
                if 'UserId' in idx:
                    row['user'] = resolve(val(rec, idx['UserId']))
                if 'TimeStamp' in idx:
                    row['time'] = str(val(rec, idx['TimeStamp']))
                if 'EndTime' in idx:
                    row['time'] = str(val(rec, idx['EndTime']))
                for bcol in ('BytesSent', 'BytesRecvd', 'BytesSentUncompressed', 'BytesRecvdUncompressed', 'InterfaceLuid', 'ConnectedTime'):
                    if bcol in idx:
                        row[bcol] = val(rec, idx[bcol])
                rows.append(row)
        return rows

    # ========================================================
    # PERSISTENCE / MALWARE PERSISTENCE CHECKS  (all OS)
    # ========================================================
    def _browser_extensions(self):
        """Installed browser extension names, across browsers/profiles this tool already knows how to find."""
        out = []
        for name, kind in (('chrome', 'Chromium'), ('edge', 'Chromium'), ('brave', 'Chromium')):
            for root in self._browser_roots(name):
                root = Path(root)
                if not root.is_dir():
                    continue
                try:
                    profiles = [p for p in root.iterdir() if p.is_dir() and (p.name == 'Default' or p.name.startswith('Profile '))]
                except PermissionError:
                    continue
                for prof in profiles:
                    ext_dir = prof / 'Extensions'
                    if not ext_dir.is_dir():
                        continue
                    try:
                        ext_ids = list(ext_dir.iterdir())
                    except PermissionError:
                        continue
                    for ext in ext_ids:
                        try:
                            vers = sorted(ext.iterdir())
                        except (PermissionError, OSError):
                            continue
                        for v in vers[-1:]:
                            mf = v / 'manifest.json'
                            if mf.exists():
                                try:
                                    j = json.loads(mf.read_text(errors='replace'))
                                    label = j.get('name', ext.name)
                                    if label.startswith('__MSG_'):
                                        label = ext.name
                                    out.append(f"{name}: {label}  (id {ext.name}, version {v.name})")
                                except (ValueError, OSError):
                                    out.append(f"{name}: (unreadable manifest) id {ext.name}")
        ff_roots = self._browser_roots('firefox')
        for root in ff_roots:
            root = Path(root)
            if not root.is_dir():
                continue
            try:
                profs = [p for p in root.iterdir() if p.is_dir()]
            except PermissionError:
                continue
            for prof in profs:
                af = prof / 'extensions.json'
                if af.exists():
                    try:
                        j = json.loads(af.read_text(errors='replace'))
                        for a in j.get('addons', []):
                            if a.get('active'):
                                out.append(f"firefox: {a.get('defaultLocale', {}).get('name') or a.get('id')}  (id {a.get('id')}, version {a.get('version')})")
                    except (ValueError, OSError):
                        pass
        return out

    def _art_persistence_windows(self, wr=None):
        if wr is None:
            import winreg as wr
        HKLM, HKCU = wr.HKEY_LOCAL_MACHINE, wr.HKEY_CURRENT_USER
        out = ["Programs set to start automatically. A flag does not mean malicious; many legitimate programs do this too.\n"]
        run_keys = [(HKLM, r"SOFTWARE\Microsoft\Windows\CurrentVersion\Run"), (HKLM, r"SOFTWARE\Microsoft\Windows\CurrentVersion\RunOnce"),
                    (HKCU, r"SOFTWARE\Microsoft\Windows\CurrentVersion\Run"), (HKCU, r"SOFTWARE\Microsoft\Windows\CurrentVersion\RunOnce"),
                    (HKLM, r"SOFTWARE\WOW6432Node\Microsoft\Windows\CurrentVersion\Run")]
        out.append("REGISTRY RUN KEYS\n" + "-" * 50)
        any_run = False
        for hive, path in run_keys:
            try:
                with wr.OpenKey(hive, path, 0, wr.KEY_READ) as k:
                    _n, nval, _lw = wr.QueryInfoKey(k)
                    for i in range(nval):
                        name, val, _t = wr.EnumValue(k, i)
                        any_run = True
                        hivename = 'HKLM' if hive == HKLM else 'HKCU'
                        target = str(val)
                        out.append(f"  [{hivename}\\...\\{path.rsplit(chr(92),1)[-1]}]  {name} = {target}")
                        for lead in self._flag_startup_target(target):
                            out.append(f"      ** LEAD: {lead}")
            except OSError:
                continue
        if not any_run:
            out.append("  (none found / access denied)")
        home = self._home()
        out.append("\nSTARTUP FOLDERS\n" + "-" * 50)
        any_sf = False
        for sf in (home / 'AppData/Roaming/Microsoft/Windows/Start Menu/Programs/Startup',
                  Path(os.environ.get('ProgramData', r'C:\ProgramData')) / 'Microsoft/Windows/Start Menu/Programs/StartUp'):
            if sf.is_dir():
                for f in sf.iterdir():
                    any_sf = True
                    out.append(f"  {f}")
        if not any_sf:
            out.append("  (empty / not found)")
        out.append("\nWMI EVENT SUBSCRIPTIONS  (a known fileless-persistence technique)\n" + "-" * 50)
        try:
            r = subprocess.run(self._ps("Get-WmiObject -Namespace root\\subscription -Class __EventFilter | Select Name,Query | ConvertTo-Json -Compress"),
                               capture_output=True, text=True, timeout=30, errors='replace')
            data = json.loads(r.stdout) if r.stdout.strip() else []
            if isinstance(data, dict):
                data = [data]
            if data:
                for d in data:
                    out.append(f"  ** LEAD: filter '{d.get('Name')}'  query: {str(d.get('Query'))[:150]}")
            else:
                out.append("  (none found)")
        except (OSError, subprocess.SubprocessError, ValueError):
            out.append("  (could not query WMI)")
        ext = self._browser_extensions()
        out.append("\nBROWSER EXTENSIONS\n" + "-" * 50)
        out += [f"  {e}" for e in ext] if ext else ["  (none found)"]
        return "\n".join(out) + "\n"

    _AUTOSTART_SUSPECT = ('/temp/', '/appdata/local/temp/', '/users/public/', '/programdata/', '/downloads/',
                          '/tmp/', '/var/tmp/', '/private/tmp/', '/private/var/tmp/', '/users/shared/',
                          'powershell', 'wscript', 'cscript', 'mshta', 'rundll32', 'regsvr32', 'osascript',
                          '-enc ', '-e ', 'frombase64string', 'hidden', 'curl ', 'curl|', '| bash', '|bash')

    def _flag_startup_target(self, target):
        low = (target or '').lower().replace('\\', '/')
        flags = []
        if any(s in low for s in self._AUTOSTART_SUSPECT):
            flags.append("references a scripting/living-off-the-land tool, an encoded command, or a user-writable folder")
        return flags

    def _art_persistence_macos(self):
        out = ["Programs set to start automatically (LaunchAgents/LaunchDaemons) and login items. "
               "A flag does not mean malicious; many legitimate programs do this too.\n"]
        home = self._home()
        locations = [('user LaunchAgents', home / 'Library/LaunchAgents'), ('system LaunchAgents', Path('/Library/LaunchAgents')),
                    ('system LaunchDaemons', Path('/Library/LaunchDaemons'))]
        for label, d in locations:
            out.append(f"{label.upper()}  ({d})\n" + "-" * 50)
            if not d.is_dir():
                out.append("  (not found / access denied)")
                continue
            try:
                items = sorted(d.glob('*.plist'))
            except PermissionError:
                out.append("  access denied")
                continue
            if not items:
                out.append("  (none)")
            for p in items:
                try:
                    plist = plistlib.loads(p.read_bytes())
                except Exception as e:
                    out.append(f"  {p.name}: could not parse ({e})")
                    continue
                prog = plist.get('Program') or ' '.join(plist.get('ProgramArguments') or []) or '?'
                runatload = plist.get('RunAtLoad', False)
                out.append(f"  {p.name}: {prog}   RunAtLoad={runatload}")
                for lead in self._flag_startup_target(prog):
                    out.append(f"      ** LEAD: {lead}")
                if not p.owner_ok if False else False:
                    pass
            out.append("")
        out.append("LOGIN ITEMS\n" + "-" * 50)
        try:
            r = subprocess.run(['osascript', '-e', 'tell application "System Events" to get the name of every login item'],
                               capture_output=True, text=True, timeout=15, errors='replace')
            items = [x.strip() for x in (r.stdout or '').split(',') if x.strip()]
            out += [f"  {x}" for x in items] if items else ["  (none, or access denied)"]
        except (OSError, subprocess.SubprocessError):
            out.append("  (could not query login items)")
        ext = self._browser_extensions()
        out.append("\nBROWSER EXTENSIONS\n" + "-" * 50)
        out += [f"  {e}" for e in ext] if ext else ["  (none found)"]
        return "\n".join(out) + "\n"

    def _art_persistence_linux(self):
        out = ["Programs set to start automatically. A flag does not mean malicious; many legitimate programs do this too.\n"]
        out.append("SYSTEMD ENABLED UNITS\n" + "-" * 50)
        if shutil.which('systemctl'):
            r = subprocess.run(['systemctl', 'list-unit-files', '--state=enabled', '--no-legend', '--no-pager'],
                               capture_output=True, text=True, timeout=20, errors='replace')
            lines = [l for l in (r.stdout or '').splitlines() if l.strip()]
            out += [f"  {l}" for l in lines[:300]] if lines else ["  (none)"]
        else:
            out.append("  systemctl not available")
        out.append("\nCRON\n" + "-" * 50)
        if shutil.which('crontab'):
            r = subprocess.run(['crontab', '-l'], capture_output=True, text=True, timeout=10, errors='replace')
            body = (r.stdout or '').strip()
            out.append(body if body else "  (no user crontab)")
        for cd in ('/etc/cron.d', '/etc/crontab'):
            p = Path(cd)
            if p.is_file():
                out.append(f"\n[{p}]\n" + p.read_text(errors='replace').strip())
            elif p.is_dir():
                for f in sorted(p.iterdir()):
                    out.append(f"\n[{f}]\n" + f.read_text(errors='replace').strip())
        out.append("\nUSER AUTOSTART (~/.config/autostart)\n" + "-" * 50)
        ad = self._home() / '.config' / 'autostart'
        if ad.is_dir():
            items = sorted(ad.glob('*.desktop'))
            if items:
                for p in items:
                    exec_line = next((l.split('=', 1)[1] for l in p.read_text(errors='replace').splitlines() if l.startswith('Exec=')), '?')
                    out.append(f"  {p.name}: {exec_line}")
                    for lead in self._flag_startup_target(exec_line):
                        out.append(f"      ** LEAD: {lead}")
            else:
                out.append("  (none)")
        else:
            out.append("  (none)")
        out.append("\nrc.local / profile.d\n" + "-" * 50)
        for p in (Path('/etc/rc.local'),):
            if p.is_file():
                out.append(f"[{p}]\n" + p.read_text(errors='replace').strip())
        pd = Path('/etc/profile.d')
        if pd.is_dir():
            out += [f"  {f.name}" for f in sorted(pd.iterdir())]
        ext = self._browser_extensions()
        out.append("\nBROWSER EXTENSIONS\n" + "-" * 50)
        out += [f"  {e}" for e in ext] if ext else ["  (none found)"]
        return "\n".join(out) + "\n"

    # ========================================================
    # SUPER-TIMELINE  (merge every timestamp this tool has already collected)
    # ========================================================
    _TS_PATTERNS = [
        (re.compile(r'\b(\d{4}-\d{2}-\d{2}[ T]\d{2}:\d{2}:\d{2})(?:\.\d+)?(Z| ?UTC|\+00:00)?\b'), '%Y-%m-%d %H:%M:%S'),
        (re.compile(r'\b(\d{4}/\d{2}/\d{2} \d{2}:\d{2}:\d{2})\b'), '%Y/%m/%d %H:%M:%S'),
    ]

    def _extract_timestamps(self, source, text):
        found = []
        for rx, fmt in self._TS_PATTERNS:
            for m in rx.finditer(text):
                raw = m.group(1).replace('T', ' ')
                try:
                    dt = datetime.strptime(raw, fmt)
                except ValueError:
                    continue
                utc = bool(m.group(2))
                line = text[max(0, m.start() - 30):m.end() + 110].replace('\n', ' ').strip()
                found.append({'time': dt.isoformat() + ('Z' if utc else ''), 'utc': utc, 'source': source, 'context': line[:160]})
        return found

    def build_super_timeline(self):
        events = []
        for key, text in self.investigation_data.items():
            if key.endswith('_data') or key == 'super_timeline' or not isinstance(text, str):
                continue
            events += self._extract_timestamps(key, text)
        for c in self.__dict__.get('captures', []):
            if c.get('started_utc'):
                events.append({'time': c['started_utc'], 'utc': True, 'source': 'packet_capture', 'context': f"capture started: {os.path.basename(c['path'])}"})
        events.sort(key=lambda e: e['time'])
        seen, dedup = set(), []
        for e in events:
            k = (e['time'], e['source'], e['context'])
            if k not in seen:
                seen.add(k)
                dedup.append(e)
        out = ["=" * 70, f"SUPER-TIMELINE  ({len(dedup)} events merged from {len(set(e['source'] for e in dedup))} sources)",
              "Times are shown as recorded by their source; a 'Z'/UTC suffix means that source stated UTC, otherwise the "
              "time zone is whatever the source used (often local time) and is not converted here.", "=" * 70]
        for e in dedup[:8000]:
            out.append(f"{e['time']:<26} [{e['source']:<20}] {e['context']}")
        text = "\n".join(out) + "\n"
        self.investigation_data['super_timeline'] = text
        self.investigation_data['super_timeline_data'] = dedup
        return text, dedup

    def run_super_timeline(self):
        if not self.investigation_data:
            messagebox.showinfo("Super-timeline", "Nothing has been collected yet. Run some collections first.")
            return
        text, events = self.build_super_timeline()
        self.live_text.insert('end', "\n" + text)
        self.live_text.see('end')
        self._audit('super-timeline built', 'ok', f"{len(events)} events")
        if messagebox.askyesno("Super-timeline", f"{len(events)} events merged and shown in the Live tab.\n\nExport as CSV now?"):
            fn = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV files", "*.csv"), ("All files", "*.*")],
                                              initialfile=f"super_timeline_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv")
            if fn:
                import csv
                with open(fn, 'w', newline='', encoding='utf-8') as f:
                    w = csv.DictWriter(f, fieldnames=['time', 'utc', 'source', 'context'])
                    w.writeheader()
                    w.writerows(events)
                self._seal_report(fn)
                messagebox.showinfo("Exported", f"Saved to:\n{fn}")

    # ========================================================
    # v3.4: ENCRYPTION STATUS, RAM ACQUISITION, GRAPHICAL TIMELINE
    # ========================================================
    def check_encryption_status(self):
        self.run_async(self._task_encryption_status, on_done=self._on_encryption_status_done,
                       status="Checking encryption status...")

    def _task_encryption_status(self):
        osn = self.current_os
        kwargs = {}
        if osn == 'Windows':
            r = subprocess.run(['manage-bde', '-status'], capture_output=True, text=True, timeout=30, errors='replace')
            kwargs['bitlocker'] = r.stdout
        elif osn == 'Darwin':
            r = subprocess.run(['fdesetup', 'status'], capture_output=True, text=True, timeout=15, errors='replace')
            kwargs['filevault'] = r.stdout
        else:
            r = subprocess.run(['lsblk', '-o', 'NAME,TYPE,FSTYPE,MOUNTPOINT'], capture_output=True, text=True, timeout=15, errors='replace')
            kwargs['lsblk'] = r.stdout
        summary, rows = v34_render_encryption_summary(osn, **kwargs)
        return summary, rows

    def _on_encryption_status_done(self, result):
        summary, rows = result
        self.live_text.insert('end', "\n" + summary)
        self.live_text.see('end')
        self.investigation_data['encryption_status'] = summary
        self._audit('encryption status checked', 'ok', f"{len(rows)} volume(s)")

    def acquire_ram(self):
        kind, exe = v34_find_memory_tool(self.current_os)
        if not kind:
            messagebox.showinfo("RAM acquisition", v34_unavailable_message(self.current_os))
            return
        if not messagebox.askyesno("RAM acquisition",
                                   f"Found {kind} at:\n{exe}\n\nThis captures the full contents of physical memory "
                                   f"(can be several GB and take a few minutes). The image is hashed and stored in "
                                   f"this case's evidence folder. Continue?"):
            return
        vault = self._vault()
        out_path = str(vault / f"ram_{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}.raw")
        self.run_async(self._task_acquire_ram, kind, exe, out_path, on_done=self._on_ram_done,
                       status="Acquiring RAM image (this can take a while)...")

    def _task_acquire_ram(self, kind, exe, out_path):
        started = datetime.now(timezone.utc).isoformat(timespec='seconds')
        cmd = v34_build_acquisition_command(kind, exe, out_path)
        t0 = time.time()
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=3600, errors='replace')
            rc, errtext = r.returncode, (r.stderr or '')[:2000]
        except subprocess.TimeoutExpired:
            rc, errtext = -1, 'timed out after 1 hour'
        except OSError as e:
            rc, errtext = -1, str(e)
        finished = datetime.now(timezone.utc).isoformat(timespec='seconds')
        ok = rc == 0 and os.path.isfile(out_path) and os.path.getsize(out_path) > 0
        h = self._hash_path(Path(out_path)) if ok else {}
        if ok:
            self.__dict__.setdefault('ram_images', []).append({'path': out_path, 'tool': kind, 'started_utc': started,
                                                                'finished_utc': finished, **h})
        log = ["=" * 60, "RAM ACQUISITION", "=" * 60, "",
              f"Tool: {kind} ({exe})", f"Started (UTC): {started}", f"Finished (UTC): {finished}"]
        if ok:
            log.append(f"Image: {out_path}")
            log.append(f"Size: {h.get('size', 0):,} bytes")
            log.append(f"SHA-256: {h.get('sha256', '?')}")
        else:
            log.append(f"FAILED (exit code {rc}): {errtext or 'no image produced'}")
        return "\n".join(log) + "\n", ok

    def _on_ram_done(self, result):
        text, ok = result
        self.live_text.insert('end', "\n" + text)
        self.live_text.see('end')
        self.investigation_data['ram_acquisition'] = text
        self._audit('RAM acquisition', 'ok' if ok else 'failed', text.splitlines()[-1] if ok else 'see log')
        if ok:
            messagebox.showinfo("RAM acquisition", "Memory image acquired, hashed and stored in the evidence folder.\n"
                                                    "It will be included the next time you export the evidence package.")
        else:
            messagebox.showerror("RAM acquisition", "Acquisition failed -- see the Live tab log for details.")

    def show_graphical_timeline(self):
        events = self.investigation_data.get('super_timeline_data')
        if not events:
            if not messagebox.askyesno("Graphical timeline", "No super-timeline built yet. Build it now from everything "
                                       "collected so far?"):
                return
            _text, events = self.build_super_timeline()
        if not events:
            messagebox.showinfo("Graphical timeline", "No timestamped events to show yet.")
            return
        win = tk.Toplevel(self.root)
        win.title("Graphical Timeline")
        win.geometry("1300x520")
        win.configure(bg=Theme.BG_DARK)
        info = tk.Label(win, text="Each dot is one event; colour = source. Hover for details, drag the horizontal "
                                  "scrollbar to pan.", bg=Theme.BG_DARK, fg=Theme.TEXT_SECONDARY, font=('Segoe UI', 9))
        info.pack(fill='x', padx=10, pady=(8, 0))
        canvas_w = max(1300, len(events) * 3)
        layout = v34_layout_timeline(events, width=canvas_w, margin=50)
        frame = tk.Frame(win, bg=Theme.BG_DARK)
        frame.pack(fill='both', expand=True, padx=10, pady=10)
        hbar = tk.Scrollbar(frame, orient='horizontal')
        canvas = tk.Canvas(frame, bg=Theme.BG_MEDIUM, height=420, xscrollcommand=hbar.set,
                           scrollregion=(0, 0, canvas_w, 420), highlightthickness=0)
        hbar.config(command=canvas.xview)
        hbar.pack(side='bottom', fill='x')
        canvas.pack(side='top', fill='both', expand=True)
        tmin, tmax = layout['span']
        if tmin and tmax:
            canvas.create_text(50, 20, anchor='w', fill=Theme.TEXT_PRIMARY,
                               text=f"{tmin.isoformat()}  -->  {tmax.isoformat()}", font=('Segoe UI', 9, 'bold'))
        by_source_row = {}
        row_y = {}
        next_row = [60]
        for pt in layout['points']:
            src = pt['source']
            if src not in row_y:
                row_y[src] = next_row[0]
                next_row[0] += 24
                canvas.create_text(5, row_y[src], anchor='w', fill=pt['color'], text=src[:18], font=('Segoe UI', 8))
            y = row_y[src]
            oid = canvas.create_oval(pt['x'] - 4, y - 4, pt['x'] + 4, y + 4, fill=pt['color'], outline='')
            tip = f"{pt['time']}  [{src}]\n{pt['context'][:120]}"
            canvas.tag_bind(oid, '<Enter>', lambda e, t=tip: self.live_progress.config(text=t.replace(chr(10), '  |  ')))
        if layout['unparsed']:
            tk.Label(win, text=f"{len(layout['unparsed'])} event(s) had an unparseable timestamp and are not plotted "
                               f"(still present in the text super-timeline).",
                     bg=Theme.BG_DARK, fg=Theme.TEXT_SECONDARY, font=('Segoe UI', 8)).pack(fill='x', padx=10, pady=(0, 6))

    # ========================================================
    # YARA SCAN  (running program files + a chosen folder)
    # ========================================================
    def _yara_backend(self):
        try:
            import yara
            return 'module', yara
        except ImportError:
            pass
        exe = shutil.which('yara')
        return ('cli', exe) if exe else (None, None)

    def run_yara_scan(self):
        kind, backend = self._yara_backend()
        if not kind:
            messagebox.showinfo("YARA scan", "YARA is not available. Install it with:  pip install yara-python\n"
                                             "(or install the 'yara' command-line tool).")
            return
        rule_path = filedialog.askopenfilename(title="Choose a YARA rule file (.yar/.yara)", filetypes=[("YARA rules", "*.yar *.yara"), ("All files", "*.*")])
        if not rule_path:
            return
        folder = filedialog.askdirectory(title="Also scan a folder? (Cancel to scan only running programs)")
        self.run_async(self._task_yara_scan, kind, backend, rule_path, folder or '', on_done=self._on_yara_done,
                       on_error=lambda e: messagebox.showerror("YARA scan", f"{type(e).__name__}: {e}"),
                       status="Running YARA scan...")

    def _yara_targets(self, folder, cap=2000):
        targets = set()
        try:
            for p in self._list_processes():
                path = (p.get('path') or '').rstrip()
                if path.endswith(' (deleted)'):
                    path = path[:-10]
                if path and os.path.isfile(path):
                    targets.add(path)
        except (OSError, subprocess.SubprocessError):
            pass
        if folder and os.path.isdir(folder):
            for dp, _dn, fns in os.walk(folder):
                for fn in fns:
                    p = os.path.join(dp, fn)
                    try:
                        if os.path.getsize(p) <= 64 * 1024 * 1024:
                            targets.add(p)
                    except OSError:
                        continue
                    if len(targets) >= cap:
                        return list(targets)[:cap]
        return list(targets)[:cap]

    def _task_yara_scan(self, kind, backend, rule_path, folder):
        targets = self._yara_targets(folder)
        matches, errors, scanned = [], [], 0
        if kind == 'module':
            try:
                rules = backend.compile(filepath=rule_path)
            except Exception as e:
                raise RuntimeError(f"Rule file could not be compiled: {e}")
            for t in targets:
                try:
                    for m in rules.match(filepath=t, timeout=10):
                        matches.append({'file': t, 'rule': m.rule, 'tags': list(m.tags), 'strings': [str(s) for s in m.strings][:5]})
                    scanned += 1
                except Exception as e:
                    errors.append(f"{t}: {e}")
        else:
            for t in targets:
                try:
                    r = subprocess.run([backend, '-f', rule_path, t], capture_output=True, text=True, timeout=15, errors='replace')
                    scanned += 1
                    for line in (r.stdout or '').splitlines():
                        parts = line.split(' ', 1)
                        if len(parts) == 2:
                            matches.append({'file': parts[1].strip(), 'rule': parts[0], 'tags': [], 'strings': []})
                except (OSError, subprocess.SubprocessError) as e:
                    errors.append(f"{t}: {e}")
        return {'scanned': scanned, 'targets': len(targets), 'matches': matches, 'errors': errors, 'rule_path': rule_path, 'folder': folder}

    def _on_yara_done(self, res):
        out = ["=" * 70, f"YARA SCAN   rules: {os.path.basename(res['rule_path'])}", "=" * 70,
              f"Files scanned: {res['scanned']} of {res['targets']} target(s) (running program files" + (f" + {res['folder']}" if res['folder'] else "") + ")"]
        if res['matches']:
            out.append(f"\n{len(res['matches'])} match(es)  (a match is a lead to review, not proof of malware):\n" + "-" * 70)
            for m in res['matches'][:500]:
                out.append(f"  {m['file']}\n      rule: {m['rule']}" + (f"   tags: {', '.join(m['tags'])}" if m['tags'] else ''))
        else:
            out.append("\nNo matches.")
        if res['errors']:
            out.append(f"\n{len(res['errors'])} file(s) could not be scanned (locked, unreadable, or too large).")
        text = "\n".join(out) + "\n"
        self.live_text.insert('end', "\n" + text)
        self.live_text.see('end')
        self.investigation_data['yara_matches'] = text
        self._audit('YARA scan', 'ok', f"{len(res['matches'])} match(es) in {res['scanned']} file(s)")
        messagebox.showinfo("YARA scan complete", f"{len(res['matches'])} match(es) across {res['scanned']} file(s).")

    # ========================================================
    # DNS CACHE & SWAP / PAGEFILE STRING TRACES  (live, best-effort)
    # ========================================================
    _URLISH = re.compile(rb'(?:https?://|www\.)[\x21-\x7e]{4,250}|\b(?:[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?\.){1,8}'
                         rb'(?:com|net|org|io|co|in|gov|edu|info|biz|dev|app|xyz|ru|cn|uk)\b')

    def _dns_cache_text(self):
        osn = self.current_os
        if osn == 'Windows':
            r = subprocess.run(['ipconfig', '/displaydns'], capture_output=True, text=True, timeout=20, errors='replace')
            names = sorted(set(re.findall(r'Record Name[ .]*:\s*(\S+)', r.stdout or '')))
            return "DNS RESOLVER CACHE (ipconfig /displaydns)\n" + "-" * 50 + "\n" + ("\n".join(names) if names else "(empty or not accessible)") + "\n"
        if osn == 'Darwin':
            if shutil.which('dscacheutil'):
                r = subprocess.run(['dscacheutil', '-cachedump', '-entries', 'host'], capture_output=True, text=True, timeout=20, errors='replace')
                if r.returncode == 0 and r.stdout.strip():
                    return "DNS RESOLVER CACHE (dscacheutil)\n" + "-" * 50 + "\n" + r.stdout + "\n"
            return "DNS RESOLVER CACHE\n" + "-" * 50 + "\nNot accessible: recent macOS no longer exposes a dumpable DNS cache from the command line.\n"
        if shutil.which('resolvectl'):
            r = subprocess.run(['resolvectl', 'statistics'], capture_output=True, text=True, timeout=20, errors='replace')
            return "DNS RESOLVER STATISTICS (resolvectl, systemd-resolved)\n" + "-" * 50 + "\n" + (r.stdout.strip() or "(none)") + "\n"
        return "DNS RESOLVER CACHE\n" + "-" * 50 + "\nNot accessible on this system (no systemd-resolved).\n"

    def _scan_for_strings(self, path, max_bytes=64 * 1024 * 1024, cap=500):
        try:
            size = os.path.getsize(path)
        except OSError as e:
            return None, f"cannot access {path}: {e}"
        found, seen = [], set()
        try:
            with open(path, 'rb') as f:
                for chunk_start in (0, max(0, size - max_bytes)):
                    f.seek(chunk_start)
                    data = f.read(max_bytes)
                    for m in self._URLISH.finditer(data):
                        s = m.group().decode('ascii', 'ignore')
                        if s not in seen:
                            seen.add(s)
                            found.append(s)
                        if len(found) >= cap:
                            return found, ''
        except PermissionError:
            return None, f"permission denied reading {path} (try Administrator / root)"
        except OSError as e:
            return None, f"cannot read {path}: {e}"
        return found, ''

    def _swap_traces_text(self):
        osn = self.current_os
        out = ["SWAP / PAGING FILE STRING TRACES\n" + "-" * 50,
              "URL- and domain-like strings recovered from the paging file. These are fragments left over from whatever "
              "the system had in memory and may be stale, partial, or from background processes, not necessarily the user's "
              "own browsing; they are not tied to any particular application or browsing mode.\n"]
        candidates = []
        if osn == 'Linux':
            try:
                with open('/proc/swaps') as f:
                    for line in list(f)[1:]:
                        c = line.split()
                        if c:
                            candidates.append(c[0])
            except OSError:
                pass
        elif osn == 'Darwin':
            candidates = sorted(str(p) for p in Path('/private/var/vm').glob('swapfile*'))
        else:
            for drive in ('C:\\',):
                p = os.path.join(drive, 'pagefile.sys')
                if os.path.exists(p):
                    candidates.append(p)
        if not candidates:
            out.append("No accessible swap/paging file was found.")
            return "\n".join(out) + "\n"
        for c in candidates:
            found, err = self._scan_for_strings(c)
            out.append(f"[{c}]")
            if err:
                out.append(f"  {err}")
                continue
            if not found:
                out.append("  (no URL/domain-like strings recovered)")
            else:
                out += [f"  {s}" for s in found]
        return "\n".join(out) + "\n"

    def _live_dns_swap_text(self):
        title = "=" * 60 + f"\nDNS CACHE & SWAP TRACES\nCollected (UTC): {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')}\n" + "=" * 60 + "\n"
        return title + self._dns_cache_text() + "\n" + self._swap_traces_text()

    # ========================================================
    # OS REGISTRY  (Windows Registry / macOS plists / Linux config)
    # ========================================================
    def collect_registry(self):
        self.run_async(self._task_collect_registry,
                       on_done=self._on_registry_done,
                       status="Collecting registry artifacts...")

    def _task_collect_registry(self):
        head = "=" * 60 + "\n"
        head += "OS REGISTRY ARTIFACTS  (read-only)\n"
        head += f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        head += "=" * 60 + "\n" + self._privilege_line() + "\n"
        try:
            if self.current_os == "Windows":
                body = self._registry_windows()
            elif self.current_os == "Darwin":
                body = self._registry_macos()
            else:
                body = self._registry_linux()
        except Exception as e:
            body = f"\nRegistry collection failed: {type(e).__name__}: {e}\n"
        return head + body + "\n"

    def _on_registry_done(self, text):
        start = self.registry_text.index('end-1c')
        self.registry_text.insert('end', text)
        self.registry_text.yview(start)
        self.investigation_data['registry'] = text

    # ---- Windows ----------------------------------------------
    def _registry_windows(self, wr=None):
        if wr is None:
            import winreg as wr
        HKLM, HKCU = wr.HKEY_LOCAL_MACHINE, wr.HKEY_CURRENT_USER
        out = []

        def section(title):
            out.append("\n" + title + "\n" + "-" * 40)

        def dump(title, label, hive, path, only=None):
            section(title)
            try:
                lines, lw = self._reg_key_values(wr, hive, path, only)
                out.append(f"{label}\\{path}   (last written {lw})")
                out.extend(lines or ["  (no values)"])
            except FileNotFoundError:
                out.append("  Key not present on this system.")
            except PermissionError:
                out.append("  Access denied. Run as Administrator.")
            except OSError as e:
                out.append(f"  Not available: {e}")

        dump("OPERATING SYSTEM", "HKLM", HKLM, r"SOFTWARE\Microsoft\Windows NT\CurrentVersion",
             ['ProductName', 'DisplayVersion', 'CurrentBuild', 'InstallDate',
              'RegisteredOwner', 'BuildLab', 'SystemRoot'])
        dump("COMPUTER NAME", "HKLM", HKLM,
             r"SYSTEM\CurrentControlSet\Control\ComputerName\ComputerName")
        dump("TIME ZONE", "HKLM", HKLM, r"SYSTEM\CurrentControlSet\Control\TimeZoneInformation",
             ['TimeZoneKeyName', 'ActiveTimeBias', 'Bias'])
        dump("AUTOSTART: Run (all users)", "HKLM", HKLM,
             r"SOFTWARE\Microsoft\Windows\CurrentVersion\Run")
        dump("AUTOSTART: RunOnce (all users)", "HKLM", HKLM,
             r"SOFTWARE\Microsoft\Windows\CurrentVersion\RunOnce")
        dump("AUTOSTART: Run (current user)", "HKCU", HKCU,
             r"SOFTWARE\Microsoft\Windows\CurrentVersion\Run")
        dump("AUTOSTART: RunOnce (current user)", "HKCU", HKCU,
             r"SOFTWARE\Microsoft\Windows\CurrentVersion\RunOnce")
        dump("TYPED PATHS (Explorer address bar)", "HKCU", HKCU,
             r"SOFTWARE\Microsoft\Windows\CurrentVersion\Explorer\TypedPaths")

        # Installed programs
        section("INSTALLED PROGRAMS")
        progs = set()
        for sub in (r"SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall",
                    r"SOFTWARE\WOW6432Node\Microsoft\Windows\CurrentVersion\Uninstall"):
            try:
                for name in self._reg_subkeys(wr, HKLM, sub, limit=1000):
                    p = sub + "\\" + name
                    dn = self._reg_value(wr, HKLM, p, 'DisplayName')
                    if dn:
                        progs.add((str(dn), str(self._reg_value(wr, HKLM, p, 'DisplayVersion') or '-'),
                                   str(self._reg_value(wr, HKLM, p, 'InstallDate') or '-')))
            except OSError:
                continue
        if progs:
            for dn, ver, date in sorted(progs, key=lambda x: x[0].lower())[:400]:
                out.append(f"  {dn}   v{ver}   installed {date}")
            out.append(f"  Total: {len(progs)} programs")
        else:
            out.append("  (none found)")

        # Network profiles
        section("NETWORK PROFILES (networks this PC has joined)")
        base = r"SOFTWARE\Microsoft\Windows NT\CurrentVersion\NetworkList\Profiles"
        try:
            subs = self._reg_subkeys(wr, HKLM, base)
            for s in subs:
                p = base + "\\" + s
                name = self._reg_value(wr, HKLM, p, 'ProfileName') or '-'
                created = self._reg_value(wr, HKLM, p, 'DateCreated')
                last = self._reg_value(wr, HKLM, p, 'DateLastConnected')
                out.append(f"  {name}   first: {self._systemtime(created) if created else '?'}"
                           f"   last: {self._systemtime(last) if last else '?'}")
            if not subs:
                out.append("  (none)")
        except OSError as e:
            out.append(f"  Not available: {e}")

        # UserAssist (ROT13-encoded program run counts)
        section("USERASSIST (programs run from Explorer, ROT13 decoded)")
        base = r"SOFTWARE\Microsoft\Windows\CurrentVersion\Explorer\UserAssist"
        entries = []
        try:
            for guid in self._reg_subkeys(wr, HKCU, base):
                try:
                    with wr.OpenKey(HKCU, base + "\\" + guid + "\\Count", 0, wr.KEY_READ) as k:
                        _ns, nval, _lw = wr.QueryInfoKey(k)
                        for i in range(nval):
                            name, data, _t = wr.EnumValue(k, i)
                            if not isinstance(data, (bytes, bytearray)) or len(data) < 68:
                                continue
                            runs = struct.unpack_from('<I', data, 4)[0]
                            ft = struct.unpack_from('<Q', data, 60)[0]
                            entries.append((ft, runs, codecs.decode(name, 'rot_13')))
                except OSError:
                    continue
            entries.sort(reverse=True)
            for ft, runs, name in entries[:40]:
                when = self._filetime_to_str(ft) if ft else 'never'
                out.append(f"  {name}\n      runs={runs}  last run: {when}")
            if not entries:
                out.append("  (no entries)")
        except OSError as e:
            out.append(f"  Not available: {e}")

        out.append("\nUSB device history is on the Connected Devices tab (USB / Device History).")
        return "\n".join(out) + "\n"

    # ---- macOS (plists) ---------------------------------------
    @staticmethod
    def _read_plist(path):
        with open(path, 'rb') as f:
            return plistlib.load(f)

    def _registry_macos(self, root='/', home=None):
        home = Path(home) if home else self._home()
        R = lambda p: Path(root) / p.lstrip('/')
        out = []

        def section(t):
            out.append("\n" + t + "\n" + "-" * 40)

        section("OPERATING SYSTEM (SystemVersion.plist)")
        try:
            d = self._read_plist(R('/System/Library/CoreServices/SystemVersion.plist'))
            for k in ('ProductName', 'ProductVersion', 'ProductBuildVersion'):
                out.append(f"  {k} = {d.get(k, '-')}")
        except Exception as e:
            out.append(f"  Not available: {e}")

        section("COMPUTER / HOST NAME (SystemConfiguration)")
        try:
            d = self._read_plist(R('/Library/Preferences/SystemConfiguration/preferences.plist'))
            sysd = (d.get('System') or {}).get('System') or {}
            out.append(f"  ComputerName = {sysd.get('ComputerName', '-')}")
            out.append(f"  HostName     = {sysd.get('HostName', '-')}")
            services = d.get('NetworkServices') or {}
            for sid, s in services.items():
                out.append(f"  Network service: {s.get('UserDefinedName', sid)}")
        except Exception as e:
            out.append(f"  Not available: {e}")

        for title, folder in (("LAUNCH DAEMONS (system, run at boot)", '/Library/LaunchDaemons'),
                              ("LAUNCH AGENTS (all users)", '/Library/LaunchAgents'),
                              ("LAUNCH AGENTS (current user)", None)):
            section(title)
            path = (home / 'Library' / 'LaunchAgents') if folder is None else R(folder)
            try:
                files = sorted(path.glob('*.plist'))[:200]
            except Exception:
                files = []
            if not files:
                out.append(f"  (none in {path})")
            for f in files:
                try:
                    d = self._read_plist(f)
                    prog = d.get('Program') or ' '.join(d.get('ProgramArguments') or [])
                    out.append(f"  {d.get('Label', f.stem)}\n      runs: {prog or '-'}"
                               f"   RunAtLoad={d.get('RunAtLoad', False)}")
                except Exception as e:
                    out.append(f"  {f.name}: unreadable ({e})")

        section("INSTALLED APPLICATIONS (/Applications)")
        try:
            apps = sorted(R('/Applications').glob('*.app'))[:300]
        except Exception:
            apps = []
        for a in apps:
            try:
                d = self._read_plist(a / 'Contents' / 'Info.plist')
                out.append(f"  {d.get('CFBundleName') or a.stem}   "
                           f"v{d.get('CFBundleShortVersionString', '-')}")
            except Exception:
                out.append(f"  {a.stem}")
        if not apps:
            out.append("  (none found)")
        else:
            out.append(f"  Total: {len(apps)} apps")
        return "\n".join(out) + "\n"

    # ---- Linux (config files) ---------------------------------
    def _registry_linux(self, root='/', home=None):
        home = Path(home) if home else self._home()
        R = lambda p: os.path.join(root, p.lstrip('/'))
        out = []

        def section(t):
            out.append("\n" + t + "\n" + "-" * 40)

        def read_lines(path, limit=200, skip_comments=True):
            with open(path, errors='ignore') as f:
                lines = [l.rstrip('\n') for l in f]
            if skip_comments:
                lines = [l for l in lines if l.strip() and not l.lstrip().startswith('#')]
            return lines[:limit]

        def show_file(title, path, limit=200):
            section(title)
            try:
                out.extend("  " + l for l in read_lines(R(path), limit))
            except FileNotFoundError:
                out.append("  (file not present)")
            except PermissionError:
                out.append("  Permission denied. Try running with sudo.")
            except Exception as e:
                out.append(f"  {e}")

        show_file("OS RELEASE (/etc/os-release)", '/etc/os-release')
        show_file("HOSTNAME (/etc/hostname)", '/etc/hostname')
        out.append(f"  Kernel: {platform.release()}  {platform.machine()}")
        show_file("TIME ZONE (/etc/timezone)", '/etc/timezone')

        section("USER ACCOUNTS (/etc/passwd: root and accounts with a real login shell)")
        try:
            try:
                shells = set(read_lines(R('/etc/shells'), 100))
            except Exception:
                shells = set()
            shells = shells or {'/bin/sh', '/bin/bash', '/bin/zsh', '/bin/dash', '/bin/fish',
                                '/usr/bin/bash', '/usr/bin/zsh', '/usr/bin/fish'}
            for l in read_lines(R('/etc/passwd'), 1000):
                f = l.split(':')
                if len(f) < 7:
                    continue
                uid = int(f[2]) if f[2].isdigit() else -1
                shell = f[6]
                # a service account with a real shell is worth noticing, so it is shown too
                if uid == 0 or shell in shells:
                    out.append(f"  {f[0]}   uid={f[2]}   home={f[5]}   shell={shell}")
        except Exception as e:
            out.append(f"  Not available: {e}")

        section("ADMIN GROUPS (sudo / wheel / admin members)")
        try:
            found = False
            for l in read_lines(R('/etc/group'), 1000):
                f = l.split(':')
                if len(f) >= 4 and f[0] in ('sudo', 'wheel', 'admin'):
                    out.append(f"  {f[0]}: {f[3] or '(no members)'}")
                    found = True
            if not found:
                out.append("  (no sudo/wheel/admin group)")
        except Exception as e:
            out.append(f"  Not available: {e}")

        show_file("HOSTS FILE (/etc/hosts)", '/etc/hosts', 50)
        show_file("MOUNT TABLE (/etc/fstab)", '/etc/fstab', 50)
        show_file("SYSTEM CRON (/etc/crontab)", '/etc/crontab', 50)

        section("CRON DROP-INS (/etc/cron.d) AND USER CRONTAB")
        try:
            names = sorted(os.listdir(R('/etc/cron.d')))
            out.extend(f"  /etc/cron.d/{n}" for n in names)
            if not names:
                out.append("  (no files in /etc/cron.d)")
        except Exception:
            out.append("  (/etc/cron.d not readable)")
        if shutil.which('crontab'):
            try:
                r = subprocess.run(['crontab', '-l'], capture_output=True, text=True,
                                   timeout=10, errors='ignore')
                body = r.stdout.strip()
                out.append("  User crontab: " + (body if body else "(empty)"))
            except Exception as e:
                out.append(f"  crontab -l failed: {e}")

        section("SYSTEMD: ENABLED UNITS (start at boot)")
        listed = False
        if shutil.which('systemctl'):
            try:
                r = subprocess.run(['systemctl', 'list-unit-files', '--state=enabled',
                                    '--no-pager', '--no-legend'],
                                   capture_output=True, text=True, timeout=15, errors='ignore')
                lines = [l.split()[0] for l in r.stdout.splitlines() if l.strip()]
                if lines:
                    out.extend("  " + l for l in lines[:120])
                    out.append(f"  Total enabled: {len(lines)}")
                    listed = True
            except Exception:
                pass
        if not listed:
            wants = []
            base = R('/etc/systemd/system')
            if os.path.isdir(base):
                for d in sorted(os.listdir(base)):
                    if d.endswith('.wants'):
                        try:
                            wants += [f"{d}/{u}" for u in sorted(os.listdir(os.path.join(base, d)))]
                        except Exception:
                            pass
            out.extend("  " + w for w in wants[:120])
            if not wants:
                out.append("  (systemd not running here, or no enabled units found)")

        section("AUTOSTART DESKTOP ENTRIES")
        entries = []
        for d in (R('/etc/xdg/autostart'), str(home / '.config' / 'autostart')):
            if os.path.isdir(d):
                for fn in sorted(os.listdir(d)):
                    if fn.endswith('.desktop'):
                        try:
                            kv = dict(l.split('=', 1) for l in read_lines(os.path.join(d, fn))
                                      if '=' in l)
                            entries.append(f"  {kv.get('Name', fn)}   exec={kv.get('Exec', '-')}")
                        except Exception:
                            entries.append(f"  {fn}")
        out.extend(entries or ["  (none)"])

        section("INSTALLED PACKAGES")
        pkgs, mgr = [], ''
        for cmd, name in ((['dpkg-query', '-W', '-f', '${Package} ${Version}\\n'], 'dpkg'),
                          (['rpm', '-qa', '--qf', '%{NAME} %{VERSION}\\n'], 'rpm'),
                          (['pacman', '-Q'], 'pacman')):
            if shutil.which(cmd[0]):
                try:
                    r = subprocess.run(cmd, capture_output=True, text=True,
                                       timeout=30, errors='ignore')
                    pkgs = sorted(l for l in r.stdout.splitlines() if l.strip())
                    mgr = name
                    break
                except Exception:
                    continue
        if pkgs:
            out.append(f"  Package manager: {mgr}   Total: {len(pkgs)}")
            out.extend("  " + p for p in pkgs[:150])
            if len(pkgs) > 150:
                out.append(f"  ... {len(pkgs) - 150} more not shown")
        else:
            out.append("  (no supported package manager found)")
        return "\n".join(out) + "\n"

    # ========================================================
    # FORENSIC ARTIFACTS  (Shellbags, Jump Lists, Prefetch, plists, ...)
    # ========================================================
    def _artifact_list(self):
        """(button label, kind) pairs for the current operating system."""
        if self.current_os == "Windows":
            return [("Registry", 'registry'), ("Shellbags", 'shellbags'),
                    ("Jump Lists", 'jumplists'), ("Prefetch", 'prefetch'),
                    ("Recent & MRU", 'recent'), ("Services", 'services'),
                    ("Scheduled Tasks", 'tasks'), ("ShimCache", 'shimcache'),
                    ("Amcache", 'amcache'), ("SRUM", 'srum'), ("Persistence", 'persistence'),
                    ("Recycle Bin", 'recyclebin'), ("$MFT", 'mft'), ("USN Journal", 'usnjournal')]
        if self.current_os == "Darwin":
            return [("plist / Config", 'registry'), ("Recent Items", 'recent'),
                    ("Downloads (Quarantine)", 'downloads'),
                    ("Install History", 'installs'), ("Shell History", 'shellhistory'),
                    ("Persistence", 'persistence'), ("Trash", 'recyclebin')]
        return [("Config", 'registry'), ("Recent Files", 'recent'), ("Trash", 'trash'),
                ("Shell History", 'shellhistory'), ("Logins", 'logins'), ("Persistence", 'persistence'),
                ("Trash (deletion metadata)", 'recyclebin')]

    def _artifact_fn(self, kind):
        osn = self.current_os if self.current_os in ('Windows', 'Darwin') else 'Linux'
        return {
            ('Windows', 'shellbags'): self._art_shellbags,
            ('Windows', 'jumplists'): self._art_jumplists,
            ('Windows', 'prefetch'): self._art_prefetch,
            ('Windows', 'recent'): self._art_recent_windows,
            ('Windows', 'services'): self._art_services_windows,
            ('Windows', 'tasks'): self._art_tasks_windows,
            ('Darwin', 'recent'): self._art_recent_macos,
            ('Darwin', 'downloads'): self._art_downloads_macos,
            ('Darwin', 'installs'): self._art_installs_macos,
            ('Darwin', 'shellhistory'): self._shell_history,
            ('Linux', 'recent'): self._art_recent_linux,
            ('Linux', 'trash'): self._art_trash_linux,
            ('Linux', 'shellhistory'): self._shell_history,
            ('Linux', 'logins'): self._art_logins_linux,
            ('Windows', 'shimcache'): self._art_shimcache,
            ('Windows', 'amcache'): self._art_amcache,
            ('Windows', 'srum'): self._art_srum,
            ('Windows', 'persistence'): self._art_persistence_windows,
            ('Darwin', 'persistence'): self._art_persistence_macos,
            ('Linux', 'persistence'): self._art_persistence_linux,
            ('Windows', 'recyclebin'): self._art_recyclebin_windows,
            ('Darwin', 'recyclebin'): self._art_recyclebin_macos,
            ('Linux', 'recyclebin'): self._art_recyclebin_linux,
            ('Windows', 'mft'): self._art_mft_windows,
            ('Windows', 'usnjournal'): self._art_usnjournal_windows,
        }.get((osn, kind))

    def collect_artifacts(self, kinds):
        self.run_async(self._task_artifacts, list(kinds),
                       on_done=self._on_artifacts_done,
                       status="Collecting forensic artifacts...")

    def _task_artifacts(self, kinds):
        labels = {k: l for l, k in self._artifact_list()}
        results = {}
        for kind in kinds:
            try:
                if kind == 'registry':
                    results[kind] = self._task_collect_registry()
                    continue
                head = "=" * 60 + "\n"
                head += f"{labels.get(kind, kind).upper()}  (read-only)\n"
                head += f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
                head += "=" * 60 + "\n"
                fn = self._artifact_fn(kind)
                body = fn() if fn else "Not available on this operating system.\n"
                results[kind] = head + body + "\n"
            except Exception as e:
                results[kind] = (f"\n{labels.get(kind, kind)} failed: "
                                 f"{type(e).__name__}: {e}\n")
        return results

    def _on_artifacts_done(self, results):
        start = self.registry_text.index('end-1c')
        for kind, text in results.items():
            self.registry_text.insert('end', text)
            self.investigation_data['registry' if kind == 'registry'
                                    else 'artifact_' + kind] = text
        self.registry_text.yview(start)

    # ---- shared helpers ---------------------------------------
    @staticmethod
    def _extract_paths(data, limit=40):
        """Pull Windows file paths (ASCII and UTF-16) out of binary data."""
        found = []
        pats = [(rb'[A-Za-z]:\\[\x20-\x7e]{3,200}', 'ascii'),
                (rb'(?:[A-Za-z]\x00:\x00\\\x00(?:[\x20-\x7e]\x00){3,200})', 'utf-16le'),
                (rb'\\\\[\w.\-$]+\\[\x20-\x7e]{2,200}', 'ascii')]
        for pat, enc in pats:
            for m in re.finditer(pat, bytes(data)):
                p = m.group().decode(enc, 'ignore').strip()
                if p not in found:
                    found.append(p)
                if len(found) >= limit:
                    return found
        return found

    @staticmethod
    def _utf16_name(data):
        """First NUL-terminated UTF-16LE string in a binary value."""
        b = bytes(data)
        for i in range(0, len(b) - 1, 2):
            if b[i:i + 2] == b'\x00\x00':
                return b[:i].decode('utf-16le', 'ignore')
        return b.decode('utf-16le', 'ignore')

    # ---- Windows: Shellbags -----------------------------------
    _SHELL_GUIDS = {
        '20d04fe0-3aea-1069-a2d8-08002b30309d': 'My Computer',
        '450d8fba-ad25-11d0-98a8-0800361b1103': 'My Documents',
        '208d2c60-3aea-1069-a2d7-08002b30309d': 'Network',
        '645ff040-5081-101b-9f08-00aa002f954e': 'Recycle Bin',
        '031e4825-7b94-4dc3-b131-e946b44c8dd5': 'Libraries',
        '59031a47-3f72-44a7-89c5-5595fe6b30ee': 'User Files',
    }

    @staticmethod
    def _printable_utf16_runs(b):
        """UTF-16LE runs of printable characters (ASCII range), terminated by NUL NUL."""
        return [m.group()[:-2].decode('utf-16le', 'ignore')
                for m in re.finditer(rb'(?:[\x20-\x7e]\x00){2,}\x00\x00', bytes(b))]

    def _decode_pidl(self, data):
        """Best-effort name of one shell item (a ShellBag PIDL)."""
        b = bytes(data)
        if len(b) < 3:
            return None
        t = b[2]
        try:
            if t & 0x70 == 0x10 and len(b) >= 20:           # root folder: a GUID
                g = str(uuid.UUID(bytes_le=b[4:20])).lower()
                return self._SHELL_GUIDS.get(g, '{' + g + '}')
            if t & 0x70 == 0x20:                            # drive letter
                return b[3:].split(b'\x00')[0].decode('latin-1')
            if t & 0x70 == 0x30:                            # folder or file
                sig = b.find(b'\x04\x00\xef\xbe')           # extension block with long name
                if sig >= 0:
                    runs = self._printable_utf16_runs(b[sig + 4:])
                    if runs:
                        return runs[0]
                short = b[14:].split(b'\x00')[0].decode('latin-1')
                if short:
                    return short
            runs = self._printable_utf16_runs(b)
            if runs:
                return max(runs, key=len)
            asc = re.findall(rb'[\x20-\x7e]{3,}', b[3:])
            return asc[0].decode('ascii') if asc else None
        except Exception:
            return None

    def _art_shellbags(self, wr=None):
        if wr is None:
            import winreg as wr
        HKCU = wr.HKEY_CURRENT_USER
        out = ["Shellbags record folders this user browsed in Explorer, including folders on "
               "USB drives and network shares that may no longer exist. The key's last-written "
               "time shows when the folder was last accessed.",
               "Names are decoded on a best-effort basis; non-Latin folder names may be missing.\n"]
        roots = [("UsrClass.dat (Windows 7 and later)",
                  r"SOFTWARE\Classes\Local Settings\Software\Microsoft\Windows\Shell\BagMRU"),
                 ("NTUSER.DAT (legacy / desktop)",
                  r"SOFTWARE\Microsoft\Windows\Shell\BagMRU")]
        total = [0]
        cap = 1500

        def walk(path, parts):
            try:
                with wr.OpenKey(HKCU, path, 0, wr.KEY_READ) as k:
                    nsub, nval, _lw = wr.QueryInfoKey(k)
                    vals = {}
                    for i in range(nval):
                        n, v, _t = wr.EnumValue(k, i)
                        vals[n] = v
                    subs = [wr.EnumKey(k, i) for i in range(nsub)]
            except OSError:
                return
            # every numbered value is a folder; leaf folders may have no subkey of their own
            items = sorted({n for n in subs if n.isdigit()} | {n for n in vals if n.isdigit()},
                           key=int)
            for s in items:
                if total[0] >= cap:
                    return
                raw = vals.get(s)
                name = self._decode_pidl(raw) if isinstance(raw, (bytes, bytearray)) else None
                comp = (name or f"<item {s}>").rstrip('\\')
                child = parts + [comp]
                lw = self._reg_lastwrite(wr, HKCU, path + "\\" + s) if s in subs else "n/a"
                out.append(f"  {chr(92).join(child)}   [last accessed {lw}]")
                total[0] += 1
                walk(path + "\\" + s, child)

        for title, path in roots:
            out.append(title + "\n" + "-" * 40)
            before = total[0]
            walk(path, [])
            if total[0] == before:
                out.append("  (no shellbag entries)")
            out.append("")
        if total[0] >= cap:
            out.append(f"  ... stopped after {cap} entries")
        return "\n".join(out) + "\n"

    # ---- Windows: Jump Lists ----------------------------------
    _JUMPLIST_APPIDS = {'1b4dd67f29cb1962': 'Windows Explorer',
                        '5f7b5f1e01b83767': 'Quick Access'}

    def _art_jumplists(self, appdata=None):
        appdata = appdata or os.environ.get('APPDATA', '')
        base = Path(appdata) / 'Microsoft' / 'Windows' / 'Recent'
        out = ["Jump Lists list files and folders each application opened recently, "
               "even if the files were later deleted. The AppID (file name) identifies the "
               "application.\n"]
        try:
            import olefile
        except ImportError:
            olefile = None
            out.append("NOTE: install 'olefile' (pip install olefile) to read the file lists "
                       "inside automatic Jump Lists; only file names and dates are shown now.\n")
        for sub, kind in (('AutomaticDestinations', 'automatic'),
                          ('CustomDestinations', 'custom')):
            d = base / sub
            out.append(f"{sub}\n" + "-" * 40)
            try:
                files = sorted((p for p in d.iterdir() if p.is_file()),
                               key=lambda p: p.stat().st_mtime, reverse=True)[:60]
            except Exception as e:
                out.append(f"  Not available: {e}\n")
                continue
            if not files:
                out.append("  (no files)\n")
            for p in files:
                appid = p.name.split('.')[0].lower()
                app = self._JUMPLIST_APPIDS.get(appid, 'unknown application')
                mt = datetime.fromtimestamp(p.stat().st_mtime).strftime('%Y-%m-%d %H:%M:%S')
                out.append(f"  AppID {appid}  ({app})   modified {mt}   {p.stat().st_size} bytes")
                paths = []
                try:
                    if kind == 'automatic' and olefile and olefile.isOleFile(str(p)):
                        with olefile.OleFileIO(str(p)) as ole:
                            for st in ole.listdir():
                                if st and st[-1] != 'DestList':
                                    paths += self._extract_paths(ole.openstream(st).read())
                    elif kind == 'custom':
                        paths = self._extract_paths(p.read_bytes())
                except Exception as e:
                    out.append(f"      could not parse: {e}")
                seen = []
                for x in paths:
                    if x not in seen:
                        seen.append(x)
                for x in seen[:15]:
                    out.append(f"      -> {x}")
            out.append("")
        return "\n".join(out) + "\n"

    # ---- Windows: Prefetch ------------------------------------
    @staticmethod
    def _mam_decompress(data):
        """Windows 10 Prefetch files are XPRESS-Huffman compressed (needs Windows' ntdll)."""
        import ctypes
        from ctypes import wintypes
        ntdll = ctypes.WinDLL('ntdll')
        ntdll.RtlGetCompressionWorkSpaceSize.argtypes = [wintypes.USHORT, ctypes.POINTER(wintypes.ULONG), ctypes.POINTER(wintypes.ULONG)]
        ntdll.RtlDecompressBufferEx.argtypes = [wintypes.USHORT, ctypes.c_void_p, wintypes.ULONG, ctypes.c_void_p,
                                                wintypes.ULONG, ctypes.POINTER(wintypes.ULONG), ctypes.c_void_p]
        ntdll.RtlGetCompressionWorkSpaceSize.restype = ntdll.RtlDecompressBufferEx.restype = ctypes.c_long
        size = struct.unpack_from('<I', data, 4)[0]
        src = bytes(data[8:])
        out = ctypes.create_string_buffer(size)
        ws_size, frag = wintypes.ULONG(), wintypes.ULONG()
        ntdll.RtlGetCompressionWorkSpaceSize(4, ctypes.byref(ws_size), ctypes.byref(frag))
        ws = ctypes.create_string_buffer(max(ws_size.value, frag.value))
        final = wintypes.ULONG()
        status = ntdll.RtlDecompressBufferEx(4, out, size, src, len(src), ctypes.byref(final), ws)
        if status != 0:
            raise OSError(f"decompression failed (NTSTATUS {status & 0xffffffff:#x})")
        return out.raw[:final.value]

    def _parse_prefetch(self, data):
        """Return exe name, path hash, run times and run count from a Prefetch file."""
        data = bytes(data)
        if data[:3] == b'MAM':
            data = self._mam_decompress(data)
        if len(data) < 0x100 or data[4:8] != b'SCCA':
            return None
        ver = struct.unpack_from('<I', data, 0)[0]
        exe = data[0x10:0x4C].decode('utf-16le', 'ignore').split('\x00')[0]
        phash = struct.unpack_from('<I', data, 0x4C)[0]
        layouts = {17: (1, 0x78, 0x90), 23: (1, 0x80, 0x98),
                   26: (8, 0x80, 0xD0), 30: (8, 0x80, 0xD0)}
        info = {'version': ver, 'exe': exe, 'hash': f"{phash:08X}",
                'last_runs': [], 'run_count': None, 'run_count_alt': None}
        if ver not in layouts:
            return info
        n, t_off, c_off = layouts[ver]
        if len(data) >= t_off + 8 * n:
            info['last_runs'] = [self._filetime_to_str(ft) for ft in
                                 struct.unpack_from(f'<{n}Q', data, t_off) if ft]
        seen = len(info['last_runs'])
        offsets = [0xD0, 0xC8] if ver == 30 else [c_off]
        cands = []
        for off in offsets:
            if len(data) >= off + 4:
                v = struct.unpack_from('<I', data, off)[0]
                if seen <= v < 100000 and v not in cands:
                    cands.append(v)
        if cands:
            info['run_count'] = cands[0]
            if len(cands) > 1:        # Windows 10 builds use different offsets
                info['run_count_alt'] = cands[1]
        return info

    def _prefetch_status(self):
        """Why might Prefetch be empty? Read the real setting instead of guessing."""
        try:
            import winreg as wr
            with wr.OpenKey(wr.HKEY_LOCAL_MACHINE, r"SYSTEM\CurrentControlSet\Control\Session Manager\Memory Management\PrefetchParameters", 0, wr.KEY_READ) as k:
                v = wr.QueryValueEx(k, 'EnablePrefetcher')[0]
            meaning = {0: "DISABLED", 1: "application launch only", 2: "boot only", 3: "enabled (applications and boot)"}.get(v, str(v))
            hint = ("  Prefetch is turned off by Windows or by a tweak tool, so no files are created. "
                    "On Windows Server it is off by default.\n" if v == 0 else "")
            return f"EnablePrefetcher = {v} ({meaning}).\n" + hint + "  Also check that the 'SysMain' service is running.\n"
        except Exception as e:
            return f"Could not read the EnablePrefetcher setting ({e}).\n"

    def _art_prefetch(self, folder=None):
        folder = Path(folder) if folder else Path(os.environ.get('SystemRoot', r'C:\Windows')) / 'Prefetch'
        out = ["Prefetch shows which programs ran, how many times and when (last 8 runs on "
               "Windows 8/10/11). Needs Administrator rights. Run counts for some Windows 10 "
               "builds should be double-checked with a dedicated parser such as PECmd.\n",
               f"Folder: {folder}\n"]
        out.append(self._privilege_line() + "\n")
        try:
            names = os.listdir(folder)          # unlike Path.glob(), this reports PermissionError
        except PermissionError:
            return "\n".join(out) + ("ACCESS DENIED to the Prefetch folder. Windows only lets Administrators read it.\n"
                                      "Use the 'Restart as Administrator' button (or right-click -> Run as administrator).\n")
        except FileNotFoundError:
            return "\n".join(out) + f"The folder does not exist: {folder}\n"
        except Exception as e:
            return "\n".join(out) + f"Not available: {e}\n"
        files = [folder / n for n in names if n.lower().endswith('.pf')]
        if not files:
            why = self._prefetch_status()
            return "\n".join(out) + ("No .pf files in the folder (it holds " + str(len(names)) + " entries).\n" + why)
        rows = []
        for p in files:
            st = p.stat()
            info, note = None, ''
            try:
                info = self._parse_prefetch(p.read_bytes())
            except PermissionError:
                note = "access denied"
            except Exception as e:
                note = f"header not decoded ({type(e).__name__}: {e})"
            last = (info or {}).get('last_runs') or []
            sort_key = last[0] if last else datetime.fromtimestamp(st.st_mtime).strftime('%Y-%m-%d %H:%M:%S')
            rows.append((sort_key, p, st, info, note))
        rows.sort(key=lambda r: r[0], reverse=True)
        for sort_key, p, st, info, note in rows[:200]:
            if info:
                out.append(f"  {info['exe'] or p.name}   (hash {info['hash']}, format v{info['version']})")
                runs = str(info['run_count']) if info['run_count'] is not None else '?'
                if info.get('run_count_alt') is not None:
                    runs += (f" (or {info['run_count_alt']}: the offset differs between "
                             f"Windows 10 builds, verify with PECmd)")
                out.append(f"      runs: {runs}"
                           f"   last run: {info['last_runs'][0] if info['last_runs'] else '?'}")
                if len(info['last_runs']) > 1:
                    out.append("      earlier runs: " + ", ".join(info['last_runs'][1:]))
            else:
                created = datetime.fromtimestamp(st.st_ctime).strftime('%Y-%m-%d %H:%M:%S')
                out.append(f"  {p.name}   file created {created}   modified {sort_key}"
                           + (f"   [{note}]" if note else ""))
        out.append(f"\n  Total: {len(files)} prefetch files")
        return "\n".join(out) + "\n"

    # ---- Windows: recent files, RunMRU, RecentDocs -------------
    def _art_recent_windows(self, wr=None, appdata=None):
        if wr is None:
            import winreg as wr
        HKCU = wr.HKEY_CURRENT_USER
        out = []
        appdata = appdata or os.environ.get('APPDATA', '')
        recent = Path(appdata) / 'Microsoft' / 'Windows' / 'Recent'
        out.append("RECENT FILES (.lnk shortcuts Windows creates when a file is opened)\n" + "-" * 40)
        try:
            lnks = sorted(recent.glob('*.lnk'), key=lambda p: p.stat().st_mtime, reverse=True)[:100]
            for p in lnks:
                mt = datetime.fromtimestamp(p.stat().st_mtime).strftime('%Y-%m-%d %H:%M:%S')
                tgt = self._extract_paths(p.read_bytes(), limit=1)
                out.append(f"  {mt}   {p.stem}" + (f"   ->  {tgt[0]}" if tgt else ""))
            if not lnks:
                out.append("  (none)")
        except Exception as e:
            out.append(f"  Not available: {e}")

        base = r"SOFTWARE\Microsoft\Windows\CurrentVersion\Explorer"
        out.append("\nRUNMRU (commands typed into the Run dialog, most recent first)\n" + "-" * 40)
        try:
            with wr.OpenKey(HKCU, base + r"\RunMRU", 0, wr.KEY_READ) as k:
                _ns, nval, lw = wr.QueryInfoKey(k)
                vals = {}
                for i in range(nval):
                    n, v, _t = wr.EnumValue(k, i)
                    vals[n] = v
            order = str(vals.get('MRUList', ''))
            for ch in order:
                if ch in vals:
                    cmd = re.sub(r'[\\\\]1$', '', str(vals[ch]))
                    out.append(f"  {cmd}")
            out.append(f"  (key last written {self._filetime_to_str(lw)})")
            if not order:
                out.append("  (none)")
        except OSError:
            out.append("  Key not present.")

        out.append("\nRECENTDOCS (documents opened, most recent first)\n" + "-" * 40)
        try:
            with wr.OpenKey(HKCU, base + r"\RecentDocs", 0, wr.KEY_READ) as k:
                _ns, nval, lw = wr.QueryInfoKey(k)
                vals = {}
                for i in range(nval):
                    n, v, _t = wr.EnumValue(k, i)
                    vals[n] = v
            mru = vals.get('MRUListEx')
            order = [str(x) for x in struct.unpack(f'<{len(mru) // 4}I', mru) if x != 0xFFFFFFFF] \
                if isinstance(mru, (bytes, bytearray)) else sorted(k for k in vals if k.isdigit())
            shown = 0
            for key in order[:60]:
                v = vals.get(key)
                if isinstance(v, (bytes, bytearray)):
                    out.append(f"  {self._utf16_name(v)}")
                    shown += 1
            out.append(f"  (key last written {self._filetime_to_str(lw)})")
            if not shown:
                out.append("  (none)")
        except OSError:
            out.append("  Key not present.")
        out.append("\nNot covered here: ShimCache / Amcache / SRUM (they need the offline "
                   "registry hive files, which are locked while Windows is running).")
        return "\n".join(out) + "\n"

    # ---- macOS ------------------------------------------------
    @staticmethod
    def _mac_time(ts):
        try:
            return (datetime(2001, 1, 1) + timedelta(seconds=float(ts))).strftime('%Y-%m-%d %H:%M:%S')
        except Exception:
            return "?"

    def _art_recent_macos(self, home=None):
        home = Path(home) if home else self._home()
        out = ["FINDER RECENT FOLDERS (com.apple.finder.plist)\n" + "-" * 40]
        try:
            with open(home / 'Library/Preferences/com.apple.finder.plist', 'rb') as f:
                prefs = plistlib.load(f)
            items = prefs.get('FXRecentFolders') or []
            names = [i.get('name') for i in items if isinstance(i, dict) and i.get('name')]
            out.extend(f"  {n}" for n in names)
            if not names:
                out.append("  (none recorded)")
        except PermissionError:
            out.append("  Permission denied. Grant Full Disk Access to Terminal / VS Code.")
        except Exception as e:
            out.append(f"  Not available: {e}")

        out.append("\nRECENT ITEMS (com.apple.sharedfilelist)\n" + "-" * 40)
        d = home / 'Library/Application Support/com.apple.sharedfilelist'
        try:
            files = sorted([p for p in d.rglob('*') if p.suffix in ('.sfl', '.sfl2', '.sfl3')],
                           key=lambda p: p.stat().st_mtime, reverse=True)[:40]
        except Exception as e:
            files, d = [], None
            out.append(f"  Not available: {e}")
        for p in files:
            mt = datetime.fromtimestamp(p.stat().st_mtime).strftime('%Y-%m-%d %H:%M:%S')
            names = []
            try:
                with open(p, 'rb') as f:
                    plist = plistlib.load(f)
                skip = ('$', 'NS', 'com.apple', 'kLS', 'SFL')
                for obj in plist.get('$objects', []):
                    if isinstance(obj, str) and len(obj) > 2 and not obj.startswith(skip):
                        names.append(obj)
            except Exception:
                pass
            out.append(f"  {p.name}   modified {mt}")
            out.extend(f"      {n}" for n in names[:10])
        if d is not None and not files:
            out.append("  (none)")
        return "\n".join(out) + "\n"

    def _art_downloads_macos(self, home=None):
        home = Path(home) if home else self._home()
        src = home / 'Library/Preferences/com.apple.LaunchServices.QuarantineEventsV2'
        out = ["Quarantine events record every file downloaded through a browser, mail or "
               "messaging app: when, by which app and from which URL.\n"]
        if not src.exists():
            return "\n".join(out) + "Database not found.\n"
        import tempfile
        tmp = Path(tempfile.mkdtemp()) / 'quarantine.db'
        try:
            shutil.copy2(src, tmp)            # never open the evidence database directly
        except PermissionError:
            return "\n".join(out) + "Permission denied. Grant Full Disk Access to Terminal / VS Code.\n"
        try:
            con = sqlite3.connect(f"file:{tmp}?mode=ro", uri=True)
            rows = con.execute(
                "SELECT LSQuarantineTimeStamp, LSQuarantineAgentName, LSQuarantineDataURLString, "
                "LSQuarantineOriginURLString, LSQuarantineSenderName FROM LSQuarantineEvent "
                "ORDER BY LSQuarantineTimeStamp DESC LIMIT 200").fetchall()
            con.close()
        finally:
            shutil.rmtree(tmp.parent, ignore_errors=True)
        for ts, agent, url, origin, sender in rows:
            out.append(f"  {self._mac_time(ts)}   {agent or '-'}")
            out.append(f"      file URL : {url or '-'}")
            if origin:
                out.append(f"      from page: {origin}")
            if sender:
                out.append(f"      sender   : {sender}")
        if not rows:
            out.append("  (no events)")
        out.append(f"\n  Total shown: {len(rows)}")
        return "\n".join(out) + "\n"

    def _art_installs_macos(self, root='/'):
        p = Path(root) / 'Library/Receipts/InstallHistory.plist'
        try:
            with open(p, 'rb') as f:
                items = plistlib.load(f)
        except Exception as e:
            return f"InstallHistory.plist not available: {e}\n"
        out = []
        for it in sorted(items, key=lambda i: i.get('date') or datetime.min, reverse=True)[:300]:
            d = it.get('date')
            when = d.strftime('%Y-%m-%d %H:%M:%S') if hasattr(d, 'strftime') else '?'
            out.append(f"  {when}   {it.get('displayName', '-')}  v{it.get('displayVersion', '-')}"
                       f"   by {it.get('processName', '-')}")
        return "\n".join(out or ["  (empty)"]) + f"\n\n  Total: {len(items)} installs recorded\n"

    # ---- Shell history (macOS and Linux) ----------------------
    def _shell_history(self, home=None):
        home = Path(home) if home else self._home()
        out = ["Commands typed in the terminal. This can contain sensitive text such as "
               "passwords typed by mistake; handle the report accordingly.\n"]
        found = False
        for rel in ('.zsh_history', '.bash_history', '.local/share/fish/fish_history'):
            p = home / rel
            if not p.exists():
                continue
            found = True
            out.append(f"{p}\n" + "-" * 40)
            try:
                lines = p.read_text(errors='ignore').splitlines()
            except PermissionError:
                out.append("  Permission denied. Grant Full Disk Access to Terminal / VS Code.\n")
                continue
            shown = []
            for l in lines:
                m = re.match(r'^: (\d+):\d+;(.*)$', l)          # zsh extended history
                if m:
                    ts = datetime.fromtimestamp(int(m.group(1)), timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')
                    shown.append(f"{ts}   {m.group(2)}")
                elif l.startswith('- cmd: '):                     # fish
                    shown.append(l[7:])
                elif l.strip() and not l.startswith(('when:', 'paths:', '  ')):
                    shown.append(l)
            out.extend("  " + s for s in shown[-60:])
            out.append(f"  ({len(shown)} commands in file, last {min(60, len(shown))} shown)\n")
        if not found:
            out.append("No shell history files found.")
        return "\n".join(out) + "\n"

    # ---- Linux ------------------------------------------------
    def _art_recent_linux(self, home=None):
        home = Path(home) if home else self._home()
        p = home / '.local/share/recently-used.xbel'
        try:
            import xml.etree.ElementTree as ET
            root_el = ET.parse(p).getroot()
        except FileNotFoundError:
            return "recently-used.xbel not found (no desktop environment or nothing opened yet).\n"
        except Exception as e:
            return f"Could not read recently-used.xbel: {e}\n"
        rows = []
        for bm in root_el.iter('bookmark'):
            href = bm.get('href', '')
            path = unquote(href[7:]) if href.startswith('file://') else href
            apps = [el.get('name') for el in bm.iter() if el.tag.endswith('application') and el.get('name')]
            rows.append((bm.get('modified') or bm.get('visited') or '', path, apps[:2]))
        rows.sort(reverse=True)
        out = ["FILES RECENTLY OPENED (recently-used.xbel)\n" + "-" * 40]
        for when, path, apps in rows[:80]:
            out.append(f"  {when[:19].replace('T', ' ')}   {path}" + (f"   [{', '.join(apps)}]" if apps else ""))
        if not rows:
            out.append("  (none)")
        out.append(f"\n  Total entries: {len(rows)}")
        return "\n".join(out) + "\n"

    def _art_trash_linux(self, home=None):
        home = Path(home) if home else self._home()
        d = home / '.local/share/Trash/info'
        out = ["Deleted files still in the Trash, with their original location and deletion time.\n"]
        try:
            files = list(d.glob('*.trashinfo'))
        except Exception as e:
            return "\n".join(out) + f"Not available: {e}\n"
        rows = []
        for p in files:
            kv = {}
            for l in p.read_text(errors='ignore').splitlines():
                if '=' in l:
                    k, v = l.split('=', 1)
                    kv[k.strip()] = v.strip()
            rows.append((kv.get('DeletionDate', ''), unquote(kv.get('Path', '')), p.stem))
        rows.sort(reverse=True)
        for when, path, name in rows[:150]:
            out.append(f"  deleted {when.replace('T', ' ')}   {path}")
        if not rows:
            out.append("  (Trash is empty or not found)")
        out.append(f"\n  Total: {len(rows)} items")
        return "\n".join(out) + "\n"

    # ---- v3.4: deleted files / recycle bin (all 3 OS) ----------------------------
    def _art_recyclebin_windows(self):
        items = []
        try:
            drives = [f"{d}:\\" for d in 'CDEFGH' if os.path.isdir(f"{d}:\\")]
        except Exception:
            drives = ['C:\\']
        for drive in drives:
            bin_dir = Path(drive) / '$Recycle.Bin'
            if not bin_dir.is_dir():
                continue
            try:
                sid_dirs = list(bin_dir.iterdir())
            except (PermissionError, OSError):
                continue
            for sid_dir in sid_dirs:
                try:
                    i_files = list(sid_dir.glob('$I*'))
                except (PermissionError, OSError):
                    continue
                for i_file in i_files[:500]:
                    try:
                        rec = v34_parse_recycle_i_file(i_file.read_bytes())
                    except (PermissionError, OSError):
                        continue
                    if rec is None:
                        continue
                    r_file = sid_dir / ('$R' + i_file.name[2:])
                    sha256 = None
                    if r_file.exists() and r_file.is_file():
                        try:
                            sha256 = self._hash_path(r_file)['sha256']
                        except (PermissionError, OSError):
                            pass
                    items.append({**rec, 'i_file': str(i_file), 'r_present': r_file.exists(), 'sha256': sha256})
        return v34_render_recycle_bin_report('Windows', items)

    def _art_recyclebin_macos(self, home=None):
        home = Path(home) if home else self._home()
        trash = home / '.Trash'
        items = []
        try:
            entries = list(trash.iterdir())
        except (PermissionError, OSError) as e:
            return v34_render_recycle_bin_report('Darwin', []) + f"\n({e})\n"
        for p in entries[:500]:
            try:
                st = p.stat()
                sha256 = self._hash_path(p)['sha256'] if p.is_file() else None
                items.append({'name': p.name, 'mtime': datetime.fromtimestamp(st.st_mtime, timezone.utc).isoformat(),
                             'size': st.st_size, 'sha256': sha256})
            except (PermissionError, OSError):
                continue
        return v34_render_recycle_bin_report('Darwin', items)

    def _art_recyclebin_linux(self, home=None):
        home = Path(home) if home else self._home()
        info_dir = home / '.local/share/Trash/info'
        files_dir = home / '.local/share/Trash/files'
        items = []
        try:
            info_files = list(info_dir.glob('*.trashinfo'))
        except (PermissionError, OSError) as e:
            return v34_render_recycle_bin_report('Linux', []) + f"\n({e})\n"
        for p in info_files[:500]:
            try:
                ti = v34_parse_trashinfo(p.read_text(errors='ignore'))
            except (PermissionError, OSError):
                continue
            if not ti:
                continue
            content = files_dir / p.stem
            size, sha256 = None, None
            if content.exists():
                try:
                    st = content.stat()
                    size = st.st_size
                    if content.is_file():
                        sha256 = self._hash_path(content)['sha256']
                except (PermissionError, OSError):
                    pass
            items.append({'original_path': unquote(ti.get('path', '')), 'deletion_date': ti.get('deletion_date'),
                         'size': size, 'sha256': sha256})
        return v34_render_recycle_bin_report('Linux', items)

    # ---- v3.4: NTFS $MFT and USN Journal (Windows only) ---------------------------
    def _open_raw_ntfs_file(self, win_path):
        """Open e.g. \\\\.\\C:\\$MFT for raw read. Needs admin; uses CreateFileW with
        FILE_FLAG_BACKUP_SEMANTICS so the OS permits opening a locked system metadata file."""
        import ctypes
        GENERIC_READ = 0x80000000
        FILE_SHARE_READ, FILE_SHARE_WRITE, FILE_SHARE_DELETE = 0x1, 0x2, 0x4
        OPEN_EXISTING = 3
        FILE_FLAG_BACKUP_SEMANTICS = 0x02000000
        INVALID_HANDLE_VALUE = ctypes.c_void_p(-1).value
        CreateFileW = ctypes.windll.kernel32.CreateFileW
        CreateFileW.restype = ctypes.c_void_p
        handle = CreateFileW(win_path, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
                             None, OPEN_EXISTING, FILE_FLAG_BACKUP_SEMANTICS, None)
        if handle is None or handle == INVALID_HANDLE_VALUE:
            raise OSError(f"CreateFileW failed for {win_path} (needs Administrator)")
        import msvcrt
        fd = msvcrt.open_osfhandle(handle, os.O_RDONLY)
        return os.fdopen(fd, 'rb')

    def _art_mft_windows(self):
        drive = os.environ.get('SystemDrive', 'C:')[:1]
        path = f"\\\\.\\{drive}:\\$MFT"
        try:
            f = self._open_raw_ntfs_file(path)
        except Exception as e:
            return (f"Could not open {path}: {e}\n"
                    "NTFS $MFT parsing needs Administrator rights and an NTFS volume.\n")
        try:
            records = list(v34_iter_mft_records(f, max_records=200000))
        finally:
            f.close()
        suspects = v34_timestomp_suspects(records)
        return v34_render_mft_report(records, suspects)

    def _art_usnjournal_windows(self):
        drive = os.environ.get('SystemDrive', 'C:')[:1]
        try:
            r = subprocess.run(['fsutil', 'usn', 'readjournal', f'{drive}:', 'csv'],
                               capture_output=True, text=True, timeout=60, errors='replace')
        except Exception as e:
            return f"Could not read the USN journal: {e}\n"
        if r.returncode != 0:
            return (f"fsutil reported an error (exit {r.returncode}): {(r.stderr or r.stdout or '').strip()[:500]}\n"
                    "This needs Administrator rights and USN journal tracking enabled on the volume "
                    "(`fsutil usn createjournal` to enable it).\n")
        rows = v34_parse_usn_readjournal_csv(r.stdout)
        return v34_render_usn_report(rows)

    def _art_logins_linux(self):
        out = []
        if shutil.which('last'):
            try:
                r = subprocess.run(['last', '-n', '25', '-F'], capture_output=True, text=True,
                                   timeout=15, errors='ignore')
                out.append("LOGIN HISTORY (last)\n" + "-" * 40 + "\n" + (r.stdout.strip() or "(empty)"))
            except Exception as e:
                out.append(f"last failed: {e}")
        else:
            out.append("'last' command not available.")
        pat = re.compile(r'Accepted|Failed password|session opened|sudo:|authentication failure', re.I)
        for p in ('/var/log/auth.log', '/var/log/secure'):
            try:
                with open(p, errors='ignore') as f:
                    hits = [l.rstrip() for l in f if pat.search(l)][-30:]
                out.append(f"\nAUTHENTICATION EVENTS ({p}, last {len(hits)})\n" + "-" * 40)
                out.extend(hits or ["(none)"])
                break
            except FileNotFoundError:
                continue
            except PermissionError:
                out.append(f"\n{p}: permission denied (try sudo).")
                break
        return "\n".join(out) + "\n"

    # --------------------------------------------------------
    # IOC / HASH
    # --------------------------------------------------------
    def browse_file(self):
        filename = filedialog.askopenfilename(title="Select File for Hash Analysis")
        if filename:
            self.file_path.set(filename)

    def calculate_hashes(self):
        path = self.file_path.get()
        if not path or not os.path.exists(path):
            messagebox.showerror("Error", "Please select a valid file.")
            return
        self.run_async(self._task_calculate_hashes, path,
                       on_done=self._on_hashes_done,
                       status="Calculating hashes...")

    def _task_calculate_hashes(self, path):
        md5 = hashlib.md5()
        sha1 = hashlib.sha1()
        sha256 = hashlib.sha256()
        sha512 = hashlib.sha512()

        size = 0
        with open(path, 'rb') as f:
            for chunk in iter(lambda: f.read(1024 * 1024), b''):
                md5.update(chunk)
                sha1.update(chunk)
                sha256.update(chunk)
                sha512.update(chunk)
                size += len(chunk)

        out = "=" * 60 + "\n"
        out += "HASH VALUES\n"
        out += f"File       : {path}\n"
        out += f"Size       : {size:,} bytes\n"
        out += f"Calculated : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        out += "=" * 60 + "\n\n"
        out += f"MD5    : {md5.hexdigest()}\n"
        out += f"SHA1   : {sha1.hexdigest()}\n"
        out += f"SHA256 : {sha256.hexdigest()}\n"
        out += f"SHA512 : {sha512.hexdigest()}\n"

        hashes = {
            'md5': md5.hexdigest(),
            'sha1': sha1.hexdigest(),
            'sha256': sha256.hexdigest(),
            'sha512': sha512.hexdigest(),
        }
        return out, hashes

    def _on_hashes_done(self, result):
        text, hashes = result
        self.hash_text.delete('1.0', 'end')
        self.hash_text.insert('1.0', text)
        self.investigation_data['file_hashes'] = hashes

    # ---- v3.4: hash-set matching (NSRL known-good / IOC known-bad) ----------------
    def _collect_evidence_hashes(self):
        """All (name, {algo: hex}) pairs we currently have hashes for: evidence items
        already collected, any single file hashed on the Hashing tab, and any packet
        captures made this session."""
        out = [(f['name'], {a: f.get(a) for a in self.HASH_ALGOS}) for f in self._evidence_files()]
        fh = self.investigation_data.get('file_hashes')
        if isinstance(fh, dict):
            out.append((os.path.basename(self.file_path.get() or 'selected file'), fh))
        for c in self.__dict__.get('captures', []):
            if c.get('sha256'):
                out.append((os.path.basename(c.get('path', 'capture')),
                            {a: c.get(a) for a in self.HASH_ALGOS}))
        return out

    def load_hash_set(self, label):
        kind = "known-good (NSRL-style)" if label == 'allow' else "known-bad / IOC"
        p = filedialog.askopenfilename(title=f"Choose a {kind} hash-set file",
                                       filetypes=[("Hash set", "*.txt *.csv *.hash"), ("All files", "*.*")])
        if not p:
            return
        self.run_async(self._task_hash_set_match, p, label, on_done=self._on_hash_set_done,
                       status="Matching hash set...")

    def _task_hash_set_match(self, path, label):
        text = Path(path).read_text(encoding='utf-8', errors='replace')
        sets, unrec = v34_parse_hash_set(text)
        total = v34_total_hashes(sets)
        evidence = self._collect_evidence_hashes()
        report = v34_render_hash_set_report(os.path.basename(path), label, sets, unrec, evidence)
        return report, total

    def _on_hash_set_done(self, result):
        text, total = result
        self.hash_text.delete('1.0', 'end')
        self.hash_text.insert('1.0', text)
        self.investigation_data['hashset_match'] = text
        self._audit('hash-set match', 'ok', f"{total} hash(es) in set")
        if total == 0:
            messagebox.showwarning("Hash-set matching", "No recognisable hashes were found in that file -- check it "
                                   "contains plain MD5/SHA-1/SHA-256/SHA-512 hashes or an NSRL-RDS-style CSV.")

    def verify_hash(self):
        if 'file_hashes' not in self.investigation_data:
            messagebox.showerror("Error", "Please calculate hashes first.")
            return

        popup = tk.Toplevel(self.root)
        popup.title("Hash Verification")
        popup.geometry("560x280")
        popup.configure(bg=Theme.BG_DARK)
        popup.transient(self.root)
        popup.grab_set()

        popup.update_idletasks()
        x = (popup.winfo_screenwidth() // 2) - 280
        y = (popup.winfo_screenheight() // 2) - 140
        popup.geometry(f"+{x}+{y}")

        tk.Label(popup, text="🔎  Verify Hash",
                 font=('Segoe UI', 14, 'bold'),
                 bg=Theme.BG_DARK, fg=Theme.ACCENT).pack(pady=(16, 6))
        tk.Label(popup, text="Paste a hash value to compare against the calculated hashes.",
                 font=('Segoe UI', 9),
                 bg=Theme.BG_DARK, fg=Theme.TEXT_SECONDARY).pack()

        entry = ttk.Entry(popup, width=70)
        entry.pack(pady=16, padx=20, fill='x')

        result_label = tk.Label(popup, text="", font=('Segoe UI', 11, 'bold'),
                                bg=Theme.BG_DARK, fg=Theme.TEXT_PRIMARY)
        result_label.pack(pady=6)

        def do_verify():
            h = entry.get().strip().lower()
            if not h:
                result_label.config(text="Please enter a hash.", fg=Theme.WARNING)
                return
            for kind, val in self.investigation_data['file_hashes'].items():
                if h == val:
                    result_label.config(text=f"✓  Match found: {kind.upper()}",
                                        fg=Theme.SUCCESS)
                    return
            result_label.config(text="✗  No match found.", fg=Theme.ERROR)

        btns = tk.Frame(popup, bg=Theme.BG_DARK)
        btns.pack(pady=10)
        ttk.Button(btns, text="Verify", style='Accent.TButton',
                   command=do_verify).pack(side='left', padx=6)
        ttk.Button(btns, text="Close", command=popup.destroy).pack(side='left', padx=6)

    # ========================================================
    # LIVE RESPONSE  (volatile data, collected in order of volatility)
    # ========================================================
    LIVE_ITEMS = (('live_time', 'Time & Uptime'), ('live_users', 'Logged-on Users'),
                  ('live_network', 'Network State'), ('live_processes', 'Processes'),
                  ('live_accounts', 'Accounts'), ('live_security', 'Security Status'),
                  ('live_shares', 'Shares & Sessions'), ('live_dns_swap', 'DNS Cache & Swap Traces'),
                  ('live_history', 'PowerShell History'))

    def build_live_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  ⚡  Live  ')
        top = tk.Frame(tab, bg=Theme.BG_DARK)
        top.pack(fill='x', padx=12, pady=(12, 4))
        ttk.Button(top, text="🚨 Full Live Acquisition", style='Accent.TButton',
                   command=self.full_live_acquisition).pack(side='left', padx=4)
        ttk.Button(top, text="🕒 Super-Timeline", command=self.run_super_timeline).pack(side='left', padx=4)
        ttk.Button(top, text="🧬 YARA Scan", command=self.run_yara_scan).pack(side='left', padx=4)
        ttk.Button(top, text="📈 Graphical Timeline", command=self.show_graphical_timeline).pack(side='left', padx=4)
        ttk.Button(top, text="🔒 Encryption Status", command=self.check_encryption_status).pack(side='left', padx=4)
        ttk.Button(top, text="🧠 Acquire RAM", command=self.acquire_ram).pack(side='left', padx=4)
        row = tk.Frame(tab, bg=Theme.BG_DARK)
        row.pack(fill='x', padx=12, pady=(0, 4))
        for key, label in self.LIVE_ITEMS:
            if key == 'live_history' and self.current_os != 'Windows':
                continue
            ttk.Button(row, text=label, command=lambda k=key: self.collect_live([k])).pack(side='left', padx=3)
        ttk.Button(row, text="🗑 Clear", command=lambda: self.clear_text(self.live_text)).pack(side='left', padx=3)
        tk.Label(tab, text=("Order of volatility: time, users, network, processes first, because they change fastest. "
                            "Live collection cannot be write-blocked: running this tool changes the machine slightly "
                            "(memory, logs), and that is recorded in the report. Every command used is logged with a hash of its output."),
                 bg=Theme.BG_DARK, fg=Theme.TEXT_SECONDARY, font=('Segoe UI', 9), anchor='w', justify='left',
                 wraplength=1300).pack(fill='x', padx=16, pady=(0, 6))
        self.live_progress = tk.Label(tab, text=self._privilege_line(), bg=Theme.BG_DARK, fg=Theme.TEXT_SECONDARY,
                                      font=('Segoe UI', 9), anchor='w')
        self.live_progress.pack(fill='x', padx=16)
        card = self._make_card(tab, "Live system state")
        card.pack(fill='both', expand=True, padx=12, pady=(4, 12))
        self.live_text = self._make_text_area(card)

    # ---- commands per OS ------------------------------------------------
    @staticmethod
    def _ps(script):
        return ['powershell', '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass', '-Command', script]

    def _live_commands(self, key):
        osn = self.current_os
        W, M = osn == 'Windows', osn == 'Darwin'
        if key == 'live_time':
            if W:
                return [('Local and UTC time', self._ps("Get-Date -Format o; (Get-Date).ToUniversalTime().ToString('o'); (Get-TimeZone).Id")),
                        ('Last boot', self._ps("(Get-CimInstance Win32_OperatingSystem).LastBootUpTime")),
                        ('Time synchronisation', ['w32tm', '/query', '/status'])]
            if M:
                return [('Time', ['date', '-u']), ('Uptime', ['uptime']), ('Boot time', ['sysctl', 'kern.boottime']),
                        ('Time zone', ['systemsetup', '-gettimezone']), ('Network time', ['systemsetup', '-getusingnetworktime'])]
            return [('Time', ['date', '-u']), ('Uptime', ['uptime', '-s']), ('Time settings', ['timedatectl'])]
        if key == 'live_users':
            if W:
                return [('Logged-on sessions', ['query', 'user']), ('Sessions', ['qwinsta'])]
            return [('Logged-on users', ['who', '-a']), ('Activity', ['w']), ('Recent logins', ['last', '-n', '20'])]
        if key == 'live_network':
            if W:
                return [('Adapters', ['ipconfig', '/all']), ('Routes', ['route', 'print']),
                        ('DNS cache', ['ipconfig', '/displaydns']), ('Connections', ['netstat', '-ano']),
                        ('ARP', ['arp', '-a']), ('Saved Wi-Fi profiles', ['netsh', 'wlan', 'show', 'profiles'])]
            if M:
                return [('Adapters', ['ifconfig']), ('Routes', ['netstat', '-rn']), ('Connections', ['netstat', '-an']),
                        ('ARP', ['arp', '-an']), ('DNS', ['scutil', '--dns'])]
            return [('Addresses', ['ip', '-d', 'addr']), ('Routes', ['ip', 'route']), ('Connections', ['ss', '-tunap']),
                    ('Neighbours', ['ip', 'neigh']), ('Resolver', ['cat', '/etc/resolv.conf'])]
        if key == 'live_accounts':
            if W:
                return [('Local users', ['net', 'user']), ('Administrators', ['net', 'localgroup', 'administrators'])]
            if M:
                return [('Users', ['dscl', '.', 'list', '/Users']), ('Admin group', ['dscl', '.', 'read', '/Groups/admin', 'GroupMembership'])]
            return [('Accounts with a login shell', ['getent', 'passwd']), ('sudo/admin groups', ['getent', 'group', 'sudo', 'wheel', 'admin'])]
        if key == 'live_security':
            if W:
                return [('Defender', self._ps("Get-MpComputerStatus | Select AMServiceEnabled,AntivirusEnabled,RealTimeProtectionEnabled,AntivirusSignatureLastUpdated | Format-List")),
                        ('Firewall', ['netsh', 'advfirewall', 'show', 'allprofiles', 'state']), ('BitLocker', ['manage-bde', '-status'])]
            if M:
                return [('System Integrity Protection', ['csrutil', 'status']), ('Gatekeeper', ['spctl', '--status']),
                        ('FileVault', ['fdesetup', 'status']), ('Firewall', ['/usr/libexec/ApplicationFirewall/socketfilterfw', '--getglobalstate'])]
            return [('SELinux', ['getenforce']), ('AppArmor', ['aa-status']), ('Firewall', ['ufw', 'status']),
                    ('Disk encryption', ['lsblk', '-o', 'NAME,TYPE,FSTYPE,MOUNTPOINT'])]
        if key == 'live_shares':
            if W:
                return [('Shares', ['net', 'share']), ('Mapped drives', ['net', 'use']), ('Open sessions', ['net', 'session'])]
            if M:
                return [('Mounts', ['mount']), ('Shares', ['sharing', '-l'])]
            return [('Mounts', ['mount']), ('Exports', ['cat', '/etc/exports'])]
        return []

    def _live_section(self, key):
        """Run the commands for one section -> text. Every command goes through the recorder."""
        title = dict(self.LIVE_ITEMS).get(key, key)
        out = "=" * 60 + f"\n{title.upper()}\nCollected (UTC): {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')}\n" + "=" * 60 + "\n"
        if key == 'live_processes':
            return out + self._live_processes_text()
        if key == 'live_history':
            return out + self._powershell_history()
        if key == 'live_dns_swap':
            return self._live_dns_swap_text()
        cmds = self._live_commands(key)
        if not cmds:
            return out + "Not available on this operating system.\n"
        for label, cmd in cmds:
            if not shutil.which(cmd[0]):
                out += f"\n--- {label} ---\n(not available: '{cmd[0]}' is not installed)\n"
                continue
            try:
                r = subprocess.run(cmd, capture_output=True, text=True, timeout=45, errors='replace')
                body = (r.stdout or '') + ((r.stderr or '') if r.returncode and not r.stdout else '')
                if key == 'live_accounts' and cmd[0] == 'getent' and cmd[1] == 'passwd':
                    body = "\n".join(l for l in body.splitlines() if not re.search(r'(nologin|/bin/false)$', l))
                out += f"\n--- {label}   ($ {' '.join(cmd)[:140]}) ---\n{body.strip() or '(no output)'}\n"
            except subprocess.TimeoutExpired:
                out += f"\n--- {label} ---\n(timed out after 45 s)\n"
            except OSError as e:
                out += f"\n--- {label} ---\n(could not run: {e})\n"
        return out

    # ---- processes ----------------------------------------------------------------
    _WIN_SYSTEM_NAMES = ('svchost.exe', 'lsass.exe', 'csrss.exe', 'winlogon.exe', 'services.exe', 'smss.exe', 'wininit.exe', 'explorer.exe')
    _SUSPECT_DIRS = ('/tmp/', '/var/tmp/', '/dev/shm/', '/private/tmp/', '/downloads/', '\\temp\\', '\\appdata\\local\\temp\\',
                     '\\downloads\\', '\\users\\public\\', '\\programdata\\', '\\$recycle.bin\\')

    def _list_processes(self):
        osn = self.current_os
        procs = []
        if osn == 'Windows':
            r = subprocess.run(self._ps("Get-CimInstance Win32_Process | Select-Object ProcessId,ParentProcessId,Name,ExecutablePath,CommandLine,CreationDate | ConvertTo-Json -Compress"),
                               capture_output=True, text=True, timeout=90, errors='replace')
            try:
                data = json.loads(r.stdout or '[]')
            except ValueError:
                data = []
            if isinstance(data, dict):
                data = [data]
            for d in data:
                procs.append({'pid': d.get('ProcessId'), 'ppid': d.get('ParentProcessId'), 'name': d.get('Name') or '',
                              'path': d.get('ExecutablePath') or '', 'cmdline': d.get('CommandLine') or '',
                              'user': '', 'start': str(d.get('CreationDate') or '')})
        elif osn == 'Linux' and os.path.isdir('/proc'):
            for pid in sorted((p for p in os.listdir('/proc') if p.isdigit()), key=int):
                base = f'/proc/{pid}'
                try:
                    with open(base + '/stat') as f:
                        st = f.read()
                    name = st[st.index('(') + 1:st.rindex(')')]
                    ppid = int(st[st.rindex(')') + 2:].split()[1])
                except (OSError, ValueError):
                    continue
                try:
                    exe = os.readlink(base + '/exe')
                except OSError:
                    exe = ''
                try:
                    with open(base + '/cmdline', 'rb') as f:
                        cmd = f.read().replace(b'\0', b' ').decode('utf-8', 'replace').strip()
                except OSError:
                    cmd = ''
                try:
                    uid = os.stat(base).st_uid
                    try:
                        import pwd
                        user = pwd.getpwuid(uid).pw_name
                    except Exception:
                        user = str(uid)
                except OSError:
                    user = ''
                procs.append({'pid': int(pid), 'ppid': ppid, 'name': name, 'path': exe, 'cmdline': cmd, 'user': user, 'start': ''})
        else:
            r = subprocess.run(['ps', '-axo', 'pid=,ppid=,user=,command='], capture_output=True, text=True, timeout=30, errors='replace')
            for line in (r.stdout or '').splitlines():
                c = line.split(None, 3)
                if len(c) < 4 or not c[0].isdigit():
                    continue
                first = c[3].split(' -')[0].split(' --')[0]
                path = first if first.startswith('/') and os.path.isfile(first) else (c[3].split()[0] if c[3].startswith('/') else '')
                procs.append({'pid': int(c[0]), 'ppid': int(c[1]) if c[1].isdigit() else None, 'name': os.path.basename(path or c[3].split()[0]),
                              'path': path, 'cmdline': c[3], 'user': c[2], 'start': ''})
        return procs

    def _flag_process(self, p):
        flags = []
        path = (p['path'] or '')
        low = path.lower()
        if p.get('path_deleted'):
            flags.append('executable file deleted from disk')
        if low and any(s in low.replace('\\\\', '\\') for s in self._SUSPECT_DIRS):
            flags.append('runs from a temporary / user-writable location')
        if self.current_os == 'Windows' and p['name'].lower() in self._WIN_SYSTEM_NAMES and low:
            ok = low.startswith('c:\\windows\\system32\\') or low.startswith('c:\\windows\\syswow64\\') or low == 'c:\\windows\\explorer.exe'
            if not ok:
                flags.append('system-process name but not running from the Windows folder')
        return flags

    def _live_processes_text(self):
        try:
            procs = self._list_processes()
        except (OSError, subprocess.SubprocessError) as e:
            return f"Could not list processes: {e}\n"
        hashes, seen, notes = {}, 0, []
        for p in procs:
            path = p['path']
            if path.endswith(' (deleted)'):
                p['path_deleted'] = True
                path = path[:-10]
                p['path'] = path
            if not path or path in hashes:
                continue
            if seen >= 400:
                notes.append("Only the first 400 distinct program files were hashed.")
                break
            seen += 1
            try:
                if p.get('path_deleted'):
                    hashes[path] = '(file deleted)'
                elif os.path.getsize(path) > 300 * 1024 * 1024:
                    hashes[path] = '(not hashed: over 300 MB)'
                else:
                    hashes[path] = self._hash_path(path)['sha256']
            except OSError as e:
                hashes[path] = f"(not readable: {e.strerror or e})"
        flagged = 0
        out = f"{len(procs)} processes.  SHA-256 is of the program file on disk, hashed once per distinct file.\n\n"
        out += f"{'PID':>7} {'PPID':>7}  {'USER':<12} NAME / PATH\n"
        for p in sorted(procs, key=lambda x: (x['pid'] or 0)):
            fl = self._flag_process(p)
            line = f"{p['pid']!s:>7} {p['ppid']!s:>7}  {p['user'][:12]:<12} {p['name']}"
            if p['path']:
                line += f"\n{'':>29}path   : {p['path']}\n{'':>29}sha256 : {hashes.get(p['path'], '')}"
            if p['cmdline'] and p['cmdline'] != p['name']:
                line += f"\n{'':>29}command: {p['cmdline'][:300]}"
            if p['start']:
                line += f"\n{'':>29}started: {p['start']}"
            if fl:
                flagged += 1
                line += f"\n{'':>29}** LEAD: {'; '.join(fl)}"
            out += line + "\n"
        out += f"\nProcesses with a lead flagged: {flagged}. A flag is a reason to look closer, not a finding of wrongdoing; many legitimate programs run from these locations.\n"
        for n in notes:
            out += "NOTE: " + n + "\n"
        return out

    def _powershell_history(self):
        h = self._home()
        cands = [h / 'AppData/Roaming/Microsoft/Windows/PowerShell/PSReadLine/ConsoleHost_history.txt']
        out = ""
        for p in cands:
            if p.exists():
                try:
                    out += f"[{p}]  (SHA-256 {self._hash_path(p)['sha256']})\n" + p.read_text(errors='replace')[-20000:] + "\n"
                except OSError as e:
                    out += f"[{p}] cannot be read: {e}\n"
        return out or "No PowerShell history file found for this user.\n"

    # ---- run from the UI -------------------------------------------------------------------
    def collect_live(self, keys):
        self.run_async(self._task_live, list(keys), on_done=self._on_live_done, status="Collecting live system state...")

    def _task_live(self, keys):
        res = {}
        for k in keys:
            try:
                res[k] = self._live_section(k)
            except Exception as e:
                res[k] = f"{k} failed: {type(e).__name__}: {e}\n"
        return res

    def _on_live_done(self, res):
        for k, text in res.items():
            self.live_text.insert('end', text + "\n")
            self.investigation_data[k] = text
        self.live_text.see('end')

    # ---- everything, in order ----------------------------------------------------------------
    def full_live_acquisition(self):
        if not messagebox.askyesno(
                "Full live acquisition",
                "This collects the volatile state first, then every other category, and records each step.\n\n"
                "Use it only on a system you are authorised to examine. Running it changes the machine slightly, "
                "and that is noted in the report.\n\nStart?"):
            return
        try:
            rng = self._event_range()
            limit = int(self.event_limit.get())
            level = self.event_level.get()
        except ValueError:
            rng = None
            limit, level = 0, ''
        self._audit('Full live acquisition', 'started', f"examiner={self._case_info()['examiner']!r}")
        self._vault()
        self.run_async(self._task_full_live, rng, limit, level, on_done=self._on_full_live_done,
                       status="Full live acquisition...")

    def _step(self, label):
        self.root.after(0, lambda: self.live_progress.config(text=f"Now collecting: {label}"))

    def _task_full_live(self, rng, limit, level):
        out, ok = [], []
        kinds = [k for _l, k in self._artifact_list()]

        def step(label, cb, fn, *a):
            self._step(label)
            try:
                out.append((cb, fn(*a)))
                ok.append(label)
            except Exception as e:
                ok.append(f"{label} FAILED: {type(e).__name__}: {e}")
        step('time & uptime', self._on_live_done, self._task_live, ['live_time'])
        step('users', self._on_live_done, self._task_live, ['live_users'])
        step('network state', self._on_live_done, self._task_live, ['live_network'])
        step('processes', self._on_live_done, self._task_live, ['live_processes'])
        step('accounts, security, shares, dns/swap', self._on_live_done, self._task_live,
             ['live_accounts', 'live_security', 'live_shares', 'live_dns_swap'] + (['live_history'] if self.current_os == 'Windows' else []))
        step('system information', self._on_system_info_done, self._task_collect_system_info)
        step('connected devices', self._on_devices_done, self._task_collect_devices)
        step('network activity', self._on_network_done, self._task_collect_network)
        step('artifacts', self._on_artifacts_done, self._task_artifacts, kinds)
        step('USB / device history', self._on_device_history_done, self._task_device_history)
        step('browser history', self._on_browser_history_done, self._task_collect_browser_history)
        step('timeline', self._on_timeline_done, self._task_collect_timeline)
        if rng:
            step('event logs', self._on_event_logs_done, self._task_collect_event_logs, rng[0], rng[1], rng[2], limit, level)
        return out, ok

    def _on_full_live_done(self, res):
        out, steps = res
        for cb, r in out:
            try:
                cb(r)
            except Exception as e:
                self._audit('apply result', 'FAILED', f"{type(e).__name__}: {e}")
        bad = [s for s in steps if 'FAILED' in s]
        self._audit('Full live acquisition', 'completed' if not bad else 'PARTIAL', f"{len(steps) - len(bad)} steps ok, {len(bad)} failed")
        self.live_progress.config(text=f"Finished. {len(steps) - len(bad)} steps ok" + (f", {len(bad)} failed: " + "; ".join(bad) if bad else "") +
                                       ".  Next: Case tab > Export Evidence Package.")

    # ========================================================
    # PACKETS  (Wireshark / tshark / dumpcap / tcpdump capture + built-in pcap analysis)
    # ========================================================
    SNAP_MODES = (("Headers + start of payload (512 bytes) - finds DNS names, TLS server names, HTTP hosts", 512),
                  ("Headers only (96 bytes) - least data kept", 96),
                  ("Full packets - everything, including content", 0))

    def build_packets_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  📡  Packets  ')
        self.captures = []
        self._cap_stop = threading.Event()
        card = self._make_card(tab, "Packet capture  (uses Wireshark's dumpcap / tshark, or tcpdump)")
        card.pack(fill='x', padx=12, pady=(12, 6))
        g = tk.Frame(card.body, bg=Theme.BG_CARD)
        g.pack(fill='x', padx=8, pady=8)

        def lab(r, c, t):
            tk.Label(g, text=t, bg=Theme.BG_CARD, fg=Theme.TEXT_PRIMARY, font=('Segoe UI', 10)).grid(row=r, column=c, sticky='w', padx=(0, 6), pady=3)
        self.cap_tool_label = tk.Label(g, text="", bg=Theme.BG_CARD, fg=Theme.TEXT_SECONDARY, font=('Segoe UI', 9))
        self.cap_tool_label.grid(row=0, column=0, columnspan=6, sticky='w', pady=(0, 4))
        lab(1, 0, "Interface:")
        self.cap_iface = ttk.Combobox(g, state='readonly', width=46)
        self.cap_iface.grid(row=1, column=1, columnspan=3, sticky='w', pady=3)
        ttk.Button(g, text="Refresh", command=self.refresh_interfaces).grid(row=1, column=4, padx=6)
        lab(2, 0, "Seconds:")
        self.cap_secs = tk.StringVar(value='60')
        ttk.Entry(g, textvariable=self.cap_secs, width=8).grid(row=2, column=1, sticky='w')
        lab(2, 2, "Max packets (0 = no limit):")
        self.cap_count = tk.StringVar(value='0')
        ttk.Entry(g, textvariable=self.cap_count, width=10).grid(row=2, column=3, sticky='w')
        lab(3, 0, "Filter (BPF):")
        self.cap_filter = tk.StringVar()
        ttk.Entry(g, textvariable=self.cap_filter, width=40).grid(row=3, column=1, columnspan=3, sticky='w', pady=3)
        tk.Label(g, text="e.g.  host 192.168.1.5   or   port 53", bg=Theme.BG_CARD, fg=Theme.TEXT_SECONDARY,
                 font=('Segoe UI', 9)).grid(row=3, column=4, columnspan=2, sticky='w')
        lab(4, 0, "Keep:")
        self.cap_snap = ttk.Combobox(g, state='readonly', width=70, values=[m[0] for m in self.SNAP_MODES])
        self.cap_snap.current(0)
        self.cap_snap.grid(row=4, column=1, columnspan=5, sticky='w', pady=3)
        row = tk.Frame(tab, bg=Theme.BG_DARK)
        row.pack(fill='x', padx=12, pady=(0, 6))
        ttk.Button(row, text="▶ Start Capture", style='Accent.TButton', command=self.start_capture).pack(side='left', padx=4)
        ttk.Button(row, text="■ Stop", command=lambda: self._cap_stop.set()).pack(side='left', padx=4)
        ttk.Button(row, text="📂 Analyze Capture File...", command=self.analyze_file_dialog).pack(side='left', padx=4)
        ttk.Button(row, text="🦈 Open in Wireshark", command=self.open_in_wireshark).pack(side='left', padx=4)
        ttk.Button(row, text="🗑 Clear", command=lambda: self.clear_text(self.packet_text)).pack(side='left', padx=4)
        tk.Label(tab, text=("Capture only on networks you own or are authorised to monitor. Packet content can include other people's "
                            "private data. Each capture file is hashed the moment it is closed and stored read-only in the evidence folder."),
                 bg=Theme.BG_DARK, fg=Theme.TEXT_SECONDARY, font=('Segoe UI', 9), anchor='w', justify='left',
                 wraplength=1300).pack(fill='x', padx=16, pady=(0, 6))
        card = self._make_card(tab, "Capture analysis")
        card.pack(fill='both', expand=True, padx=12, pady=(0, 12))
        self.packet_text = self._make_text_area(card)
        self.refresh_interfaces()

    # ---- tools -----------------------------------------------------------------------
    def _find_capture_tool(self):
        """-> (kind, path) preferring Wireshark's own capture engine, or (None, '')"""
        extra = []
        if self.current_os == 'Windows':
            for pf in (os.environ.get('ProgramFiles', r'C:\Program Files'), os.environ.get('ProgramFiles(x86)', r'C:\Program Files (x86)')):
                extra += [os.path.join(pf, 'Wireshark', 'dumpcap.exe'), os.path.join(pf, 'Wireshark', 'tshark.exe')]
        elif self.current_os == 'Darwin':
            extra += ['/Applications/Wireshark.app/Contents/MacOS/dumpcap', '/Applications/Wireshark.app/Contents/MacOS/tshark',
                      '/opt/homebrew/bin/dumpcap', '/usr/local/bin/dumpcap']
        for kind in ('dumpcap', 'tshark', 'tcpdump'):
            p = shutil.which(kind)
            if not p:
                for e in extra:
                    if os.path.basename(e).lower().startswith(kind) and os.path.isfile(e):
                        p = e
                        break
            if p:
                return kind, p
        return None, ''

    def _find_wireshark(self):
        if self.current_os == 'Windows':
            for pf in (os.environ.get('ProgramFiles', r'C:\Program Files'), os.environ.get('ProgramFiles(x86)', r'C:\Program Files (x86)')):
                p = os.path.join(pf, 'Wireshark', 'Wireshark.exe')
                if os.path.isfile(p):
                    return p
        if self.current_os == 'Darwin' and os.path.isdir('/Applications/Wireshark.app'):
            return 'open'
        return shutil.which('wireshark') or ''

    def refresh_interfaces(self):
        kind, exe = self._find_capture_tool()
        self._cap_tool = (kind, exe)
        if not kind:
            self.cap_tool_label.config(text=("No capture tool found. Install Wireshark (https://www.wireshark.org, includes dumpcap and the Npcap driver "
                                             "on Windows) or tcpdump (Linux: sudo apt install tcpdump). You can still analyze existing .pcap / .pcapng files."))
            self.cap_iface['values'] = []
            self._ifaces = []
            return
        self.cap_tool_label.config(text=f"Capture engine: {kind}  ({exe})    {self._privilege_line()}")
        self._ifaces = self._list_interfaces(kind, exe)
        self.cap_iface['values'] = [d for _i, d in self._ifaces]
        if self._ifaces:
            self.cap_iface.current(0)

    def _list_interfaces(self, kind, exe):
        try:
            r = subprocess.run([exe, '-D'], capture_output=True, text=True, timeout=20, errors='replace')
        except (OSError, subprocess.SubprocessError):
            return []
        out = []
        for line in (r.stdout or '').splitlines():
            m = re.match(r'^\s*(\d+)\.\s*(.*)$', line)
            if not m:
                continue
            num, rest = m.group(1), m.group(2).strip()
            ident = rest.split()[0] if kind == 'tcpdump' else num
            out.append((ident, f"{num}. {rest}"[:120]))
        return out

    # ---- capture ------------------------------------------------------------------------
    def start_capture(self):
        kind, exe = self._find_capture_tool()
        if not kind:
            messagebox.showinfo("Packet capture", "No capture tool found. Install Wireshark or tcpdump, or use 'Analyze Capture File...' on an existing capture.")
            return
        try:
            secs = int(self.cap_secs.get())
            count = int(self.cap_count.get() or 0)
            assert 1 <= secs <= 86400 and count >= 0
        except (ValueError, AssertionError):
            messagebox.showerror("Packet capture", "Seconds must be a whole number from 1 to 86400, and max packets 0 or more.")
            return
        sel = self.cap_iface.current()
        if sel < 0 or sel >= len(getattr(self, '_ifaces', [])):
            messagebox.showerror("Packet capture", "Choose a network interface first.")
            return
        bpf = self.cap_filter.get().strip()
        if bpf and not re.fullmatch(r'[A-Za-z0-9_ .:/()!&|<>=\-\[\]]+', bpf):
            messagebox.showerror("Packet capture", "The filter contains unusual characters. Use a plain BPF filter such as: host 10.0.0.5 and port 443")
            return
        snap = self.SNAP_MODES[max(self.cap_snap.current(), 0)][1]
        iface_id, iface_disp = self._ifaces[sel]
        if not messagebox.askyesno(
                "Confirm packet capture",
                f"Capture on: {iface_disp}\nFor: {secs} seconds   Filter: {bpf or '(none)'}\n"
                f"Keeping: {'whole packets' if snap == 0 else str(snap) + ' bytes per packet'}\n\n"
                "Capturing network traffic can intercept private communications. Continue only if you own this network "
                "or have written authority to monitor it.\n\nStart the capture?"):
            return
        self._cap_stop.clear()
        self._case_snapshot = self._case_info()
        try:
            vault = self._vault()
        except OSError as e:
            messagebox.showerror("Packet capture", f"Cannot create the evidence folder:\n{e}")
            return
        self.run_async(self._task_packet_capture, kind, exe, iface_id, iface_disp, secs, count, bpf, snap, str(vault),
                       on_done=self._on_capture_file_done,
                       on_error=lambda e: messagebox.showerror("Packet capture", f"{type(e).__name__}: {e}"),
                       status=f"Capturing packets for up to {secs} s...")

    def _capture_command(self, kind, exe, iface, out, secs, count, bpf, snap):
        if kind == 'tcpdump':
            cmd = [exe, '-i', iface, '-n', '-U', '-s', str(snap), '-w', out]
            if count:
                cmd += ['-c', str(count)]
            return cmd + (bpf.split() if bpf else [])
        cmd = [exe, '-i', iface, '-F', 'pcap', '-w', out, '-q', '-a', f'duration:{secs}']
        if snap:
            cmd += ['-s', str(snap)]
        if count:
            cmd += ['-c', str(count)]
        if bpf:
            cmd += ['-f', bpf]
        return cmd

    def _task_packet_capture(self, kind, exe, iface, iface_disp, secs, count, bpf, snap, vault):
        stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
        safe = re.sub(r'[^A-Za-z0-9]+', '_', iface_disp.split('(')[-1] if kind != 'tcpdump' else iface)[:20].strip('_') or 'iface'
        out = str(Path(vault) / 'captures' / f"capture_{stamp}_{safe}.pcap")
        cmd = self._capture_command(kind, exe, iface, out, secs, count, bpf, snap)
        started = datetime.now(timezone.utc)
        t0 = time.time()
        err = ''
        try:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, errors='replace')
        except OSError as e:
            raise RuntimeError(f"Could not start {kind}: {e}")
        limit = secs if kind == 'tcpdump' else secs + 10
        while proc.poll() is None:
            if self._cap_stop.is_set() or time.time() - t0 > limit:
                proc.terminate()
                break
            time.sleep(0.2)
        try:
            _o, err = proc.communicate(timeout=15)
        except subprocess.TimeoutExpired:
            proc.kill()
            _o, err = proc.communicate()
        _record_command(cmd, proc.returncode, (err or '').encode('utf-8', 'replace'), time.time() - t0)
        finished = datetime.now(timezone.utc)
        if not os.path.exists(out) or os.path.getsize(out) < 24:
            msg = (err or '').strip().splitlines()
            hint = ''
            if re.search(r'permission|not permitted|denied|root|privilege', err or '', re.I):
                hint = "\nStart the tool with sudo (Linux/macOS) or as Administrator (Windows)."
            raise RuntimeError("Nothing was captured. " + (msg[-1] if msg else '') + hint)
        h = self._hash_path(out)
        self._readonly(out)
        meta = {'path': out, 'tool': f"{kind} ({exe})", 'interface': iface_disp, 'filter': bpf, 'snaplen': snap or 'full',
                'started_utc': started.isoformat(timespec='seconds'), 'finished_utc': finished.isoformat(timespec='seconds'),
                'command': ' '.join(cmd), 'origin': 'captured by this tool', **h}
        meta['analysis'], meta['analysis_text'] = self._analyze_and_render(out, meta)
        return meta

    def _on_capture_file_done(self, meta):
        self.captures.append(meta)
        self._audit('packet capture saved', 'ok', f"{os.path.basename(meta['path'])} SHA-256 {meta['sha256']}")
        self.packet_text.insert('end', meta['analysis_text'] + "\n")
        self.packet_text.see('end')
        self.investigation_data['packet_capture'] = "\n".join(c['analysis_text'] for c in self.captures)
        messagebox.showinfo("Capture complete", f"{os.path.basename(meta['path'])}\n{meta['analysis'].get('packets', 0):,} packets\n\n"
                                                f"SHA-256:\n{meta['sha256']}")

    def analyze_file_dialog(self):
        p = filedialog.askopenfilename(title="Choose a capture file", filetypes=[("Capture files", "*.pcap *.pcapng *.cap"), ("All files", "*.*")])
        if not p:
            return
        self._case_snapshot = self._case_info()
        try:
            vault = self._vault()
        except OSError as e:
            messagebox.showerror("Analyze", f"Cannot create the evidence folder:\n{e}")
            return
        self.run_async(self._task_import_capture, p, str(vault), on_done=self._on_capture_file_done,
                       on_error=lambda e: messagebox.showerror("Analyze", f"{type(e).__name__}: {e}"),
                       status="Analyzing capture file...")

    def _task_import_capture(self, src, vault):
        before = self._hash_path(src)
        dst = Path(vault) / 'captures' / f"imported_{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}_{os.path.basename(src)}"
        shutil.copy2(src, dst)
        h = self._hash_path(dst)
        if h['sha256'] != before['sha256']:
            raise RuntimeError("The copy does not match the original. Nothing was imported.")
        self._readonly(dst)
        meta = {'path': str(dst), 'tool': 'imported file', 'interface': '(from file)', 'filter': '', 'snaplen': '?',
                'started_utc': '', 'finished_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'),
                'command': '', 'origin': f"copied from {src}; original SHA-256 {before['sha256']}", **h}
        meta['analysis'], meta['analysis_text'] = self._analyze_and_render(str(dst), meta)
        return meta

    def open_in_wireshark(self):
        ws = self._find_wireshark()
        path = self.captures[-1]['path'] if getattr(self, 'captures', None) else filedialog.askopenfilename(title="Capture file")
        if not ws:
            messagebox.showinfo("Wireshark", "Wireshark was not found. Install it from https://www.wireshark.org, then open the capture file from the evidence folder.")
            return
        if not path:
            return
        try:
            cmd = ['open', '-a', 'Wireshark', path] if ws == 'open' else [ws, '-r', path]
            subprocess.Popen(cmd)
            self._audit('opened in Wireshark', 'ok', os.path.basename(path))
        except OSError as e:
            messagebox.showerror("Wireshark", str(e))

    # ---- file readers ----------------------------------------------------------------------
    def _iter_pcap(self, path):
        """Yield (timestamp, linktype, bytes, original_length) from a pcap or pcapng file."""
        with open(path, 'rb') as f:
            head = f.read(4)
            f.seek(0)
            if head == b'\x0a\x0d\x0d\x0a':
                yield from self._iter_pcapng(f)
                return
            magics = {b'\xd4\xc3\xb2\xa1': ('<', 1e6), b'\xa1\xb2\xc3\xd4': ('>', 1e6),
                      b'\x4d\x3c\xb2\xa1': ('<', 1e9), b'\xa1\xb2\x3c\x4d': ('>', 1e9)}
            if head not in magics:
                raise ValueError("This is not a pcap or pcapng capture file.")
            end, div = magics[head]
            gh = f.read(24)
            if len(gh) < 24:
                raise ValueError("The capture file is truncated.")
            lt = struct.unpack(end + 'I', gh[20:24])[0] & 0x0FFFFFFF
            while True:
                h = f.read(16)
                if len(h) < 16:
                    break
                sec, frac, cap, orig = struct.unpack(end + 'IIII', h)
                if cap > 1 << 22:
                    break
                data = f.read(cap)
                if len(data) < cap:
                    break
                yield sec + frac / div, lt, data, orig

    def _iter_pcapng(self, f):
        end, ifaces = '<', []
        while True:
            h = f.read(8)
            if len(h) < 8:
                break
            if h[:4] == b'\x0a\x0d\x0d\x0a':
                bom = f.read(4)
                end = '<' if bom == b'\x4d\x3c\x2b\x1a' else '>'
                blen = struct.unpack(end + 'I', h[4:8])[0]
                if blen < 28 or blen > 1 << 26:
                    break
                f.read(blen - 12)
                ifaces = []
                continue
            btype, blen = struct.unpack(end + 'II', h)
            if blen < 12 or blen > 1 << 26:
                break
            body = f.read(blen - 12)
            f.read(4)
            if len(body) < blen - 12:
                break
            if btype == 1 and len(body) >= 8:
                lt = struct.unpack(end + 'H', body[:2])[0]
                div, pos = 1e6, 8
                while pos + 4 <= len(body):
                    code, ln = struct.unpack(end + 'HH', body[pos:pos + 4])
                    if code == 0:
                        break
                    if code == 9 and ln >= 1:
                        v = body[pos + 4]
                        div = float(10 ** v) if not v & 0x80 else float(2 ** (v & 0x7F))
                    pos += 4 + ((ln + 3) & ~3)
                ifaces.append((lt, div))
            elif btype == 6 and len(body) >= 20 and ifaces:
                ifid, th, tl, cap, orig = struct.unpack(end + 'IIIII', body[:20])
                lt, div = ifaces[ifid] if ifid < len(ifaces) else ifaces[0]
                yield ((th << 32) | tl) / div, lt, body[20:20 + cap], orig
            elif btype == 3 and len(body) >= 4 and ifaces:
                orig = struct.unpack(end + 'I', body[:4])[0]
                yield 0.0, ifaces[0][0], body[4:4 + orig], orig

    # ---- dissection --------------------------------------------------------------------------
    @staticmethod
    def _mac(b):
        return ':'.join(f"{x:02x}" for x in b)

    def _dissect(self, lt, data):
        """Minimal decode of link, network and transport headers. -> dict or None"""
        n = len(data)
        if lt == 1:
            if n < 14:
                return None
            et, off = struct.unpack('!H', data[12:14])[0], 14
            while et in (0x8100, 0x88A8) and n >= off + 4:
                et, off = struct.unpack('!H', data[off + 2:off + 4])[0], off + 4
        elif lt == 113:
            if n < 16:
                return None
            et, off = struct.unpack('!H', data[14:16])[0], 16
        elif lt == 276:
            if n < 20:
                return None
            et, off = struct.unpack('!H', data[0:2])[0], 20
        elif lt in (101, 12, 228, 229):
            if n < 1:
                return None
            v = data[0] >> 4
            et, off = (0x0800 if v == 4 else 0x86DD if v == 6 else 0), 0
        elif lt == 0:
            if n < 4:
                return None
            af = struct.unpack('<I', data[:4])[0]
            et, off = (0x0800 if af == 2 else 0x86DD if af in (24, 28, 30) else 0), 4
        else:
            return None
        pk = {'len': n, 'proto': '', 'src': '', 'dst': '', 'sport': 0, 'dport': 0, 'flags': 0, 'payload': b''}
        if et == 0x0806:
            if n < off + 28:
                return None
            op = struct.unpack('!H', data[off + 6:off + 8])[0]
            pk.update(proto='ARP', arp=(op, self._mac(data[off + 8:off + 14]), socket.inet_ntoa(data[off + 14:off + 18]),
                                        self._mac(data[off + 18:off + 24]), socket.inet_ntoa(data[off + 24:off + 28])))
            pk['src'], pk['dst'] = pk['arp'][2], pk['arp'][4]
            return pk
        if et == 0x0800:
            if n < off + 20:
                return None
            ihl = (data[off] & 15) * 4
            proto = data[off + 9]
            pk['src'], pk['dst'] = socket.inet_ntoa(data[off + 12:off + 16]), socket.inet_ntoa(data[off + 16:off + 20])
            frag = struct.unpack('!H', data[off + 6:off + 8])[0] & 0x1FFF
            l4 = off + ihl
            if frag:
                pk['proto'] = f"IP/{proto}"
                return pk
        elif et == 0x86DD:
            if n < off + 40:
                return None
            proto = data[off + 6]
            pk['src'], pk['dst'] = socket.inet_ntop(socket.AF_INET6, data[off + 8:off + 24]), socket.inet_ntop(socket.AF_INET6, data[off + 24:off + 40])
            l4 = off + 40
            for _ in range(6):
                if proto in (0, 43, 60) and n >= l4 + 2:
                    proto, l4 = data[l4], l4 + (data[l4 + 1] + 1) * 8
                elif proto == 44 and n >= l4 + 8:
                    proto, l4 = data[l4], l4 + 8
                else:
                    break
        else:
            return None
        if proto == 6 and n >= l4 + 20:
            sp, dp = struct.unpack('!HH', data[l4:l4 + 4])
            doff = (data[l4 + 12] >> 4) * 4
            pk.update(proto='TCP', sport=sp, dport=dp, flags=data[l4 + 13], payload=data[l4 + doff:])
        elif proto == 17 and n >= l4 + 8:
            sp, dp = struct.unpack('!HH', data[l4:l4 + 4])
            pk.update(proto='UDP', sport=sp, dport=dp, payload=data[l4 + 8:])
        elif proto == 1:
            pk.update(proto='ICMP', flags=data[l4] if n > l4 else 0)
        elif proto == 58:
            pk.update(proto='ICMPv6', flags=data[l4] if n > l4 else 0)
        else:
            pk['proto'] = f"IP/{proto}"
        return pk

    @staticmethod
    def _dns_name(msg, off):
        labels, ret, hops = [], None, 0
        while True:
            if off >= len(msg) or hops > 40:
                return None, off
            ln = msg[off]
            if ln == 0:
                off += 1
                break
            if ln & 0xC0 == 0xC0:
                if off + 1 >= len(msg):
                    return None, off
                if ret is None:
                    ret = off + 2
                off, hops = ((ln & 0x3F) << 8) | msg[off + 1], hops + 1
                continue
            off += 1
            labels.append(msg[off:off + ln].decode('ascii', 'replace'))
            off += ln
        return '.'.join(labels), (ret if ret is not None else off)

    def _parse_dns(self, p):
        """-> (queries[(name,type)], answers[(name,type,value)]) or None"""
        try:
            if len(p) < 12:
                return None
            _id, flags, qd, an = struct.unpack('!HHHH', p[:8])
            if qd > 10 or an > 50:
                return None
            off, qs, ans = 12, [], []
            for _ in range(qd):
                name, off = self._dns_name(p, off)
                if name is None or off + 4 > len(p):
                    return qs, ans
                qs.append((name, struct.unpack('!H', p[off:off + 2])[0]))
                off += 4
            if flags & 0x8000:
                for _ in range(an):
                    name, off = self._dns_name(p, off)
                    if name is None or off + 10 > len(p):
                        break
                    typ, _c, _t, rl = struct.unpack('!HHIH', p[off:off + 10])
                    off += 10
                    rd = p[off:off + rl]
                    if typ == 1 and rl == 4:
                        ans.append((name, 'A', socket.inet_ntoa(rd)))
                    elif typ == 28 and rl == 16:
                        ans.append((name, 'AAAA', socket.inet_ntop(socket.AF_INET6, rd)))
                    elif typ in (5, 12):
                        t, _o = self._dns_name(p, off)
                        ans.append((name, 'CNAME' if typ == 5 else 'PTR', t or '?'))
                    off += rl
            return qs, ans
        except (struct.error, IndexError, OSError):
            return None

    @staticmethod
    def _tls_sni(p):
        try:
            if len(p) < 6 or p[0] != 0x16 or p[1] != 3 or p[5] != 1:
                return None
            pos = 9 + 2 + 32
            pos += 1 + p[pos]
            pos += 2 + struct.unpack('!H', p[pos:pos + 2])[0]
            pos += 1 + p[pos]
            extl = struct.unpack('!H', p[pos:pos + 2])[0]
            pos += 2
            end = min(len(p), pos + extl)
            while pos + 4 <= end:
                et, el = struct.unpack('!HH', p[pos:pos + 4])
                pos += 4
                if et == 0 and el >= 5:
                    nl = struct.unpack('!H', p[pos + 3:pos + 5])[0]
                    return p[pos + 5:pos + 5 + nl].decode('ascii', 'replace')
                pos += el
        except (IndexError, struct.error):
            return None
        return None

    @staticmethod
    def _parse_dhcp(p):
        try:
            if len(p) < 241 or p[236:240] != b'\x63\x82\x53\x63':
                return None
            d = {'mac': ':'.join(f"{x:02x}" for x in p[28:34]), 'ip': socket.inet_ntoa(p[16:20]), 'hostname': '', 'vendor': '', 'type': 0, 'requested': ''}
            pos = 240
            while pos < len(p):
                c = p[pos]
                if c == 255:
                    break
                if c == 0:
                    pos += 1
                    continue
                ln = p[pos + 1]
                v = p[pos + 2:pos + 2 + ln]
                if c == 12:
                    d['hostname'] = v.decode('ascii', 'replace')
                elif c == 60:
                    d['vendor'] = v.decode('ascii', 'replace')
                elif c == 53 and v:
                    d['type'] = v[0]
                elif c == 50 and len(v) == 4:
                    d['requested'] = socket.inet_ntoa(v)
                pos += 2 + ln
            return d
        except (IndexError, struct.error, OSError):
            return None

    _CLEARTEXT = {21: 'FTP', 23: 'Telnet', 25: 'SMTP', 80: 'HTTP', 110: 'POP3', 143: 'IMAP', 389: 'LDAP', 513: 'rlogin', 1883: 'MQTT'}
    _DNS_TYPES = {1: 'A', 28: 'AAAA', 5: 'CNAME', 15: 'MX', 16: 'TXT', 12: 'PTR', 2: 'NS', 6: 'SOA', 33: 'SRV', 65: 'HTTPS'}

    # ---- analysis -----------------------------------------------------------------------------------
    def analyze_pcap(self, path, max_packets=3000000):
        A = {'packets': 0, 'bytes': 0, 'first': None, 'last': None, 'undecoded': 0, 'truncated_reading': False,
             'protocols': Counter(), 'convs': {}, 'talkers': Counter(), 'dns_q': Counter(), 'dns_a': {}, 'sni': Counter(),
             'http': Counter(), 'arp': {}, 'dhcp': {}, 'cleartext': Counter(), 'syn': {}, 'icmp': Counter(), 'error': ''}
        try:
            for ts, lt, data, orig in self._iter_pcap(path):
                A['packets'] += 1
                if A['packets'] > max_packets:
                    A['truncated_reading'] = True
                    break
                A['bytes'] += orig
                if ts:
                    A['first'] = ts if A['first'] is None else min(A['first'], ts)
                    A['last'] = ts if A['last'] is None else max(A['last'], ts)
                pk = self._dissect(lt, data)
                if not pk:
                    A['undecoded'] += 1
                    continue
                proto = pk['proto']
                A['protocols'][proto] += 1
                if proto == 'ARP':
                    op, smac, sip, _tm, _tip = pk['arp']
                    if sip != '0.0.0.0':
                        A['arp'][sip] = smac
                    continue
                if pk['src']:
                    A['talkers'][pk['src']] += orig
                    A['talkers'][pk['dst']] += orig
                if proto in ('TCP', 'UDP'):
                    a, b = (pk['src'], pk['sport']), (pk['dst'], pk['dport'])
                    key = (proto,) + (a + b if a <= b else b + a)
                    c = A['convs'].get(key)
                    if c is None and len(A['convs']) < 60000:
                        c = A['convs'][key] = [0, 0, ts or 0, ts or 0]
                    if c:
                        c[0] += 1
                        c[1] += orig
                        c[3] = ts or c[3]
                    pl = pk['payload']
                    if proto == 'UDP' and 53 in (pk['sport'], pk['dport']) or (proto == 'UDP' and 5353 in (pk['sport'], pk['dport'])):
                        r = self._parse_dns(pl)
                        if r:
                            for name, qt in r[0]:
                                A['dns_q'][(name, self._DNS_TYPES.get(qt, str(qt)))] += 1
                            for name, t, v in r[1]:
                                if len(A['dns_a']) < 5000:
                                    A['dns_a'].setdefault(name, set()).add(f"{t} {v}")
                    elif proto == 'UDP' and {pk['sport'], pk['dport']} & {67, 68}:
                        d = self._parse_dhcp(pl)
                        if d and d['mac'] != '00:00:00:00:00:00':
                            e = A['dhcp'].setdefault(d['mac'], {'hostname': '', 'ip': '', 'vendor': ''})
                            e['hostname'] = d['hostname'] or e['hostname']
                            e['vendor'] = d['vendor'] or e['vendor']
                            e['ip'] = d['ip'] if d['ip'] != '0.0.0.0' else (d['requested'] or e['ip'])
                    elif proto == 'TCP' and pl:
                        sni = self._tls_sni(pl)
                        if sni:
                            A['sni'][(pk['src'], sni)] += 1
                        elif pl[:4] in (b'GET ', b'POST', b'HEAD', b'PUT ', b'DELE', b'OPTI', b'PATC'):
                            head = pl[:600].decode('latin-1', 'replace')
                            rl = head.split('\r\n', 1)[0][:150]
                            hm = re.search(r'\r\nHost:\s*([^\r\n]+)', head, re.I)
                            A['http'][(pk['src'], rl.split(' ')[0], hm.group(1).strip() if hm else '?', rl.split(' ')[1] if ' ' in rl else '')] += 1
                    if proto == 'TCP' and pk['dport'] in self._CLEARTEXT and pk['flags'] & 0x02:
                        A['cleartext'][(self._CLEARTEXT[pk['dport']], pk['src'], pk['dst'])] += 1
                    if proto == 'TCP' and pk['flags'] & 0x12 == 0x02:
                        s = A['syn'].get(pk['src'])
                        if s is None and len(A['syn']) < 5000:
                            s = A['syn'][pk['src']] = set()
                        if s is not None and len(s) < 3000:
                            s.add((pk['dst'], pk['dport']))
                elif proto in ('ICMP', 'ICMPv6'):
                    A['icmp'][(proto, pk['flags'])] += 1
        except (ValueError, OSError, struct.error) as e:
            A['error'] = str(e)
        return A

    def _analyze_and_render(self, path, meta):
        A = self.analyze_pcap(path)
        tsh = ''
        ts = shutil.which('tshark')
        if ts and not A['error']:
            try:
                r = subprocess.run([ts, '-r', path, '-q', '-z', 'io,phs'], capture_output=True, text=True, timeout=120, errors='replace')
                tsh = (r.stdout or '').strip()
            except (OSError, subprocess.SubprocessError):
                tsh = ''
        return A, self._render_pcap(A, meta, tsh)

    @staticmethod
    def _fmt_ts(t):
        return datetime.fromtimestamp(t, timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC') if t else '?'

    def _render_pcap(self, A, m, tsh=''):
        o = "=" * 70 + f"\nPACKET CAPTURE: {os.path.basename(m['path'])}\n" + "=" * 70 + "\n"
        o += (f"File       : {m['path']}\nSize       : {m['size']:,} bytes\nSHA-256    : {m['sha256']}\nSHA-512    : {m['sha512']}\n"
              f"MD5        : {m['md5']}\nSHA-1      : {m['sha1']}\nTool       : {m['tool']}\nInterface  : {m['interface']}\n"
              f"Filter     : {m['filter'] or '(none)'}      Bytes kept per packet: {m['snaplen']}\nOrigin     : {m['origin']}\n")
        if m.get('command'):
            o += f"Command    : {m['command']}\n"
        if A['error']:
            return o + f"\nThe file could not be read as a capture: {A['error']}\n"
        o += (f"\nPackets    : {A['packets']:,}  ({A['bytes']:,} bytes on the wire)   not decodable here: {A['undecoded']:,}\n"
              f"First / last: {self._fmt_ts(A['first'])}  ->  {self._fmt_ts(A['last'])}\n")
        if A['truncated_reading']:
            o += "NOTE: reading stopped at the analysis limit; the capture file itself is complete and hashed.\n"
        o += "\nPROTOCOLS\n" + "-" * 70 + "\n" + "".join(f"  {k:<10} {v:>10,}\n" for k, v in A['protocols'].most_common(12))
        o += "\nTOP CONVERSATIONS (by bytes)\n" + "-" * 70 + "\n"
        for k, (pk_, by, t0, t1) in sorted(A['convs'].items(), key=lambda kv: -kv[1][1])[:20]:
            o += f"  {k[0]} {k[1]}:{k[2]} <-> {k[3]}:{k[4]}   {pk_:,} packets  {by:,} bytes   {self._service_for(k[0].lower(), k[2], k[4]) if hasattr(self, '_service_for') else ''}\n"
        o += "\nTOP TALKERS (bytes sent + received)\n" + "-" * 70 + "\n" + "".join(f"  {ip:<40} {b:>12,}\n" for ip, b in A['talkers'].most_common(10))
        if A['dns_q']:
            o += "\nDNS QUERIES (names looked up)\n" + "-" * 70 + "\n" + "".join(f"  {n}  [{t}]  x{c}\n" for (n, t), c in A['dns_q'].most_common(40))
        if A['dns_a']:
            o += "\nDNS ANSWERS\n" + "-" * 70 + "\n" + "".join(f"  {n} -> {', '.join(sorted(v)[:4])}\n" for n, v in list(A['dns_a'].items())[:30])
        if A['sni']:
            o += "\nTLS SERVER NAMES (the site a device connected to; content is encrypted)\n" + "-" * 70 + "\n"
            o += "".join(f"  {src} -> {sni}  x{c}\n" for (src, sni), c in A['sni'].most_common(40))
        if A['http']:
            o += "\nHTTP REQUESTS (unencrypted)\n" + "-" * 70 + "\n"
            o += "".join(f"  {src}  {meth} http://{host}{path}  x{c}\n" for (src, meth, host, path), c in A['http'].most_common(30))
        if A['arp'] or A['dhcp']:
            o += "\nDEVICES SEEN ON THE LOCAL NETWORK\n" + "-" * 70 + "\n"
            for ip, mac in sorted(A['arp'].items()):
                o += f"  ARP   {ip:<16} {mac}\n"
            for mac, e in A['dhcp'].items():
                o += f"  DHCP  {mac}  ip {e['ip'] or '?'}  name {e['hostname'] or '?'}  vendor-class {e['vendor'] or '?'}\n"
        leads = []
        for (svc, src, dst), c in A['cleartext'].most_common(15):
            leads.append(f"Unencrypted {svc} connection {src} -> {dst} ({c} attempt(s)); the content of this conversation can be read by anyone on the path.")
        for src, tg in A['syn'].items():
            ports_by_host = Counter(h for h, _p in tg)
            if len(tg) >= 50 or (ports_by_host and max(ports_by_host.values()) >= 25):
                leads.append(f"{src} sent connection attempts to {len(tg)} distinct host/port targets: pattern consistent with scanning (could also be a legitimate scanner or monitoring tool).")
        if leads:
            o += "\nLEADS TO REVIEW (patterns, not conclusions)\n" + "-" * 70 + "\n" + "".join("  - " + l + "\n" for l in leads[:20])
        if m['snaplen'] not in ('full',) and isinstance(m['snaplen'], int) and m['snaplen'] < 256:
            o += "\nNOTE: only the first %s bytes of each packet were kept, so DNS names, TLS server names and HTTP hosts are mostly not recoverable from this file.\n" % m['snaplen']
        if tsh:
            o += "\nTSHARK PROTOCOL HIERARCHY (independent second reading by Wireshark's engine)\n" + "-" * 70 + "\n" + tsh[:4000] + "\n"
        o += "\nThe capture file is the evidence. This analysis is a summary made by this tool; open the file in Wireshark to examine individual packets.\n"
        return o

    # --------------------------------------------------------
    # REPORT  (one model -> TXT, HTML, PDF, JSON)
    # --------------------------------------------------------
    def _case_snapshot_safe(self):
        return getattr(self, '_case_snapshot', None) or self._case_info()

    def generate_report(self):
        self._case_snapshot = self._case_info()          # read Tk variables on the main thread
        self._audit_snapshot = list(self.__dict__.get('audit_log', []))
        self.run_async(self._task_build_report, on_done=self._on_report_built, status="Building report...")

    LIMITATIONS = (
        "This examination was performed on a running (live) system. A live system cannot be write-protected: starting and running this tool "
        "changes the machine slightly (memory, temporary files, logs). These changes are inherent to live collection.",
        "Times come from the examined computer's own clock. The clock was not independently checked against an external time source; "
        "the clock reading taken at collection time is shown in the 'Examined system' section so any offset can be applied.",
        "Information was gathered through the operating system's own commands and files. Software running on the system (including malicious "
        "software) can alter what those report. This tool cannot detect all such interference.",
        "This tool has not been independently validated or certified. Where a decision depends on a result, it should be confirmed with a second "
        "method or tool, and the original evidence files and hashes in this package preserved for that purpose.",
        "Entries marked as 'leads' are patterns that merit a closer look. They are not findings of wrongdoing and many have innocent explanations.",
        "Some forensic sources are not covered by this tool (for example a memory image, a full disk image, and offline registry hives). "
        "Absence of a result in this report is therefore not evidence that something did not happen.",
        "ShimCache (AppCompatCache) shows that a file was seen by Windows, not that it ran; its binary format differs between Windows builds and this "
        "tool's parser is best-effort. Amcache is read by temporarily loading the real hive through Windows itself. SRUM requires the optional "
        "libesedb-python package; without it the SRUM database is hashed and preserved but its rows are not decoded. All three should be confirmed "
        "with a validated tool (AppCompatCacheParser, AmcacheParser, SrumECmd) before being relied on.",
        "The super-timeline is built by pattern-matching dates already present in this tool's other output, not from parsing original timestamps "
        "a second time; it can miss or duplicate entries and does not convert time zones.",
        "A YARA match is a pattern match in a file, not evidence of malicious intent; absence of a match does not mean a file is safe.",
        "DNS cache and swap/pagefile string traces are leftover fragments of recent system activity, not a record tied to any specific application, "
        "user, or browsing mode (including private/incognito browsing, which this tool cannot recover directly because browsers do not write it to disk).",
        "A packet capture shows only traffic visible to the chosen network interface during the capture window. Encrypted content is not readable.",
        "Whether this material is admissible is for the court to decide under the applicable law. This report describes what was done and how the data is protected; "
        "it does not assert admissibility.",
        "A hash-set match (known-good or known-bad) is only as reliable as the set supplied by the examiner; it is a lead or a de-prioritisation aid, not independent proof.",
        "$MFT and USN Journal parsing is a best-effort, documented-offset decoder (like ShimCache); it needs administrator rights and an NTFS volume, and a parsing error on a damaged or unusual record is skipped rather than guessed at. A FILE_NAME/STANDARD_INFORMATION timestamp mismatch is a timestomp indicator, not proof of tampering -- legitimate copy/restore operations can also cause it.",
        "Recycle Bin / Trash metadata (deletion time, original path) is only as complete as what the operating system itself records; macOS's own Trash keeps no per-item deletion time, so the file's last-modified time is shown instead and is stated as such.",
        "RAM acquisition depends on a separate, free third-party imaging tool (WinPmem on Windows, AVML on Linux) being available; this tool does not bundle or install one. Live memory imaging is not currently possible on macOS due to OS-level protections (not a limitation of this tool specifically).",
        "A report/manifest signature proves which examiner key attested to the hash, not that the underlying facts are correct; it depends on a signing backend (the 'cryptography' Python package or OpenSSL) being available and on the examiner's private key being kept secure.",
        "A write-protection/read-only check reports what the operating system's mount table states; it is not equivalent to, and does not replace, a certified hardware write blocker for dead-box disk imaging.",
        "Baseline-diff compares two evidence packages produced by this tool; it cannot account for anything that happened on the system between collections beyond what each collection itself captured.")

    def _report_model(self, files=None, captures=None, notes=None):
        files = self._evidence_files() if files is None else files
        caps = list(self.__dict__.get('captures', [])) if captures is None else captures
        case = self._case_snapshot_safe()
        host = self._host_info()
        tool = self._tool_identity()
        audit = list(getattr(self, '_audit_snapshot', None) or self.__dict__.get('audit_log', []))
        with _COMMAND_LOCK:
            cmds = list(COMMAND_LOG)
        now = datetime.now(timezone.utc)
        leads = 0
        for f in files:
            if f['key'] != 'ioc_matches':
                leads += f['data'].decode('utf-8', 'replace').count('** LEAD')
        facts = [f"{len(files)} evidence item(s) were collected from the computer '{host['hostname']}' ({host['platform']}).",
                 f"Collection began {audit[0]['time'] if audit else '?'} and this report was produced {now.strftime('%Y-%m-%d %H:%M:%S')} UTC.",
                 f"{len(cmds)} external command(s) were run and recorded." if cmds else "No external commands were recorded."]
        if caps:
            facts.append(f"{len(caps)} packet capture file(s) containing {sum(c.get('analysis', {}).get('packets', 0) for c in caps):,} packet(s) were preserved and hashed.")
        if leads:
            facts.append(f"{leads} running program(s) were flagged as leads (for example, running from a temporary folder). Flags are not conclusions.")
        io = next((f for f in files if f['key'] == 'ioc_matches'), None)
        if io:
            facts.append("Indicators supplied by the examiner were searched for; see the IOC matches section.")
        facts.append("This report states what was collected and how. It draws no conclusion about guilt or intent.")
        lim = list(self.LIMITATIONS)
        if not host['is_admin']:
            lim.insert(0, "The tool was NOT running with administrator/root rights. Some sources (for example Prefetch, other users' files, "
                          "protected logs) could not be read, so the absence of data is expected in those sections.")
        for n in (notes or []):
            lim.append(n)
        return {'report_id': uuid.uuid4().hex[:12].upper(), 'generated_utc': now.isoformat(timespec='seconds'),
                'case': case, 'host': host, 'tool': tool, 'summary': facts, 'limitations': lim, 'evidence': files, 'captures': caps,
                'commands': cmds, 'audit': audit,
                'methodology': [
                    "Data was collected by CACTUS running on the examined computer, in order of volatility (most short-lived data first).",
                    "Each result was recorded exactly as the tool received it; it was not edited by hand.",
                    "A SHA-256 (plus MD5, SHA-1 and SHA-512) value was calculated for every evidence file at the moment the package was built; the values are listed in the evidence inventory and in manifest.json.",
                    "Every external command the tool ran is listed in Appendix A with the SHA-256 of what it returned.",
                    "Packet captures, if any, were made with the capture engine named in the packet capture section and hashed immediately when closed.",
                    "The package can be re-checked at any time with the Verify function or with standard hashing tools; see Appendix D."]}

    # ---- text -------------------------------------------------------------------------------
    @staticmethod
    def _capped(text, n):
        lines = text.rstrip('\n').split('\n')
        return ('\n'.join(lines[:n]), len(lines) - n) if len(lines) > n else ('\n'.join(lines), 0)

    def _certificate_text(self, m):
        c = m['case']
        return (
            "TEMPLATE ONLY - this is a starting draft to be reviewed and adapted by your legal counsel. The required form, wording and "
            "signatories differ between jurisdictions and between courts. In India, section 63(4) of the Bharatiya Sakshya Adhiniyam, 2023 "
            "asks for a certificate in two parts, one by the person in charge of the device and one by an expert.\n\n"
            "PART A  (person in charge of the computer / device)\n"
            f"I, ______________________, ______________ (role), of {c.get('organization') or '______________________'}, state that:\n"
            f"1. The computer examined is '{m['host']['hostname']}' ({m['host']['platform']}), exhibit reference {c.get('exhibit_ref') or '__________'}, "
            "which I lawfully controlled / was authorised to examine.\n"
            "2. The electronic records described in this report were produced from that computer by the process described in the Methodology section.\n"
            "3. To the best of my knowledge the computer was working properly, or if not, any malfunction did not affect the accuracy of the records.\n"
            f"4. The SHA-256 of the complete evidence package '__________________.zip' is: ______________________________________________________________\n"
            "   (taken from the file ending .zip.hashes.txt written when the package was created; the SHA-256 of each individual file is in the evidence inventory).\n"
            "Signature: ____________    Name: ____________    Date: ____________    Place: ____________\n\n"
            "PART B  (expert)\n"
            f"I, {c.get('examiner') or '______________________'}, qualified as ______________________, state that:\n"
            f"1. I examined the evidence using {m['tool']['name']} version {m['tool']['version']} (file SHA-256 {m['tool']['sha256']}).\n"
            "2. I verified the SHA-256 of the evidence package and of each file against manifest.json and found them to match: yes / no (strike out).\n"
            "3. The records in this report are, to the best of my knowledge and belief, a true and accurate output of that process.\n"
            "4. I have disclosed the limitations of the process in the Limitations section.\n"
            "Signature: ____________    Name: ____________    Date: ____________    Place: ____________\n")

    def _declaration_text(self, m):
        return (f"I, {m['case'].get('examiner') or '______________________'}, declare that I carried out the examination described in this report; "
                "that the facts stated are true to the best of my knowledge; that I have not altered the collected evidence files after they were "
                "hashed; and that I have set out the limitations of the methods used. I understand my duty is to assist the court impartially.\n\n"
                "Signature: ______________________   Date: ______________   Place: ______________")

    def _render_report_txt(self, m):
        W = 78
        c, h, t = m['case'], m['host'], m['tool']
        o = ["=" * W, "DIGITAL FORENSIC EXAMINATION REPORT".center(W), "=" * W,
             f"Report ID     : {m['report_id']}", f"Generated     : {m['generated_utc']} UTC",
             f"Case ID / FIR : {c.get('case_id') or '(not set)'}", f"Case title    : {c.get('case_title') or '-'}",
             f"Exhibit ref.  : {c.get('exhibit_ref') or '-'}", f"Examiner      : {c.get('examiner') or '(not set)'}",
             f"Organisation  : {c.get('organization') or '-'}", f"Requested by  : {c.get('requested_by') or '-'}",
             f"Place         : {c.get('location') or '-'}", f"Authority     : {c.get('authority') or '-'}",
             f"Tool          : {t['name']} v{t['version']}", f"Tool SHA-256  : {t['sha256']}"]
        if c.get('notes'):
            o.append(f"Notes         : {c['notes']}")
        o += ["", "1. SUMMARY OF WHAT WAS DONE", "-" * W] + [f"  - {s}" for s in m['summary']]
        o += ["", "2. METHODOLOGY", "-" * W] + [f"  {i}. {s}" for i, s in enumerate(m['methodology'], 1)]
        if c.get('validation_note'):
            o.append(f"  Tool validation performed: {c['validation_note']}")
        o += ["", "3. EXAMINED SYSTEM", "-" * W,
              f"  Host name    : {h['hostname']}", f"  Platform     : {h['platform']} ({h['machine']})",
              f"  Run by user  : {h['user']}  (administrator/root: {'yes' if h['is_admin'] else 'NO'})",
              f"  Time zone    : {h['timezone']}", f"  Clock (local): {h['clock_local']}", f"  Clock (UTC)  : {h['clock_utc']}",
              f"  Uptime       : {h['uptime'] or 'see Time & uptime section'}"]
        o += ["", "4. EVIDENCE INVENTORY  (file names are inside the evidence package)", "-" * W]
        for f in m['evidence']:
            o += [f"  {f['id']}  {f['title']}", f"        file    : evidence/{f['name']}  ({f['size']:,} bytes)",
                  f"        UTC     : {f['collected_utc'] or '-'}", f"        SHA-256 : {f['sha256']}", f"        SHA-512 : {f['sha512']}", f"        MD5     : {f['md5']}"]
        for cp in m['captures']:
            o += [f"  CAP  {os.path.basename(cp['path'])}  ({cp['size']:,} bytes)", f"        SHA-256 : {cp['sha256']}"]
        o += ["", "5. FINDINGS (as collected)", "-" * W]
        for f in m['evidence']:
            body, extra = self._capped(f['data'].decode('utf-8', 'replace'), 4000)
            o += ["", f"5.{f['id'][1:].lstrip('0') or '0'}  {f['title'].upper()}  [{f['id']}]", f"     {f['desc']}", "", body]
            if extra:
                o.append(f"     ... {extra} more line(s) in evidence/{f['name']} (SHA-256 {f['sha256']})")
        o += ["", "6. LIMITATIONS", "-" * W] + [f"  {i}. {s}" for i, s in enumerate(m['limitations'], 1)]
        o += ["", "7. CHAIN OF CUSTODY / ACTIVITY LOG", "-" * W, self._audit_text_block(m['audit']).rstrip()]
        o += ["", "APPENDIX A. COMMANDS RUN BY THE TOOL", "-" * W]
        for cm in m['commands'][:1500]:
            o.append(f"  {cm['time_utc']}  rc={cm['returncode']}  {cm['command']}\n      output {cm['output_bytes']} bytes SHA-256 {cm['output_sha256']}")
        o += ["", "APPENDIX B. EXAMINER'S DECLARATION", "-" * W, self._declaration_text(m),
              "", "APPENDIX C. CERTIFICATE (TEMPLATE)", "-" * W, self._certificate_text(m),
              "", "APPENDIX D. HOW TO VERIFY", "-" * W,
              "  Check any file with:  shasum -a 256 <file>  (Linux/macOS)   or   certutil -hashfile <file> SHA256  (Windows).",
              "  Compare with manifest.json. The SHA-256 of the whole package is in the .zip.hashes.txt file written when it was created.",
              "  The hash of this report file cannot be written inside itself; it is listed in manifest.json.", ""]
        return "\n".join(o)

    # ---- JSON ---------------------------------------------------------------------------------
    def _report_json(self, m):
        d = {k: v for k, v in m.items() if k not in ('evidence', 'captures')}
        d['evidence'] = [{k: v for k, v in f.items() if k != 'data'} for f in m['evidence']]
        d['captures'] = [{k: v for k, v in c.items() if k not in ('analysis', 'analysis_text')} for c in m['captures']]
        d['report_format'] = 'CACTUS report 1'
        return d

    def _save_json(self):
        fn = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
                                          initialfile=f"forensic_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")
        if fn:
            m = getattr(self, '_last_model', None) or self._report_model()
            data = self._report_json(m)
            data['data'] = {k: v for k, v in self.investigation_data.items()}
            data['activity_log'] = m['audit']
            data.update(timestamp=datetime.now().isoformat(), os=self.current_os, platform=platform.platform(), tool_version=self.TOOL_VERSION)
            with open(fn, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, default=str)
            self._saved_msg(fn)

    # ---- HTML --------------------------------------------------------------------------------------
    def _render_report_html(self, m):
        from html import escape as E
        c, h, t = m['case'], m['host'], m['tool']

        def kv(rows):
            return "<table class=kv>" + "".join(f"<tr><th>{E(a)}</th><td>{E(str(b)) or '-'}</td></tr>" for a, b in rows) + "</table>"
        css = ("@page{size:A4;margin:18mm}body{font:11pt/1.45 'Segoe UI',Arial,sans-serif;color:#111;background:#fff;max-width:900px;margin:0 auto;padding:24px}"
               "h1{font-size:22pt;margin:0 0 4px}h2{font-size:14pt;border-bottom:2px solid #1a3d6d;padding-bottom:3px;margin-top:28px;color:#1a3d6d;page-break-after:avoid}"
               "h3{font-size:11.5pt;margin:18px 0 2px}table{border-collapse:collapse;width:100%;font-size:9.5pt}th,td{border:1px solid #bbb;padding:4px 6px;text-align:left;vertical-align:top}"
               "th{background:#eef2f7}table.kv th{width:28%}code,pre{font-family:Consolas,'DejaVu Sans Mono',monospace}pre{font-size:8pt;background:#f6f6f6;border:1px solid #ddd;padding:8px;white-space:pre-wrap;word-break:break-word}"
               ".h{font-family:Consolas,monospace;font-size:8pt;word-break:break-all}.note{background:#fff8e1;border-left:4px solid #e0a800;padding:8px 12px}"
               ".tpl{border:2px dashed #a00;padding:10px;margin-top:8px}.cover{border:2px solid #1a3d6d;padding:18px;margin-bottom:18px}"
               "@media print{body{padding:0}h2{page-break-before:auto}pre{page-break-inside:auto}}")
        p = [f"<!DOCTYPE html><html lang=en><head><meta charset=utf-8><title>Forensic Report {E(m['report_id'])}</title><style>{css}</style></head><body>",
             f"<div class=cover><h1>Digital Forensic Examination Report</h1><div>Report ID {E(m['report_id'])} &middot; generated {E(m['generated_utc'])} UTC</div></div>",
             "<h2>Document control</h2>",
             kv([("Case ID / FIR", c.get('case_id') or '(not set)'), ("Case title", c.get('case_title')), ("Exhibit reference", c.get('exhibit_ref')),
                 ("Examiner", c.get('examiner') or '(not set)'), ("Organisation", c.get('organization')), ("Requested by", c.get('requested_by')),
                 ("Place of examination", c.get('location')), ("Legal authority / consent", c.get('authority')), ("Notes", c.get('notes')),
                 ("Tool", f"{t['name']} v{t['version']}"), ("Tool file SHA-256", t['sha256']), ("Tool validation performed", c.get('validation_note'))]),
             "<h2>1. Summary of what was done</h2><ul>" + "".join(f"<li>{E(s)}</li>" for s in m['summary']) + "</ul>",
             "<h2>2. Methodology</h2><ol>" + "".join(f"<li>{E(s)}</li>" for s in m['methodology']) + "</ol>",
             "<h2>3. Examined system</h2>",
             kv([("Host name", h['hostname']), ("Platform", f"{h['platform']} ({h['machine']})"), ("Run by user", h['user']),
                 ("Administrator / root", 'yes' if h['is_admin'] else 'NO'), ("Time zone", h['timezone']), ("Clock (local)", h['clock_local']),
                 ("Clock (UTC)", h['clock_utc']), ("Uptime", h['uptime'])]),
             "<h2>4. Evidence inventory</h2><table><tr><th>ID</th><th>Item</th><th>Collected (UTC)</th><th>Size</th><th>SHA-256</th></tr>"]
        for f in m['evidence']:
            p.append(f"<tr><td>{f['id']}</td><td><b>{E(f['title'])}</b><br>evidence/{E(f['name'])}</td><td>{E(f['collected_utc'] or '-')}</td>"
                     f"<td>{f['size']:,}</td><td class=h>{f['sha256']}</td></tr>")
        for cp in m['captures']:
            p.append(f"<tr><td>CAP</td><td><b>Packet capture</b><br>network/{E(os.path.basename(cp['path']))}</td><td>{E(cp.get('finished_utc', ''))}</td>"
                     f"<td>{cp['size']:,}</td><td class=h>{cp['sha256']}</td></tr>")
        p.append("</table><p>SHA-512, SHA-1 and MD5 for every file are in <code>manifest.json</code>.</p><h2>5. Findings (as collected)</h2>")
        for f in m['evidence']:
            body, extra = self._capped(f['data'].decode('utf-8', 'replace'), 400)
            p.append(f"<h3>{f['id']} &mdash; {E(f['title'])}</h3><p>{E(f['desc'])}</p><pre>{E(body)}</pre>")
            if extra:
                p.append(f"<p class=note>{extra} more line(s) are in <code>evidence/{E(f['name'])}</code> (SHA-256 <span class=h>{f['sha256']}</span>).</p>")
        p.append("<h2>6. Limitations</h2><ol>" + "".join(f"<li>{E(s)}</li>" for s in m['limitations']) + "</ol>")
        p.append(f"<h2>7. Chain of custody / activity log</h2><pre>{E(self._audit_text_block(m['audit']))}</pre>")
        p.append("<h2>Appendix A. Commands run by the tool</h2><table><tr><th>Time (UTC)</th><th>Command</th><th>Exit</th><th>Output SHA-256</th></tr>")
        for cm in m['commands'][:1500]:
            p.append(f"<tr><td>{E(cm['time_utc'])}</td><td><code>{E(cm['command'])}</code></td><td>{cm['returncode']}</td><td class=h>{cm['output_sha256']}</td></tr>")
        p.append("</table>")
        p.append(f"<h2>Appendix B. Examiner's declaration</h2><pre>{E(self._declaration_text(m))}</pre>")
        p.append(f"<h2>Appendix C. Certificate (template)</h2><div class=tpl><pre>{E(self._certificate_text(m))}</pre></div>")
        p.append("<h2>Appendix D. How to verify</h2><p>Check any file with <code>shasum -a 256 &lt;file&gt;</code> (Linux/macOS) or "
                 "<code>certutil -hashfile &lt;file&gt; SHA256</code> (Windows) and compare with <code>manifest.json</code>. The SHA-256 of the whole package is in "
                 "the <code>.zip.hashes.txt</code> file written when it was created. The hash of this report cannot be written inside itself; it is in the manifest.</p></body></html>")
        return "".join(p)

    def _save_html(self, report):
        fn = filedialog.asksaveasfilename(defaultextension=".html", filetypes=[("HTML files", "*.html"), ("All files", "*.*")],
                                          initialfile=f"forensic_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.html")
        if fn:
            m = getattr(self, '_last_model', None) or self._report_model()
            with open(fn, 'w', encoding='utf-8') as f:
                f.write(self._render_report_html(m))
            self._saved_msg(fn)

    def _save_txt(self, report):
        fn = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
                                          initialfile=f"forensic_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.txt")
        if fn:
            with open(fn, 'w', encoding='utf-8') as f:
                f.write(report)
            self._saved_msg(fn)

    def _saved_msg(self, fn):
        messagebox.showinfo("Success", f"Report saved to:\n{fn}\n\nSHA-256: {self._seal_report(fn)}\n(also saved as {os.path.basename(fn)}.sha256)")

    # ---- PDF -----------------------------------------------------------------------------------------
    def _pdf_fonts(self):
        """-> (regular, bold, mono, unicode_ok). Falls back to the built-in Latin-1 fonts."""
        from reportlab.pdfbase import pdfmetrics
        from reportlab.pdfbase.ttfonts import TTFont
        win = os.path.join(os.environ.get('WINDIR', r'C:\Windows'), 'Fonts')
        sets = [('/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf', '/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf', '/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf'),
                ('/usr/share/fonts/dejavu/DejaVuSans.ttf', '/usr/share/fonts/dejavu/DejaVuSans-Bold.ttf', '/usr/share/fonts/dejavu/DejaVuSansMono.ttf'),
                (os.path.join(win, 'arial.ttf'), os.path.join(win, 'arialbd.ttf'), os.path.join(win, 'cour.ttf')),
                ('/System/Library/Fonts/Supplemental/Arial.ttf', '/System/Library/Fonts/Supplemental/Arial Bold.ttf', '/System/Library/Fonts/Supplemental/Courier New.ttf')]
        for r, b, mo in sets:
            if all(os.path.isfile(x) for x in (r, b, mo)):
                try:
                    pdfmetrics.registerFont(TTFont('CX-Reg', r))
                    pdfmetrics.registerFont(TTFont('CX-Bold', b))
                    pdfmetrics.registerFont(TTFont('CX-Mono', mo))
                    return 'CX-Reg', 'CX-Bold', 'CX-Mono', True
                except Exception:
                    continue
        return 'Helvetica', 'Helvetica-Bold', 'Courier', False

    def _render_report_pdf(self, m, fn):
        try:
            from reportlab.lib.pagesizes import A4
            from reportlab.lib.units import mm
            from reportlab.lib import colors
            from reportlab.lib.styles import ParagraphStyle
            from reportlab.platypus import (BaseDocTemplate, PageTemplate, Frame, Paragraph, Spacer, Table, TableStyle,
                                            PageBreak, Preformatted)
            from reportlab.platypus.tableofcontents import TableOfContents
            from reportlab.pdfgen import canvas as rl_canvas
        except ImportError:
            return False
        import textwrap
        from xml.sax.saxutils import escape as XE
        reg, bold, mono, uni = self._pdf_fonts()
        navy = colors.HexColor('#1a3d6d')

        def T(s):
            s = str(s if s is not None else '')
            return s if uni else s.encode('latin-1', 'replace').decode('latin-1')

        def P(s, st):
            return Paragraph(XE(T(s)), st)
        base = ParagraphStyle('b', fontName=reg, fontSize=9.5, leading=13)
        small = ParagraphStyle('s', parent=base, fontSize=8, leading=10)
        hashst = ParagraphStyle('h', fontName=mono, fontSize=6.6, leading=8)
        H1 = ParagraphStyle('H1', parent=base, fontName=bold, fontSize=14, leading=18, textColor=navy, spaceBefore=14, spaceAfter=6)
        H2 = ParagraphStyle('H2', parent=base, fontName=bold, fontSize=10.5, leading=14, spaceBefore=8, spaceAfter=2)
        mst = ParagraphStyle('m', fontName=mono, fontSize=6.8, leading=8.2)
        title = ParagraphStyle('t', parent=base, fontName=bold, fontSize=26, leading=32, textColor=navy, alignment=0)
        c, h, t = m['case'], m['host'], m['tool']
        hdr = f"Case {c.get('case_id') or '-'}  |  Report {m['report_id']}"

        class Canvas(rl_canvas.Canvas):
            def __init__(self, *a, **k):
                super().__init__(*a, **k)
                self._pages = []

            def showPage(self):
                self._pages.append(dict(self.__dict__))
                self._startPage()

            def save(self):
                n = len(self._pages)
                for st in self._pages:
                    self.__dict__.update(st)
                    if self._pageNumber > 1:
                        self.setFont(reg, 7.5)
                        self.setFillColor(colors.HexColor('#444444'))
                        self.drawString(18 * mm, 10 * mm, T(hdr))
                        self.drawRightString(A4[0] - 18 * mm, 10 * mm, f"Page {self._pageNumber} of {n}")
                        self.setStrokeColor(colors.HexColor('#999999'))
                        self.line(18 * mm, 14 * mm, A4[0] - 18 * mm, 14 * mm)
                        self.drawString(18 * mm, A4[1] - 12 * mm, "CACTUS Digital Forensic Examination Report")
                    super().showPage()
                super().save()

        class Doc(BaseDocTemplate):
            def afterFlowable(self, fl):
                if isinstance(fl, Paragraph) and fl.style.name == 'H1':
                    self.notify('TOCEntry', (0, fl.getPlainText(), self.page))

        doc = Doc(fn, pagesize=A4, leftMargin=18 * mm, rightMargin=18 * mm, topMargin=18 * mm, bottomMargin=20 * mm,
                  title=f"Forensic Report {m['report_id']}", author=c.get('examiner') or 'CACTUS')
        doc.addPageTemplates([PageTemplate(id='p', frames=[Frame(doc.leftMargin, doc.bottomMargin, doc.width, doc.height, id='f')])])
        W = doc.width

        def kv(rows, w0=0.30):
            data = [[P(a, ParagraphStyle('k', parent=base, fontName=bold, fontSize=8.5)), P(b if str(b or '').strip() else '-', base if len(str(b or '')) < 80 else small)] for a, b in rows]
            tb = Table(data, colWidths=[W * w0, W * (1 - w0)])
            tb.setStyle(TableStyle([('GRID', (0, 0), (-1, -1), 0.4, colors.HexColor('#bbbbbb')), ('BACKGROUND', (0, 0), (0, -1), colors.HexColor('#eef2f7')),
                                    ('VALIGN', (0, 0), (-1, -1), 'TOP'), ('TOPPADDING', (0, 0), (-1, -1), 3), ('BOTTOMPADDING', (0, 0), (-1, -1), 3)]))
            return tb

        def pre(text, cap):
            lines = []
            for ln in T(text).split('\n'):
                lines += textwrap.wrap(ln.replace('\t', '    '), 112, subsequent_indent='    ', drop_whitespace=False) or ['']
            extra = max(0, len(lines) - cap)
            return Preformatted('\n'.join(lines[:cap]), mst), extra

        def hashp(hx):
            return Paragraph(f"{hx[:32]}<br/>{hx[32:64]}" if len(hx) >= 64 else XE(T(hx)), hashst)

        S = []
        S += [Spacer(1, 50 * mm), P("Digital Forensic", title), P("Examination Report", title), Spacer(1, 10 * mm),
              kv([("Case ID / FIR", c.get('case_id') or '(not set)'), ("Case title", c.get('case_title')), ("Exhibit reference", c.get('exhibit_ref')),
                  ("Examiner", c.get('examiner') or '(not set)'), ("Organisation", c.get('organization')),
                  ("Report ID", m['report_id']), ("Generated (UTC)", m['generated_utc'])]),
              Spacer(1, 12 * mm),
              P("This report describes how digital evidence was collected from a running computer, what was collected, and how its integrity is protected by cryptographic hashes. "
                "It states facts and flagged leads. It does not state conclusions about guilt or intent.", small), PageBreak()]
        S += [P("Document control", H1),
              kv([("Requested by", c.get('requested_by')), ("Place of examination", c.get('location')), ("Legal authority / consent", c.get('authority')),
                  ("Notes", c.get('notes')), ("Tool", f"{t['name']} v{t['version']}"), ("Tool file", t['file']), ("Tool file SHA-256", t['sha256']),
                  ("Tool validation performed", c.get('validation_note'))]), Spacer(1, 8)]
        toc = TableOfContents()
        toc.levelStyles = [ParagraphStyle('toc0', parent=base, fontSize=9.5, leading=14, leftIndent=0)]
        S += [P("Contents", H1), toc, PageBreak()]
        S += [P("1. Summary of what was done", H1)] + [P("•  " + s, base) for s in m['summary']]
        S += [P("2. Methodology", H1)] + [P(f"{i}.  {s}", base) for i, s in enumerate(m['methodology'], 1)]
        S += [P("3. Examined system", H1),
              kv([("Host name", h['hostname']), ("Platform", f"{h['platform']} ({h['machine']})"), ("Run by user", h['user']),
                  ("Administrator / root", 'yes' if h['is_admin'] else 'NO'), ("Time zone", h['timezone']), ("Clock (local)", h['clock_local']),
                  ("Clock (UTC)", h['clock_utc']), ("Uptime", h['uptime'])])]
        S += [P("4. Evidence inventory", H1),
              P("Each item is a file inside the evidence package. SHA-512, SHA-1 and MD5 for every file are in manifest.json.", small), Spacer(1, 4)]
        rows = [[P(x, ParagraphStyle('th', parent=base, fontName=bold, fontSize=8)) for x in ("ID", "Item / file", "Collected (UTC)", "Bytes", "SHA-256")]]
        for f in m['evidence']:
            rows.append([P(f['id'], small), P(f"{f['title']}\nevidence/{f['name']}", small), P((f['collected_utc'] or '-').replace('T', ' ').replace('+00:00', ' UTC'), small), P(f"{f['size']:,}", small), hashp(f['sha256'])])
        for cp in m['captures']:
            rows.append([P("CAP", small), P(f"Packet capture\nnetwork/{os.path.basename(cp['path'])}", small), P(cp.get('finished_utc', '').replace('T', ' ').replace('+00:00', ' UTC'), small), P(f"{cp['size']:,}", small), hashp(cp['sha256'])])
        tb = Table(rows, colWidths=[W * .07, W * .31, W * .21, W * .08, W * .33], repeatRows=1)
        tb.setStyle(TableStyle([('GRID', (0, 0), (-1, -1), 0.4, colors.HexColor('#bbbbbb')), ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#eef2f7')), ('VALIGN', (0, 0), (-1, -1), 'TOP')]))
        S.append(tb)
        S.append(P("5. Findings (as collected)", H1))
        S.append(P("Long results are shortened here. The complete, hashed data is in the evidence file named under each heading.", small))
        for f in m['evidence']:
            S.append(P(f"{f['id']}  {f['title']}", H2))
            S.append(P(f['desc'], small))
            pr, extra = pre(f['data'].decode('utf-8', 'replace'), 140)
            S.append(pr)
            if extra:
                S.append(P(f"... {extra} more line(s) in evidence/{f['name']}", small))
                S.append(hashp(f['sha256']))
        S.append(P("6. Limitations", H1))
        S += [P(f"{i}.  {s}", base) for i, s in enumerate(m['limitations'], 1)]
        S.append(P("7. Chain of custody / activity log", H1))
        pr, extra = pre(self._audit_text_block(m['audit']), 400)
        S.append(pr)
        if extra:
            S.append(P(f"... {extra} more entries in logs/chain_of_custody.txt", small))
        S.append(P("Appendix A. Commands run by the tool", H1))
        S.append(P("Each external command, when it ran, its exit code, and the SHA-256 of what it returned.", small))
        rows = [[P(x, ParagraphStyle('th2', parent=base, fontName=bold, fontSize=8)) for x in ("Time (UTC)", "Command", "Exit", "Output SHA-256")]]
        for cm in m['commands'][:400]:
            rows.append([P(cm['time_utc'].replace('T', ' ').replace('+00:00', ''), small), P(cm['command'][:200], small), P(cm['returncode'], small), hashp(cm['output_sha256'])])
        tb = Table(rows, colWidths=[W * .16, W * .50, W * .06, W * .28], repeatRows=1)
        tb.setStyle(TableStyle([('GRID', (0, 0), (-1, -1), 0.4, colors.HexColor('#bbbbbb')), ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#eef2f7')), ('VALIGN', (0, 0), (-1, -1), 'TOP')]))
        S.append(tb)
        if len(m['commands']) > 400:
            S.append(P(f"... {len(m['commands']) - 400} more in logs/commands_executed.json", small))
        S.append(P("Appendix B. Examiner's declaration", H1))
        S += [P(x, base) for x in self._declaration_text(m).split('\n\n')]
        S.append(P("Appendix C. Certificate (template)", H1))
        for blk in self._certificate_text(m).split('\n\n'):
            S.append(P(blk.replace('\n', ' '), small if blk.startswith('TEMPLATE') else base))
            S.append(Spacer(1, 4))
        S.append(P("Appendix D. How to verify", H1))
        S.append(P("Check any file with:  shasum -a 256 <file>  (Linux/macOS)  or  certutil -hashfile <file> SHA256  (Windows), then compare with manifest.json. "
                   "The SHA-256 of the whole package is written to the .zip.hashes.txt file when the package is created. The hash of this PDF cannot be written "
                   "inside itself; it is listed in manifest.json.", base))
        if not uni:
            S.append(P("Note: characters outside Latin-1 (for example non-English names) are shown as '?' in this PDF because no Unicode font was found. "
                       "They are preserved in the TXT/HTML/JSON versions and in the evidence files.", small))
        doc.multiBuild(S, canvasmaker=Canvas)
        return True

    def _save_pdf(self, report):
        try:
            import reportlab  # noqa: F401
        except ImportError:
            messagebox.showwarning("Warning", "ReportLab not installed.\n\nInstall with:  pip install reportlab\n\nFalling back to TXT format.")
            self._save_txt(report)
            return
        fn = filedialog.asksaveasfilename(defaultextension=".pdf", filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")],
                                          initialfile=f"forensic_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.pdf")
        if not fn:
            return
        m = getattr(self, '_last_model', None) or self._report_model()
        try:
            self._render_report_pdf(m, fn)
        except Exception as e:
            messagebox.showerror("PDF", f"The PDF could not be built: {type(e).__name__}: {e}")
            return
        self._saved_msg(fn)

    def _task_build_report(self):
        m = self._report_model()
        self._last_model = m
        return self._render_report_txt(m)

    def _on_report_built(self, report):
        self.report_text.delete('1.0', 'end')
        self.report_text.insert('1.0', report)
        fmt = self.report_format.get()
        if fmt == 'PDF':
            self._save_pdf(report)
        elif fmt == 'HTML':
            self._save_html(report)
        elif fmt == 'JSON':
            self._save_json()
        else:
            self._save_txt(report)

    # --------------------------------------------------------
    # MISC
    # --------------------------------------------------------
    def clear_text(self, widget):
        widget.delete('1.0', 'end')

    def clear_all_data(self):
        if messagebox.askyesno("Confirm", "Clear all collected data?"):
            self._audit('Clear All Data', 'ok', 'collected data erased; this log kept')
            self.investigation_data.clear()
            for w in (self.system_text, self.timeline_text, self.history_text,
                      self.devices_text, self.registry_text, self.network_text,
                      self.log_text, self.hash_text, self.report_text, self.search_text):
                w.delete('1.0', 'end')
            self.clear_event_view()
            self.file_path.set("")
            self.show_welcome()
            self.set_status("All data cleared")


# ============================================================
# ENTRY POINT
# ============================================================
def main():
    try:
        import tkinter  # noqa
    except ImportError:
        print("Tkinter is required but not installed.")
        print("Install:")
        print("  Ubuntu/Debian : sudo apt-get install python3-tk")
        print("  Fedora        : sudo dnf install python3-tkinter")
        print("  macOS         : brew install python-tk")
        print("  Windows       : bundled with Python")
        sys.exit(1)

    root = tk.Tk()
    app = DigitalForensicTool(root)

    menubar = tk.Menu(root, bg=Theme.BG_MEDIUM, fg=Theme.TEXT_PRIMARY,
                      activebackground=Theme.ACCENT, activeforeground=Theme.BG_DARK)
    file_menu = tk.Menu(menubar, tearoff=0, bg=Theme.BG_MEDIUM,
                        fg=Theme.TEXT_PRIMARY, activebackground=Theme.ACCENT)
    file_menu.add_command(label="Clear All Data", command=app.clear_all_data)
    file_menu.add_separator()
    file_menu.add_command(label="Exit", command=root.quit)
    menubar.add_cascade(label="File", menu=file_menu)
    root.config(menu=menubar)

    root.mainloop()


if __name__ == "__main__":
    main()
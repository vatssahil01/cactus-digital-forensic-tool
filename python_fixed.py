#!/usr/bin/env python
# coding: utf-8

"""
Cactus v2.0
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
class DigitalForensicTool:
    def __init__(self, root):
        self.root = root
        self.root.title("Cactus v2.0")
        self.root.geometry("1500x900")
        self.root.minsize(1200, 700)
        self.root.configure(bg=Theme.BG_DARK)

        # State
        self.current_os = platform.system()
        self.investigation_data = {}
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
        self.build_ioc_tab()
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
        self.notebook.add(tab, text='  📊  System Analysis  ')

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
        self.notebook.add(tab, text='  🌐  Browser Artifacts  ')

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
        self.notebook.add(tab, text='  📋  Event Logs  ')

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
        self.notebook.add(tab, text='  🌐  Network Activity  ')

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
        self.notebook.add(tab, text='  🔐  IOC Extraction  ')

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

    # --------------------------------------------------------
    # TAB: REPORT
    # --------------------------------------------------------
    def build_report_tab(self):
        tab = tk.Frame(self.notebook, bg=Theme.BG_DARK)
        self.notebook.add(tab, text='  📄  Report Generation  ')

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
        self.notebook.add(tab, text='  💽  Connected Devices  ')

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
        self.notebook.add(tab, text='  🗝  Registry & Artifacts  ')

        actions = tk.Frame(tab, bg=Theme.BG_DARK)
        actions.pack(fill='x', padx=12, pady=(12, 4))
        ttk.Button(actions, text="⚡ Collect All", style='Accent.TButton',
                   command=lambda: self.collect_artifacts(
                       [k for _l, k in self._artifact_list()])).pack(side='left', padx=4)
        for label, kind in self._artifact_list():
            ttk.Button(actions, text=label,
                       command=lambda k=kind: self.collect_artifacts([k])
                       ).pack(side='left', padx=4)
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

        def wrapped_done(result):
            self.root.after(0, lambda: self._finish_task(on_done, result))

        def wrapped_error(e):
            self.root.after(0, lambda: self._finish_task_error(on_error, e))

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
            "║                   Cactus v2.0                            ║\n"
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
    def collect_timeline(self):
        self.run_async(self._task_collect_timeline,
                       on_done=self._on_timeline_done,
                       status="Collecting timeline...")

    def _task_collect_timeline(self):
        out = "=" * 60 + "\n"
        out += "SYSTEM TIMELINE\n"
        out += f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        out += "=" * 60 + "\n\n"
        out += "Recently Modified Files:\n" + "-" * 40 + "\n"

        home = os.path.expanduser("~")
        if self.current_os == "Windows":
            paths = [os.path.join(home, "Documents"),
                     os.path.join(home, "Downloads"),
                     os.path.join(home, "Desktop")]
        else:
            paths = [os.path.join(home, "Documents"),
                     os.path.join(home, "Downloads"),
                     os.path.join(home, "Desktop")]

        for path in paths:
            if os.path.exists(path):
                out += f"\nDirectory: {path}\n"
                try:
                    files = os.listdir(path)[:10]
                    for f in files:
                        fp = os.path.join(path, f)
                        if os.path.isfile(fp):
                            mtime = datetime.fromtimestamp(os.path.getmtime(fp))
                            out += f"  {f}  →  {mtime.strftime('%Y-%m-%d %H:%M:%S')}\n"
                except Exception:
                    pass
        return out

    def _on_timeline_done(self, text):
        self.timeline_text.insert('end', text)
        self.timeline_text.see('end')
        self.investigation_data['timeline'] = text

    # --------------------------------------------------------
    # BROWSER HISTORY
    # --------------------------------------------------------
    def collect_browser_history(self):
        self.run_async(self._task_collect_browser_history,
                       on_done=self._on_browser_history_done,
                       status="Collecting browser history...")

    def _task_collect_browser_history(self):
        out = "=" * 60 + "\n"
        out += "BROWSER HISTORY & ACTIVITY\n"
        out += f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        out += "=" * 60 + "\n\n"

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
            full = os.path.expanduser(p)
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

    # --- Browser readers (return (data, denied)) ---
    def _read_chromium_db(self, path):
        """Safely copy and read a Chromium-style History DB."""
        if not os.path.exists(path):
            return "History file not found.\n", False
        try:
            with open(path, 'rb'):
                pass
        except PermissionError:
            return ("Permission denied — cannot read history.\n", True)
        except OSError as e:
            return (f"Cannot access history: {e}\n", False)

        temp = f"temp_{os.getpid()}_{threading.get_ident()}.db"
        try:
            shutil.copy2(path, temp)
            conn = sqlite3.connect(temp)
            cur = conn.cursor()
            cur.execute(
                "SELECT url, title, last_visit_time FROM urls "
                "ORDER BY last_visit_time DESC LIMIT 25"
            )
            rows = cur.fetchall()
            conn.close()
            out = ""
            for url, title, _ in rows:
                if title:
                    out += f"URL   : {url}\nTitle : {title}\n" + "-" * 30 + "\n"
            return out or "No entries found.\n", False
        except PermissionError:
            return "Permission denied while reading history.\n", True
        except Exception as e:
            return f"Error reading history: {e}\n", False
        finally:
            try:
                os.remove(temp)
            except Exception:
                pass

    def _chrome_history(self):
        paths = {
            'Windows': '~/AppData/Local/Google/Chrome/User Data/Default/History',
            'Linux': '~/.config/google-chrome/Default/History',
            'Darwin': '~/Library/Application Support/Google/Chrome/Default/History',
        }
        return self._read_chromium_db(os.path.expanduser(paths.get(self.current_os, '')))

    def _edge_history(self):
        paths = {
            'Windows': '~/AppData/Local/Microsoft/Edge/User Data/Default/History',
            'Linux': '~/.config/microsoft-edge/Default/History',
            'Darwin': '~/Library/Application Support/Microsoft Edge/Default/History',
        }
        return self._read_chromium_db(os.path.expanduser(paths.get(self.current_os, '')))

    def _brave_history(self):
        paths = {
            'Windows': '~/AppData/Local/BraveSoftware/Brave-Browser/User Data/Default/History',
            'Linux': '~/.config/BraveSoftware/Brave-Browser/Default/History',
            'Darwin': '~/Library/Application Support/BraveSoftware/Brave-Browser/Default/History',
        }
        return self._read_chromium_db(os.path.expanduser(paths.get(self.current_os, '')))

    def _firefox_history(self):
        paths = {
            'Windows': '~/AppData/Roaming/Mozilla/Firefox/Profiles',
            'Linux': '~/.mozilla/firefox',
            'Darwin': '~/Library/Application Support/Firefox/Profiles',
        }
        base = os.path.expanduser(paths.get(self.current_os, ''))
        if not base or not os.path.exists(base):
            return "Firefox path not found.\n", False
        try:
            os.listdir(base)
        except PermissionError:
            return "Permission denied — cannot read Firefox profiles.\n", True

        try:
            profiles = [d for d in os.listdir(base)
                        if d.endswith('.default') or d.endswith('.default-release')]
            if not profiles:
                return "Firefox profile not found.\n", False

            places = os.path.join(base, profiles[0], 'places.sqlite')
            if not os.path.exists(places):
                return "Firefox places.sqlite not found.\n", False

            try:
                with open(places, 'rb'):
                    pass
            except PermissionError:
                return "Permission denied — cannot read places.sqlite.\n", True

            temp = f"temp_ff_{os.getpid()}.db"
            try:
                shutil.copy2(places, temp)
                conn = sqlite3.connect(temp)
                cur = conn.cursor()
                cur.execute(
                    "SELECT url, title, last_visit_date FROM moz_places "
                    "ORDER BY last_visit_date DESC LIMIT 25"
                )
                rows = cur.fetchall()
                conn.close()
                out = ""
                for url, title, _ in rows:
                    if title:
                        out += f"URL   : {url}\nTitle : {title}\n" + "-" * 30 + "\n"
                return out or "No entries found.\n", False
            finally:
                try:
                    os.remove(temp)
                except Exception:
                    pass
        except PermissionError:
            return "Permission denied reading Firefox data.\n", True
        except Exception as e:
            return f"Error reading Firefox history: {e}\n", False

    def _safari_history(self):
        if self.current_os != "Darwin":
            return "Safari is only available on macOS.\n", False

        path = os.path.expanduser('~/Library/Safari/History.db')
        if not os.path.exists(path):
            return "Safari history database not found.\n", False

        try:
            with open(path, 'rb'):
                pass
        except PermissionError:
            return ("Permission denied — Full Disk Access required for Safari.\n", True)

        temp = f"temp_safari_{os.getpid()}.db"
        try:
            shutil.copy2(path, temp)
            conn = sqlite3.connect(temp)
            cur = conn.cursor()
            cur.execute(
                "SELECT url, title, visit_time FROM history_items "
                "ORDER BY visit_time DESC LIMIT 25"
            )
            rows = cur.fetchall()
            conn.close()
            out = ""
            for url, title, _ in rows:
                if title:
                    out += f"URL   : {url}\nTitle : {title}\n" + "-" * 30 + "\n"
            return out or "No entries found.\n", False
        except PermissionError:
            return "Permission denied — cannot read Safari history.\n", True
        except Exception as e:
            return f"Error reading Safari history: {e}\n", False
        finally:
            try:
                os.remove(temp)
            except Exception:
                pass

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
        fp = os.path.expanduser('~/Library/Preferences/com.apple.finder.plist')
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
        head += "=" * 60 + "\n"
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
        home = Path(home) if home else Path.home()
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
        home = Path(home) if home else Path.home()
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
                    ("Recent Files & MRU", 'recent')]
        if self.current_os == "Darwin":
            return [("plist / Config", 'registry'), ("Recent Items", 'recent'),
                    ("Downloads (Quarantine)", 'downloads'),
                    ("Install History", 'installs'), ("Shell History", 'shellhistory')]
        return [("Config", 'registry'), ("Recent Files", 'recent'), ("Trash", 'trash'),
                ("Shell History", 'shellhistory'), ("Logins", 'logins')]

    def _artifact_fn(self, kind):
        osn = self.current_os if self.current_os in ('Windows', 'Darwin') else 'Linux'
        return {
            ('Windows', 'shellbags'): self._art_shellbags,
            ('Windows', 'jumplists'): self._art_jumplists,
            ('Windows', 'prefetch'): self._art_prefetch,
            ('Windows', 'recent'): self._art_recent_windows,
            ('Darwin', 'recent'): self._art_recent_macos,
            ('Darwin', 'downloads'): self._art_downloads_macos,
            ('Darwin', 'installs'): self._art_installs_macos,
            ('Darwin', 'shellhistory'): self._shell_history,
            ('Linux', 'recent'): self._art_recent_linux,
            ('Linux', 'trash'): self._art_trash_linux,
            ('Linux', 'shellhistory'): self._shell_history,
            ('Linux', 'logins'): self._art_logins_linux,
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
        ntdll = ctypes.windll.ntdll
        size = struct.unpack_from('<I', data, 4)[0]
        src = bytes(data[8:])
        out = ctypes.create_string_buffer(size)
        ws_size, frag = ctypes.c_ulong(), ctypes.c_ulong()
        ntdll.RtlGetCompressionWorkSpaceSize(ctypes.c_ushort(4), ctypes.byref(ws_size),
                                             ctypes.byref(frag))
        ws = ctypes.create_string_buffer(max(ws_size.value, frag.value))
        final = ctypes.c_ulong()
        status = ntdll.RtlDecompressBufferEx(ctypes.c_ushort(4), out, size, src, len(src),
                                             ctypes.byref(final), ws)
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

    def _art_prefetch(self, folder=None):
        folder = Path(folder) if folder else Path(os.environ.get('SystemRoot', r'C:\Windows')) / 'Prefetch'
        out = ["Prefetch shows which programs ran, how many times and when (last 8 runs on "
               "Windows 8/10/11). Needs Administrator rights. Run counts for some Windows 10 "
               "builds should be double-checked with a dedicated parser such as PECmd.\n",
               f"Folder: {folder}\n"]
        try:
            files = list(folder.glob('*.pf'))
        except Exception as e:
            return "\n".join(out) + f"Not available: {e}\n"
        if not files:
            return "\n".join(out) + ("No .pf files found. Prefetch may be disabled, the drive may be "
                                     "an SSD with it turned off, or you need Administrator rights.\n")
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
        home = Path(home) if home else Path.home()
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
        home = Path(home) if home else Path.home()
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
        home = Path(home) if home else Path.home()
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
        home = Path(home) if home else Path.home()
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
        home = Path(home) if home else Path.home()
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

    # --------------------------------------------------------
    # REPORT GENERATION
    # --------------------------------------------------------
    def generate_report(self):
        self.run_async(self._task_build_report,
                       on_done=self._on_report_built,
                       status="Building report...")

    def _task_build_report(self):
        report = "=" * 70 + "\n"
        report += "DIGITAL FORENSIC INVESTIGATION REPORT\n"
        report += "=" * 70 + "\n"
        report += f"Generated : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        report += f"OS        : {self.current_os}\n"
        report += "=" * 70 + "\n\n"

        sections = [
            ('SYSTEM INFORMATION', 'system_info'),
            ('TIMELINE', 'timeline'),
            ('BROWSER HISTORY', 'browser_history'),
            ('CONNECTED DEVICES', 'connected_devices'),
            ('USB / DEVICE HISTORY', 'device_history'),
            ('OS REGISTRY ARTIFACTS', 'registry'),
            ('SHELLBAGS', 'artifact_shellbags'),
            ('JUMP LISTS', 'artifact_jumplists'),
            ('PREFETCH', 'artifact_prefetch'),
            ('RECENT FILES', 'artifact_recent'),
            ('DOWNLOADS (QUARANTINE)', 'artifact_downloads'),
            ('INSTALL HISTORY', 'artifact_installs'),
            ('SHELL HISTORY', 'artifact_shellhistory'),
            ('TRASH', 'artifact_trash'),
            ('LOGINS', 'artifact_logins'),
            ('EVENT LOGS', 'event_logs'),
            ('NETWORK ACTIVITY', 'network_activity'),
            ('PASSIVE PROTOCOL CAPTURE', 'protocol_capture'),
        ]
        for title, key in sections:
            if key in self.investigation_data:
                report += f"\n{title}\n" + "-" * 40 + "\n"
                report += self.investigation_data[key] + "\n"

        if 'file_hashes' in self.investigation_data:
            report += "\nFILE HASHES\n" + "-" * 40 + "\n"
            for k, v in self.investigation_data['file_hashes'].items():
                report += f"{k.upper():8s}: {v}\n"

        return report

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

    def _save_txt(self, report):
        fn = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
            initialfile=f"forensic_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.txt")
        if fn:
            with open(fn, 'w') as f:
                f.write(report)
            messagebox.showinfo("Success", f"Report saved to:\n{fn}")

    def _save_html(self, report):
        fn = filedialog.asksaveasfilename(
            defaultextension=".html",
            filetypes=[("HTML files", "*.html"), ("All files", "*.*")],
            initialfile=f"forensic_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.html")
        if fn:
            html = f"""<!DOCTYPE html>
<html><head><meta charset="utf-8">
<title>Digital Forensic Report</title>
<style>
  body {{ font-family: -apple-system, 'Segoe UI', Roboto, sans-serif;
         margin: 0; padding: 40px; background: #0f1419; color: #e8eef5; }}
  h1 {{ color: #00d4ff; border-bottom: 2px solid #00d4ff; padding-bottom: 8px; }}
  pre {{ background: #1e2a3a; padding: 20px; border-radius: 8px;
         white-space: pre-wrap; word-wrap: break-word; font-size: 13px;
         border-left: 4px solid #00d4ff; }}
</style></head><body>
<h1>🔍 🌵 Cactus v2.0 — Forensic Investigation Report</h1>
<pre>{report}</pre>
</body></html>"""
            with open(fn, 'w') as f:
                f.write(html)
            messagebox.showinfo("Success", f"Report saved to:\n{fn}")

    def _save_json(self):
        fn = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            initialfile=f"forensic_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")
        if fn:
            data = {
                'timestamp': datetime.now().isoformat(),
                'os': self.current_os,
                'platform': platform.platform(),
                'data': self.investigation_data,
            }
            with open(fn, 'w') as f:
                json.dump(data, f, indent=2, default=str)
            messagebox.showinfo("Success", f"Report saved to:\n{fn}")

    def _save_pdf(self, report):
        try:
            from reportlab.lib.pagesizes import letter
            from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer
            from reportlab.lib.styles import getSampleStyleSheet

            fn = filedialog.asksaveasfilename(
                defaultextension=".pdf",
                filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")],
                initialfile=f"forensic_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.pdf")
            if not fn:
                return

            doc = SimpleDocTemplate(fn, pagesize=letter)
            styles = getSampleStyleSheet()
            story = []
            for line in report.split('\n'):
                if line.strip():
                    story.append(Paragraph(line.replace('&', '&amp;')
                                                .replace('<', '&lt;')
                                                .replace('>', '&gt;'),
                                           styles['Normal']))
                    story.append(Spacer(1, 4))
            doc.build(story)
            messagebox.showinfo("Success", f"Report saved to:\n{fn}")

        except ImportError:
            messagebox.showwarning("Warning",
                "ReportLab not installed.\n\n"
                "Install with:  pip install reportlab\n\n"
                "Falling back to TXT format.")
            self._save_txt(report)

    # --------------------------------------------------------
    # MISC
    # --------------------------------------------------------
    def clear_text(self, widget):
        widget.delete('1.0', 'end')

    def clear_all_data(self):
        if messagebox.askyesno("Confirm", "Clear all collected data?"):
            self.investigation_data = {}
            for w in (self.system_text, self.timeline_text, self.history_text,
                      self.devices_text, self.registry_text, self.network_text,
                      self.log_text, self.hash_text, self.report_text):
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
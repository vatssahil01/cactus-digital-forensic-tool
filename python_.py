#!/usr/bin/env python
# coding: utf-8

"""
Digital Forensic Investigation Tool v3.0
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
from datetime import datetime
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
class DigitalForensicTool:
    def __init__(self, root):
        self.root = root
        self.root.title("Digital Forensic Investigation Tool  •  v3.0")
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
        self.build_events_tab()
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
        tk.Label(title_box, text="Digital Forensic Investigation Tool",
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

        actions = tk.Frame(tab, bg=Theme.BG_DARK)
        actions.pack(fill='x', padx=12, pady=12)
        ttk.Button(actions, text="⚡ Collect Event Logs", style='Accent.TButton',
                   command=self.collect_event_logs).pack(side='left', padx=4)
        ttk.Button(actions, text="🌐 Collect Network Activity",
                   command=self.collect_network_activity).pack(side='left', padx=4)
        ttk.Button(actions, text="🗑 Clear",
                   command=lambda: self.clear_text(self.log_text)).pack(side='left', padx=4)

        card = self._make_card(tab, "System Events, Logs & Network")
        card.pack(fill='both', expand=True, padx=12, pady=(0, 12))
        self.log_text = self._make_text_area(card)

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
    def run_async(self, task, on_done, on_error=None, status="Working..."):
        """Run task in background thread, call callbacks on main thread."""
        self.set_status(status, busy=True)

        def wrapped_done(result):
            self.root.after(0, lambda: self._finish_task(on_done, result))

        def wrapped_error(e):
            self.root.after(0, lambda: self._finish_task_error(on_error, e))

        worker = Worker(task, wrapped_done, wrapped_error)
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
            "║      DIGITAL FORENSIC INVESTIGATION TOOL  v3.0          ║\n"
            "╚══════════════════════════════════════════════════════════╝\n\n"
            f"  Operating System : {self.current_os}\n"
            f"  Platform         : {platform.platform()}\n"
            f"  Processor        : {platform.processor()}\n"
            f"  Python Version   : {sys.version.split()[0]}\n\n"
            "  Capabilities:\n"
            "  ─────────────────────────────────────────────\n"
            "  ✓  System Information Collection\n"
            "  ✓  Browser History (Chrome, Firefox, Safari, Edge, Brave)\n"
            "  ✓  Event Logs & Network Activity\n"
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

    # --------------------------------------------------------
    # EVENT LOGS
    # --------------------------------------------------------
    def collect_event_logs(self):
        self.run_async(self._task_collect_event_logs,
                       on_done=self._on_event_logs_done,
                       status="Collecting event logs...")

    def _task_collect_event_logs(self):
        out = "=" * 60 + "\n"
        out += "SYSTEM EVENT LOGS\n"
        out += f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        out += "=" * 60 + "\n\n"

        if self.current_os == "Windows":
            try:
                r = subprocess.run(['wevtutil', 'qe', 'System', '/c:10', '/f:text'],
                                   capture_output=True, text=True, timeout=15,
                                   errors='ignore')
                out += "System Log (last 10 events):\n" + r.stdout[:1500] + "...\n\n"
            except Exception:
                out += "Unable to read System log. Run as administrator.\n\n"
            try:
                r = subprocess.run(['wevtutil', 'qe', 'Application', '/c:10', '/f:text'],
                                   capture_output=True, text=True, timeout=15,
                                   errors='ignore')
                out += "Application Log (last 10 events):\n" + r.stdout[:1500] + "...\n\n"
            except Exception:
                out += "Unable to read Application log. Run as administrator.\n\n"

        elif self.current_os == "Linux":
            for path in ['/var/log/syslog', '/var/log/messages', '/var/log/auth.log']:
                if os.path.exists(path):
                    try:
                        with open(path, errors='ignore') as f:
                            lines = f.readlines()[-25:]
                        out += f"{path} (last 25 lines):\n" + ''.join(lines) + "\n\n"
                    except PermissionError:
                        out += f"{path}: Permission denied.\n\n"
                    except Exception as e:
                        out += f"{path}: {e}\n\n"

        elif self.current_os == "Darwin":
            try:
                r = subprocess.run(['log', 'show', '--last', '10m'],
                                   capture_output=True, text=True, timeout=20,
                                   errors='ignore')
                out += "System Log (last 10 min):\n" + r.stdout[:2000] + "...\n\n"
            except Exception:
                out += "Unable to read system log.\n\n"
        return out

    def _on_event_logs_done(self, text):
        self.log_text.insert('end', text)
        self.log_text.see('end')
        self.investigation_data['event_logs'] = text

    # --------------------------------------------------------
    # NETWORK ACTIVITY
    # --------------------------------------------------------
    def collect_network_activity(self):
        self.run_async(self._task_collect_network,
                       on_done=self._on_network_done,
                       status="Collecting network activity...")

    def _task_collect_network(self):
        out = "\n" + "=" * 60 + "\n"
        out += "NETWORK ACTIVITY\n"
        out += f"Collected: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        out += "=" * 60 + "\n\n"
        out += "Network Connections:\n" + "-" * 40 + "\n"

        try:
            cmd = ['netstat', '-an'] if self.current_os == "Windows" else ['netstat', '-tuln']
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=10,
                               errors='ignore')
            out += r.stdout[:2000] + "...\n\n"
        except Exception as e:
            out += f"Could not retrieve connections: {e}\n\n"

        out += "Active Connections (Detailed):\n" + "-" * 40 + "\n"
        try:
            cmd = (['netstat', '-b'] if self.current_os == "Windows"
                   else ['netstat', '-tunp'])
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=10,
                               errors='ignore')
            out += r.stdout[:1000] + "...\n"
        except Exception as e:
            out += f"Could not retrieve detailed connections: {e}\n"
        return out

    def _on_network_done(self, text):
        self.log_text.insert('end', text)
        self.log_text.see('end')
        self.investigation_data['network_activity'] = text

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
            ('EVENT LOGS', 'event_logs'),
            ('NETWORK ACTIVITY', 'network_activity'),
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
<h1>🔍 Digital Forensic Investigation Report</h1>
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
                      self.log_text, self.hash_text, self.report_text):
                w.delete('1.0', 'end')
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
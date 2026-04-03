"""
E-AES Encryption Tool
======================
Encrypts a single 16-character plaintext using a 16-character AES key
and an auxiliary key value x (1–255).

The Enhanced AES (E-AES) modifications applied:
  • Enhanced SubBytes  — S-box lookup XORed with round-key-derived mask
  • Dynamic ShiftRows  — shift offsets determined by plaintext ⊕ round key
  • RNS Round Key      — extra XOR layer per round using RGKA (Equation 3)

Output: 32-character hex ciphertext + full metric breakdown.
Save button exports result to a timestamped .txt file.
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import math
import time
import tracemalloc
import statistics
import threading
import datetime
import os

# ═══════════════════════════════════════════════════════════════════════════
#  AES TABLES
# ═══════════════════════════════════════════════════════════════════════════

SBOX = [
    0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
    0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
    0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
    0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
    0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
    0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
    0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
    0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
    0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
    0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
    0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
    0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
    0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
    0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
    0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
    0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16,
]

RCON = [0x00,0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1b,0x36]

# ═══════════════════════════════════════════════════════════════════════════
#  CORE ENCRYPTION ENGINE
# ═══════════════════════════════════════════════════════════════════════════

def xtime(a: int) -> int:
    return ((a << 1) ^ 0x1b) & 0xff if a & 0x80 else (a << 1) & 0xff

def get_rns_block(x: int, n: int) -> list:
    m1, m2, m3, m4 = 2*n+1, 3*n+1, 5*n+2, 7*n+4
    r1, r2, r3, r4 = x % m1, x % m2, x % m3, x % m4
    return [((r1 ^ (r2 << 1)) + 3*r3 + 5*r4 + i*i) % 256 for i in range(16)]

def key_expansion(key_bytes: bytes) -> list:
    w = [list(key_bytes[i:i+4]) for i in range(0, 16, 4)]
    for i in range(4, 44):
        temp = list(w[i-1])
        if i % 4 == 0:
            temp = [SBOX[b] for b in (temp[1:] + temp[:1])]
            temp[0] ^= RCON[i // 4]
        w.append([w[i-4][j] ^ temp[j] for j in range(4)])
    return [b for word in w for b in word]

def enhanced_sub_bytes(state: list, round_key: list) -> list:
    state_rows = [[state[r + c*4]     for c in range(4)] for r in range(4)]
    key_rows   = [[round_key[r + c*4] for c in range(4)] for r in range(4)]
    exor_keys  = [k[0]^k[1]^k[2]^k[3] for k in key_rows]
    new_state  = list(state)
    for r in range(4):
        for c in range(4):
            new_state[r + c*4] = SBOX[state_rows[r][c] ^ exor_keys[r]]
    return new_state

def dynamic_shift_rows(state: list, round_key: list) -> list:
    rows    = [[state[r + c*4]     for c in range(4)] for r in range(4)]
    rk_rows = [[round_key[r + c*4] for c in range(4)] for r in range(4)]
    positions = []
    for r in range(4):
        pos_val = 0
        for c in range(4):
            pos_val ^= (rows[r][c] ^ rk_rows[r][c])
        positions.append((pos_val, r))
    sorted_rows = sorted(positions, key=lambda item: (item[0], item[1]))
    new_state   = list(state)
    for shift, (_, row_idx) in enumerate(sorted_rows):
        row     = rows[row_idx]
        shifted = row[shift:] + row[:shift]
        for c in range(4):
            new_state[row_idx + c*4] = shifted[c]
    return new_state

def mix_columns(state: list) -> list:
    new_state = []
    for i in range(0, 16, 4):
        col = state[i:i+4]
        t   = col[0] ^ col[1] ^ col[2] ^ col[3]
        u   = col[0]
        new_state.extend([
            col[0] ^ t ^ xtime(col[0] ^ col[1]),
            col[1] ^ t ^ xtime(col[1] ^ col[2]),
            col[2] ^ t ^ xtime(col[2] ^ col[3]),
            col[3] ^ t ^ xtime(col[3] ^ u),
        ])
    return new_state

def apply_rns_round_key(state: list, round_key: list, rns_block: list) -> list:
    return [state[i] ^ round_key[i] ^ rns_block[i] for i in range(16)]

def encrypt(plaintext: bytes, key: bytes, x: int) -> str:
    expanded = key_expansion(key)
    state    = list(plaintext)
    state    = [state[i] ^ expanded[i] for i in range(16)]
    for r in range(1, 10):
        rnsk  = get_rns_block(x, r)
        state = enhanced_sub_bytes(state, expanded[r*16:(r+1)*16])
        state = dynamic_shift_rows(state, expanded[r*16:(r+1)*16])
        state = mix_columns(state)
        state = apply_rns_round_key(state, expanded[r*16:(r+1)*16], rnsk)
    rnsk  = get_rns_block(x, 10)
    state = enhanced_sub_bytes(state, expanded[160:176])
    state = dynamic_shift_rows(state, expanded[160:176])
    state = apply_rns_round_key(state, expanded[160:176], rnsk)
    return bytes(state).hex()

# ═══════════════════════════════════════════════════════════════════════════
#  METRICS
# ═══════════════════════════════════════════════════════════════════════════

def shannon_entropy(ct_hex: str) -> float:
    raw  = bytes.fromhex(ct_hex)
    freq = [raw.count(b) / len(raw) for b in set(raw)]
    return -sum(p * math.log2(p) for p in freq if p > 0)

def bit_balance(ct_hex: str) -> float:
    bits = bin(int(ct_hex, 16))[2:].zfill(128)
    return bits.count('1') / 128 * 100

def measure_enc_time_ms(pt: bytes, key: bytes, x: int, repeats=5) -> float:
    times = []
    for _ in range(repeats):
        t0 = time.perf_counter()
        encrypt(pt, key, x)
        t1 = time.perf_counter()
        times.append((t1 - t0) * 1000)
    return round(statistics.mean(times), 4)

def measure_peak_memory_kb(pt: bytes, key: bytes, x: int) -> float:
    tracemalloc.start()
    encrypt(pt, key, x)
    _, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    return round(peak / 1024, 3)

# ═══════════════════════════════════════════════════════════════════════════
#  COLOUR PALETTE & FONTS
# ═══════════════════════════════════════════════════════════════════════════

BG        = "#0d1117"
PANEL     = "#161b22"
BORDER    = "#30363d"
ACCENT    = "#58a6ff"
ACCENT2   = "#3fb950"
WARN      = "#f85149"
TEXT      = "#0d1117"
TEXT_MUTE = "#8b949e"
ENTRY_BG  = "#ffffff"
BTN_ENC   = "#000000"
BTN_ENC_H = "#1a1a1a"
BTN_SAV   = "#1f6feb"
BTN_SAV_H = "#388bfd"
BTN_CLR   = "#30363d"
BTN_CLR_H = "#484f58"

FONT_HEAD  = ("Consolas", 18, "bold")
FONT_LABEL = ("Consolas", 10)
FONT_ENTRY = ("Consolas", 11)
FONT_MONO  = ("Consolas", 10)
FONT_SMALL = ("Consolas", 9)

# ═══════════════════════════════════════════════════════════════════════════
#  GUI
# ═══════════════════════════════════════════════════════════════════════════

class EncryptApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self._last_result = {}
        self._setup_window()
        self._build_ui()

    # ── WINDOW SETUP ───────────────────────────────────────────────────────

    def _setup_window(self):
        self.root.title("E-AES  ·  Encryption")
        self.root.geometry("680x820")
        self.root.resizable(False, False)
        self.root.configure(bg=BG)
        try:
            self.root.tk_setPalette(background=BG)
        except Exception:
            pass

    # ── UI BUILDER ─────────────────────────────────────────────────────────

    def _build_ui(self):
        # ── header ─────────────────────────────────────────────────────────
        hdr = tk.Frame(self.root, bg=BG)
        hdr.pack(fill="x", padx=24, pady=(22, 4))
        tk.Label(hdr, text="E-AES", font=("Consolas", 28, "bold"),
                 fg=ACCENT, bg=BG).pack(side="left")
        tk.Label(hdr, text="  Encryption Tool", font=("Consolas", 16),
                 fg=TEXT_MUTE, bg=BG).pack(side="left", pady=(8, 0))
        tk.Label(self.root,
                 text="Enhanced AES  ·  SubBytes  ·  Dynamic ShiftRows  ·  RNS Round Key",
                 font=FONT_SMALL, fg=TEXT_MUTE, bg=BG).pack(anchor="w", padx=24)

        self._divider()

        # ── inputs panel ───────────────────────────────────────────────────
        panel = tk.Frame(self.root, bg=PANEL, relief="flat",
                         highlightbackground=BORDER, highlightthickness=1)
        panel.pack(fill="x", padx=24, pady=(0, 10))

        self._lbl(panel, "PLAINTEXT", "(exactly 16 characters)")
        self.e_pt = self._entry(panel)
        self.e_pt.insert(0, "I Love Unilorin!")
        self._char_counter(panel, self.e_pt)

        self._lbl(panel, "AES KEY", "(exactly 16 characters)")
        self.e_key = self._entry(panel, show="")
        self.e_key.insert(0, "dKro9Wahme#dHrn7")
        self._char_counter(panel, self.e_key)

        self._lbl(panel, "AUXILIARY KEY  x", "(integer 1 – 255)")
        xrow = tk.Frame(panel, bg=PANEL)
        xrow.pack(fill="x", padx=14, pady=(0, 4))
        self.x_var = tk.IntVar(value=7)
        self.x_spin = tk.Spinbox(
            xrow, from_=1, to=255, textvariable=self.x_var,
            width=6, font=FONT_ENTRY,
            bg=ENTRY_BG, fg=TEXT, insertbackground=TEXT,
            selectbackground=ACCENT, selectforeground=BG,
            relief="flat", highlightbackground=BORDER,
            highlightthickness=1, buttonbackground=PANEL,
        )
        self.x_spin.pack(side="left")
        tk.Label(xrow, text="   Best results typically near x = 7 or x = 128",
                 font=FONT_SMALL, fg=TEXT_MUTE, bg=PANEL).pack(side="left")

        tk.Frame(panel, bg=BORDER, height=1).pack(fill="x", padx=14, pady=8)

        # ── show/hide key ──────────────────────────────────────────────────
        self._show_key = False
        self.btn_eye = tk.Label(panel, text="⊙  Show key",
                                font=FONT_SMALL, fg=ACCENT, bg=PANEL, cursor="hand2")
        self.btn_eye.pack(anchor="w", padx=14, pady=(0, 10))
        self.btn_eye.bind("<Button-1>", self._toggle_key)

    # ── progress bar ────────────────────────────────────────────────────────
        self.prog_frame = tk.Frame(self.root, bg=BG)
        self.prog_frame.pack(fill="x", padx=24)
        self.prog_label = tk.Label(self.prog_frame, text="",
                                   font=FONT_SMALL, fg=TEXT_MUTE, bg=BG)
        self.prog_label.pack(anchor="w")
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Enc.Horizontal.TProgressbar",
                        troughcolor=PANEL, background=ACCENT2,
                        bordercolor=BORDER, lightcolor=ACCENT2,
                        darkcolor=ACCENT2, thickness=6)
        self.prog = ttk.Progressbar(self.prog_frame, style="Enc.Horizontal.TProgressbar",
                                    length=632, mode="indeterminate")
        self.prog.pack(pady=(2, 6))

        # ── buttons ────────────────────────────────────────────────────────
        brow = tk.Frame(self.root, bg=BG)
        brow.pack(fill="x", padx=24, pady=(0, 10))
        self.btn_enc = self._btn(brow, "⚡  Encrypt", BTN_ENC, BTN_ENC_H, self._encrypt)
        self.btn_enc.pack(side="left", padx=(0, 8))
        self.btn_clr = self._btn(brow, "↺  Clear", BTN_CLR, BTN_CLR_H, self._clear)
        self.btn_clr.pack(side="left")
        self.btn_sav = self._btn(brow, "💾  Save Result", BTN_SAV, BTN_SAV_H, self._save)
        self.btn_sav.pack(side="right")
        self.btn_sav.config(state="disabled")

        self._divider()

        # ── output panel ───────────────────────────────────────────────────
        out = tk.Frame(self.root, bg=PANEL, relief="flat",
                       highlightbackground=BORDER, highlightthickness=1)
        out.pack(fill="x", padx=24, pady=(0, 10))

        tk.Label(out, text="CIPHERTEXT", font=FONT_LABEL,
                 fg=TEXT_MUTE, bg=PANEL).pack(anchor="w", padx=14, pady=(10, 2))
        ct_row = tk.Frame(out, bg=PANEL)
        ct_row.pack(fill="x", padx=14, pady=(0, 10))
        self.ct_var = tk.StringVar()
        ct_entry = tk.Entry(ct_row, textvariable=self.ct_var,
                            font=("Consolas", 13, "bold"),
                            fg=ACCENT2, bg=ENTRY_BG, relief="flat",
                            highlightbackground=BORDER, highlightthickness=1,
                            state="readonly", readonlybackground=ENTRY_BG,
                            width=40)
        ct_entry.pack(side="left", ipady=6)
        self.btn_copy = self._btn(ct_row, "⎘ Copy", BTN_CLR, BTN_CLR_H, self._copy_ct)
        self.btn_copy.pack(side="left", padx=(8, 0))

        tk.Frame(out, bg=BORDER, height=1).pack(fill="x", padx=14)

        # ── metrics grid ───────────────────────────────────────────────────
        mf = tk.Frame(out, bg=PANEL)
        mf.pack(fill="x", padx=14, pady=10)
        self._metrics_vars = {}
        metrics_def = [
            ("Shannon Entropy",  "bits",  "entropy"),
            ("Bit Balance",      "%",     "balance"),
            ("Encryption Time",  "ms",    "enc_time"),
            ("Peak Memory",      "KB",    "memory"),
        ]
        for col, (label, unit, key) in enumerate(metrics_def):
            mf.columnconfigure(col, weight=1)
            cell = tk.Frame(mf, bg=BG, relief="flat",
                            highlightbackground=BORDER, highlightthickness=1)
            cell.grid(row=0, column=col, padx=4, pady=2, sticky="nsew")
            tk.Label(cell, text=label, font=FONT_SMALL,
                     fg=TEXT_MUTE, bg=BG).pack(pady=(8, 0))
            v = tk.StringVar(value="—")
            self._metrics_vars[key] = v
            tk.Label(cell, textvariable=v, font=("Consolas", 13, "bold"),
                     fg=ACCENT, bg=BG).pack()
            tk.Label(cell, text=unit, font=FONT_SMALL,
                     fg=TEXT_MUTE, bg=BG).pack(pady=(0, 8))

        # ── status bar ─────────────────────────────────────────────────────
        self.status = tk.StringVar(value="Ready — enter plaintext, key, and x value.")
        tk.Label(self.root, textvariable=self.status, font=FONT_SMALL,
                 fg=TEXT_MUTE, bg=BG, anchor="w").pack(
                     fill="x", padx=24, pady=(4, 16))

    # ── WIDGET HELPERS ─────────────────────────────────────────────────────

    def _divider(self):
        tk.Frame(self.root, bg=BORDER, height=1).pack(
            fill="x", padx=24, pady=6)

    def _lbl(self, parent, title, sub=""):
        row = tk.Frame(parent, bg=PANEL)
        row.pack(fill="x", padx=14, pady=(10, 2))
        tk.Label(row, text=title, font=("Consolas", 9, "bold"),
                 fg=ACCENT, bg=PANEL).pack(side="left")
        if sub:
            tk.Label(row, text=f"  {sub}", font=FONT_SMALL,
                     fg=TEXT_MUTE, bg=PANEL).pack(side="left")

    def _entry(self, parent, show=""):
        e = tk.Entry(parent, font=FONT_ENTRY,
                     bg=ENTRY_BG, fg=TEXT,
                     insertbackground=TEXT,
                     selectbackground=ACCENT, selectforeground=BG,
                     relief="flat",
                     highlightbackground=BORDER, highlightthickness=1,
                     show=show)
        e.pack(fill="x", padx=14, ipady=7)
        return e

    def _char_counter(self, parent, entry):
        row = tk.Frame(parent, bg=PANEL)
        row.pack(fill="x", padx=14)
        lbl = tk.Label(row, text="0 / 16 characters", font=FONT_SMALL,
                       fg=TEXT_MUTE, bg=PANEL)
        lbl.pack(side="right")

        def update(*_):
            n   = len(entry.get())
            col = ACCENT2 if n == 16 else WARN if n > 16 else TEXT_MUTE
            lbl.config(text=f"{n} / 16 characters", fg=col)
        entry.bind("<KeyRelease>", update)
        entry.bind("<FocusOut>", update)
        update()

    def _btn(self, parent, text, bg, bg_h, cmd):
        b = tk.Button(parent, text=text, command=cmd,
                      bg=bg, fg=TEXT,
                      activebackground=bg_h, activeforeground=TEXT,
                      font=("Consolas", 10, "bold"),
                      relief="flat", padx=14, pady=6,
                      cursor="hand2", bd=0)
        b.bind("<Enter>", lambda _: b.config(bg=bg_h))
        b.bind("<Leave>", lambda _: b.config(bg=bg))
        return b

    # ── ACTIONS ────────────────────────────────────────────────────────────

    def _toggle_key(self, _=None):
        self._show_key = not self._show_key
        self.e_key.config(show="" if self._show_key else "•")
        self.btn_eye.config(
            text="⊙  Hide key" if self._show_key else "⊙  Show key")

    def _validate_inputs(self):
        pt  = self.e_pt.get()
        key = self.e_key.get()
        x   = self.x_var.get()
        if len(pt) != 16:
            messagebox.showerror("Input Error",
                f"Plaintext must be exactly 16 characters.\nCurrent length: {len(pt)}")
            return None
        if len(key) != 16:
            messagebox.showerror("Input Error",
                f"AES key must be exactly 16 characters.\nCurrent length: {len(key)}")
            return None
        if not (1 <= x <= 255):
            messagebox.showerror("Input Error",
                "Auxiliary key x must be between 1 and 255.")
            return None
        return pt.encode(), key.encode(), x

    def _encrypt(self):
        validated = self._validate_inputs()
        if validated is None:
            return
        pt_bytes, key_bytes, x = validated
        self.btn_enc.config(state="disabled", text="Encrypting…")
        self.btn_sav.config(state="disabled")
        self.prog.start(12)
        self.prog_label.config(text="Encrypting, measuring metrics…")
        for k in self._metrics_vars:
            self._metrics_vars[k].set("…")
        self.ct_var.set("")
        self.status.set("Running E-AES encryption…")
        threading.Thread(
            target=self._encrypt_thread,
            args=(pt_bytes, key_bytes, x), daemon=True).start()

    def _encrypt_thread(self, pt, key, x):
        try:
            ct       = encrypt(pt, key, x)
            enc_time = measure_enc_time_ms(pt, key, x)
            mem      = measure_peak_memory_kb(pt, key, x)
            ent      = round(shannon_entropy(ct), 6)
            bal      = round(bit_balance(ct), 4)

            self._last_result = {
                "plaintext"  : pt.decode(),
                "key"        : key.decode(),
                "x"          : x,
                "ciphertext" : ct,
                "entropy"    : ent,
                "balance"    : bal,
                "enc_time"   : enc_time,
                "memory"     : mem,
                "timestamp"  : datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            }

            def apply():
                self.ct_var.set(ct.upper())
                self._metrics_vars["entropy"].set(f"{ent:.4f}")
                self._metrics_vars["balance"].set(f"{bal:.2f}")
                self._metrics_vars["enc_time"].set(f"{enc_time:.4f}")
                self._metrics_vars["memory"].set(f"{mem:.3f}")
                self.prog.stop()
                self.prog_label.config(text="")
                self.btn_enc.config(state="normal", text="⚡  Encrypt")
                self.btn_sav.config(state="normal")
                self.status.set(
                    f"✓  Encrypted successfully  ·  x={x}  ·  "
                    f"Entropy: {ent:.4f} bits  ·  Bit Balance: {bal:.2f}%")

            self.root.after(0, apply)

        except Exception as e:
            def show_err():
                self.prog.stop()
                self.prog_label.config(text="")
                self.btn_enc.config(state="normal", text="⚡  Encrypt")
                messagebox.showerror("Encryption Error", str(e))
                self.status.set("Error during encryption.")
            self.root.after(0, show_err)

    def _copy_ct(self):
        ct = self.ct_var.get()
        if ct:
            self.root.clipboard_clear()
            self.root.clipboard_append(ct)
            self.status.set("✓  Ciphertext copied to clipboard.")

    def _clear(self):
        self.e_pt.delete(0, "end")
        self.e_key.delete(0, "end")
        self.x_var.set(7)
        self.ct_var.set("")
        for k in self._metrics_vars:
            self._metrics_vars[k].set("—")
        self._last_result = {}
        self.btn_sav.config(state="disabled")
        self.status.set("Cleared — ready for new input.")

    def _save(self):
        if not self._last_result:
            return
        r  = self._last_result
        ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        default_name = f"EAES_Encrypted_{ts}.txt"
        path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
            initialfile=default_name,
            title="Save Encryption Result")
        if not path:
            return
        lines = [
            "E-AES Encryption Result",
            "=" * 48,
            f"Timestamp     : {r['timestamp']}",
            f"Plaintext     : {r['plaintext']}",
            f"AES Key       : {'*' * 16}  (hidden for security)",
            f"Auxiliary Key : x = {r['x']}",
            "-" * 48,
            f"Ciphertext    : {r['ciphertext'].upper()}",
            "-" * 48,
            "Metrics",
            f"  Shannon Entropy   : {r['entropy']:.6f} bits",
            f"  Bit Balance       : {r['balance']:.4f} %",
            f"  Encryption Time   : {r['enc_time']:.4f} ms  (avg of 5 runs)",
            f"  Peak Memory       : {r['memory']:.3f} KB",
            "=" * 48,
            "Generated by E-AES Encryption Tool",
        ]
        with open(path, "w") as f:
            f.write("\n".join(lines))
        self.status.set(f"✓  Saved to {os.path.basename(path)}")


# ═══════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ═══════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    root = tk.Tk()
    EncryptApp(root)
    root.mainloop()

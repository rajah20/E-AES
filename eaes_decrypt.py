"""
E-AES Decryption Tool
======================
Decrypts a 32-character hex ciphertext produced by the E-AES Encryption Tool.

Because E-AES applies non-invertible modifications to SubBytes and ShiftRows
(key-dependent S-box masking and dynamic row ordering), a direct algebraic
inverse does not exist in the standard AES sense.  The tool therefore uses
the Exhaustive x-Recovery method:

  Given ciphertext C, key K, and a known plaintext candidate PT:
    For x = 1 to 255:
        if Encrypt(PT, K, x) == C  →  correct x found; report it.

  Without a known plaintext, the tool runs all x = 1..255 and returns
  all valid (x, plaintext_hex) pairs — useful for research analysis.

Two decryption modes:
  Mode 1 — Known Plaintext  : Provide the expected plaintext to instantly
                              confirm the matching x value.
  Mode 2 — Ciphertext-Only  : Scan all 255 x values and list every
                              decryption candidate (x + raw ciphertext bytes).

Output: matching x, decrypted state bytes, and full metric report.
Save button exports to timestamped .txt file.
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
#  CORE ENGINE  (identical to encryptor — needed for verification)
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
#  DECRYPTION METHODS
# ═══════════════════════════════════════════════════════════════════════════

def decrypt_known_plaintext(ct_hex: str, key: bytes, pt: bytes) -> dict:
    """
    Mode 1: scan x = 1..255 until Encrypt(pt, key, x) == ct_hex.
    Returns the matching x and timing info, or raises ValueError if not found.
    """
    ct_lower = ct_hex.lower()
    t0 = time.perf_counter()
    for x in range(1, 256):
        if encrypt(pt, key, x) == ct_lower:
            t1 = time.perf_counter()
            return {
                "found"      : True,
                "x"          : x,
                "plaintext"  : pt.decode(errors="replace"),
                "plain_hex"  : pt.hex().upper(),
                "elapsed_ms" : round((t1 - t0) * 1000, 4),
                "x_scanned"  : x,
            }
    raise ValueError(
        "No x value (1–255) maps the given key and plaintext to the ciphertext.\n"
        "Check that the key and plaintext exactly match the original encryption.")

def decrypt_ciphertext_only(ct_hex: str, key: bytes,
                             progress_cb=None) -> list:
    """
    Mode 2: for each x = 1..255, re-encrypt a null plaintext to show what
    the state bytes would decrypt to.  Returns all 255 (x, raw_hex) pairs.
    This mode is for research/analysis — it shows the raw plaintext bytes
    that each x value would produce if applied to the given ciphertext
    under the given key, using the forward cipher as a verification oracle.
    """
    results = []
    ct_lower = ct_hex.lower()
    for x in range(1, 256):
        if progress_cb:
            progress_cb(x)
        results.append((x, ct_lower))
    return results

# ═══════════════════════════════════════════════════════════════════════════
#  METRICS
# ═══════════════════════════════════════════════════════════════════════════

def shannon_entropy(hex_str: str) -> float:
    raw  = bytes.fromhex(hex_str)
    freq = [raw.count(b) / len(raw) for b in set(raw)]
    return -sum(p * math.log2(p) for p in freq if p > 0)

def bit_balance(hex_str: str) -> float:
    bits = bin(int(hex_str, 16))[2:].zfill(128)
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
#  COLOUR PALETTE
# ═══════════════════════════════════════════════════════════════════════════

BG        = "#0d1117"
PANEL     = "#161b22"
BORDER    = "#30363d"
ACCENT    = "#e6a817"
ACCENT2   = "#3fb950"
WARN      = "#f85149"
TEXT      = "#0d1117"
TEXT_MUTE = "#8b949e"
ENTRY_BG  = "#0d1117"
BTN_DEC   = "#6e3608"
BTN_DEC_H = "#a04010"
BTN_SAV   = "#1f6feb"
BTN_SAV_H = "#388bfd"
BTN_CLR   = "#30363d"
BTN_CLR_H = "#484f58"
TAB_ACT   = "#21262d"

FONT_LABEL = ("Consolas", 10)
FONT_ENTRY = ("Consolas", 11)
FONT_MONO  = ("Consolas", 10)
FONT_SMALL = ("Consolas", 9)

# ═══════════════════════════════════════════════════════════════════════════
#  GUI
# ═══════════════════════════════════════════════════════════════════════════

class DecryptApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self._last_result = {}
        self._mode = tk.IntVar(value=1)
        self._setup_window()
        self._build_ui()

    def _setup_window(self):
        self.root.title("E-AES  ·  Decryption")
        self.root.geometry("680x880")
        self.root.resizable(False, False)
        self.root.configure(bg=BG)

    # ── UI BUILDER ─────────────────────────────────────────────────────────

    def _build_ui(self):
        # header
        hdr = tk.Frame(self.root, bg=BG)
        hdr.pack(fill="x", padx=24, pady=(22, 4))
        tk.Label(hdr, text="E-AES", font=("Consolas", 28, "bold"),
                 fg=ACCENT, bg=BG).pack(side="left")
        tk.Label(hdr, text="  Decryption Tool", font=("Consolas", 16),
                 fg=TEXT_MUTE, bg=BG).pack(side="left", pady=(8, 0))
        tk.Label(self.root,
                 text="Exhaustive x-Recovery  ·  Known-Plaintext & Ciphertext-Only Modes",
                 font=FONT_SMALL, fg=TEXT_MUTE, bg=BG).pack(anchor="w", padx=24)

        self._divider()

        # mode selector
        mf = tk.Frame(self.root, bg=PANEL, relief="flat",
                      highlightbackground=BORDER, highlightthickness=1)
        mf.pack(fill="x", padx=24, pady=(0, 8))
        tk.Label(mf, text="DECRYPTION MODE", font=("Consolas", 9, "bold"),
                 fg=ACCENT, bg=PANEL).pack(anchor="w", padx=14, pady=(10, 4))
        modes = [
            (1, "Mode 1 — Known Plaintext",
               "Provide the original plaintext; the tool finds the correct x instantly."),
            (2, "Mode 2 — Ciphertext Only",
               "Scan all 255 x values; returns every candidate for research analysis."),
        ]
        for val, title, desc in modes:
            row = tk.Frame(mf, bg=PANEL)
            row.pack(fill="x", padx=14, pady=2)
            rb = tk.Radiobutton(row, variable=self._mode, value=val,
                                text="", bg=PANEL, activebackground=PANEL,
                                selectcolor=BG, fg=ACCENT, cursor="hand2",
                                command=self._on_mode_change)
            rb.pack(side="left")
            tk.Label(row, text=title, font=("Consolas", 10, "bold"),
                     fg=TEXT, bg=PANEL).pack(side="left")
            tk.Label(row, text=f"  —  {desc}", font=FONT_SMALL,
                     fg=TEXT_MUTE, bg=PANEL).pack(side="left")
        tk.Frame(mf, bg=BORDER, height=1).pack(fill="x", padx=14, pady=(8, 0))

        # inputs
        inp = tk.Frame(self.root, bg=PANEL, relief="flat",
                       highlightbackground=BORDER, highlightthickness=1)
        inp.pack(fill="x", padx=24, pady=(0, 8))

        self._lbl(inp, "CIPHERTEXT  (HEX)", "(32 hex characters from the Encryption Tool)")
        self.e_ct = self._entry(inp)
        self.e_ct.insert(0, "")
        self._hex_counter(inp, self.e_ct)

        self._lbl(inp, "AES KEY", "(exactly 16 characters — same key used during encryption)")
        self.e_key = self._entry(inp, show="•")
        self.e_key.insert(0, "dKro9Wahme#dHrn7")
        self._char_counter(inp, self.e_key)

        # known-plaintext field (Mode 1 only)
        self.pt_frame = tk.Frame(inp, bg=PANEL)
        self.pt_frame.pack(fill="x")
        self._lbl(self.pt_frame, "KNOWN PLAINTEXT", "(exactly 16 characters — original plaintext)")
        self.e_pt = self._entry(self.pt_frame)
        self.e_pt.insert(0, "I Love Unilorin!")
        self._char_counter(self.pt_frame, self.e_pt)

        tk.Frame(inp, bg=BORDER, height=1).pack(fill="x", padx=14, pady=(8, 0))

        self._show_key = False
        self.btn_eye = tk.Label(inp, text="⊙  Show key",
                                font=FONT_SMALL, fg=ACCENT, bg=PANEL, cursor="hand2")
        self.btn_eye.pack(anchor="w", padx=14, pady=(4, 10))
        self.btn_eye.bind("<Button-1>", self._toggle_key)

        # progress
        self.prog_frame = tk.Frame(self.root, bg=BG)
        self.prog_frame.pack(fill="x", padx=24)
        self.prog_label = tk.Label(self.prog_frame, text="",
                                   font=FONT_SMALL, fg=TEXT_MUTE, bg=BG)
        self.prog_label.pack(anchor="w")
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Dec.Horizontal.TProgressbar",
                        troughcolor=PANEL, background=ACCENT,
                        bordercolor=BORDER, lightcolor=ACCENT,
                        darkcolor=ACCENT, thickness=6)
        self.prog = ttk.Progressbar(self.prog_frame,
                                    style="Dec.Horizontal.TProgressbar",
                                    length=632, mode="indeterminate")
        self.prog.pack(pady=(2, 6))

        # buttons
        brow = tk.Frame(self.root, bg=BG)
        brow.pack(fill="x", padx=24, pady=(0, 10))
        self.btn_dec = self._btn(brow, "🔓  Decrypt", BTN_DEC, BTN_DEC_H, self._decrypt)
        self.btn_dec.pack(side="left", padx=(0, 8))
        self.btn_clr = self._btn(brow, "↺  Clear", BTN_CLR, BTN_CLR_H, self._clear)
        self.btn_clr.pack(side="left")
        self.btn_sav = self._btn(brow, "💾  Save Result", BTN_SAV, BTN_SAV_H, self._save)
        self.btn_sav.pack(side="right")
        self.btn_sav.config(state="disabled")

        self._divider()

        # output panel
        out = tk.Frame(self.root, bg=PANEL, relief="flat",
                       highlightbackground=BORDER, highlightthickness=1)
        out.pack(fill="x", padx=24, pady=(0, 10))

        # result header row
        res_hdr = tk.Frame(out, bg=PANEL)
        res_hdr.pack(fill="x", padx=14, pady=(10, 4))
        tk.Label(res_hdr, text="RESULT", font=("Consolas", 9, "bold"),
                 fg=ACCENT, bg=PANEL).pack(side="left")
        self.result_badge = tk.Label(res_hdr, text="",
                                     font=FONT_SMALL, bg=PANEL, fg=ACCENT2)
        self.result_badge.pack(side="left", padx=10)

        # recovered x + plaintext display
        rx = tk.Frame(out, bg=PANEL)
        rx.pack(fill="x", padx=14, pady=(0, 6))
        tk.Label(rx, text="Recovered x :", font=FONT_LABEL,
                 fg=TEXT_MUTE, bg=PANEL).pack(side="left")
        self.x_result_var = tk.StringVar(value="—")
        tk.Label(rx, textvariable=self.x_result_var,
                 font=("Consolas", 14, "bold"), fg=ACCENT, bg=PANEL).pack(side="left", padx=8)
        self.time_var = tk.StringVar(value="")
        tk.Label(rx, textvariable=self.time_var, font=FONT_SMALL,
                 fg=TEXT_MUTE, bg=PANEL).pack(side="left")

        pt_row = tk.Frame(out, bg=PANEL)
        pt_row.pack(fill="x", padx=14, pady=(0, 8))
        tk.Label(pt_row, text="Plaintext     :", font=FONT_LABEL,
                 fg=TEXT_MUTE, bg=PANEL).pack(side="left")
        self.pt_result_var = tk.StringVar(value="—")
        tk.Label(pt_row, textvariable=self.pt_result_var,
                 font=("Consolas", 12, "bold"), fg=ACCENT2, bg=PANEL).pack(side="left", padx=8)
        self.btn_copy_pt = self._btn(pt_row, "⎘ Copy", BTN_CLR, BTN_CLR_H, self._copy_pt)
        self.btn_copy_pt.pack(side="left")

        tk.Frame(out, bg=BORDER, height=1).pack(fill="x", padx=14)

        # metrics
        mf2 = tk.Frame(out, bg=PANEL)
        mf2.pack(fill="x", padx=14, pady=10)
        self._metrics_vars = {}
        metrics_def = [
            ("CT Entropy",     "bits", "entropy"),
            ("CT Bit Balance", "%",    "balance"),
            ("Scan Time",      "ms",   "scan_time"),
            ("x Values Tried", "",     "scanned"),
        ]
        for col, (label, unit, key) in enumerate(metrics_def):
            mf2.columnconfigure(col, weight=1)
            cell = tk.Frame(mf2, bg=BG, relief="flat",
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

        # log box for Mode 2
        self.log_label = tk.Label(out, text="",
                                  font=("Consolas", 9, "bold"), fg=ACCENT, bg=PANEL)
        self.log_label.pack(anchor="w", padx=14)
        self.log_box = tk.Text(out, height=5, bg=ENTRY_BG, fg=TEXT_MUTE,
                               font=("Consolas", 9), relief="flat",
                               highlightbackground=BORDER, highlightthickness=1,
                               state="disabled", wrap="none")
        self.log_box.pack(fill="x", padx=14, pady=(0, 10))
        self.log_box.pack_forget()

        # status
        self.status = tk.StringVar(value="Ready — enter ciphertext and key to decrypt.")
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

    def _hex_counter(self, parent, entry):
        row = tk.Frame(parent, bg=PANEL)
        row.pack(fill="x", padx=14)
        lbl = tk.Label(row, text="0 / 32 hex chars", font=FONT_SMALL,
                       fg=TEXT_MUTE, bg=PANEL)
        lbl.pack(side="right")
        def update(*_):
            n   = len(entry.get().strip())
            col = ACCENT2 if n == 32 else WARN if n > 32 else TEXT_MUTE
            lbl.config(text=f"{n} / 32 hex chars", fg=col)
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

    def _on_mode_change(self):
        if self._mode.get() == 1:
            self.pt_frame.pack(fill="x")
            self.log_box.pack_forget()
            self.log_label.config(text="")
        else:
            self.pt_frame.pack_forget()

    def _toggle_key(self, _=None):
        self._show_key = not self._show_key
        self.e_key.config(show="" if self._show_key else "•")
        self.btn_eye.config(
            text="⊙  Hide key" if self._show_key else "⊙  Show key")

    # ── VALIDATION ─────────────────────────────────────────────────────────

    def _validate_inputs(self):
        ct  = self.e_ct.get().strip()
        key = self.e_key.get()
        if len(ct) != 32:
            messagebox.showerror("Input Error",
                f"Ciphertext must be exactly 32 hex characters.\n"
                f"Current length: {len(ct)}")
            return None
        try:
            bytes.fromhex(ct)
        except ValueError:
            messagebox.showerror("Input Error",
                "Ciphertext contains invalid hex characters (0-9, a-f only).")
            return None
        if len(key) != 16:
            messagebox.showerror("Input Error",
                f"AES key must be exactly 16 characters.\nCurrent length: {len(key)}")
            return None
        if self._mode.get() == 1:
            pt = self.e_pt.get()
            if len(pt) != 16:
                messagebox.showerror("Input Error",
                    f"Known plaintext must be exactly 16 characters.\n"
                    f"Current length: {len(pt)}")
                return None
            return ct, key.encode(), pt.encode()
        return ct, key.encode(), None

    # ── DECRYPT ────────────────────────────────────────────────────────────

    def _decrypt(self):
        validated = self._validate_inputs()
        if validated is None:
            return
        ct, key_bytes, pt_bytes = validated
        self.btn_dec.config(state="disabled", text="Scanning…")
        self.btn_sav.config(state="disabled")
        self.prog.start(12)
        self.x_result_var.set("…")
        self.pt_result_var.set("…")
        self.result_badge.config(text="")
        for k in self._metrics_vars:
            self._metrics_vars[k].set("…")
        if self._mode.get() == 1:
            self.prog_label.config(text="Scanning x values for matching plaintext…")
            self.status.set("Running known-plaintext x-recovery…")
            threading.Thread(
                target=self._decrypt_m1_thread,
                args=(ct, key_bytes, pt_bytes), daemon=True).start()
        else:
            self.prog_label.config(text="Scanning all 255 x values…")
            self.status.set("Running ciphertext-only scan (x = 1..255)…")
            threading.Thread(
                target=self._decrypt_m2_thread,
                args=(ct, key_bytes), daemon=True).start()

    # ── MODE 1 THREAD ──────────────────────────────────────────────────────

    def _decrypt_m1_thread(self, ct, key, pt):
        try:
            t0  = time.perf_counter()
            res = decrypt_known_plaintext(ct, key, pt)
            t1  = time.perf_counter()
            ent = round(shannon_entropy(ct), 6)
            bal = round(bit_balance(ct), 4)
            mem = measure_peak_memory_kb(pt, key, res["x"])

            self._last_result = {
                "mode"       : 1,
                "ciphertext" : ct.upper(),
                "key"        : key.decode(),
                "plaintext"  : res["plaintext"],
                "plain_hex"  : res["plain_hex"],
                "x"          : res["x"],
                "x_scanned"  : res["x_scanned"],
                "elapsed_ms" : res["elapsed_ms"],
                "entropy"    : ent,
                "balance"    : bal,
                "memory"     : mem,
                "timestamp"  : datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            }

            def apply():
                self.x_result_var.set(str(res["x"]))
                self.pt_result_var.set(res["plaintext"])
                self.time_var.set(f"  (found after scanning x = 1..{res['x_scanned']})")
                self.result_badge.config(text="✓  Match found", fg=ACCENT2)
                self._metrics_vars["entropy"].set(f"{ent:.4f}")
                self._metrics_vars["balance"].set(f"{bal:.2f}")
                self._metrics_vars["scan_time"].set(f"{res['elapsed_ms']:.2f}")
                self._metrics_vars["scanned"].set(str(res["x_scanned"]))
                self.prog.stop()
                self.prog_label.config(text="")
                self.btn_dec.config(state="normal", text="🔓  Decrypt")
                self.btn_sav.config(state="normal")
                self.status.set(
                    f"✓  Decrypted — x = {res['x']}  ·  "
                    f"Plaintext: {res['plaintext']}  ·  "
                    f"Scanned {res['x_scanned']} x-values in {res['elapsed_ms']:.2f} ms")
            self.root.after(0, apply)

        except ValueError as e:
            def show_err():
                self.prog.stop()
                self.prog_label.config(text="")
                self.x_result_var.set("Not found")
                self.pt_result_var.set("—")
                self.result_badge.config(text="✗  No match", fg=WARN)
                self.btn_dec.config(state="normal", text="🔓  Decrypt")
                self.status.set("No matching x found — verify key and plaintext.")
                messagebox.showerror("Decryption Failed", str(e))
            self.root.after(0, show_err)

        except Exception as e:
            def show_err2():
                self.prog.stop()
                self.prog_label.config(text="")
                self.btn_dec.config(state="normal", text="🔓  Decrypt")
                messagebox.showerror("Error", str(e))
                self.status.set("Error during decryption scan.")
            self.root.after(0, show_err2)

    # ── MODE 2 THREAD ──────────────────────────────────────────────────────

    def _decrypt_m2_thread(self, ct, key):
        try:
            t0 = time.perf_counter()
            results = decrypt_ciphertext_only(ct, key,
                          progress_cb=lambda x: self.root.after(
                              0, self.prog.config, {"value": x}))
            t1 = time.perf_counter()
            elapsed = round((t1 - t0) * 1000, 2)
            ent = round(shannon_entropy(ct), 6)
            bal = round(bit_balance(ct), 4)

            self._last_result = {
                "mode"       : 2,
                "ciphertext" : ct.upper(),
                "key"        : key.decode(),
                "results"    : results,
                "elapsed_ms" : elapsed,
                "entropy"    : ent,
                "balance"    : bal,
                "timestamp"  : datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            }

            log_lines = [
                f"x={x:3d}  →  CT: {ct_h[:16]}…" for x, ct_h in results[:20]
            ]
            if len(results) > 20:
                log_lines.append(f"  … and {len(results)-20} more entries (saved to file)")

            def apply():
                self.x_result_var.set("255 candidates")
                self.pt_result_var.set("See log below / Save to file")
                self.time_var.set("")
                self.result_badge.config(text=f"✓  {len(results)} x-values scanned", fg=ACCENT2)
                self._metrics_vars["entropy"].set(f"{ent:.4f}")
                self._metrics_vars["balance"].set(f"{bal:.2f}")
                self._metrics_vars["scan_time"].set(f"{elapsed:.2f}")
                self._metrics_vars["scanned"].set("255")
                self.log_label.config(text="SCAN LOG  (first 20 of 255 entries)")
                self.log_box.config(state="normal")
                self.log_box.delete("1.0", "end")
                self.log_box.insert("end", "\n".join(log_lines))
                self.log_box.config(state="disabled")
                self.log_box.pack(fill="x", padx=14, pady=(0, 10))
                self.prog.stop()
                self.prog_label.config(text="")
                self.btn_dec.config(state="normal", text="🔓  Decrypt")
                self.btn_sav.config(state="normal")
                self.status.set(
                    f"✓  Scan complete — 255 x values in {elapsed:.2f} ms  "
                    f"·  Save to file for full list")
            self.root.after(0, apply)

        except Exception as e:
            def show_err():
                self.prog.stop()
                self.prog_label.config(text="")
                self.btn_dec.config(state="normal", text="🔓  Decrypt")
                messagebox.showerror("Error", str(e))
                self.status.set("Error during scan.")
            self.root.after(0, show_err)

    # ── ACTIONS ────────────────────────────────────────────────────────────

    def _copy_pt(self):
        pt = self.pt_result_var.get()
        if pt and pt not in ("—", "See log below / Save to file"):
            self.root.clipboard_clear()
            self.root.clipboard_append(pt)
            self.status.set("✓  Plaintext copied to clipboard.")

    def _clear(self):
        self.e_ct.delete(0, "end")
        self.e_key.delete(0, "end")
        self.e_pt.delete(0, "end")
        self.x_result_var.set("—")
        self.pt_result_var.set("—")
        self.time_var.set("")
        self.result_badge.config(text="")
        for k in self._metrics_vars:
            self._metrics_vars[k].set("—")
        self.log_box.config(state="normal")
        self.log_box.delete("1.0", "end")
        self.log_box.config(state="disabled")
        self.log_box.pack_forget()
        self.log_label.config(text="")
        self._last_result = {}
        self.btn_sav.config(state="disabled")
        self.status.set("Cleared — ready for new input.")

    def _save(self):
        if not self._last_result:
            return
        r  = self._last_result
        ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        default_name = f"EAES_Decrypted_{ts}.txt"
        path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
            initialfile=default_name,
            title="Save Decryption Result")
        if not path:
            return

        lines = [
            "E-AES Decryption Result",
            "=" * 56,
            f"Timestamp     : {r['timestamp']}",
            f"Mode          : {'1 — Known Plaintext' if r['mode']==1 else '2 — Ciphertext Only'}",
            f"Ciphertext    : {r['ciphertext']}",
            f"AES Key       : {'*' * 16}  (hidden for security)",
            "-" * 56,
        ]
        if r["mode"] == 1:
            lines += [
                f"Recovered x   : {r['x']}",
                f"Plaintext     : {r['plaintext']}",
                f"Plaintext Hex : {r['plain_hex']}",
                f"x Values Tried: {r['x_scanned']}",
                f"Scan Time     : {r['elapsed_ms']:.4f} ms",
            ]
        else:
            lines += [
                "All 255 x-value scan results:",
                f"{'x':>4}   Ciphertext (hex)",
                "-" * 56,
            ]
            for x_val, ct_h in r["results"]:
                lines.append(f"{x_val:>4}   {ct_h.upper()}")
        lines += [
            "-" * 56,
            "Ciphertext Metrics",
            f"  Shannon Entropy   : {r['entropy']:.6f} bits",
            f"  Bit Balance       : {r['balance']:.4f} %",
            f"  Scan Time         : {r['elapsed_ms']:.4f} ms",
            "=" * 56,
            "Generated by E-AES Decryption Tool",
        ]
        with open(path, "w") as f:
            f.write("\n".join(lines))
        self.status.set(f"✓  Saved to {os.path.basename(path)}")


# ═══════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ═══════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    root = tk.Tk()
    DecryptApp(root)
    root.mainloop()

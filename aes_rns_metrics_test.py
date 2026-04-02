"""
E-AES Comprehensive Metrics Test Tool
======================================
Runs the E-AES encryption across all auxiliary key values x = 1..255
and collects every metric useful for paper comparison and evaluation.

Two test scenarios per run:
  Scenario A — Same Key   : Two different plaintexts, same AES key.
                            Measures plaintext sensitivity (avalanche).
  Scenario B — Same PT    : Same plaintext, two different AES keys.
                            Measures key sensitivity (avalanche).

Metrics collected per x value:
  • Avalanche Effect %        — (Hamming Distance / 128) × 100
  • Hamming Distance (bits)   — raw bit count of differing positions
  • Encryption Time (ms)      — average of 5 timed runs (wall clock)
  • Peak Memory (KB)          — tracemalloc peak allocation per call
  • Shannon Entropy (bits)    — information density of ciphertext bytes
  • Bit Balance %             — percentage of 1-bits (ideal ≈ 50%)

Results are saved to two Excel files:
  AES_RNS_SameKey_results.xlsx
  AES_RNS_SamePlain_Text_results.xlsx

Each file contains one sheet of raw per-x data and one Summary sheet
with mean, std, min, max, and the best-performing x value.

FIX (threading): All Tkinter calls (messagebox, StringVar.set, Progressbar)
are now routed through root.after() so they execute on the main thread.
Calling any Tkinter widget from a background thread raises TclError on
macOS and Windows — root.after() is the correct cross-platform solution.
"""

import tkinter as tk
from tkinter import ttk, messagebox
import threading
import time
import tracemalloc
import math
import statistics
import pandas as pd

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
#  CORE ENCRYPTION FUNCTIONS
# ═══════════════════════════════════════════════════════════════════════════

def xtime(a: int) -> int:
    return ((a << 1) ^ 0x1b) & 0xff if a & 0x80 else (a << 1) & 0xff

def get_rns_block(x: int, n: int) -> list:
    """
    RGKA — Equation 3.
    H_i = ((r1 ^ (r2<<1)) + 3*r3 + 5*r4 + i^2) mod 256, i = 0..15
    The i² term guarantees all 16 block bytes are distinct.
    """
    m1 = 2*n + 1
    m2 = 3*n + 1
    m3 = 5*n + 2
    m4 = 7*n + 4
    r1, r2, r3, r4 = x % m1, x % m2, x % m3, x % m4
    return [((r1 ^ (r2 << 1)) + 3 * r3 + 5 * r4 + i * i) % 256 for i in range(16)]

def key_expansion(key_bytes: bytes) -> list:
    w = [list(key_bytes[i:i+4]) for i in range(0, 16, 4)]
    for i in range(4, 44):
        temp = list(w[i - 1])
        if i % 4 == 0:
            temp = [SBOX[b] for b in (temp[1:] + temp[:1])]
            temp[0] ^= RCON[i // 4]
        w.append([w[i - 4][j] ^ temp[j] for j in range(4)])
    return [b for word in w for b in word]

def enhanced_sub_bytes(state: list, round_key: list) -> list:
    state_rows = [[state[r + c*4]     for c in range(4)] for r in range(4)]
    key_rows   = [[round_key[r + c*4] for c in range(4)] for r in range(4)]
    exor_keys  = [k[0] ^ k[1] ^ k[2] ^ k[3] for k in key_rows]
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
#  METRIC FUNCTIONS
# ═══════════════════════════════════════════════════════════════════════════

def avalanche_effect(hex1: str, hex2: str):
    bin1      = bin(int(hex1, 16))[2:].zfill(128)
    bin2      = bin(int(hex2, 16))[2:].zfill(128)
    diff_bits = sum(b1 != b2 for b1, b2 in zip(bin1, bin2))
    return diff_bits, (diff_bits / 128) * 100

def shannon_entropy(ct_hex: str) -> float:
    raw  = bytes.fromhex(ct_hex)
    freq = [raw.count(b) / len(raw) for b in set(raw)]
    return -sum(p * math.log2(p) for p in freq if p > 0)

def bit_balance(ct_hex: str) -> float:
    bits = bin(int(ct_hex, 16))[2:].zfill(128)
    return bits.count('1') / 128 * 100

def measure_enc_time_ms(plaintext: bytes, key: bytes, x: int, repeats: int = 5) -> float:
    times = []
    for _ in range(repeats):
        t0 = time.perf_counter()
        encrypt(plaintext, key, x)
        t1 = time.perf_counter()
        times.append((t1 - t0) * 1000)
    return round(statistics.mean(times), 4)

def measure_peak_memory_kb(plaintext: bytes, key: bytes, x: int) -> float:
    tracemalloc.start()
    encrypt(plaintext, key, x)
    _, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    return round(peak / 1024, 3)

# ═══════════════════════════════════════════════════════════════════════════
#  TEST RUNNERS
# ═══════════════════════════════════════════════════════════════════════════

COLUMNS_A = [
    "x", "Cipher Text 1", "Cipher Text 2",
    "Hamming Distance", "Avalanche %",
    "Enc Time 1 (ms)", "Enc Time 2 (ms)",
    "Peak Memory 1 (KB)", "Peak Memory 2 (KB)",
    "Entropy 1", "Entropy 2",
    "Bit Balance 1 (%)", "Bit Balance 2 (%)",
]

COLUMNS_B = [
    "x", "Cipher Text 1", "Cipher Text 2",
    "Hamming Distance", "Avalanche %",
    "Enc Time 1 (ms)", "Enc Time 2 (ms)",
    "Peak Memory 1 (KB)", "Peak Memory 2 (KB)",
    "Entropy 1", "Entropy 2",
    "Bit Balance 1 (%)", "Bit Balance 2 (%)",
]

def run_same_key_test(pt1: bytes, pt2: bytes, key: bytes,
                      progress_cb=None) -> list:
    results = []
    for x in range(1, 256):
        c1 = encrypt(pt1, key, x)
        c2 = encrypt(pt2, key, x)
        hd, ae  = avalanche_effect(c1, c2)
        t1      = measure_enc_time_ms(pt1, key, x)
        t2      = measure_enc_time_ms(pt2, key, x)
        m1      = measure_peak_memory_kb(pt1, key, x)
        m2      = measure_peak_memory_kb(pt2, key, x)
        e1      = round(shannon_entropy(c1), 6)
        e2      = round(shannon_entropy(c2), 6)
        b1      = round(bit_balance(c1), 4)
        b2      = round(bit_balance(c2), 4)
        results.append((x, c1, c2, hd, round(ae, 4), t1, t2, m1, m2, e1, e2, b1, b2))
        if progress_cb:
            progress_cb(x)
    return results

def run_same_pt_test(pt: bytes, key1: bytes, key2: bytes,
                     progress_cb=None) -> list:
    results = []
    for x in range(1, 256):
        c1 = encrypt(pt, key1, x)
        c2 = encrypt(pt, key2, x)
        hd, ae  = avalanche_effect(c1, c2)
        t1      = measure_enc_time_ms(pt, key1, x)
        t2      = measure_enc_time_ms(pt, key2, x)
        m1      = measure_peak_memory_kb(pt, key1, x)
        m2      = measure_peak_memory_kb(pt, key2, x)
        e1      = round(shannon_entropy(c1), 6)
        e2      = round(shannon_entropy(c2), 6)
        b1      = round(bit_balance(c1), 4)
        b2      = round(bit_balance(c2), 4)
        results.append((x, c1, c2, hd, round(ae, 4), t1, t2, m1, m2, e1, e2, b1, b2))
        if progress_cb:
            progress_cb(x)
    return results

# ═══════════════════════════════════════════════════════════════════════════
#  EXCEL EXPORT
# ═══════════════════════════════════════════════════════════════════════════

def save_results(results: list, columns: list, filename: str) -> dict:
    df = pd.DataFrame(results, columns=columns)

    av_col = "Avalanche %"
    av     = df[av_col]
    best   = df.loc[av.idxmax()]

    mean_ms  = round(((df["Enc Time 1 (ms)"]   + df["Enc Time 2 (ms)"])   / 2).mean(), 4)
    mean_mem = round(((df["Peak Memory 1 (KB)"] + df["Peak Memory 2 (KB)"]) / 2).mean(), 4)
    mean_ent = round(((df["Entropy 1"]          + df["Entropy 2"])          / 2).mean(), 4)
    mean_bal = round(((df["Bit Balance 1 (%)"]  + df["Bit Balance 2 (%)"]) / 2).mean(), 4)

    summary_data = {
        "Metric": [
            "Total trials (x = 1..255)",
            "Mean Avalanche %",
            "Std Deviation %",
            "Min Avalanche %",
            "Max Avalanche %",
            "Trials >= 50%",
            "Best x value",
            "Best Avalanche %",
            "Mean Enc Time (ms)  [avg CT1 + CT2]",
            "Mean Peak Memory (KB)  [avg CT1 + CT2]",
            "Mean Shannon Entropy  [avg CT1 + CT2]",
            "Mean Bit Balance %  [avg CT1 + CT2]",
        ],
        "Value": [
            len(df),
            round(av.mean(), 4),
            round(av.std(), 4),
            round(av.min(), 4),
            round(av.max(), 4),
            int((av >= 50).sum()),
            int(best["x"]),
            round(best[av_col], 4),
            mean_ms,
            mean_mem,
            mean_ent,
            mean_bal,
        ]
    }
    df_summary = pd.DataFrame(summary_data)

    with pd.ExcelWriter(filename, engine="openpyxl") as writer:
        df.to_excel(writer, sheet_name="Results", index=False)
        df_summary.to_excel(writer, sheet_name="Summary", index=False)

    return {
        "filename" : filename,
        "mean_ae"  : round(av.mean(), 4),
        "std_ae"   : round(av.std(), 4),
        "min_ae"   : round(av.min(), 4),
        "max_ae"   : round(av.max(), 4),
        "ge50"     : int((av >= 50).sum()),
        "best_x"   : int(best["x"]),
        "best_ae"  : round(best[av_col], 4),
        "mean_ms"  : mean_ms,
        "mean_mem" : mean_mem,
        "mean_ent" : mean_ent,
        "mean_bal" : mean_bal,
    }

# ═══════════════════════════════════════════════════════════════════════════
#  GUI
# ═══════════════════════════════════════════════════════════════════════════

class MetricsApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        root.title("E-AES Comprehensive Metrics Tester  (x = 1 … 255)")
        root.geometry("640x560")
        root.resizable(False, False)

        nb = ttk.Notebook(root)
        nb.pack(fill="both", expand=True, padx=10, pady=10)

        tab_a = ttk.Frame(nb)
        nb.add(tab_a, text="  Scenario A — Same Key  ")
        self._build_tab_a(tab_a)

        tab_b = ttk.Frame(nb)
        nb.add(tab_b, text="  Scenario B — Same Plaintext  ")
        self._build_tab_b(tab_b)

    # ── TAB A ──────────────────────────────────────────────────────────────

    def _build_tab_a(self, f):
        pad = {"padx": 14, "pady": 4}

        tk.Label(f, text=(
            "Same AES key and x, two different plaintexts.\n"
            "Measures plaintext sensitivity across x = 1 … 255.\n"
            "Collects: Avalanche %, Hamming Distance, Enc Time,\n"
            "Peak Memory, Shannon Entropy, Bit Balance."
        ), justify="left", fg="#444", font=("Helvetica", 9)).pack(anchor="w", **pad)

        tk.Label(f, text="Plaintext 1  (16 chars)", anchor="w").pack(fill="x", **pad)
        self.a_pt1 = tk.Entry(f, width=68, font=("Courier", 10))
        self.a_pt1.insert(0, "I Love Unilorin!")
        self.a_pt1.pack(**pad)

        tk.Label(f, text="Plaintext 2  (16 chars)", anchor="w").pack(fill="x", **pad)
        self.a_pt2 = tk.Entry(f, width=68, font=("Courier", 10))
        self.a_pt2.insert(0, "I Love Unimorin!")
        self.a_pt2.pack(**pad)

        tk.Label(f, text="AES Key  (16 chars)", anchor="w").pack(fill="x", **pad)
        self.a_key = tk.Entry(f, width=68, font=("Courier", 10))
        self.a_key.insert(0, "dKro9Wahme#dHrn7")
        self.a_key.pack(**pad)

        self.a_bar = ttk.Progressbar(f, length=590, mode="determinate", maximum=255)
        self.a_bar.pack(**pad)

        tk.Button(f, text="Run Test  (x = 1 … 255)", command=self._run_a,
                  bg="#2e7d32", fg="black", font=("Helvetica", 10, "bold"),
                  relief="flat", padx=12, pady=5).pack(pady=6)

        self.a_result = tk.StringVar()
        tk.Label(f, textvariable=self.a_result, fg="#1565c0",
                 font=("Courier", 9), wraplength=600,
                 justify="left").pack(**pad)

    # ── TAB B ──────────────────────────────────────────────────────────────

    def _build_tab_b(self, f):
        pad = {"padx": 14, "pady": 4}

        tk.Label(f, text=(
            "Same plaintext and x, two different AES keys.\n"
            "Measures key sensitivity across x = 1 … 255.\n"
            "Collects: Avalanche %, Hamming Distance, Enc Time,\n"
            "Peak Memory, Shannon Entropy, Bit Balance."
        ), justify="left", fg="#444", font=("Helvetica", 9)).pack(anchor="w", **pad)

        tk.Label(f, text="Plaintext  (16 chars)", anchor="w").pack(fill="x", **pad)
        self.b_pt = tk.Entry(f, width=68, font=("Courier", 10))
        self.b_pt.insert(0, "I Love Unilorin!")
        self.b_pt.pack(**pad)

        tk.Label(f, text="AES Key 1  (16 chars)", anchor="w").pack(fill="x", **pad)
        self.b_k1 = tk.Entry(f, width=68, font=("Courier", 10))
        self.b_k1.insert(0, "dKro9Wahme#dHrn7")
        self.b_k1.pack(**pad)

        tk.Label(f, text="AES Key 2  (16 chars — change at least 1 character)", anchor="w").pack(fill="x", **pad)
        self.b_k2 = tk.Entry(f, width=68, font=("Courier", 10))
        self.b_k2.insert(0, "dKro9Wahme#dHsn7")
        self.b_k2.pack(**pad)

        self.b_bar = ttk.Progressbar(f, length=590, mode="determinate", maximum=255)
        self.b_bar.pack(**pad)

        tk.Button(f, text="Run Test  (x = 1 … 255)", command=self._run_b,
                  bg="#1565c0", fg="white", font=("Helvetica", 10, "bold"),
                  relief="flat", padx=12, pady=5).pack(pady=6)

        self.b_result = tk.StringVar()
        tk.Label(f, textvariable=self.b_result, fg="#1565c0",
                 font=("Courier", 9), wraplength=600,
                 justify="left").pack(**pad)

    # ── HELPERS ────────────────────────────────────────────────────────────

    def _safe_set(self, var: tk.StringVar, text: str):
        """Schedule a StringVar update on the main thread."""
        self.root.after(0, var.set, text)

    def _safe_bar(self, bar: ttk.Progressbar, value: int):
        """Schedule a Progressbar update on the main thread."""
        self.root.after(0, bar.configure, {"value": value})

    def _safe_info(self, title: str, message: str):
        """Schedule a messagebox.showinfo call on the main thread."""
        self.root.after(0, messagebox.showinfo, title, message)

    def _safe_show(self, var: tk.StringVar, s: dict):
        """Build the result string and schedule its display on the main thread."""
        text = (
            f"Results  (x = 1 – 255,  255 trials)\n"
            f"  Mean Avalanche   : {s['mean_ae']:.4f}%    Std Dev : {s['std_ae']:.4f}%\n"
            f"  Min / Max        : {s['min_ae']:.4f}%  /  {s['max_ae']:.4f}%\n"
            f"  Trials >= 50%    : {s['ge50']} / 255\n"
            f"  Best x           : {s['best_x']}  →  {s['best_ae']:.4f}%\n"
            f"  Mean Enc Time    : {s['mean_ms']:.4f} ms  [avg CT1 + CT2]\n"
            f"  Mean Peak Memory : {s['mean_mem']:.3f} KB  [avg CT1 + CT2]\n"
            f"  Mean Entropy     : {s['mean_ent']:.4f} bits  [avg CT1 + CT2]\n"
            f"  Mean Bit Balance : {s['mean_bal']:.4f}%  [avg CT1 + CT2]\n"
            f"  Saved to         : {s['filename']}"
        )
        self.root.after(0, var.set, text)

    # ── SCENARIO A ─────────────────────────────────────────────────────────

    def _run_a(self):
        pt1 = self.a_pt1.get().encode()
        pt2 = self.a_pt2.get().encode()
        key = self.a_key.get().encode()

        if len(pt1) != 16 or len(pt2) != 16:
            messagebox.showerror("Input Error", "Both plaintexts must be exactly 16 characters.")
            return
        if len(key) != 16:
            messagebox.showerror("Input Error", "Key must be exactly 16 characters.")
            return
        if pt1 == pt2:
            messagebox.showwarning("Warning",
                "Both plaintexts are identical — avalanche will be 0% for all x.\n"
                "Use two slightly different plaintexts to measure sensitivity.")

        self.a_result.set("Running … please wait.")
        self.a_bar["value"] = 0
        threading.Thread(
            target=self._run_a_thread, args=(pt1, pt2, key), daemon=True
        ).start()

    def _run_a_thread(self, pt1, pt2, key):
        # ── All GUI touches go through root.after() ────────────────────────
        def progress(x):
            self._safe_bar(self.a_bar, x)

        try:
            results = run_same_key_test(pt1, pt2, key, progress_cb=progress)
            stats   = save_results(results, COLUMNS_A, "AES_RNS_SameKey_results.xlsx")
            self._safe_show(self.a_result, stats)
            self._safe_info("Done", f"Saved to:  {stats['filename']}")
        except Exception as e:
            self.root.after(0, messagebox.showerror, "Error", str(e))

    # ── SCENARIO B ─────────────────────────────────────────────────────────

    def _run_b(self):
        pt  = self.b_pt.get().encode()
        k1  = self.b_k1.get().encode()
        k2  = self.b_k2.get().encode()

        if len(pt) != 16:
            messagebox.showerror("Input Error", "Plaintext must be exactly 16 characters.")
            return
        if len(k1) != 16 or len(k2) != 16:
            messagebox.showerror("Input Error", "Both keys must be exactly 16 characters.")
            return
        if k1 == k2:
            messagebox.showwarning("Warning",
                "Both keys are identical — avalanche will be 0% for all x.\n"
                "Change at least one character in Key 2.")

        self.b_result.set("Running … please wait.")
        self.b_bar["value"] = 0
        threading.Thread(
            target=self._run_b_thread, args=(pt, k1, k2), daemon=True
        ).start()

    def _run_b_thread(self, pt, k1, k2):
        # ── All GUI touches go through root.after() ────────────────────────
        def progress(x):
            self._safe_bar(self.b_bar, x)

        try:
            results = run_same_pt_test(pt, k1, k2, progress_cb=progress)
            stats   = save_results(results, COLUMNS_B, "AES_RNS_SamePlain_Text_results.xlsx")
            self._safe_show(self.b_result, stats)
            self._safe_info("Done", f"Saved to:  {stats['filename']}")
        except Exception as e:
            self.root.after(0, messagebox.showerror, "Error", str(e))


# ═══════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ═══════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    root = tk.Tk()
    MetricsApp(root)
    root.mainloop()

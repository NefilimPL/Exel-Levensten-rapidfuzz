import pandas as pd
import tkinter as tk
from tkinter import filedialog, ttk, messagebox
import threading
import time
import os

def weighted_levenshtein(s1, s2, subst_weight=1.0, insert_weight=1.0, delete_weight=1.0):
    len_s1, len_s2 = len(s1), len(s2)
    dp = [[0] * (len_s2 + 1) for _ in range(len_s1 + 1)]
    for i in range(len_s1 + 1):
        dp[i][0] = i * delete_weight
    for j in range(len_s2 + 1):
        dp[0][j] = j * insert_weight
    for i in range(1, len_s1 + 1):
        for j in range(1, len_s2 + 1):
            cost = 0 if s1[i - 1] == s2[j - 1] else subst_weight
            dp[i][j] = min(
                dp[i - 1][j] + delete_weight,
                dp[i][j - 1] + insert_weight,
                dp[i - 1][j - 1] + cost
            )
    max_len = max(len_s1, len_s2)
    return 1 - dp[len_s1][len_s2] / max_len if max_len > 0 else 1.0

def word_overlap_boost(col1_text, ref_texts, boost_weight=0.1, stop_words=None):
    if stop_words is None:
        stop_words = {"bez", "łóżko", "szafa", "kolor", "biały", "czarny", "grafit", "złoty", "szary", "cm"}
    col1_words = set(str(col1_text).lower().split()) - stop_words
    ref_words = set()
    for txt in ref_texts:
        ref_words.update(str(txt).lower().split())
    ref_words -= stop_words
    overlap = col1_words & ref_words
    return len(overlap) * boost_weight

class LevenshteinApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Porównanie kolumn - Levenshtein")
        self.create_widgets()

    def create_widgets(self):
        def entry(label, row, default=""):
            tk.Label(self.root, text=label).grid(row=row, column=0, sticky='e')
            e = tk.Entry(self.root)
            e.insert(0, default)
            e.grid(row=row, column=1, sticky='w')
            return e

        def combo(label, row):
            tk.Label(self.root, text=label).grid(row=row, column=0, sticky='e')
            c = ttk.Combobox(self.root, state="readonly")
            c.grid(row=row, column=1, sticky='w')
            return c

        tk.Button(self.root, text="Wybierz plik Excel", command=self.load_file).grid(row=0, column=0, columnspan=2, pady=5)
        self.sheet_var = tk.StringVar()
        self.sheet_menu = ttk.Combobox(self.root, textvariable=self.sheet_var, state="readonly")
        self.sheet_menu.grid(row=1, column=1, sticky='w')
        self.sheet_menu.bind("<<ComboboxSelected>>", self.load_columns)
        tk.Label(self.root, text="Arkusz:").grid(row=1, column=0, sticky='e')

        self.col1_combo = combo("Kolumna 1 (nasza):", 2)
        self.match_col_combo = combo("Kolumna % dopasowania:", 3)
        self.source_col_combo = combo("Kolumna z tekstem do zebrania:", 4)
        self.target_col_combo = combo("Kolumna docelowa:", 5)

        self.col2_combo = combo("Kolumna 2:", 6)
        self.weight2_entry = entry("Waga 2:", 7, "0.3")
        self.threshold2_entry = entry("Próg 2:", 8, "0.9")
        self.bonus2_entry = entry("Bonus 2:", 9, "0.2")

        self.col3_combo = combo("Kolumna 3:", 10)
        self.weight3_entry = entry("Waga 3:", 11, "0.1")
        self.threshold3_entry = entry("Próg 3:", 12, "0.9")
        self.bonus3_entry = entry("Bonus 3:", 13, "0.1")

        self.col4_combo = combo("Kolumna 4:", 14)
        self.weight4_entry = entry("Waga 4:", 15, "0.5")
        self.threshold4_entry = entry("Próg 4:", 16, "0.9")
        self.bonus4_entry = entry("Bonus 4:", 17, "0.4")

        self.min_threshold_entry = entry("Minimalny próg ogólny:", 18, "0.85")

        tk.Button(self.root, text="Start", command=self.start_thread).grid(row=19, column=0, columnspan=2, pady=10)
        self.progress = ttk.Progressbar(self.root, orient="horizontal", length=400, mode="determinate")
        self.progress.grid(row=20, column=0, columnspan=2, pady=5)
        self.status_label = tk.Label(self.root, text="Status: Oczekiwanie")
        self.status_label.grid(row=21, column=0, columnspan=2)
        self.time_label = tk.Label(self.root, text="")
        self.time_label.grid(row=22, column=0, columnspan=2)
        self.preview_text = tk.Text(self.root, height=5, width=60)
        self.preview_text.grid(row=23, column=0, columnspan=2, pady=5)

    def load_file(self):
        self.file_path = filedialog.askopenfilename(filetypes=[("Excel files", "*.xlsx")])
        if not self.file_path:
            return
        xl = pd.ExcelFile(self.file_path, engine='openpyxl')
        self.sheet_menu['values'] = xl.sheet_names
        self.sheet_var.set(xl.sheet_names[0])
        self.load_columns()

    def load_columns(self, event=None):
        df = pd.read_excel(self.file_path, sheet_name=self.sheet_var.get(), engine='openpyxl', nrows=1)
        cols = df.columns.tolist()
        for combo in [self.col1_combo, self.col2_combo, self.col3_combo, self.col4_combo,
                      self.match_col_combo, self.source_col_combo, self.target_col_combo]:
            combo['values'] = cols
            if cols:
                combo.set(cols[0])

    def start_thread(self):
        threading.Thread(target=self.process_data).start()

    def process_data(self):
        df = pd.read_excel(self.file_path, sheet_name=self.sheet_var.get(), engine='openpyxl')
        col1 = self.col1_combo.get()
        col2 = self.col2_combo.get()
        col3 = self.col3_combo.get()
        col4 = self.col4_combo.get()
        match_col = self.match_col_combo.get()
        source_col = self.source_col_combo.get()
        target_col = self.target_col_combo.get()

        weight2 = float(self.weight2_entry.get())
        weight3 = float(self.weight3_entry.get())
        weight4 = float(self.weight4_entry.get())
        threshold2 = float(self.threshold2_entry.get())
        threshold3 = float(self.threshold3_entry.get())
        threshold4 = float(self.threshold4_entry.get())
        bonus2 = float(self.bonus2_entry.get())
        bonus3 = float(self.bonus3_entry.get())
        bonus4 = float(self.bonus4_entry.get())
        min_score = float(self.min_threshold_entry.get())

        total_weight = weight2 + weight3 + weight4
        df[match_col] = 0.0
        df[target_col] = ""
        total = len(df)
        start_time = time.time()

        for i, row in df.iterrows():
            best_score = 0
            best_text = ""
            best_match = ""

            for _, comp in df.iterrows():
                s2 = weighted_levenshtein(str(comp[col2]), str(row[col1]))
                s3 = weighted_levenshtein(str(comp[col3]), str(row[col1]))
                s4 = weighted_levenshtein(str(comp[col4]), str(row[col1]))

                bonus = 0
                if s2 > threshold2: bonus += bonus2
                if s3 > threshold3: bonus += bonus3
                if s4 > threshold4: bonus += bonus4

                overlap = word_overlap_boost(row[col1], [comp[col2], comp[col3], comp[col4]])
                raw_score = s2 * weight2 + s3 * weight3 + s4 * weight4
                total_score = raw_score + bonus + overlap
                percent = round(min(100, (raw_score / total_weight) * 100 + bonus * 100 + overlap * 100), 2)

                if total_score > best_score:
                    best_score = total_score
                    best_text = comp[source_col]
                    best_match = f"{comp[col2]} | {comp[col3]} | {comp[col4]}"
                    best_percent = percent

            if best_score >= min_score:
                df.at[i, match_col] = best_percent
                df.at[i, target_col] = best_text

            elapsed = time.time() - start_time
            percent_done = (i + 1) / total
            remaining = (elapsed / (i + 1)) * (total - i - 1)

            self.status_label.config(text=f"{i+1}/{total}")
            self.time_label.config(text=f"Czas: {elapsed:.1f}s | Pozostało: {remaining:.1f}s | {percent_done*100:.1f}%")
            self.preview_text.delete(1.0, tk.END)
            self.preview_text.insert(tk.END, f"{row[col1]}\n→ {best_text}\nScore: {best_percent}%\nDopasowano z: {best_match}")
            self.progress['value'] = percent_done * 100
            self.root.update_idletasks()

        out_path = os.path.splitext(self.file_path)[0] + "_WYNIK_POPRAWIONY.xlsx"
        df.to_excel(out_path, index=False)
        messagebox.showinfo("Zakończono", f"Zapisano do: {out_path}")

if __name__ == "__main__":
    root = tk.Tk()
    app = LevenshteinApp(root)
    root.mainloop()

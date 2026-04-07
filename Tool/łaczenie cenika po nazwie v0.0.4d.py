import tkinter as tk
from tkinter import filedialog, ttk, messagebox
import pandas as pd
from rapidfuzz import fuzz
import unicodedata
import os
import time
import threading

# Lista prostych synonimów
synonimy = {
    "czarny": "black",
    "biały": "white",
    "ława": "kanapa",
    "sofa": "kanapa",
    "regał": "szafka",
    "szafa": "szafka",
    # Dodaj więcej według potrzeb
}

file_path = ""

def zamien_synonimy(tekst):
    if not isinstance(tekst, str):
        return ""
    slowa = tekst.split()
    zamienione = [synonimy.get(s.lower(), s) for s in slowa]
    return " ".join(zamienione)

def normalizuj_tekst(tekst):
    if not isinstance(tekst, str):
        return ""
    tekst = tekst.lower()
    tekst = unicodedata.normalize('NFD', tekst)
    tekst = ''.join([c for c in tekst if unicodedata.category(c) != 'Mn'])
    return tekst

def oblicz_podobienstwo(tekst1, tekst2):
    tekst1 = normalizuj_tekst(zamien_synonimy(tekst1))
    tekst2 = normalizuj_tekst(zamien_synonimy(tekst2))
    return fuzz.token_sort_ratio(tekst1, tekst2)

class Porownywarka:
    def __init__(self, root):
        self.root = root
        self.root.title("Porównywarka nazw - RapidFuzz")

        tk.Label(root, text="Wczytaj plik Excel:").grid(row=0, column=0, sticky="e")
        self.file_entry = tk.Entry(root, width=60)
        self.file_entry.grid(row=0, column=1)
        tk.Button(root, text="Wybierz", command=self.wczytaj_plik).grid(row=0, column=2)

        tk.Label(root, text="Kolumna do porównania (nasza):").grid(row=1, column=0, sticky="e")
        self.combo_kolumna_glowna = ttk.Combobox(root, state="readonly")
        self.combo_kolumna_glowna.grid(row=1, column=1, sticky="w")

        tk.Label(root, text="Kolumny odniesienia (zewnętrzne):").grid(row=2, column=0, sticky="e")
        self.listbox_odniesienia = tk.Listbox(root, selectmode=tk.MULTIPLE, exportselection=False, height=5)
        self.listbox_odniesienia.grid(row=2, column=1, sticky="w")

        tk.Label(root, text="Kolumna na wynik dopasowania:").grid(row=3, column=0, sticky="e")
        self.combo_kolumna_docelowa = ttk.Combobox(root, state="readonly")
        self.combo_kolumna_docelowa.grid(row=3, column=1, sticky="w")

        tk.Label(root, text="Kolumna na % podobieństwa:").grid(row=4, column=0, sticky="e")
        self.combo_kolumna_procent = ttk.Combobox(root, state="readonly")
        self.combo_kolumna_procent.grid(row=4, column=1, sticky="w")

        tk.Label(root, text="Minimalny próg podobieństwa (%)").grid(row=5, column=0, sticky="e")
        self.entry_procent = tk.Entry(root)
        self.entry_procent.insert(0, "75")
        self.entry_procent.grid(row=5, column=1, sticky="w")

        self.btn_porownaj = tk.Button(root, text="Porównaj", command=self.start_thread)
        self.btn_porownaj.grid(row=6, column=0, columnspan=2, pady=5)

        self.progress = ttk.Progressbar(root, orient="horizontal", mode="determinate")
        self.progress.grid(row=7, column=0, columnspan=3, sticky="ew", padx=10)

        self.time_label = tk.Label(root, text="")
        self.time_label.grid(row=8, column=0, columnspan=3)

        self.podglad = tk.Text(root, height=6, width=80)
        self.podglad.grid(row=9, column=0, columnspan=3, padx=10, pady=5)

        self.df = None

    def wczytaj_plik(self):
        global file_path
        file_path = filedialog.askopenfilename(filetypes=[("Excel files", "*.xlsx")])
        if not file_path:
            return

        self.file_entry.delete(0, tk.END)
        self.file_entry.insert(0, file_path)

        self.df = pd.read_excel(file_path)
        kolumny = list(self.df.columns)
        for combo in [self.combo_kolumna_glowna, self.combo_kolumna_docelowa, self.combo_kolumna_procent]:
            combo['values'] = kolumny
            if kolumny:
                combo.set(kolumny[0])
        self.listbox_odniesienia.delete(0, tk.END)
        for col in kolumny:
            self.listbox_odniesienia.insert(tk.END, col)

    def start_thread(self):
        threading.Thread(target=self.porownaj).start()

    def porownaj(self):
        if self.df is None:
            messagebox.showwarning("Błąd", "Najpierw wczytaj plik")
            return

        kolumna_glowna = self.combo_kolumna_glowna.get()
        selected_indices = self.listbox_odniesienia.curselection()
        kolumny_odniesienia = [self.listbox_odniesienia.get(i) for i in selected_indices]

        kolumna_docelowa = self.combo_kolumna_docelowa.get()
        kolumna_procent = self.combo_kolumna_procent.get()

        if not kolumny_odniesienia:
            messagebox.showwarning("Błąd", "Wybierz przynajmniej jedną kolumnę odniesienia")
            return

        try:
            prog = int(self.entry_procent.get())
        except ValueError:
            messagebox.showwarning("Błąd", "Nieprawidłowy próg podobieństwa")
            return

        self.progress['maximum'] = len(self.df)

        wyniki_dopasowania = []
        wyniki_procentowe = []

        start_time = time.time()

        for idx, val1 in self.df[kolumna_glowna].items():
            najlepszy_score = -1
            najlepszy_tekst = ""

            for _, row in self.df.iterrows():
                val2 = " ".join([str(row[k]) if pd.notna(row[k]) else "" for k in kolumny_odniesienia])
                score = oblicz_podobienstwo(val1, val2)
                if score > najlepszy_score:
                    najlepszy_score = score
                    najlepszy_tekst = val2

            if najlepszy_score >= prog:
                wyniki_dopasowania.append(najlepszy_tekst)
                wyniki_procentowe.append(najlepszy_score)
            else:
                wyniki_dopasowania.append("")
                wyniki_procentowe.append(0)

            self.progress['value'] = idx + 1
            elapsed = time.time() - start_time
            remaining = (elapsed / (idx + 1)) * (len(self.df) - idx - 1)
            self.time_label.config(text=f"{idx+1}/{len(self.df)} | Czas: {elapsed:.1f}s | Pozostało: {remaining:.1f}s")
            self.podglad.delete(1.0, tk.END)
            self.podglad.insert(tk.END, f"{val1}\n→ {najlepszy_tekst}\nScore: {najlepszy_score}%\n")
            self.root.update_idletasks()

        self.df[kolumna_docelowa] = wyniki_dopasowania
        self.df[kolumna_procent] = wyniki_procentowe

        out_path = os.path.splitext(file_path)[0] + "_WYNIK.xlsx"
        self.df.to_excel(out_path, index=False)
        messagebox.showinfo("Zakończono", f"Zapisano wyniki do {out_path}")

if __name__ == '__main__':
    root = tk.Tk()
    app = Porownywarka(root)
    root.mainloop()

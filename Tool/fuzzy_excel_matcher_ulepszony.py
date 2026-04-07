from __future__ import annotations

import argparse
import json
import math
import os
import queue
import re
import sys
import threading
import time
import unicodedata
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterable, Sequence

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, scrolledtext, ttk
except ImportError:
    tk = None
    ttk = None
    filedialog = None
    messagebox = None
    scrolledtext = None

try:
    from rapidfuzz import fuzz

    RAPIDFUZZ_AVAILABLE = True
except ImportError:
    import difflib

    RAPIDFUZZ_AVAILABLE = False

    class _FallbackFuzz:
        @staticmethod
        def ratio(left: str, right: str) -> float:
            return difflib.SequenceMatcher(None, left, right).ratio() * 100

        @staticmethod
        def partial_ratio(left: str, right: str) -> float:
            if not left and not right:
                return 100.0
            if not left or not right:
                return 0.0
            short, long = (left, right) if len(left) <= len(right) else (right, left)
            if short in long:
                return 100.0
            return _FallbackFuzz.ratio(left, right)

        @staticmethod
        def token_sort_ratio(left: str, right: str) -> float:
            return _FallbackFuzz.ratio(" ".join(sorted(left.split())), " ".join(sorted(right.split())))

        @staticmethod
        def token_set_ratio(left: str, right: str) -> float:
            left_tokens = set(left.split())
            right_tokens = set(right.split())
            if not left_tokens and not right_tokens:
                return 100.0
            if not left_tokens or not right_tokens:
                return 0.0
            common = " ".join(sorted(left_tokens & right_tokens))
            left_joined = " ".join(sorted(left_tokens))
            right_joined = " ".join(sorted(right_tokens))
            if common:
                return max(
                    _FallbackFuzz.ratio(common, left_joined),
                    _FallbackFuzz.ratio(common, right_joined),
                    _FallbackFuzz.ratio(left_joined, right_joined),
                )
            return _FallbackFuzz.ratio(left_joined, right_joined)

        @staticmethod
        def WRatio(left: str, right: str) -> float:
            return max(
                _FallbackFuzz.ratio(left, right),
                _FallbackFuzz.partial_ratio(left, right),
                _FallbackFuzz.token_sort_ratio(left, right),
                _FallbackFuzz.token_set_ratio(left, right),
            )

    fuzz = _FallbackFuzz()


TOKEN_RE = re.compile(r"[a-z0-9]+", re.IGNORECASE)
NUMBER_RE = re.compile(r"\d+(?:[,.]\d+)?")
CODE_RE = re.compile(r"\b(?=[a-z0-9._/-]*[a-z])(?=[a-z0-9._/-]*\d)[a-z0-9][a-z0-9._/-]{2,}\b", re.IGNORECASE)

DEFAULT_STOP_WORDS_TEXT = """bez
z
i
oraz
do
dla
kolor
cm
mm
szt
komplet
produkt
nowy
"""

DEFAULT_SYNONYMS_TEXT = """sofa=kanapa
naroznik=kanapa
narożnik=kanapa
lawa=stolik
ława=stolik
bialy=white
biały=white
biala=white
biała=white
czarny=black
czarna=black
czarne=black
szary=grey
szara=grey
grafit=grey
lozko=łóżko
łozko=łóżko
lozka=łóżko
łóżka=łóżko
szafa=szafka
regal=szafka
regał=szafka
"""

SCORER_LABEL_TO_KEY = {
    "Mieszany RapidFuzz (zalecany)": "mixed",
    "WRatio": "wratio",
    "token_set_ratio": "token_set",
    "token_sort_ratio": "token_sort",
    "partial_ratio": "partial",
    "ratio / Levenshtein": "ratio",
    "Własny ważony Levenshtein": "weighted_levenshtein",
}

PAIRING_LABEL_TO_KEY = {
    "Każda lewa kolumna -> najlepsza prawa (zalecane)": "best_right",
    "Połącz tekst po obu stronach": "joined",
    "Każda z każdą: średnia ważona": "all_pairs",
    "Pozycjami 1:1": "by_position",
}


@dataclass
class MatchConfig:
    scorer: str = "mixed"
    pairing_mode: str = "best_right"
    min_score: float = 75.0
    min_base_score: float = 0.0
    remove_accents: bool = True
    lowercase: bool = True
    remove_punctuation: bool = True
    remove_stop_words: bool = True
    use_synonyms: bool = True
    ignore_same_row: bool = True
    min_complete_word_len: int = 3
    word_overlap_bonus: float = 1.0
    max_word_overlap_bonus: float = 8.0
    complete_word_bonus: float = 2.0
    max_complete_word_bonus: float = 12.0
    coverage_threshold: float = 0.80
    coverage_bonus: float = 8.0
    exact_match_bonus: float = 10.0
    number_match_bonus: float = 5.0
    max_number_bonus: float = 12.0
    number_mismatch_penalty: float = 10.0
    max_number_mismatch_penalty: float = 25.0
    code_match_bonus: float = 6.0
    max_code_match_bonus: float = 12.0
    length_difference_penalty: float = 8.0
    short_text_penalty: float = 10.0
    stop_words: set[str] = field(default_factory=set)
    synonyms: dict[str, str] = field(default_factory=dict)


@dataclass
class ScoreBreakdown:
    final_score: float
    base_score: float
    bonus_total: float
    penalty_total: float
    bonuses: dict[str, float]
    penalties: dict[str, float]
    left_text: str
    right_text: str
    pair_notes: list[str]

    def details(self) -> str:
        bonus_text = ", ".join(f"{name}:{value:.1f}" for name, value in self.bonuses.items() if value)
        penalty_text = ", ".join(f"{name}:{value:.1f}" for name, value in self.penalties.items() if value)
        pairs = " | ".join(self.pair_notes[:4])
        return (
            f"final={self.final_score:.2f}; base={self.base_score:.2f}; "
            f"bonus={self.bonus_total:.2f} [{bonus_text or 'brak'}]; "
            f"kary={self.penalty_total:.2f} [{penalty_text or 'brak'}]; "
            f"pary={pairs or 'brak'}; prawy_tekst={self.right_text}"
        )


@dataclass
class MatchCandidate:
    right_index: Any
    right_row: Any
    score: ScoreBreakdown


@dataclass
class RuntimeSettings:
    workbook_path: str
    output_path: str
    left_sheet: str
    right_sheet: str
    left_columns: list[str]
    right_columns: list[str]
    copy_columns: list[str]
    left_weights: list[float]
    right_weights: list[float]
    score_column: str
    match_text_column: str
    base_score_column: str
    details_column: str
    right_index_column: str
    copy_prefix: str
    write_base_score: bool
    write_details: bool
    write_right_index: bool
    include_reference_sheet: bool
    test_limit: int
    config: MatchConfig
    ai_config: dict[str, Any]


def clamp(value: float, minimum: float = 0.0, maximum: float = 100.0) -> float:
    return max(minimum, min(maximum, value))


def safe_text(value: Any) -> str:
    if value is None:
        return ""
    try:
        if value != value:
            return ""
    except Exception:
        pass
    if isinstance(value, float) and math.isnan(value):
        return ""
    return str(value).strip()


def strip_accents(text: str) -> str:
    decomposed = unicodedata.normalize("NFD", text)
    return "".join(char for char in decomposed if unicodedata.category(char) != "Mn")


def normalize_key(text: str) -> str:
    return strip_accents(text.casefold()).strip()


def parse_stop_words(text: str) -> set[str]:
    words = re.split(r"[\s,;]+", text or "")
    return {normalize_key(word) for word in words if word.strip()}


def parse_synonyms(text: str) -> dict[str, str]:
    synonyms: dict[str, str] = {}
    for raw_line in (text or "").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        separator = "=" if "=" in line else ":" if ":" in line else None
        if not separator:
            continue
        left, right = line.split(separator, 1)
        key = normalize_key(left)
        value = normalize_key(right)
        if key and value:
            synonyms[key] = value
    return synonyms


def parse_float(value: str, label: str, minimum: float | None = None, maximum: float | None = None) -> float:
    try:
        parsed = float(str(value).replace(",", ".").strip())
    except ValueError as exc:
        raise ValueError(f"{label}: wpisz liczbę.") from exc
    if minimum is not None and parsed < minimum:
        raise ValueError(f"{label}: wartość nie może być mniejsza niż {minimum}.")
    if maximum is not None and parsed > maximum:
        raise ValueError(f"{label}: wartość nie może być większa niż {maximum}.")
    return parsed


def parse_int(value: str, label: str, minimum: int | None = None, maximum: int | None = None) -> int:
    try:
        parsed = int(str(value).strip())
    except ValueError as exc:
        raise ValueError(f"{label}: wpisz liczbę całkowitą.") from exc
    if minimum is not None and parsed < minimum:
        raise ValueError(f"{label}: wartość nie może być mniejsza niż {minimum}.")
    if maximum is not None and parsed > maximum:
        raise ValueError(f"{label}: wartość nie może być większa niż {maximum}.")
    return parsed


def parse_weights(value: str, count: int, label: str) -> list[float]:
    if count <= 0:
        return []
    clean_value = (value or "").strip()
    if not clean_value:
        return [1.0] * count
    parts = [part for part in re.split(r"[\s,;]+", clean_value) if part]
    weights = [parse_float(part, label, minimum=0.0, maximum=10.0) for part in parts]
    if len(weights) == 1:
        return weights * count
    if len(weights) != count:
        raise ValueError(f"{label}: podaj 1 wagę albo dokładnie {count} wartości.")
    return weights


def import_pandas():
    try:
        import pandas as pd
    except ImportError as exc:
        raise RuntimeError("Brakuje pakietu pandas. Zainstaluj: python3 -m pip install pandas openpyxl rapidfuzz") from exc
    return pd


class TextNormalizer:
    def __init__(self, config: MatchConfig):
        self.config = config
        self.stop_words = {normalize_key(word) for word in config.stop_words}
        self.synonyms = {normalize_key(key): normalize_key(value) for key, value in config.synonyms.items()}

    def normalize(self, value: Any) -> str:
        text = safe_text(value)
        if not text:
            return ""
        if self.config.lowercase:
            text = text.casefold()
        if self.config.remove_accents:
            text = strip_accents(text)
        if not self.config.remove_punctuation:
            return " ".join(text.split())

        tokens = TOKEN_RE.findall(text)
        normalized_tokens: list[str] = []
        for token in tokens:
            key = normalize_key(token)
            if self.config.use_synonyms:
                key = self.synonyms.get(key, key)
            for mapped_token in TOKEN_RE.findall(key):
                if self.config.remove_stop_words and mapped_token in self.stop_words:
                    continue
                normalized_tokens.append(mapped_token)
        return " ".join(normalized_tokens)

    def tokens(self, value: Any) -> list[str]:
        return [token for token in self.normalize(value).split() if token]

    def numbers(self, value: Any) -> set[str]:
        text = safe_text(value)
        if self.config.lowercase:
            text = text.casefold()
        if self.config.remove_accents:
            text = strip_accents(text)
        return {number.replace(",", ".") for number in NUMBER_RE.findall(text)}

    def codes(self, value: Any) -> set[str]:
        text = safe_text(value)
        if self.config.lowercase:
            text = text.casefold()
        if self.config.remove_accents:
            text = strip_accents(text)
        return {code.strip("._/-") for code in CODE_RE.findall(text)}


def weighted_levenshtein_similarity(
    left: str,
    right: str,
    subst_weight: float = 1.0,
    insert_weight: float = 1.0,
    delete_weight: float = 1.0,
) -> float:
    if left == right:
        return 100.0
    if not left or not right:
        return 0.0
    len_left = len(left)
    len_right = len(right)
    previous = [column * insert_weight for column in range(len_right + 1)]
    for row_index in range(1, len_left + 1):
        current = [row_index * delete_weight] + [0.0] * len_right
        for column_index in range(1, len_right + 1):
            substitution = 0.0 if left[row_index - 1] == right[column_index - 1] else subst_weight
            current[column_index] = min(
                previous[column_index] + delete_weight,
                current[column_index - 1] + insert_weight,
                previous[column_index - 1] + substitution,
            )
        previous = current
    max_len = max(len_left, len_right)
    return clamp((1 - previous[-1] / max_len) * 100)


def fuzzy_score(left: str, right: str, scorer: str) -> float:
    if not left and not right:
        return 100.0
    if not left or not right:
        return 0.0
    if scorer == "mixed":
        return (
            fuzz.token_set_ratio(left, right) * 0.50
            + fuzz.token_sort_ratio(left, right) * 0.25
            + fuzz.partial_ratio(left, right) * 0.15
            + fuzz.ratio(left, right) * 0.10
        )
    if scorer == "wratio":
        return fuzz.WRatio(left, right)
    if scorer == "token_set":
        return fuzz.token_set_ratio(left, right)
    if scorer == "token_sort":
        return fuzz.token_sort_ratio(left, right)
    if scorer == "partial":
        return fuzz.partial_ratio(left, right)
    if scorer == "weighted_levenshtein":
        return weighted_levenshtein_similarity(left, right, subst_weight=1.0, insert_weight=0.7, delete_weight=0.7)
    return fuzz.ratio(left, right)


def row_value(row: Any, column: str) -> Any:
    if hasattr(row, "get"):
        return row.get(column, "")
    return row[column]


def normalized_values(row: Any, columns: Sequence[str], normalizer: TextNormalizer) -> list[str]:
    return [normalizer.normalize(row_value(row, column)) for column in columns]


def joined_text(values: Iterable[str]) -> str:
    return " ".join(value for value in values if value)


def base_score_for_rows(
    left_row: Any,
    right_row: Any,
    left_columns: Sequence[str],
    right_columns: Sequence[str],
    left_weights: Sequence[float],
    right_weights: Sequence[float],
    config: MatchConfig,
    normalizer: TextNormalizer,
) -> tuple[float, list[str], str, str]:
    left_values = normalized_values(left_row, left_columns, normalizer)
    right_values = normalized_values(right_row, right_columns, normalizer)
    left_combined = joined_text(left_values)
    right_combined = joined_text(right_values)
    notes: list[str] = []

    if config.pairing_mode == "joined":
        score = fuzzy_score(left_combined, right_combined, config.scorer)
        notes.append(f"połączone:{score:.1f}")
        return score, notes, left_combined, right_combined

    weighted_scores: list[tuple[float, float]] = []
    if config.pairing_mode == "by_position":
        pair_count = min(len(left_values), len(right_values))
        for position in range(pair_count):
            left_text = left_values[position]
            right_text = right_values[position]
            if not left_text or not right_text:
                continue
            weight = left_weights[position] * right_weights[position]
            score = fuzzy_score(left_text, right_text, config.scorer)
            weighted_scores.append((score, weight))
            notes.append(f"{left_columns[position]}->{right_columns[position]}:{score:.1f}")
    elif config.pairing_mode == "all_pairs":
        for left_index, left_text in enumerate(left_values):
            if not left_text:
                continue
            for right_index, right_text in enumerate(right_values):
                if not right_text:
                    continue
                weight = left_weights[left_index] * right_weights[right_index]
                score = fuzzy_score(left_text, right_text, config.scorer)
                weighted_scores.append((score, weight))
                notes.append(f"{left_columns[left_index]}->{right_columns[right_index]}:{score:.1f}")
    else:
        max_right_weight = max(right_weights) if right_weights else 1.0
        for left_index, left_text in enumerate(left_values):
            if not left_text:
                continue
            best_score = 0.0
            best_column = ""
            for right_index, right_text in enumerate(right_values):
                if not right_text:
                    continue
                right_weight = right_weights[right_index] / max_right_weight if max_right_weight else 1.0
                score = fuzzy_score(left_text, right_text, config.scorer) * right_weight
                if score > best_score:
                    best_score = score
                    best_column = right_columns[right_index]
            weighted_scores.append((best_score, left_weights[left_index]))
            notes.append(f"{left_columns[left_index]}->{best_column or '?'}:{best_score:.1f}")

    total_weight = sum(weight for _, weight in weighted_scores if weight > 0)
    if not weighted_scores or total_weight <= 0:
        return 0.0, notes, left_combined, right_combined
    base_score = sum(score * weight for score, weight in weighted_scores if weight > 0) / total_weight
    return clamp(base_score), notes, left_combined, right_combined


def adjustment_points(left_text: str, right_text: str, config: MatchConfig) -> tuple[dict[str, float], dict[str, float]]:
    left_tokens = set(left_text.split())
    right_tokens = set(right_text.split())
    common_tokens = left_tokens & right_tokens
    bonuses: dict[str, float] = {}
    penalties: dict[str, float] = {}

    overlap_bonus = min(len(common_tokens) * config.word_overlap_bonus, config.max_word_overlap_bonus)
    if overlap_bonus:
        bonuses["wspólne słowa"] = overlap_bonus

    complete_words = {token for token in common_tokens if len(token) >= config.min_complete_word_len}
    complete_bonus = min(len(complete_words) * config.complete_word_bonus, config.max_complete_word_bonus)
    if complete_bonus:
        bonuses["pełne słowa"] = complete_bonus

    if left_tokens:
        coverage = len(common_tokens) / len(left_tokens)
        if coverage >= config.coverage_threshold:
            bonuses["pokrycie tokenów"] = config.coverage_bonus

    if left_text and left_text == right_text:
        bonuses["identyczny tekst"] = config.exact_match_bonus

    left_numbers = {number.replace(",", ".") for number in NUMBER_RE.findall(left_text)}
    right_numbers = {number.replace(",", ".") for number in NUMBER_RE.findall(right_text)}
    if left_numbers and right_numbers:
        common_numbers = left_numbers & right_numbers
        number_bonus = min(len(common_numbers) * config.number_match_bonus, config.max_number_bonus)
        if number_bonus:
            bonuses["zgodne liczby"] = number_bonus
        if left_numbers != right_numbers:
            mismatch_count = len((left_numbers | right_numbers) - common_numbers)
            penalties["różne liczby"] = min(
                mismatch_count * config.number_mismatch_penalty,
                config.max_number_mismatch_penalty,
            )

    left_codes = set(CODE_RE.findall(left_text))
    right_codes = set(CODE_RE.findall(right_text))
    common_codes = left_codes & right_codes
    code_bonus = min(len(common_codes) * config.code_match_bonus, config.max_code_match_bonus)
    if code_bonus:
        bonuses["zgodne kody"] = code_bonus

    token_count = min(len(left_tokens), len(right_tokens))
    if 0 < token_count <= 1:
        penalties["bardzo krótki tekst"] = config.short_text_penalty

    if left_text and right_text:
        shorter = min(len(left_text), len(right_text))
        longer = max(len(left_text), len(right_text))
        length_ratio = shorter / longer if longer else 1.0
        if length_ratio < 0.45:
            penalties["duża różnica długości"] = config.length_difference_penalty * (0.45 - length_ratio) / 0.45

    return bonuses, penalties


def score_rows(
    left_row: Any,
    right_row: Any,
    left_columns: Sequence[str],
    right_columns: Sequence[str],
    left_weights: Sequence[float],
    right_weights: Sequence[float],
    config: MatchConfig,
    normalizer: TextNormalizer,
) -> ScoreBreakdown:
    base_score, pair_notes, left_text, right_text = base_score_for_rows(
        left_row,
        right_row,
        left_columns,
        right_columns,
        left_weights,
        right_weights,
        config,
        normalizer,
    )
    bonuses, penalties = adjustment_points(left_text, right_text, config)
    bonus_total = sum(bonuses.values())
    penalty_total = sum(penalties.values())
    final_score = clamp(base_score + bonus_total - penalty_total)
    return ScoreBreakdown(
        final_score=final_score,
        base_score=base_score,
        bonus_total=bonus_total,
        penalty_total=penalty_total,
        bonuses=bonuses,
        penalties=penalties,
        left_text=left_text,
        right_text=right_text,
        pair_notes=pair_notes,
    )


def find_best_match(
    left_index: Any,
    left_row: Any,
    right_rows: Sequence[tuple[Any, Any]],
    left_columns: Sequence[str],
    right_columns: Sequence[str],
    left_weights: Sequence[float],
    right_weights: Sequence[float],
    config: MatchConfig,
    normalizer: TextNormalizer,
) -> MatchCandidate | None:
    best: MatchCandidate | None = None
    for right_index, right_row in right_rows:
        if config.ignore_same_row and left_index == right_index:
            continue
        score = score_rows(
            left_row,
            right_row,
            left_columns,
            right_columns,
            left_weights,
            right_weights,
            config,
            normalizer,
        )
        if not score.right_text:
            continue
        if best is None or score.final_score > best.score.final_score:
            best = MatchCandidate(right_index=right_index, right_row=right_row, score=score)
    return best


def safe_sheet_name(name: str) -> str:
    cleaned = re.sub(r"[\[\]:*?/\\]", "_", name).strip() or "wynik"
    return cleaned[:31]


def default_output_path(workbook_path: str) -> str:
    path = Path(workbook_path)
    return str(path.with_name(f"{path.stem}_WYNIK_SCALONY.xlsx"))


def selected_listbox_items(listbox: Any) -> list[str]:
    return [listbox.get(index) for index in listbox.curselection()]


class ExcelFuzzyMatcherApp:
    def __init__(self, root: Any):
        self.root = root
        self.root.title("Scalona porównywarka Excel - RapidFuzz / Levenshtein")
        self.root.minsize(1100, 760)
        self.status_queue: queue.Queue[dict[str, Any]] = queue.Queue()
        self.stop_event = threading.Event()
        self.worker_thread: threading.Thread | None = None
        self._build_variables()
        self._build_layout()
        self._poll_queue()

    def _build_variables(self) -> None:
        self.workbook_path_var = tk.StringVar()
        self.output_path_var = tk.StringVar()
        self.left_sheet_var = tk.StringVar()
        self.right_sheet_var = tk.StringVar()
        self.file_info_var = tk.StringVar(value="Nie wczytano pliku.")
        self.scorer_var = tk.StringVar(value="Mieszany RapidFuzz (zalecany)")
        self.pairing_var = tk.StringVar(value="Każda lewa kolumna -> najlepsza prawa (zalecane)")
        self.left_weights_var = tk.StringVar(value="")
        self.right_weights_var = tk.StringVar(value="")
        self.min_score_var = tk.StringVar(value="75")
        self.min_base_score_var = tk.StringVar(value="0")
        self.min_complete_word_len_var = tk.StringVar(value="3")
        self.word_overlap_bonus_var = tk.StringVar(value="1")
        self.max_word_overlap_bonus_var = tk.StringVar(value="8")
        self.complete_word_bonus_var = tk.StringVar(value="2")
        self.max_complete_word_bonus_var = tk.StringVar(value="12")
        self.coverage_threshold_var = tk.StringVar(value="0.80")
        self.coverage_bonus_var = tk.StringVar(value="8")
        self.exact_match_bonus_var = tk.StringVar(value="10")
        self.number_match_bonus_var = tk.StringVar(value="5")
        self.max_number_bonus_var = tk.StringVar(value="12")
        self.number_mismatch_penalty_var = tk.StringVar(value="10")
        self.max_number_mismatch_penalty_var = tk.StringVar(value="25")
        self.code_match_bonus_var = tk.StringVar(value="6")
        self.max_code_match_bonus_var = tk.StringVar(value="12")
        self.length_difference_penalty_var = tk.StringVar(value="8")
        self.short_text_penalty_var = tk.StringVar(value="10")
        self.score_column_var = tk.StringVar(value="match_score")
        self.base_score_column_var = tk.StringVar(value="match_base_score")
        self.match_text_column_var = tk.StringVar(value="match_text")
        self.details_column_var = tk.StringVar(value="match_details")
        self.right_index_column_var = tk.StringVar(value="match_right_index")
        self.copy_prefix_var = tk.StringVar(value="matched_")
        self.test_limit_var = tk.StringVar(value="0")
        self.remove_accents_var = tk.BooleanVar(value=True)
        self.lowercase_var = tk.BooleanVar(value=True)
        self.remove_punctuation_var = tk.BooleanVar(value=True)
        self.remove_stop_words_var = tk.BooleanVar(value=True)
        self.use_synonyms_var = tk.BooleanVar(value=True)
        self.ignore_same_row_var = tk.BooleanVar(value=True)
        self.write_base_score_var = tk.BooleanVar(value=True)
        self.write_details_var = tk.BooleanVar(value=True)
        self.write_right_index_var = tk.BooleanVar(value=True)
        self.include_reference_sheet_var = tk.BooleanVar(value=False)
        self.ai_enabled_var = tk.BooleanVar(value=False)
        self.ai_provider_var = tk.StringVar(value="Ollama lokalnie")
        self.ai_endpoint_var = tk.StringVar(value="http://localhost:11434")
        self.ai_model_var = tk.StringVar(value="llama3.1")
        self.ai_key_env_var = tk.StringVar(value="OPENAI_API_KEY")
        self.ai_top_n_var = tk.StringVar(value="5")
        self.status_var = tk.StringVar(value="Gotowe.")
        self.time_var = tk.StringVar(value="")

    def _build_layout(self) -> None:
        style = ttk.Style()
        if "clam" in style.theme_names():
            style.theme_use("clam")
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)

        main = ttk.Frame(self.root, padding=10)
        main.grid(row=0, column=0, sticky="nsew")
        main.columnconfigure(0, weight=1)
        main.rowconfigure(1, weight=1)

        self._build_file_bar(main)

        notebook = ttk.Notebook(main)
        notebook.grid(row=1, column=0, sticky="nsew", pady=(8, 8))
        self._build_columns_tab(notebook)
        self._build_scoring_tab(notebook)
        self._build_bonus_tab(notebook)
        self._build_output_tab(notebook)
        self._build_ai_tab(notebook)
        self._build_log_tab(notebook)

        self._build_action_bar(main)

    def _build_file_bar(self, parent: Any) -> None:
        frame = ttk.LabelFrame(parent, text="Plik i arkusze", padding=8)
        frame.grid(row=0, column=0, sticky="ew")
        frame.columnconfigure(1, weight=1)
        frame.columnconfigure(4, weight=1)

        ttk.Label(frame, text="Plik Excel:").grid(row=0, column=0, sticky="w")
        ttk.Entry(frame, textvariable=self.workbook_path_var).grid(row=0, column=1, columnspan=3, sticky="ew", padx=5)
        ttk.Button(frame, text="Wybierz...", command=self.browse_workbook).grid(row=0, column=4, sticky="e")

        ttk.Label(frame, text="Arkusz lewy/bazowy:").grid(row=1, column=0, sticky="w", pady=(6, 0))
        self.left_sheet_combo = ttk.Combobox(frame, textvariable=self.left_sheet_var, state="readonly", width=28)
        self.left_sheet_combo.grid(row=1, column=1, sticky="w", pady=(6, 0))
        self.left_sheet_combo.bind("<<ComboboxSelected>>", lambda _event: self.refresh_column_lists())

        ttk.Label(frame, text="Arkusz prawy/referencyjny:").grid(row=1, column=2, sticky="e", pady=(6, 0), padx=(12, 0))
        self.right_sheet_combo = ttk.Combobox(frame, textvariable=self.right_sheet_var, state="readonly", width=28)
        self.right_sheet_combo.grid(row=1, column=3, sticky="w", pady=(6, 0))
        self.right_sheet_combo.bind("<<ComboboxSelected>>", lambda _event: self.refresh_column_lists())

        ttk.Button(frame, text="Odśwież kolumny", command=self.refresh_column_lists).grid(row=1, column=4, sticky="e", pady=(6, 0))
        ttk.Label(frame, textvariable=self.file_info_var).grid(row=2, column=0, columnspan=5, sticky="w", pady=(6, 0))

    def _build_columns_tab(self, notebook: Any) -> None:
        tab = ttk.Frame(notebook, padding=10)
        notebook.add(tab, text="Kolumny")
        tab.columnconfigure(0, weight=1)
        tab.columnconfigure(1, weight=1)
        tab.columnconfigure(2, weight=1)

        left_frame = ttk.LabelFrame(tab, text="Lewa strona: kolumny bazowe do porównania", padding=8)
        right_frame = ttk.LabelFrame(tab, text="Prawa strona: kolumny referencyjne do porównania", padding=8)
        copy_frame = ttk.LabelFrame(tab, text="Kolumny z prawej strony do skopiowania do wyniku", padding=8)
        left_frame.grid(row=0, column=0, sticky="nsew", padx=(0, 6))
        right_frame.grid(row=0, column=1, sticky="nsew", padx=6)
        copy_frame.grid(row=0, column=2, sticky="nsew", padx=(6, 0))
        for frame in (left_frame, right_frame, copy_frame):
            frame.columnconfigure(0, weight=1)
            frame.rowconfigure(0, weight=1)

        self.left_columns_listbox = self._make_listbox(left_frame, height=14)
        self.right_columns_listbox = self._make_listbox(right_frame, height=14)
        self.copy_columns_listbox = self._make_listbox(copy_frame, height=14)

        ttk.Label(left_frame, text="Wagi w tej samej kolejności, np. 1, 0.7, 2. Puste = wszystkie 1.").grid(row=1, column=0, sticky="w", pady=(6, 0))
        ttk.Entry(left_frame, textvariable=self.left_weights_var).grid(row=2, column=0, sticky="ew")
        ttk.Label(right_frame, text="Wagi prawej strony. Jedna liczba oznacza tę samą wagę dla każdej kolumny.").grid(row=1, column=0, sticky="w", pady=(6, 0))
        ttk.Entry(right_frame, textvariable=self.right_weights_var).grid(row=2, column=0, sticky="ew")
        ttk.Label(copy_frame, text="Jeśli nic nie wybierzesz, zostanie zapisany tylko scalony tekst dopasowania.").grid(row=1, column=0, sticky="w", pady=(6, 0))

        hint = (
            "Zaznacz wiele pozycji klawiszem Ctrl/Shift. Lewa strona to rekord, dla którego szukasz najlepszego dopasowania. "
            "Prawa strona to kandydaci, z których wybieramy najlepszy wiersz."
        )
        ttk.Label(tab, text=hint, wraplength=1000).grid(row=1, column=0, columnspan=3, sticky="ew", pady=(10, 0))

    def _build_scoring_tab(self, notebook: Any) -> None:
        tab = ttk.Frame(notebook, padding=10)
        notebook.add(tab, text="Scoring")
        tab.columnconfigure(1, weight=1)
        tab.columnconfigure(3, weight=1)

        self._entry_row(tab, 0, "Algorytm:", self.scorer_var, values=list(SCORER_LABEL_TO_KEY))
        self._entry_row(tab, 1, "Tryb porównania kolumn:", self.pairing_var, values=list(PAIRING_LABEL_TO_KEY))
        self._entry_row(tab, 2, "Minimalny wynik końcowy 0-100:", self.min_score_var)
        self._entry_row(tab, 3, "Minimalny wynik bazowy fuzzy 0-100:", self.min_base_score_var)
        self._entry_row(tab, 4, "Minimalna długość pełnego słowa:", self.min_complete_word_len_var)

        checks = ttk.LabelFrame(tab, text="Normalizacja tekstu", padding=8)
        checks.grid(row=5, column=0, columnspan=4, sticky="ew", pady=(12, 0))
        for column in range(3):
            checks.columnconfigure(column, weight=1)
        ttk.Checkbutton(checks, text="Ignoruj wielkość liter", variable=self.lowercase_var).grid(row=0, column=0, sticky="w")
        ttk.Checkbutton(checks, text="Usuń polskie znaki", variable=self.remove_accents_var).grid(row=0, column=1, sticky="w")
        ttk.Checkbutton(checks, text="Usuń interpunkcję i tokenizuj", variable=self.remove_punctuation_var).grid(row=0, column=2, sticky="w")
        ttk.Checkbutton(checks, text="Pomijaj słowa stop", variable=self.remove_stop_words_var).grid(row=1, column=0, sticky="w", pady=(4, 0))
        ttk.Checkbutton(checks, text="Użyj synonimów", variable=self.use_synonyms_var).grid(row=1, column=1, sticky="w", pady=(4, 0))
        ttk.Checkbutton(checks, text="Nie porównuj wiersza z samym sobą", variable=self.ignore_same_row_var).grid(row=1, column=2, sticky="w", pady=(4, 0))

        text_frame = ttk.LabelFrame(tab, text="Słowa stop i synonimy", padding=8)
        text_frame.grid(row=6, column=0, columnspan=4, sticky="nsew", pady=(12, 0))
        text_frame.columnconfigure(0, weight=1)
        text_frame.columnconfigure(1, weight=1)
        ttk.Label(text_frame, text="Słowa stop: jedno na linię albo po przecinku.").grid(row=0, column=0, sticky="w")
        ttk.Label(text_frame, text="Synonimy: format słowo=zamiennik, np. sofa=kanapa.").grid(row=0, column=1, sticky="w")
        self.stop_words_text = scrolledtext.ScrolledText(text_frame, height=10, width=45, wrap=tk.WORD)
        self.synonyms_text = scrolledtext.ScrolledText(text_frame, height=10, width=45, wrap=tk.WORD)
        self.stop_words_text.grid(row=1, column=0, sticky="nsew", padx=(0, 6))
        self.synonyms_text.grid(row=1, column=1, sticky="nsew", padx=(6, 0))
        self.stop_words_text.insert("1.0", DEFAULT_STOP_WORDS_TEXT)
        self.synonyms_text.insert("1.0", DEFAULT_SYNONYMS_TEXT)

        availability = "RapidFuzz: dostępny" if RAPIDFUZZ_AVAILABLE else "RapidFuzz: brak, używany jest wolniejszy fallback difflib"
        ttk.Label(tab, text=availability).grid(row=7, column=0, columnspan=4, sticky="w", pady=(8, 0))

    def _build_bonus_tab(self, notebook: Any) -> None:
        tab = ttk.Frame(notebook, padding=10)
        notebook.add(tab, text="Bonusy i kary")
        for column in range(4):
            tab.columnconfigure(column, weight=1)

        description = (
            "Wszystkie wartości są punktami dodawanymi do wyniku 0-100 albo odejmowanymi od niego. "
            "Wynik końcowy jest zawsze obcinany do zakresu 0-100, więc bonusy nie tworzą fałszywych wartości powyżej 100%."
        )
        ttk.Label(tab, text=description, wraplength=1000).grid(row=0, column=0, columnspan=4, sticky="ew")

        entries = [
            ("Bonus za wspólne słowo:", self.word_overlap_bonus_var),
            ("Limit bonusu za wspólne słowa:", self.max_word_overlap_bonus_var),
            ("Bonus za kompletne słowo:", self.complete_word_bonus_var),
            ("Limit bonusu za kompletne słowa:", self.max_complete_word_bonus_var),
            ("Próg pokrycia tokenów 0-1:", self.coverage_threshold_var),
            ("Bonus za pokrycie tokenów:", self.coverage_bonus_var),
            ("Bonus za identyczny tekst:", self.exact_match_bonus_var),
            ("Bonus za zgodną liczbę/wymiar:", self.number_match_bonus_var),
            ("Limit bonusu za liczby:", self.max_number_bonus_var),
            ("Kara za sprzeczne liczby:", self.number_mismatch_penalty_var),
            ("Limit kary za liczby:", self.max_number_mismatch_penalty_var),
            ("Bonus za zgodny kod/SKU:", self.code_match_bonus_var),
            ("Limit bonusu za kod/SKU:", self.max_code_match_bonus_var),
            ("Kara za dużą różnicę długości:", self.length_difference_penalty_var),
            ("Kara za bardzo krótki tekst:", self.short_text_penalty_var),
        ]
        for index, (label, variable) in enumerate(entries, start=1):
            row = index
            column = 0 if index <= 8 else 2
            local_row = row if index <= 8 else index - 8
            ttk.Label(tab, text=label).grid(row=local_row, column=column, sticky="e", padx=(0, 6), pady=3)
            ttk.Entry(tab, textvariable=variable, width=16).grid(row=local_row, column=column + 1, sticky="w", pady=3)

    def _build_output_tab(self, notebook: Any) -> None:
        tab = ttk.Frame(notebook, padding=10)
        notebook.add(tab, text="Wynik")
        tab.columnconfigure(1, weight=1)

        ttk.Label(tab, text="Plik wynikowy:").grid(row=0, column=0, sticky="e", padx=(0, 6))
        ttk.Entry(tab, textvariable=self.output_path_var).grid(row=0, column=1, sticky="ew")
        ttk.Button(tab, text="Wybierz...", command=self.browse_output).grid(row=0, column=2, padx=(6, 0))

        rows = [
            ("Kolumna z wynikiem końcowym:", self.score_column_var),
            ("Kolumna z bazowym fuzzy score:", self.base_score_column_var),
            ("Kolumna z tekstem najlepszego dopasowania:", self.match_text_column_var),
            ("Kolumna z opisem decyzji:", self.details_column_var),
            ("Kolumna z indeksem wiersza po prawej:", self.right_index_column_var),
            ("Prefiks dla kopiowanych kolumn:", self.copy_prefix_var),
            ("Limit testowy wierszy (0 = wszystkie):", self.test_limit_var),
        ]
        for row, (label, variable) in enumerate(rows, start=1):
            ttk.Label(tab, text=label).grid(row=row, column=0, sticky="e", padx=(0, 6), pady=3)
            ttk.Entry(tab, textvariable=variable).grid(row=row, column=1, sticky="ew", pady=3)

        check_frame = ttk.LabelFrame(tab, text="Dodatkowe dane diagnostyczne", padding=8)
        check_frame.grid(row=8, column=0, columnspan=3, sticky="ew", pady=(12, 0))
        ttk.Checkbutton(check_frame, text="Zapisz bazowy fuzzy score", variable=self.write_base_score_var).grid(row=0, column=0, sticky="w")
        ttk.Checkbutton(check_frame, text="Zapisz opis bonusów/kar", variable=self.write_details_var).grid(row=0, column=1, sticky="w", padx=(12, 0))
        ttk.Checkbutton(check_frame, text="Zapisz indeks wiersza po prawej", variable=self.write_right_index_var).grid(row=0, column=2, sticky="w", padx=(12, 0))
        ttk.Checkbutton(check_frame, text="Dołącz arkusz referencyjny w pliku wynikowym", variable=self.include_reference_sheet_var).grid(row=1, column=0, columnspan=3, sticky="w", pady=(6, 0))

    def _build_ai_tab(self, notebook: Any) -> None:
        tab = ttk.Frame(notebook, padding=10)
        notebook.add(tab, text="AI - przyszłość")
        tab.columnconfigure(1, weight=1)
        info = (
            "Ta sekcja jest przygotowana pod przyszły reranking najlepszych kandydatów przez lokalny LLM z Ollama "
            "albo API, np. GPT. Obecna wersja nie wykonuje wywołań sieciowych i nie wysyła danych poza komputer."
        )
        ttk.Label(tab, text=info, wraplength=1000).grid(row=0, column=0, columnspan=3, sticky="ew")
        ttk.Checkbutton(tab, text="W przyszłości użyj AI jako dodatkowego rerankera top N kandydatów", variable=self.ai_enabled_var).grid(row=1, column=0, columnspan=3, sticky="w", pady=(12, 0))
        self._entry_row(tab, 2, "Provider:", self.ai_provider_var, values=["Ollama lokalnie", "OpenAI API", "Inny endpoint"])
        self._entry_row(tab, 3, "Endpoint / URL:", self.ai_endpoint_var)
        self._entry_row(tab, 4, "Model:", self.ai_model_var)
        self._entry_row(tab, 5, "Zmienna środowiskowa z kluczem API:", self.ai_key_env_var)
        self._entry_row(tab, 6, "Top N kandydatów do rerankingu:", self.ai_top_n_var)

    def _build_log_tab(self, notebook: Any) -> None:
        tab = ttk.Frame(notebook, padding=10)
        notebook.add(tab, text="Podgląd / Log")
        tab.columnconfigure(0, weight=1)
        tab.rowconfigure(4, weight=1)

        self.progress = ttk.Progressbar(tab, orient="horizontal", mode="determinate")
        self.progress.grid(row=0, column=0, sticky="ew")
        ttk.Label(tab, textvariable=self.status_var).grid(row=1, column=0, sticky="w", pady=(6, 0))
        ttk.Label(tab, textvariable=self.time_var).grid(row=2, column=0, sticky="w")

        ttk.Label(tab, text="Podgląd ostatniego dopasowania:").grid(row=3, column=0, sticky="w", pady=(10, 0))
        self.preview_text = scrolledtext.ScrolledText(tab, height=9, wrap=tk.WORD)
        self.preview_text.grid(row=4, column=0, sticky="nsew")
        ttk.Label(tab, text="Log:").grid(row=5, column=0, sticky="w", pady=(10, 0))
        self.log_text = scrolledtext.ScrolledText(tab, height=8, wrap=tk.WORD)
        self.log_text.grid(row=6, column=0, sticky="nsew")

    def _build_action_bar(self, parent: Any) -> None:
        frame = ttk.Frame(parent)
        frame.grid(row=2, column=0, sticky="ew")
        frame.columnconfigure(6, weight=1)
        self.start_button = ttk.Button(frame, text="Start", command=lambda: self.start_processing(test_only=False))
        self.test_button = ttk.Button(frame, text="Testuj na pierwszych N", command=lambda: self.start_processing(test_only=True))
        self.stop_button = ttk.Button(frame, text="Zatrzymaj", command=self.stop_processing, state=tk.DISABLED)
        self.save_preset_button = ttk.Button(frame, text="Zapisz preset", command=self.save_preset)
        self.load_preset_button = ttk.Button(frame, text="Wczytaj preset", command=self.load_preset)
        self.start_button.grid(row=0, column=0, padx=(0, 6))
        self.test_button.grid(row=0, column=1, padx=6)
        self.stop_button.grid(row=0, column=2, padx=6)
        self.save_preset_button.grid(row=0, column=3, padx=6)
        self.load_preset_button.grid(row=0, column=4, padx=6)

    def _entry_row(self, parent: Any, row: int, label: str, variable: Any, values: list[str] | None = None) -> None:
        ttk.Label(parent, text=label).grid(row=row, column=0, sticky="e", padx=(0, 6), pady=3)
        if values:
            widget = ttk.Combobox(parent, textvariable=variable, values=values, state="readonly")
        else:
            widget = ttk.Entry(parent, textvariable=variable)
        widget.grid(row=row, column=1, columnspan=3, sticky="ew", pady=3)

    def _make_listbox(self, parent: Any, height: int = 10) -> Any:
        frame = ttk.Frame(parent)
        frame.grid(row=0, column=0, sticky="nsew")
        frame.columnconfigure(0, weight=1)
        frame.rowconfigure(0, weight=1)
        listbox = tk.Listbox(frame, selectmode=tk.MULTIPLE, exportselection=False, height=height)
        scrollbar = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=listbox.yview)
        listbox.configure(yscrollcommand=scrollbar.set)
        listbox.grid(row=0, column=0, sticky="nsew")
        scrollbar.grid(row=0, column=1, sticky="ns")
        return listbox

    def browse_workbook(self) -> None:
        path = filedialog.askopenfilename(filetypes=[("Excel files", "*.xlsx *.xlsm"), ("All files", "*.*")])
        if not path:
            return
        self.workbook_path_var.set(path)
        self.output_path_var.set(default_output_path(path))
        self.load_workbook_metadata()

    def browse_output(self) -> None:
        initial = self.output_path_var.get() or default_output_path(self.workbook_path_var.get() or "wynik.xlsx")
        path = filedialog.asksaveasfilename(
            defaultextension=".xlsx",
            initialfile=Path(initial).name,
            initialdir=str(Path(initial).parent),
            filetypes=[("Excel files", "*.xlsx")],
        )
        if path:
            self.output_path_var.set(path)

    def load_workbook_metadata(self) -> None:
        path = self.workbook_path_var.get().strip()
        if not path:
            return
        if not os.path.exists(path):
            messagebox.showerror("Błąd", f"Plik nie istnieje:\n{path}")
            return
        try:
            pd = import_pandas()
            excel = pd.ExcelFile(path)
            sheet_names = excel.sheet_names
        except Exception as exc:
            messagebox.showerror("Błąd wczytywania", str(exc))
            return
        self.left_sheet_combo["values"] = sheet_names
        self.right_sheet_combo["values"] = sheet_names
        if sheet_names:
            self.left_sheet_var.set(sheet_names[0])
            self.right_sheet_var.set(sheet_names[0])
        self.refresh_column_lists()

    def refresh_column_lists(self) -> None:
        path = self.workbook_path_var.get().strip()
        left_sheet = self.left_sheet_var.get()
        right_sheet = self.right_sheet_var.get()
        if not path or not left_sheet or not right_sheet:
            return
        try:
            pd = import_pandas()
            left_cols = list(pd.read_excel(path, sheet_name=left_sheet, nrows=0).columns)
            right_cols = list(pd.read_excel(path, sheet_name=right_sheet, nrows=0).columns)
            left_count = len(pd.read_excel(path, sheet_name=left_sheet, usecols=[0])) if left_cols else 0
            right_count = len(pd.read_excel(path, sheet_name=right_sheet, usecols=[0])) if right_cols else 0
        except Exception as exc:
            messagebox.showerror("Błąd kolumn", str(exc))
            return
        self._set_listbox_values(self.left_columns_listbox, left_cols, default_count=min(2, len(left_cols)))
        self._set_listbox_values(self.right_columns_listbox, right_cols, default_count=min(3, len(right_cols)))
        self._set_listbox_values(self.copy_columns_listbox, right_cols, default_count=0)
        self.file_info_var.set(
            f"Lewy arkusz: {left_sheet} ({left_count} wierszy, {len(left_cols)} kolumn). "
            f"Prawy arkusz: {right_sheet} ({right_count} wierszy, {len(right_cols)} kolumn)."
        )

    def _set_listbox_values(self, listbox: Any, values: Sequence[str], default_count: int = 0) -> None:
        previous = set(selected_listbox_items(listbox))
        listbox.delete(0, tk.END)
        for value in values:
            listbox.insert(tk.END, value)
        selected_any = False
        for index, value in enumerate(values):
            if value in previous:
                listbox.selection_set(index)
                selected_any = True
        if not selected_any and default_count:
            listbox.selection_set(0, default_count - 1)

    def collect_settings(self, test_only: bool = False) -> RuntimeSettings:
        workbook_path = self.workbook_path_var.get().strip()
        if not workbook_path:
            raise ValueError("Wybierz plik Excel.")
        output_path = self.output_path_var.get().strip() or default_output_path(workbook_path)
        left_columns = selected_listbox_items(self.left_columns_listbox)
        right_columns = selected_listbox_items(self.right_columns_listbox)
        copy_columns = selected_listbox_items(self.copy_columns_listbox)
        if not left_columns:
            raise ValueError("Wybierz przynajmniej jedną kolumnę po lewej stronie.")
        if not right_columns:
            raise ValueError("Wybierz przynajmniej jedną kolumnę po prawej stronie.")

        config = MatchConfig(
            scorer=SCORER_LABEL_TO_KEY.get(self.scorer_var.get(), "mixed"),
            pairing_mode=PAIRING_LABEL_TO_KEY.get(self.pairing_var.get(), "best_right"),
            min_score=parse_float(self.min_score_var.get(), "Minimalny wynik końcowy", 0.0, 100.0),
            min_base_score=parse_float(self.min_base_score_var.get(), "Minimalny wynik bazowy", 0.0, 100.0),
            remove_accents=self.remove_accents_var.get(),
            lowercase=self.lowercase_var.get(),
            remove_punctuation=self.remove_punctuation_var.get(),
            remove_stop_words=self.remove_stop_words_var.get(),
            use_synonyms=self.use_synonyms_var.get(),
            ignore_same_row=self.ignore_same_row_var.get(),
            min_complete_word_len=parse_int(self.min_complete_word_len_var.get(), "Minimalna długość pełnego słowa", 1, 50),
            word_overlap_bonus=parse_float(self.word_overlap_bonus_var.get(), "Bonus za wspólne słowo", 0.0, 100.0),
            max_word_overlap_bonus=parse_float(self.max_word_overlap_bonus_var.get(), "Limit bonusu za wspólne słowa", 0.0, 100.0),
            complete_word_bonus=parse_float(self.complete_word_bonus_var.get(), "Bonus za kompletne słowo", 0.0, 100.0),
            max_complete_word_bonus=parse_float(self.max_complete_word_bonus_var.get(), "Limit bonusu za kompletne słowa", 0.0, 100.0),
            coverage_threshold=parse_float(self.coverage_threshold_var.get(), "Próg pokrycia tokenów", 0.0, 1.0),
            coverage_bonus=parse_float(self.coverage_bonus_var.get(), "Bonus za pokrycie tokenów", 0.0, 100.0),
            exact_match_bonus=parse_float(self.exact_match_bonus_var.get(), "Bonus za identyczny tekst", 0.0, 100.0),
            number_match_bonus=parse_float(self.number_match_bonus_var.get(), "Bonus za zgodną liczbę", 0.0, 100.0),
            max_number_bonus=parse_float(self.max_number_bonus_var.get(), "Limit bonusu za liczby", 0.0, 100.0),
            number_mismatch_penalty=parse_float(self.number_mismatch_penalty_var.get(), "Kara za sprzeczne liczby", 0.0, 100.0),
            max_number_mismatch_penalty=parse_float(self.max_number_mismatch_penalty_var.get(), "Limit kary za liczby", 0.0, 100.0),
            code_match_bonus=parse_float(self.code_match_bonus_var.get(), "Bonus za kod/SKU", 0.0, 100.0),
            max_code_match_bonus=parse_float(self.max_code_match_bonus_var.get(), "Limit bonusu za kod/SKU", 0.0, 100.0),
            length_difference_penalty=parse_float(self.length_difference_penalty_var.get(), "Kara za różnicę długości", 0.0, 100.0),
            short_text_penalty=parse_float(self.short_text_penalty_var.get(), "Kara za bardzo krótki tekst", 0.0, 100.0),
            stop_words=parse_stop_words(self.stop_words_text.get("1.0", tk.END)),
            synonyms=parse_synonyms(self.synonyms_text.get("1.0", tk.END)),
        )

        limit = parse_int(self.test_limit_var.get(), "Limit testowy", 0, 1_000_000)
        if test_only and limit <= 0:
            limit = 20
        return RuntimeSettings(
            workbook_path=workbook_path,
            output_path=output_path,
            left_sheet=self.left_sheet_var.get(),
            right_sheet=self.right_sheet_var.get(),
            left_columns=left_columns,
            right_columns=right_columns,
            copy_columns=copy_columns,
            left_weights=parse_weights(self.left_weights_var.get(), len(left_columns), "Wagi lewej strony"),
            right_weights=parse_weights(self.right_weights_var.get(), len(right_columns), "Wagi prawej strony"),
            score_column=self.score_column_var.get().strip() or "match_score",
            match_text_column=self.match_text_column_var.get().strip() or "match_text",
            base_score_column=self.base_score_column_var.get().strip() or "match_base_score",
            details_column=self.details_column_var.get().strip() or "match_details",
            right_index_column=self.right_index_column_var.get().strip() or "match_right_index",
            copy_prefix=self.copy_prefix_var.get(),
            write_base_score=self.write_base_score_var.get(),
            write_details=self.write_details_var.get(),
            write_right_index=self.write_right_index_var.get(),
            include_reference_sheet=self.include_reference_sheet_var.get(),
            test_limit=limit,
            config=config,
            ai_config={
                "enabled_future_placeholder": self.ai_enabled_var.get(),
                "provider": self.ai_provider_var.get(),
                "endpoint": self.ai_endpoint_var.get(),
                "model": self.ai_model_var.get(),
                "api_key_env": self.ai_key_env_var.get(),
                "top_n": parse_int(self.ai_top_n_var.get(), "Top N AI", 1, 100),
            },
        )

    def start_processing(self, test_only: bool) -> None:
        if self.worker_thread and self.worker_thread.is_alive():
            messagebox.showwarning("Praca w toku", "Proces dopasowania już działa.")
            return
        try:
            settings = self.collect_settings(test_only=test_only)
        except ValueError as exc:
            messagebox.showerror("Nieprawidłowa konfiguracja", str(exc))
            return
        self.stop_event.clear()
        self._set_running_state(True)
        self.status_var.set("Start dopasowania...")
        self.progress["value"] = 0
        self.preview_text.delete("1.0", tk.END)
        self._log(f"Start: {settings.left_sheet} -> {settings.right_sheet}; output: {settings.output_path}")
        self.worker_thread = threading.Thread(target=self._process_workbook, args=(settings,), daemon=True)
        self.worker_thread.start()

    def stop_processing(self) -> None:
        self.stop_event.set()
        self.status_var.set("Zatrzymywanie po bieżącym wierszu...")

    def _set_running_state(self, running: bool) -> None:
        state = tk.DISABLED if running else tk.NORMAL
        self.start_button.configure(state=state)
        self.test_button.configure(state=state)
        self.save_preset_button.configure(state=state)
        self.load_preset_button.configure(state=state)
        self.stop_button.configure(state=tk.NORMAL if running else tk.DISABLED)

    def _process_workbook(self, settings: RuntimeSettings) -> None:
        try:
            pd = import_pandas()
            left_df = pd.read_excel(settings.workbook_path, sheet_name=settings.left_sheet)
            right_df = pd.read_excel(settings.workbook_path, sheet_name=settings.right_sheet)
            if settings.test_limit > 0:
                left_df = left_df.head(settings.test_limit).copy()

            normalizer = TextNormalizer(settings.config)
            right_rows = list(right_df.iterrows())
            total = len(left_df)
            start_time = time.time()
            self.status_queue.put({"type": "log", "text": f"Wczytano {total} wierszy po lewej i {len(right_rows)} kandydatów po prawej."})

            output_columns = [settings.score_column, settings.match_text_column]
            if settings.write_base_score:
                output_columns.append(settings.base_score_column)
            if settings.write_details:
                output_columns.append(settings.details_column)
            if settings.write_right_index:
                output_columns.append(settings.right_index_column)
            output_columns.extend(f"{settings.copy_prefix}{column}" for column in settings.copy_columns)
            for column in output_columns:
                if column and column not in left_df.columns:
                    left_df[column] = ""

            for position, (left_index, left_row) in enumerate(left_df.iterrows(), start=1):
                if self.stop_event.is_set():
                    self.status_queue.put({"type": "log", "text": "Przerwano przez użytkownika. Zapisywany jest częściowy wynik."})
                    break

                left_preview = joined_text(normalized_values(left_row, settings.left_columns, normalizer))
                best = None if not left_preview else find_best_match(
                    left_index,
                    left_row,
                    right_rows,
                    settings.left_columns,
                    settings.right_columns,
                    settings.left_weights,
                    settings.right_weights,
                    settings.config,
                    normalizer,
                )
                accepted = (
                    best is not None
                    and best.score.final_score >= settings.config.min_score
                    and best.score.base_score >= settings.config.min_base_score
                )
                self._write_result(left_df, left_index, best, accepted, settings)

                elapsed = time.time() - start_time
                remaining = (elapsed / position) * (total - position) if position else 0.0
                preview = self._preview_text(left_row, best, accepted, settings)
                self.status_queue.put(
                    {
                        "type": "progress",
                        "position": position,
                        "total": total,
                        "elapsed": elapsed,
                        "remaining": remaining,
                        "preview": preview,
                    }
                )

            with pd.ExcelWriter(settings.output_path, engine="openpyxl") as writer:
                left_df.to_excel(writer, sheet_name=safe_sheet_name(f"{settings.left_sheet}_wynik"), index=False)
                if settings.include_reference_sheet:
                    right_df.to_excel(writer, sheet_name=safe_sheet_name(f"{settings.right_sheet}_ref"), index=False)

            self.status_queue.put({"type": "done", "path": settings.output_path})
        except Exception as exc:
            self.status_queue.put({"type": "error", "text": str(exc)})

    def _write_result(
        self,
        left_df: Any,
        left_index: Any,
        best: MatchCandidate | None,
        accepted: bool,
        settings: RuntimeSettings,
    ) -> None:
        if not best:
            left_df.at[left_index, settings.score_column] = 0.0
            left_df.at[left_index, settings.match_text_column] = ""
            if settings.write_details:
                left_df.at[left_index, settings.details_column] = "brak kandydatów / pusty tekst"
            return

        score = best.score
        left_df.at[left_index, settings.score_column] = round(score.final_score if accepted else 0.0, 2)
        left_df.at[left_index, settings.match_text_column] = score.right_text if accepted else ""
        if settings.write_base_score:
            left_df.at[left_index, settings.base_score_column] = round(score.base_score, 2)
        if settings.write_details:
            decision = "zaakceptowane" if accepted else "poniżej progu"
            left_df.at[left_index, settings.details_column] = f"{decision}; prawy_index={best.right_index}; {score.details()}"
        if settings.write_right_index:
            left_df.at[left_index, settings.right_index_column] = best.right_index if accepted else ""
        for column in settings.copy_columns:
            target = f"{settings.copy_prefix}{column}"
            left_df.at[left_index, target] = row_value(best.right_row, column) if accepted else ""

    def _preview_text(
        self,
        left_row: Any,
        best: MatchCandidate | None,
        accepted: bool,
        settings: RuntimeSettings,
    ) -> str:
        left_raw = " | ".join(safe_text(row_value(left_row, column)) for column in settings.left_columns)
        if not best:
            return f"Lewa strona:\n{left_raw}\n\nBrak kandydata."
        decision = "zaakceptowane" if accepted else "poniżej progu"
        return (
            f"Lewa strona:\n{left_raw}\n\n"
            f"Prawa strona:\n{best.score.right_text}\n\n"
            f"Wynik: {best.score.final_score:.2f} | bazowy: {best.score.base_score:.2f} | decyzja: {decision}\n"
            f"Bonusy: {best.score.bonus_total:.2f} | Kary: {best.score.penalty_total:.2f}\n"
            f"Szczegóły: {best.score.details()}"
        )

    def _poll_queue(self) -> None:
        try:
            while True:
                message = self.status_queue.get_nowait()
                kind = message.get("type")
                if kind == "progress":
                    total = max(1, message["total"])
                    position = message["position"]
                    self.progress["maximum"] = total
                    self.progress["value"] = position
                    percent = position / total * 100
                    self.status_var.set(f"{position}/{total} ({percent:.1f}%)")
                    self.time_var.set(f"Czas: {message['elapsed']:.1f}s | Pozostało: {message['remaining']:.1f}s")
                    self.preview_text.delete("1.0", tk.END)
                    self.preview_text.insert(tk.END, message["preview"])
                elif kind == "log":
                    self._log(message["text"])
                elif kind == "done":
                    self._set_running_state(False)
                    self.status_var.set("Zakończono.")
                    self._log(f"Zapisano: {message['path']}")
                    messagebox.showinfo("Zakończono", f"Zapisano wynik do:\n{message['path']}")
                elif kind == "error":
                    self._set_running_state(False)
                    self.status_var.set("Błąd.")
                    self._log(f"Błąd: {message['text']}")
                    messagebox.showerror("Błąd", message["text"])
        except queue.Empty:
            pass
        self.root.after(100, self._poll_queue)

    def _log(self, text: str) -> None:
        timestamp = time.strftime("%H:%M:%S")
        self.log_text.insert(tk.END, f"[{timestamp}] {text}\n")
        self.log_text.see(tk.END)

    def collect_preset_data(self) -> dict[str, Any]:
        return {
            "workbook_path": self.workbook_path_var.get(),
            "output_path": self.output_path_var.get(),
            "left_sheet": self.left_sheet_var.get(),
            "right_sheet": self.right_sheet_var.get(),
            "left_columns": selected_listbox_items(self.left_columns_listbox),
            "right_columns": selected_listbox_items(self.right_columns_listbox),
            "copy_columns": selected_listbox_items(self.copy_columns_listbox),
            "left_weights": self.left_weights_var.get(),
            "right_weights": self.right_weights_var.get(),
            "scorer": self.scorer_var.get(),
            "pairing": self.pairing_var.get(),
            "min_score": self.min_score_var.get(),
            "min_base_score": self.min_base_score_var.get(),
            "test_limit": self.test_limit_var.get(),
            "normalization": {
                "remove_accents": self.remove_accents_var.get(),
                "lowercase": self.lowercase_var.get(),
                "remove_punctuation": self.remove_punctuation_var.get(),
                "remove_stop_words": self.remove_stop_words_var.get(),
                "use_synonyms": self.use_synonyms_var.get(),
                "ignore_same_row": self.ignore_same_row_var.get(),
                "min_complete_word_len": self.min_complete_word_len_var.get(),
            },
            "bonuses_and_penalties": {
                "word_overlap_bonus": self.word_overlap_bonus_var.get(),
                "max_word_overlap_bonus": self.max_word_overlap_bonus_var.get(),
                "complete_word_bonus": self.complete_word_bonus_var.get(),
                "max_complete_word_bonus": self.max_complete_word_bonus_var.get(),
                "coverage_threshold": self.coverage_threshold_var.get(),
                "coverage_bonus": self.coverage_bonus_var.get(),
                "exact_match_bonus": self.exact_match_bonus_var.get(),
                "number_match_bonus": self.number_match_bonus_var.get(),
                "max_number_bonus": self.max_number_bonus_var.get(),
                "number_mismatch_penalty": self.number_mismatch_penalty_var.get(),
                "max_number_mismatch_penalty": self.max_number_mismatch_penalty_var.get(),
                "code_match_bonus": self.code_match_bonus_var.get(),
                "max_code_match_bonus": self.max_code_match_bonus_var.get(),
                "length_difference_penalty": self.length_difference_penalty_var.get(),
                "short_text_penalty": self.short_text_penalty_var.get(),
            },
            "diagnostics": {
                "write_base_score": self.write_base_score_var.get(),
                "write_details": self.write_details_var.get(),
                "write_right_index": self.write_right_index_var.get(),
                "include_reference_sheet": self.include_reference_sheet_var.get(),
            },
            "stop_words": self.stop_words_text.get("1.0", tk.END),
            "synonyms": self.synonyms_text.get("1.0", tk.END),
            "output": {
                "score_column": self.score_column_var.get(),
                "base_score_column": self.base_score_column_var.get(),
                "match_text_column": self.match_text_column_var.get(),
                "details_column": self.details_column_var.get(),
                "right_index_column": self.right_index_column_var.get(),
                "copy_prefix": self.copy_prefix_var.get(),
            },
            "ai_placeholder": {
                "enabled": self.ai_enabled_var.get(),
                "provider": self.ai_provider_var.get(),
                "endpoint": self.ai_endpoint_var.get(),
                "model": self.ai_model_var.get(),
                "api_key_env": self.ai_key_env_var.get(),
                "top_n": self.ai_top_n_var.get(),
            },
        }

    def save_preset(self) -> None:
        path = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON", "*.json")])
        if not path:
            return
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(self.collect_preset_data(), handle, indent=2, ensure_ascii=False)
        self._log(f"Zapisano preset: {path}")

    def load_preset(self) -> None:
        path = filedialog.askopenfilename(filetypes=[("JSON", "*.json"), ("All files", "*.*")])
        if not path:
            return
        with open(path, "r", encoding="utf-8") as handle:
            data = json.load(handle)

        self.workbook_path_var.set(data.get("workbook_path", ""))
        self.output_path_var.set(data.get("output_path", ""))
        self.scorer_var.set(data.get("scorer", self.scorer_var.get()))
        self.pairing_var.set(data.get("pairing", self.pairing_var.get()))
        self.min_score_var.set(data.get("min_score", self.min_score_var.get()))
        self.min_base_score_var.set(data.get("min_base_score", self.min_base_score_var.get()))
        self.test_limit_var.set(data.get("test_limit", self.test_limit_var.get()))
        self.left_weights_var.set(data.get("left_weights", ""))
        self.right_weights_var.set(data.get("right_weights", ""))

        normalization = data.get("normalization", {})
        self.remove_accents_var.set(normalization.get("remove_accents", self.remove_accents_var.get()))
        self.lowercase_var.set(normalization.get("lowercase", self.lowercase_var.get()))
        self.remove_punctuation_var.set(normalization.get("remove_punctuation", self.remove_punctuation_var.get()))
        self.remove_stop_words_var.set(normalization.get("remove_stop_words", self.remove_stop_words_var.get()))
        self.use_synonyms_var.set(normalization.get("use_synonyms", self.use_synonyms_var.get()))
        self.ignore_same_row_var.set(normalization.get("ignore_same_row", self.ignore_same_row_var.get()))
        self.min_complete_word_len_var.set(normalization.get("min_complete_word_len", self.min_complete_word_len_var.get()))

        bonus_data = data.get("bonuses_and_penalties", {})
        self.word_overlap_bonus_var.set(bonus_data.get("word_overlap_bonus", self.word_overlap_bonus_var.get()))
        self.max_word_overlap_bonus_var.set(bonus_data.get("max_word_overlap_bonus", self.max_word_overlap_bonus_var.get()))
        self.complete_word_bonus_var.set(bonus_data.get("complete_word_bonus", self.complete_word_bonus_var.get()))
        self.max_complete_word_bonus_var.set(bonus_data.get("max_complete_word_bonus", self.max_complete_word_bonus_var.get()))
        self.coverage_threshold_var.set(bonus_data.get("coverage_threshold", self.coverage_threshold_var.get()))
        self.coverage_bonus_var.set(bonus_data.get("coverage_bonus", self.coverage_bonus_var.get()))
        self.exact_match_bonus_var.set(bonus_data.get("exact_match_bonus", self.exact_match_bonus_var.get()))
        self.number_match_bonus_var.set(bonus_data.get("number_match_bonus", self.number_match_bonus_var.get()))
        self.max_number_bonus_var.set(bonus_data.get("max_number_bonus", self.max_number_bonus_var.get()))
        self.number_mismatch_penalty_var.set(bonus_data.get("number_mismatch_penalty", self.number_mismatch_penalty_var.get()))
        self.max_number_mismatch_penalty_var.set(bonus_data.get("max_number_mismatch_penalty", self.max_number_mismatch_penalty_var.get()))
        self.code_match_bonus_var.set(bonus_data.get("code_match_bonus", self.code_match_bonus_var.get()))
        self.max_code_match_bonus_var.set(bonus_data.get("max_code_match_bonus", self.max_code_match_bonus_var.get()))
        self.length_difference_penalty_var.set(bonus_data.get("length_difference_penalty", self.length_difference_penalty_var.get()))
        self.short_text_penalty_var.set(bonus_data.get("short_text_penalty", self.short_text_penalty_var.get()))

        diagnostics = data.get("diagnostics", {})
        self.write_base_score_var.set(diagnostics.get("write_base_score", self.write_base_score_var.get()))
        self.write_details_var.set(diagnostics.get("write_details", self.write_details_var.get()))
        self.write_right_index_var.set(diagnostics.get("write_right_index", self.write_right_index_var.get()))
        self.include_reference_sheet_var.set(diagnostics.get("include_reference_sheet", self.include_reference_sheet_var.get()))

        self.stop_words_text.delete("1.0", tk.END)
        self.stop_words_text.insert("1.0", data.get("stop_words", DEFAULT_STOP_WORDS_TEXT))
        self.synonyms_text.delete("1.0", tk.END)
        self.synonyms_text.insert("1.0", data.get("synonyms", DEFAULT_SYNONYMS_TEXT))

        output = data.get("output", {})
        self.score_column_var.set(output.get("score_column", self.score_column_var.get()))
        self.base_score_column_var.set(output.get("base_score_column", self.base_score_column_var.get()))
        self.match_text_column_var.set(output.get("match_text_column", self.match_text_column_var.get()))
        self.details_column_var.set(output.get("details_column", self.details_column_var.get()))
        self.right_index_column_var.set(output.get("right_index_column", self.right_index_column_var.get()))
        self.copy_prefix_var.set(output.get("copy_prefix", self.copy_prefix_var.get()))

        ai = data.get("ai_placeholder", {})
        self.ai_enabled_var.set(ai.get("enabled", self.ai_enabled_var.get()))
        self.ai_provider_var.set(ai.get("provider", self.ai_provider_var.get()))
        self.ai_endpoint_var.set(ai.get("endpoint", self.ai_endpoint_var.get()))
        self.ai_model_var.set(ai.get("model", self.ai_model_var.get()))
        self.ai_key_env_var.set(ai.get("api_key_env", self.ai_key_env_var.get()))
        self.ai_top_n_var.set(ai.get("top_n", self.ai_top_n_var.get()))

        if self.workbook_path_var.get() and os.path.exists(self.workbook_path_var.get()):
            self.load_workbook_metadata()
            self.left_sheet_var.set(data.get("left_sheet", self.left_sheet_var.get()))
            self.right_sheet_var.set(data.get("right_sheet", self.right_sheet_var.get()))
            self.refresh_column_lists()
            self._select_listbox_values(self.left_columns_listbox, data.get("left_columns", []))
            self._select_listbox_values(self.right_columns_listbox, data.get("right_columns", []))
            self._select_listbox_values(self.copy_columns_listbox, data.get("copy_columns", []))
        self._log(f"Wczytano preset: {path}")

    def _select_listbox_values(self, listbox: Any, values: Sequence[str]) -> None:
        wanted = set(values)
        listbox.selection_clear(0, tk.END)
        for index in range(listbox.size()):
            if listbox.get(index) in wanted:
                listbox.selection_set(index)


def run_gui() -> int:
    if tk is None:
        print("Brakuje tkinter. W Ubuntu/WSL zainstaluj: sudo apt install python3-tk", file=sys.stderr)
        return 1
    root = tk.Tk()
    ExcelFuzzyMatcherApp(root)
    root.mainloop()
    return 0


def run_self_test() -> int:
    config = MatchConfig(
        scorer="mixed",
        pairing_mode="best_right",
        stop_words=parse_stop_words(DEFAULT_STOP_WORDS_TEXT),
        synonyms=parse_synonyms(DEFAULT_SYNONYMS_TEXT),
    )
    normalizer = TextNormalizer(config)
    left = {"nazwa": "Sofa czarna 200 cm"}
    right = {"opis": "Kanapa black 200 cm"}
    result = score_rows(left, right, ["nazwa"], ["opis"], [1.0], [1.0], config, normalizer)
    if result.final_score < 80:
        raise AssertionError(f"Self-test score too low: {result.final_score}")
    print(f"Self-test OK: {result.final_score:.2f} ({result.details()})")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Scalona porównywarka Excel z RapidFuzz/Levenshtein.")
    parser.add_argument("--self-test", action="store_true", help="Uruchom test logiki bez GUI i bez Excela.")
    args = parser.parse_args(argv)
    if args.self_test:
        return run_self_test()
    return run_gui()


if __name__ == "__main__":
    raise SystemExit(main())

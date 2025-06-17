##promela_writer.py
"""
Lightweight helper that lets the translator emit nicely-indented Promela.
"""

from __future__ import annotations
from pathlib import Path
from typing import Iterable, List


class PromelaWriter:
    INDENT = "    "  # 4 spaces

    def __init__(self) -> None:
        self._buf: List[str] = []
        self._level: int = 0

    # -------------------------------- API ------------------------------- #

    def write(self, line: str = "") -> None:
        """Append a single logical line (no trailing newline)."""
        self._buf.append(f"{self.INDENT * self._level}{line}")

    def enter(self) -> None:       # one level deeper
        self._level += 1

    def exit(self) -> None:        # one level up
        if self._level == 0:
            raise RuntimeError("Indent underflow")
        self._level -= 1

    def extend(self, lines: Iterable[str]) -> None:
        for ln in lines:
            self.write(ln)

    def save(self, path: Path | str) -> None:
        Path(path).write_text(str(self), encoding="utf-8")

    # ----------------------------- dunder ------------------------------- #

    def __str__(self) -> str:
        return "\n".join(self._buf) + "\n"

##ast_parser.py
"""
Thin wrapper around *pycparser* so callers only care about the AST,
not preprocessing quirks.
"""

from __future__ import annotations
from pathlib import Path
from typing import Optional

from pycparser import CParser, c_ast, parse_file


def parse_c(path: Path | str, cpp_args: Optional[list[str]] = None) -> c_ast.FileAST:
    """
    Parse *path* and return the pycparser *FileAST*.
    *cpp_args* is forwarded to pycparser for -I etc.
    """
    path = Path(path)
    cpp_args = cpp_args or ["-E", r"-D__attribute__(x)=", "-std=c99"]
    try:
        # Try using the system preprocessor
        return parse_file(str(path), use_cpp=True, cpp_args=cpp_args)
    except Exception:
        # Fallback: pure-Python parsing (no external cpp)
        code = Path(path).read_text(encoding="utf-8")
        parser = CParser()
        return parser.parse(code)

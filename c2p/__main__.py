from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .ast_parser import parse_c
from .translator import C2PTranslator


def main(argv: list[str] | None = None) -> None:
    argv = argv or sys.argv[1:]
    ap = argparse.ArgumentParser(description="Translate (simple) C to Promela")
    ap.add_argument("input", help="C source file")
    ap.add_argument("-o", "--output", help="Promela output file (default: stdout)")
    ns = ap.parse_args(argv)

    ast = parse_c(ns.input)
    translator = C2PTranslator()
    promela_code = translator.translate(ast)

    if ns.output:
        Path(ns.output).write_text(promela_code, encoding="utf-8")
    else:
        print(promela_code)


if __name__ == "__main__":
    main()

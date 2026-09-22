#!/usr/bin/env python3
"""Check fixed section labels; --fix synchronizes generated numbers in src/*.lean."""

import argparse
import sys

import lean2html
import refs


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fix', action='store_true', help='節番号と参照の表示番号を自動更新する')
    args = parser.parse_args()
    result = refs.analyze(lean2html.SRC, lean2html.CHAPTERS, lean2html.SOL_FILES, lean2html.parse)
    if result.errors:
        print('\n'.join(result.errors), file=sys.stderr)
        return 1
    if args.fix:
        try:
            paths = result.write()
        except (OSError, ValueError) as exc:
            print(exc, file=sys.stderr)
            return 1
        for path in paths:
            print(f'  {path.name}: 節番号・参照を更新')
    elif result.changes:
        print('\n'.join(result.changes), file=sys.stderr)
        print('python3 tools/check_refs.py --fix で同期してください。', file=sys.stderr)
        return 1
    print(f'refcheck: {len(result.sections)} 節の固定ラベルと参照を確認')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

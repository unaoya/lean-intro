"""09_CoveringSol.lean から、問題の証明を sorry にした土台を作る。

「問題n」で始まる docstring の直後の宣言について、主張の終わり（最初の `:=`、
行頭の `|`、行末の `where` のいずれか）から後を `sorry` に置き換える。
`where` の宣言は個別に扱う（下の SPECIAL）。
"""
import re
import sys
from pathlib import Path

src = Path(sys.argv[1]).read_text().splitlines()
out = []
i = 0
PROBLEM = re.compile(r"^/-- 問題\d+")
while i < len(src):
    line = src[i]
    out.append(line)
    if not PROBLEM.match(line):
        i += 1
        continue
    # docstring の終わりまで写す
    while not src[i].rstrip().endswith("-/"):
        i += 1
        out.append(src[i])
    i += 1
    # 宣言本体: 次の「行頭から始まる空でない行」まで
    start = i
    j = i + 1
    while j < len(src) and (src[j] == "" or src[j].startswith(" ")):
        j += 1
    body = src[start:j]
    while body and body[-1] == "":
        body.pop()
    if any(l.rstrip().endswith(" where") for l in body[:1]) or body[0].startswith("def zcoverCovering"):
        # structure の値: 性質のフィールドだけ sorry にする
        kept = []
        skipping = False
        for l in body:
            m = re.match(r"^  (\w+) :=", l)
            if m:
                skipping = m.group(1) in ("star_surj", "star_inj", "injective", "surjective")
                kept.append(f"  {m.group(1)} := sorry" if skipping else l)
            elif not skipping:
                kept.append(l)
        out.extend(kept)
    else:
        sig = []
        for l in body:
            if l.startswith("  |"):
                sig[-1] = sig[-1] + " :="
                break
            if ":=" in l:
                sig.append(l[: l.index(":=")].rstrip() + " :=")
                break
            if l.rstrip().endswith(" where"):
                sig.append(l.rstrip()[: -len(" where")] + " :=")
                break
            sig.append(l)
        out.extend(sig)
        out.append("  sorry")
    out.append("")
    i = j
    # 宣言の後ろの空行は元のまま写す（次の行が空なら 1 つ飛ばす）
    while i < len(src) and src[i] == "":
        i += 1
Path(sys.argv[2]).write_text("\n".join(out) + "\n")

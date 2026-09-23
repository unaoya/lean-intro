"""問題ファイルのコードが、解答から生成した土台と一致するかを照合する。
コメント（/-! -/・/-- -/）と空行を除いたコード行を比べる。"""
import re, subprocess, sys
from pathlib import Path
S = Path(sys.argv[0]).resolve().parent
subprocess.run(["python3", S / "gen_problems.py", "src/09_CoveringSol.lean", S / "base.lean"], check=True)
def code(p):
    t = Path(p).read_text()
    t = re.sub(r"/-[-!].*?-/", "", t, flags=re.S)
    return [l.rstrip() for l in t.splitlines() if l.strip()]
a, b = code(S / "base.lean"), code("src/09_Covering.lean")
if a == b:
    print(f"OK: コード {len(a)} 行が一致")
else:
    import difflib
    print("\n".join(difflib.unified_diff(a, b, "base", "problem", lineterm="")))
    sys.exit(1)

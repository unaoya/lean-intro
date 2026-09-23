import Lake
open Lake DSL

/-!
受講者用の Lean プロジェクト（dev/tools/student.py が自動生成する。手で編集しない）。

`LeanIntro/MyWork/`（書き込み用）は git の管理外で、ここにある処理が自動で作る。
VS Code で Lean のファイルを開くと、Lean がまずこのファイルを読み、
`LeanIntro/Original/` のうち `MyWork/` にまだないファイルだけをコピーする。
すでにあるファイル（受講者が書き込んだもの）は決して上書きしない。
コピーしたときの `Original/` の状態を `MyWork/.copied/` に記録しておき、
あとで教材が更新されたかを `Start.lean` で確かめられるようにする。

章の一覧（この行が変わると Lean がこのファイルを読み直し、新しい章がコピーされる）:
@@CHAPTERS@@
-/

def setupMyWork : IO Unit := do
  let original : System.FilePath := "LeanIntro" / "Original"
  let work : System.FilePath := "LeanIntro" / "MyWork"
  unless (← original.pathExists) do return
  IO.FS.createDirAll (work / ".copied")
  for entry in (← original.readDir) do
    if entry.path.extension == some "lean" then
      let file := work / entry.fileName
      unless (← file.pathExists) do
        let content ← IO.FS.readFile entry.path
        IO.FS.writeFile file content
        IO.FS.writeFile (work / ".copied" / (entry.fileName ++ ".hash")) (toString (hash content))

#eval setupMyWork

package «lean_intro» where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib «LeanIntro» where
  globs := #[.submodules `LeanIntro]

lean_lib «Start»

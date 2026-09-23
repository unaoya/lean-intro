-- Start.lean から使う、準備と教材の更新の確認。dev/tools/student.py が自動生成する。

namespace LeanIntro

/-- `Original/` のうち `MyWork/` にないファイルをコピーし、コピーしたファイル名を返す。
すでにあるファイル（受講者が書き込んだもの）は上書きしない。
lakefile.lean にも同じ処理があるが、そちらは Lean が設定を読み直すときにしか動かないので、
開くたびに実行される Start.lean からも呼ぶ（削除したファイルの作り直し・新しい章の追加のため）。 -/
def copyMissing : IO (Array String) := do
  let original : System.FilePath := "LeanIntro" / "Original"
  let work : System.FilePath := "LeanIntro" / "MyWork"
  let mut copied : Array String := #[]
  unless (← original.pathExists) do return copied
  IO.FS.createDirAll (work / ".copied")
  for entry in (← original.readDir) do
    if entry.path.extension == some "lean" then
      let file := work / entry.fileName
      unless (← file.pathExists) do
        let content ← IO.FS.readFile entry.path
        IO.FS.writeFile file content
        IO.FS.writeFile (work / ".copied" / (entry.fileName ++ ".hash")) (toString (hash content))
        copied := copied.push entry.fileName
  return copied

/-- 書き込み用の `LeanIntro/MyWork/` を整え、コピーしたあとで `Original/` が更新された章を表示する。 -/
def status : IO Unit := do
  let original : System.FilePath := "LeanIntro" / "Original"
  let work : System.FilePath := "LeanIntro" / "MyWork"
  let copied ← copyMissing
  unless (← work.pathExists) do
    IO.println "LeanIntro/MyWork/ を作れませんでした。VS Code でリポジトリのフォルダ全体を開いているか確かめてください。"
    return
  IO.println "準備はできています（書き込み用の LeanIntro/MyWork/ があります）。"
  unless copied.isEmpty do
    IO.println "MyWork/ に次のファイルを作りました:"
    for name in copied.qsort (· < ·) do
      IO.println s!"  {name}"
  let mut updated : Array String := #[]
  for entry in (← original.readDir) do
    if entry.path.extension == some "lean" then
      let record := work / ".copied" / (entry.fileName ++ ".hash")
      if (← record.pathExists) then
        let recorded ← IO.FS.readFile record
        let current := toString (hash (← IO.FS.readFile entry.path))
        if recorded != current then
          updated := updated.push entry.fileName
  if updated.isEmpty then
    IO.println "MyWork/ にコピーしたあとの教材の更新はありません。"
  else
    IO.println "MyWork/ にコピーしたあとで、次の章の教材が更新されました:"
    for name in updated.qsort (· < ·) do
      IO.println s!"  {name}"
    IO.println "最新の内容にしたい章は、LeanIntro/MyWork/ のそのファイルを削除してから、"
    IO.println "このファイル（Start.lean）を開き直してください（その章の書き込みは消えます）。"

end LeanIntro

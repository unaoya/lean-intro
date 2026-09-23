# 被覆パート 章設計の骨子

2026-09-23 時点の計画。**第1段は 2026-09-24 に `src/09_Covering.lean`・`src/09_CoveringSol.lean` として実装済み**（章ファイルの番号つき改名に合わせて `Covering` → `09_Covering`）。
数学的な中身は `archive/probes/CoverProbeA〜D.lean`（計約1165行、sorry なし）で
すべてコンパイラ検証済みで、この計画はそれを演習の形に切り直すためのもの。

## 全体の位置づけ

3段構成（2026-09-23 合意）のうち、この計画書は**第1段（グラフの被覆）**を詳しく扱う。
第2・3段は第1段が完成してから具体化する（「具体 → 抽象」の順序を守るため）。

| 段 | ファイル | 中身 | 状態 |
|---|---|---|---|
| 1 | `Covering.lean` ＋ `CoveringSol.lean` | グラフの被覆、ゴールは π₁(花束) ≃ ℤ | この計画書 |
| 2 | 未定 | ℝ の公理的導入、単位区間のコンパクト性で Top 章を本番投入 | 骨子のみ（末尾） |
| 3 | 未定 | 位相空間の被覆、共通 interface の抽出、π₁(S¹) ≃ ℤ | 骨子のみ（末尾） |

## 形式

- Ascoli と同じ**発展演習**の形式: `sorry` 埋めの問題ファイル ＋ 全証明済みの Sol ファイル
  （ExtraSol 方式、details 埋め込みの対象外）
- `import Top`。グラフの理論そのものは位相を使わないが、最終定理を Top.lean の
  `Function.Bijective` で述べる（Top 章との唯一の接点で、読者に既知の定義を再利用する）
- lean2html: `CHAPTERS` の末尾に `"Covering"` を足し、`SOL_FILES` の除外リストと
  `SLIDE_EXCLUDED_CHAPTERS` に加える（Ascoli と同じ扱い）。refs.py も Ascoli に倣う
- Mathlib との比較・言及はしない
- 規模の見込み: 問題ファイル約800〜900行、Sol 約1200行、問題数 約30

## 冒頭の地の文で述べること

1. **位相空間の被覆の証明の骨組み**: 局所自明性 → 道の持ち上げ（区間のコンパクト性）
   → ホモトピーの持ち上げ → モノドロミー → π₁(S¹) ≃ ℤ（ℝ が単連結）
2. **グラフ版はこの骨組みから解析を全部抜いたもの**。対応表を置く:

   | 位相空間 | グラフ |
   |---|---|
   | 道 `[0,1] → X` | 辺のリスト（隣接条件つき） |
   | ホモトピー | backtrack `e ē` の挿入・削除 |
   | 局所自明性 | star（頂点から出る辺）の上の全単射 |
   | 区間のコンパクト性＋ルベーグ数 | リストの長さに関する帰納法 |
   | ℝ | 直線グラフ（頂点 ℤ） |
   | S¹ | 花束（頂点1つ・ループ1本） |
   | ℝ が単連結 | 直線グラフは木（既約な閉道がない） |

3. このグラフ版は、あとで（第3段で）位相空間版と**同じ定理の2つの実例**として
   並べることになる、という予告（先取り囲み）
4. 構成（Part A〜F）と進め方（`sorry` を埋める・解答は `CoveringSol.lean`）

## Part 構成と問題の切り方

問題番号は通し。★ は山場。「与える」は `sorry` なしで提示する宣言。

### Part A: Serre グラフと道（試作A前半・C冒頭）

- 与える: `SGraph`（反転 `bar` つき）、`term`、`Wf`（道＝隣接条件つきリスト、添字つき帰納型）、
  逆転補題 `Wf.cons_inv`・`Wf.nil_inv`、例 `bouquet`（花束）と `zcover`（直線グラフ）
- 問題1: `term_bar`（反転した辺の終点は元の始点）
- 問題2: `Wf.append`（道の連接）
- 問題3: `Wf.end_unique`（終点は始点と語で決まる）
- 問題4: `Wf.append_split`（連接の分解）
- 問題5: `Wf.revWord`（逆向きの語も道）

補足囲み: **逆転補題をなぜ与えるのか**。`cases` が `init (bar e)` と `term e` の
単一化で失敗する実例を見せる（試作で実際に踏んだエラー）。添字つき帰納型の読み方の練習になる。

### Part B: ホモトピーと正規形定理（試作A）

- 与える: `IsReduced`、`rcons`、`reduce`、`Homotopic`（挿入・削除で生成）、
  `Reduces`（削除のみ）、`Reduces.toHomotopic`、`Reduces.cons`
- 先に計算で遊ぶ: `reduce (G := bouquet) [true, false, true] = [true]` が `rfl` で通る
  （語の問題が計算で解ける）
- 問題6: `isReduced_rcons` → 問題7: `reduce_isReduced`
- 問題8 ★: `rcons_rcons_bar`（既約語に `ē`・`e` を足すと元に戻る。場合分けの芯）
- 問題9: `reduce_append_cancel`（`reduce` は backtrack の削除で不変）
- 問題10: `reduces_reduce`（どの語も正規形へ**削除だけで**到達する）
- 問題11 ★（正規形定理）: `homotopic_iff_reduce_eq`
- 問題12: `eq_of_homotopic_of_isReduced`（既約代表の一意性）
- 問題13: `Wf.of_append_cancel`（削除は道であることを保つ）
- 問題14: `Wf.reduce`（正規形も同じ端点の道）

補足囲み: **挿入は道を壊す**。任意の辺の挿入を許すと隣接条件が崩れるので、
道の水準の議論はすべて `Reduces`（削除のみ）で行い、正規形で挿入を迂回する。
紙の教科書では見えにくく、形式化で強制的に表に出る論点。

補足囲み: 証明の方針について。合流性（diamond 補題）を経由せず、
簡約関数 `reduce` を先に定義して生成関係の各段で不変なことを示す。
「関数を定義して計算に持ち込む」のが Lean で楽な理由。

### Part C: π₁ 亜群（試作C前半）

- 与える: `Homotopic.appendLeft/appendRight`（合同性）、`revWord`、`PathClass`（`Quot`）、
  `PathClass.mk`・`sound`・`mk_eq_of_eq`、`comp`・`inv` の定義（`Quot.lift` の書き方は見せる）
- 問題15: `Homotopic.revWordCong`
- 問題16: `homotopic_revWord_append`、問題17: `homotopic_append_revWord`
- 問題18: 群法則（`refl_comp`・`comp_refl`・`comp_assoc`・`inv_comp`）を `Quot.ind` で

先取り囲み: ここで作ったのは基点を固定しない**亜群**。基点 `v` のループだけ見れば群
（基本群）になる。

### Part D: 被覆と持ち上げ（試作C中盤）

- 与える: `GraphHom`、`term_toE`、`mapWord` とその基本補題、`Covering`（`GraphHom` を extends し、
  star 上の全単射を性質として持つ structure）、`mapWord_split`
- 問題19: `zcover_isCovering`（直線グラフ → 花束 は被覆）
- 問題20 ★: `exists_lift_word`（**道の持ち上げの存在。長さの帰納法一発**）
- 問題21: `lift_word_unique`（持ち上げの一意性）
- 問題22 ★（発展）: `endpoint_of_reduces`（削除は持ち上げの終点を変えない。最難問）
- 問題23: `endpoint_eq`（ホモトピックな道の持ち上げは同じ点に着く。正規形定理に帰着）

先取り囲み: 問題20が位相空間版の「区間のコンパクト性＋ルベーグ数」の仕事を丸ごと
肩代わりしていること。第2・3段でここが本物の解析に置き換わる。

### Part E: モノドロミー（試作C後半・試作Bの具体版）

- 与える: ファイバー `{y // p.toV y = v}`、`fiberExt`、`liftEnd`（`Classical.choose`）と
  `liftEnd_spec`・`liftEnd_eq`、`transport` の定義
- 問題24: `transport_refl`
- 問題25: `transport_trans`（モノドロミーは連接を合成に写す）
- 問題26: モノドロミーは全単射（逆道で戻す）。**抽象化せず具体的に**証明させる
- 例: ループの類がファイバー ℤ に +1 で作用する（2行）

先取り囲み: 問題24〜26の証明は、グラフであることを一度も使わず
「持ち上げが一意に定まる」ことだけから出ている。第3段で位相空間の被覆にも
同じ証明を書くことになり、そこで共通部分を括り出す（試作Bの `LiftSystem`）。
→ 第1段では interface を**導入しない**。読者が「同じ証明を二度書く」経験をしてから抽象化する。

### Part F: π₁(花束) ≃ ℤ（試作D）

- 与える: `mapWord_reduces`、`shiftWord`・`mapWord_shift`、`basePt`、`deg` の定義、`loop`・`loopPow`
- 問題27 ★: `zc_drift`（直線グラフの既約な道は単調に進む）
- 問題28: `zc_reduced_closed`（**直線グラフは単連結**: 既約な閉道は空）
- 問題29: `shift_wf`（平行移動はデッキ変換）→ 問題30: `transport_apply`
- 問題31: `deg_comp`（準同型）、問題32: `deg_inv`
- 問題33: `deg_eq_zero`（核が自明。単連結性を簡約の押し出しで底へ運ぶ）
- 問題34: `deg_injective`、問題35: `deg_surjective`
- 問題36（主定理）: `(∀ γ δ, deg (γ.comp δ) = deg γ + deg δ) ∧ Function.Bijective deg`
- `#print axioms` で propext・Classical.choice・Quot.sound の3つだけと確認（Top 章・Ascoli と同じ基盤）

補足囲み: `omega` は `Int.ofNat k` を原子として扱うので、後続の等式は定義計算
（`rfl`・`exact`）で閉じる。

## 決定事項（2026-09-23）

1. **被覆は「写像＋性質」を束ねた structure**:
   `structure Covering (Y X : SGraph) extends GraphHom Y X where star_surj … star_inj …`。
   Top 章の `Homeomorph`（写像というデータと連続性という命題の束）と同じ流儀。
   star の逆写像を関数として持たせることはしない（持ち上げの終点は `Classical.choose`）
2. **Nielsen–Schreier は入れない**
3. **ファンカンペンには触れない**（冒頭の1文も置かない）
4. 問題数は約36問のまま。重ければ群法則・`deg_inv` を与える側に回す

## 第2・3段の骨子（第1段完成後に具体化）

- 第2段: ℝ を**完備順序体の class として仮定**（構成はしない。lean-calculus と重複するため）。
  `#print axioms` には出ないが、仮定した class が「信じるもの」の一覧に加わることを明示する。
  単位区間の位相、Heine–Borel、連結性、部分空間・積・商位相を Top 章の上に足す
- 第3段: 位相空間の被覆、道とホモトピー、ルベーグ数による持ち上げ補題。
  第1段 Part E と同じ証明を書く段になったところで `LiftSystem` を括り出し、
  グラフ版と位相空間版の両方を instantiate する。π₁(S¹) ≃ ℤ で合流

## 作業手順

1. `CoveringSol.lean` を試作A〜Dから再構成（名前空間を1本化、Part 順に並べ替え、
   試作Bの interface は除く）。`lake build` を通す
2. `Covering.lean` を Sol から生成（問題の証明を `sorry` に置換）。主張の一字一句一致を
   照合スクリプトで確認（Ascoli と同じ）
3. 地の文・囲みを書く。出力・エラーの引用は実際のコンパイラ出力で裏取り
4. lean2html への登録、HTML 生成の確認

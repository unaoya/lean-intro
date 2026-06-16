# Ch7 タクティク入門 — tactic mode の機構と信頼

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->
<!-- 2026-06-15 再編: 1章1テーマ化。等式コーパス→Ch8・順序→Ch10・自動化→Ch9 へ分離 -->

- 前章からの問い: 残った sorry をどう埋めるか
- 到達点: 基本タクティクで短い証明が書ける。「なぜタクティクで証明になるのか（タクティクは項を書く機械）」に答えられる・**各基本タクティクが Ch1/Ch5 の導入/除去規則に対応すると分かる**
- 新しい Lean 機能: by・ゴール状態・intro/exact/apply/have/show・term↔tactic の往復・One bridge・**タクティク↔導入/除去規則の対応**
- コード: C07_Tactics.lean（One bridge＋**タクティク↔規則（ANCHOR `tactics_as_rules`）**＋公理射影＋add_left_cancel'。等式コーパス本体は Ch8）

## 7.1 by とゴール状態

- ゴール表示の読み方（Ch0 の体験の回収）。intro / exact から
- 最初の獲物: trivialPartition.increase の sorry を基本タクティクで埋める（道具の初仕事）

## 7.2 apply と「穴」

- **apply の正体はメタ変数＋単一化**: ゴールに穴 `?m.123` を開けて埋める——`_` も暗黙引数も同じ穴（Ch3・Ch4 と機構レベルで接続）

## 7.3 have・show と One bridge

- 補助ゴール（have）・ゴールの言い換え（show）。One bridge（`instance : One Real`——Ch5 Zero bridge の対・リテラル 1 の窓口・数の段階導入 0=Ch4/1=Ch7/2 以上=Ch12）
- 公理射影を term mode で（add_neg'・zero_add' 等＝`:= AddCommGroup.add_neg a` の 1 行）——「タクティク不要のものは正直に項で書く」
- add_left_cancel'（最初の派生補題）を calc で——次章の等式コーパスの足場

## 7.4 種明かし: タクティク = 導入/除去規則を逆向きに（ANCHOR `tactics_as_rules`）

- by 証明を `#print` して生成された λ 項を見る。**各タクティクは Ch1/Ch5 の導入/除去規則に対応**——新しい原理ではなく、規則を「ゴールから逆向きに」当てる機械:
  - `intro` ＝ →/∀ の**導入**（`fun` を作る）／`apply f` ＝ →/∀ の**除去**（適用を逆向きに・ゴール B を前提 A に戻す）
  - `exact ⟨…⟩`・`constructor` ＝ 帰納型の**導入**（構成子）／`cases`・`obtain` ＝ 帰納型の**除去**（recursor・IH 無し＝cases）
  - `rfl` ＝ `=` の導入（Eq.refl）／`rw` ＝ `=` の除去（Eq.rec・Ch8 で深掘り）
- 実演: Ch1 の `and_swap` を「項 ⟨h.2,h.1⟩」と「`intro`＋`obtain`＋`exact ⟨⟩`」で並べる——同じ ∧ の導入/除去だと見える。`apply` は → の除去（B を A に戻す）
- term と tactic の往復（同じ補題を両方で書く演習）。「タクティクは項を書く機械」＝規則を逆向きに綴る、が腑に落ちる

## 7.5 信頼の構造 — De Bruijn 基準

- タクティクは信じない。タクティクが吐いた項を検査する小さなカーネルだけを信じる
- 🪟 窓: カーネルと De Bruijn 基準 — 何を信じているのか

## 演習

- trivialPartition.increase を自分で・公理射影のドリル（add_neg' / zero_add' を term と tactic 両方で）

## 引き

- 「rw で書き換えてみると、効くときと効かないときがある。等しさには 2 種類あるのか？」

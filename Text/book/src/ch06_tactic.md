# Ch6 タクティク入門 — tactic mode の機構と信頼

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->
<!-- 2026-06-15 再編: 1章1テーマ化。等式コーパス→Ch7・順序→Ch9・自動化→Ch8 へ分離 -->

- 前章からの問い: 残った sorry をどう埋めるか
- 到達点: 基本タクティクで短い証明が書ける。「なぜタクティクで証明になるのか（タクティクは項を書く機械）」に答えられる
- 新しい Lean 機能: by・ゴール状態・intro/exact/apply/have/show・term↔tactic の往復・One bridge
- コード: C06_Tactics.lean（One bridge＋公理射影＋add_left_cancel'＝入門の vehicle。等式コーパス本体は Ch7）

## 6.1 by とゴール状態

- ゴール表示の読み方（Ch0 の体験の回収）。intro / exact から
- 最初の獲物: trivialPartition.increase の sorry を基本タクティクで埋める（道具の初仕事）

## 6.2 apply と「穴」

- **apply の正体はメタ変数＋単一化**: ゴールに穴 `?m.123` を開けて埋める——`_` も暗黙引数も同じ穴（Ch2・Ch3 と機構レベルで接続）

## 6.3 have・show と One bridge

- 補助ゴール（have）・ゴールの言い換え（show）。One bridge（`instance : One Real`——Ch4 Zero bridge の対・リテラル 1 の窓口・数の段階導入 0=Ch3/1=Ch6/2 以上=Ch11）
- 公理射影を term mode で（add_neg'・zero_add' 等＝`:= AddCommGroup.add_neg a` の 1 行）——「タクティク不要のものは正直に項で書く」
- add_left_cancel'（最初の派生補題）を calc で——次章の等式コーパスの足場

## 6.4 種明かし: タクティクは証明項を書く機械

- by 証明を `#print` して生成された λ 項を見る。intro=fun・exact=項の埋め込み
- term と tactic の往復（同じ補題を両方で書く演習）

## 6.5 信頼の構造 — De Bruijn 基準

- タクティクは信じない。タクティクが吐いた項を検査する小さなカーネルだけを信じる
- 🪟 窓: カーネルと De Bruijn 基準 — 何を信じているのか

## 演習

- trivialPartition.increase を自分で・公理射影のドリル（add_neg' / zero_add' を term と tactic 両方で）

## 引き

- 「rw で書き換えてみると、効くときと効かないときがある。等しさには 2 種類あるのか？」

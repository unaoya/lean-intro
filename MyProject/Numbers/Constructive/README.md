# Constructive — 実数の構成的定義（将来計画・ビルド対象外）

このディレクトリは、現在 `MyProject/Axioms.lean` で公理的に導入している実数を、
将来 Cauchy 列による構成（PInt → Rational → Real）で置き換えるための作業場である。
sorry を多数含み、lakefile のビルド対象には含まれていない。

- `PInt.lean` / `NZInt.lean` / `Rational.lean` : 正整数・非零整数・有理数の構成
- `Real.lean` : Cauchy 列の商としての実数
- `Continuity.lean` : 連続性公理の同値性（上限存在・単調収束・区間縮小法・BW・デデキント）の計画メモ

完成した暁には `Axioms.lean` の axiom 群を定理として証明し直すことができる。

# プロトタイプ第1〜5章のインポート依存関係分析

## 概要

`prototypes/chapters-1-2/src/` の5つの章ファイルについて、インポート依存関係を詳細に分析しました。結果として、**冗長なインポートと不要な依存関係**を特定できました。

---

## 1. 現在のインポート構造

### ファイル間の依存関係チェーン

```
01_TypesAndTerms.lean
  ↑
  └─ 02_Forall.lean
       ↑
       └─ 03_InductiveTypes.lean
            ↑
            ├─ 04_Exists.lean (また直接 02 をインポート)
            │    ↑
            │    └─ 05_MathematicalTools.lean (また直接 03 をインポート)
```

### 各ファイルの import 文

| ファイル | インポート内容 |
|---------|------------|
| `01_TypesAndTerms.lean` | なし（基礎章） |
| `02_Forall.lean` | `import «01_TypesAndTerms»` |
| `03_InductiveTypes.lean` | `import «02_Forall»` |
| `04_Exists.lean` | `import «02_Forall»` + `import «03_InductiveTypes»` |
| `05_MathematicalTools.lean` | `import «03_InductiveTypes»` + `import «04_Exists»` |

---

## 2. 詳細分析：各ファイルで何が実際に使われているか

### `02_Forall.lean` → `01_TypesAndTerms` の使用状況

**使用されるシンボル**: `Map`

**使用箇所**:
- 行 672–683: **練習問題の説明文**に `Map` が登場（実行可能コード ❌）
- 実行可能な定義内での使用: **なし** ❌

**判定**: ❌ **不要**（少なくとも本体コードには）

**ただし**: `02_ForallSol.lean` が `Map` を使うため、ソリューション側では必須

---

### `03_InductiveTypes.lean` → `02_Forall` の使用状況

**使用されるシンボル**: なし

**使用箇所**:
- 行 345: 練習問題の説明文に `lastIndex` への参照（実行可能コード ❌）
  - 注記：`lastIndex` は実は第1章の定義なので、第2章経由で来ている

**判定**: ❌ **不要**（第3章の実行可能コード内では消費されていない）

**ただし**: `03_InductiveTypesSol.lean` が `lastIndex` を使うため、ソリューション側では直接インポートが必要

---

### `04_Exists.lean` → `02_Forall` + `03_InductiveTypes` の使用状況

#### 第2章からの使用

**使用されるシンボル**: `comp_injective`

**使用箇所**:
- 行 216: `comp_bijective` 定義内で `comp_injective` を呼び出し ✅

**判定**: ✅ **必須**（ただし冗長）

#### 第3章からの使用

**使用されるシンボル**: `Signal.red`, `Signal.green`, `Signal.noConfusion`

**使用箇所**:
- 行 291–292: `red_ne_green` 定義で使用 ✅

**判定**: ✅ **必須**

#### 冗長性の判定

- `03_InductiveTypes.lean` は既に `02_Forall.lean` をインポートしている
- したがって `04_Exists.lean` が `02_Forall` を直接インポートするのは **冗長**
- `import «03_InductiveTypes»` だけで十分（推移的に第2章も利用可能）

---

### `05_MathematicalTools.lean` → `03_InductiveTypes` + `04_Exists` の使用状況

#### 第4章からの使用

**使用されるシンボル**: `IsEven`, `isEven_add`

**使用箇所**:
- 行 260: `EvenNat` 型定義で `IsEven` を使用 ✅
- 行 286–287: `evenFourPlusFour` で `isEven_add` を呼び出し ✅

**判定**: ✅ **必須**

#### 第3章からの使用

**使用されるシンボル**: `MyPair`, `Numbered`, `myAdd`, `MyNat`

**使用箇所**:
- 行 19, 151, 187, 231: **本文内の説明・比較**で言及（実行可能コード ❌）
- 行 918–920: **練習問題内での参照**（実行可能コード ❌）

**判定**: ❌ **不要**（実行可能コード内では消費されていない）

#### 冗長性の判定

- `04_Exists.lean` は既に `03_InductiveTypes.lean` をインポートしている
- したがって `05_MathematicalTools.lean` が `03_InductiveTypes` を直接インポートするのは **冗換**
- `import «04_Exists»` だけで十分（推移的に第3章も利用可能）

---

## 3. 問題のあるインポート一覧

| ファイル | インポート | 問題の種類 | 影響度 |
|---------|---------|--------|------|
| `02_Forall.lean` | `import «01_TypesAndTerms»` | 不要（本体コード内で未使用） | 🟡 低 |
| `03_InductiveTypes.lean` | `import «02_Forall»` | 不要（本体コード内で未使用） | 🟡 低 |
| `04_Exists.lean` | `import «02_Forall»` | 冗長（`03` 経由で取得可能） | 🟠 中 |
| `05_MathematicalTools.lean` | `import «03_InductiveTypes»` | 冗長（`04` 経由で取得可能） | 🟠 中 |

---

## 4. 改善提案

### A. 段階1：本体ファイルの整理（最小限の改善）

不要/冗長なインポートを削除：

```lean
// 02_Forall.lean
- import «01_TypesAndTerms»  // 削除：本体コード内で未使用
// 演習説明内での参照は問題ない

// 03_InductiveTypes.lean
- import «02_Forall»  // 削除：本体コード内で未使用

// 04_Exists.lean
- import «02_Forall»  // 削除：03 経由で利用可能（冗長）
+ // import «03_InductiveTypes» のみで十分

// 05_MathematicalTools.lean
- import «03_InductiveTypes»  // 削除：冗長
+ // import «04_Exists» のみで十分
```

---

### B. 段階2：ソリューションファイルの対応

ソリューションファイルが親ファイルから遡って必要な定義を参照する場合、**直接インポート**を追加：

```lean
// 02_ForallSol.lean
  import «02_Forall»  // 既存
+ import «01_TypesAndTerms»  // Map を使うので追加

// 03_InductiveTypesSol.lean
  import «03_InductiveTypes»  // 既存
+ import «01_TypesAndTerms»  // lastIndex を使うので追加

// 05_MathematicalToolsSol.lean
  import «05_MathematicalTools»  // 既存
+ // （必要に応じて第4章以前へのインポートを追加）
```

---

### C. 段階3：教材フローの設計（長期的改善）

**方針**: 各章ファイルは「直前の章のみ」をインポートする

```
新しい構造:
01_TypesAndTerms → 基礎のみ
02_Forall → import 01 のみ（本体で使う場合）
03_InductiveTypes → import 02 のみ
04_Exists → import 03 のみ
05_MathematicalTools → import 04 のみ
```

**メリット**:
- 依存関係が線形で明確
- 各章の立位置が直感的
- 前の章の複数レイヤーへの依存が避けられる
- コンパイル時間の短縮

**実装時の注意点**:
- 本文内の説明文や比較句での「前々章以前の例」への言及は OK（テキストなので実行されない）
- ただし、コード例やコードコメント内では明示的に「これは第N章の…」と記述する

---

## 5. 予想される効果

| 改善項目 | 効果 | 優先度 |
|--------|------|------|
| 不要インポート削除（段階1） | 直観的な依存構造 + わずかなコンパイル改善 | 🔴 高 |
| ソリューション直接インポート（段階2） | 各解答ファイルの独立性向上 | 🟠 中 |
| 教材フロー統一（段階3） | 長期的な保守性 + 教学効果 | 🟡 低（構造的改善） |

---

## 6. 実装上の留意点

1. **本体ファイルの削除後、ビルドテスト**
   - Lean 4.30.0 で再コンパイル
   - `checks/build.json` の検証

2. **演習説明文の確認**
   - インポート削除後も、説明内の記号参照は正しく表示される
   - 必要に応じて「第N章の `Symbol` 」と明示

3. **ソリューションファイルへのインポート追加**
   - 各ソリューション側で直接インポートを追加
   - `*Sol.lean` ファイルが独立して機能することを確認

4. **ドキュメント更新**
   - `PLAN.md` に依存構造の方針を記録
   - 新規寄稿者向けガイドラインに反映

---

## 7. チェックリスト（実装予定者向け）

- [ ] `02_Forall.lean` から `import «01_TypesAndTerms»` を削除
- [ ] `03_InductiveTypes.lean` から `import «02_Forall»` を削除
- [ ] `04_Exists.lean` から `import «02_Forall»` を削除
- [ ] `05_MathematicalTools.lean` から `import «03_InductiveTypes»` を削除
- [ ] `02_ForallSol.lean` に `import «01_TypesAndTerms»` を追加
- [ ] `03_InductiveTypesSol.lean` に `import «01_TypesAndTerms»` を追加
- [ ] Lean 4.30.0 で全ファイルを再コンパイル & ログ確認
- [ ] `checks/` の各ログを確認（警告・エラーなし）
- [ ] 本 PDF・スライド PDF を再生成してレイアウト確認
- [ ] `PLAN.md` を更新して依存構造を文書化

---

## 附録：調査に用いた手法

- **ファイル解析**: `rg`（ripgrep）による全シンボル検索
- **定義元追跡**: 各シンボルの定義位置を特定
- **使用パターン分類**: 「実行可能コード」vs「説明文・コメント」の区別
- **推移性チェック**: インポートチェーンの冗長性検証

---

**作成日**: 2026-09-27  
**分析対象**: `prototypes/chapters-1-2/src/` 全5章 + 解答5ファイル  
**ツール**: Copilot coding agent (github-deep-research)

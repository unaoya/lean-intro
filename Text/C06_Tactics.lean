-- Text/C06_Tactics.lean — Ch5 タクティク入門（tactic mode の機構と信頼）
-- by・ゴール状態・intro/exact/apply/rw/have/show を学び、「タクティクは証明項を書く
-- 機械」であることを #print で確かめる。等式補題を数本だけ手で証明して道具に慣れる。
-- 等式コーパス本体は Ch7（C07_Rewrite）、自動化は Ch8、順序と calc は Ch9。
import Text.C05_Structures

-- （One Real bridge は C03 へ前倒し済み＝加群のスカラー単位 1 を Ch5 で使うため）

-- ============================================================
-- タクティク = 導入/除去規則を「ゴールから逆向きに」適用する機械
--   Ch1/Ch4 で見た導入/除去規則は、タクティクとして現れる（新しい原理ではない）:
--     intro           ＝ →/∀ の **導入**（`fun` を作る）
--     apply f         ＝ →/∀ の **除去**（適用を逆向きに・ゴール B を前提 A に戻す）
--     exact ⟨…⟩ / constructor ＝ 帰納型の **導入**（構成子を当てる）
--     cases / obtain  ＝ 帰納型の **除去**（recursor・IH 無し＝cases）
--     rfl / rw        ＝ `=` の 導入 / 除去（Eq.refl / Eq.rec）
--   `#print` すればタクティクが綴った証明項が見える——「項を書く機械」の正体。
-- ============================================================

-- ANCHOR: tactics_as_rules
-- Ch1 の and_swap を「項」と「タクティク」で並べる——同じ ∧ の導入 ⟨⟩ と除去 .1 .2
example (A B : Prop) (h : A ∧ B) : B ∧ A := ⟨h.2, h.1⟩            -- 項（Ch1 と同じ）
example (A B : Prop) : A ∧ B → B ∧ A := by
  intro h             -- → の導入規則（`fun h => …` を作る）
  obtain ⟨a, b⟩ := h  -- ∧ の除去規則（分解＝cases）
  exact ⟨b, a⟩        -- ∧ の導入規則（構成子 ⟨⟩）

-- apply ＝ → の除去（適用を逆向きに）: ゴール B を、f : A → B の前提 A に戻す
example (A B : Prop) (f : A → B) (a : A) : B := by
  apply f             -- → の除去規則
  exact a
-- ANCHOR_END: tactics_as_rules

-- ============================================================
-- 橋渡し（クラスのフィールドを使いやすい形で取り出す）
-- ============================================================

theorem add_neg' (a : Real) : a + -a = (0 : Real) := AddCommGroup.add_neg a
theorem neg_add' (a : Real) : -a + a = (0 : Real) := AddCommGroup.neg_add a
theorem zero_add' (a : Real) : (0 : Real) + a = a := AddCommMonoid.zero_add a
theorem add_zero' (a : Real) : a + (0 : Real) = a := AddCommMonoid.add_zero a
theorem one_mul_b (a : Real) : (1 : Real) * a = a := MulCommMonoid.one_mul a
theorem mul_one_b (a : Real) : a * (1 : Real) = a := MulCommMonoid.mul_one a

theorem add_comm (a b : Real) : a + b = b + a := AddCommMonoid.add_comm a b
theorem add_assoc (a b c : Real) : a + b + c = a + (b + c) := AddCommMonoid.add_assoc a b c
theorem mul_comm (a b : Real) : a * b = b * a := MulCommMonoid.mul_comm a b
theorem mul_assoc (a b c : Real) : a * b * c = a * (b * c) := MulCommMonoid.mul_assoc a b c

theorem add_zero (a : Real) : a + 0 = a := add_zero' a
theorem one_mul (a : Real) : 1 * a = a := one_mul_b a

-- ============================================================
-- 基本計算（消去・ゼロ・符号）
-- ============================================================

theorem add_left_cancel' (a b c : Real) (h : a + b = a + c) : b = c := by
  calc b = 0 + b := (zero_add' _).symm
    _ = (-a + a) + b := by rw [neg_add']
    _ = -a + (a + b) := AddCommMonoid.add_assoc _ _ _
    _ = -a + (a + c) := by rw [h]
    _ = (-a + a) + c := (AddCommMonoid.add_assoc _ _ _).symm
    _ = 0 + c := by rw [neg_add']
    _ = c := zero_add' _

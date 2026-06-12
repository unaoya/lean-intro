-- Text/C03_Class.lean — Ch3 + と 0 はどこから来るか（実演・実験専用）
-- この章の数学的内容は C02 の精読（根幹の 2 行とインスタンス解決）。
-- ここには定義を一切足さない——実演と実験だけを置く。
-- import 連鎖の葉（C04 は C02 を直接 import する）: この時点では「0 だけの世界」
import Text.C02_Axioms

-- ============================================================
-- §1 根幹の 2 行の観察
--    axiom Real.instLOF（構造一式を公理で名指し）＋ instance（正準登録）
-- ============================================================

#check Real.instLOF
#check (inferInstance : LinearOrderedField Real)

-- `a + b` が型検査を通る——書いた覚えのない「+」をインスタンス解決が運んでくる
#check fun (a b : Real) => a + b
#check fun (a b : Real) => a ≤ b

-- TODO(P4): set_option trace.Meta.synthInstance による解決過程の観察（原稿で誘導）

-- ============================================================
-- §2 エラーの実演（Ch8 への伏線）
--    今の Real には OfNat インスタンスが 0 しかない。
--    #check_failure は「失敗すること」自体を検査するコマンド——
--    伏線がビルドで保証される（もし 2 が通るようになったらここが落ちる）
-- ============================================================

-- ANCHOR: check_failure
#check (0 : Real)         -- 通る（Σ の基底として C02 で導入済み）
#check_failure (1 : Real) -- failed to synthesize OfNat Real 1（1 は Ch6 で）
#check_failure (2 : Real) -- failed to synthesize OfNat Real 2（2 以上は Ch8 で）
-- ANCHOR_END: check_failure

-- ============================================================
-- §3 ダイヤモンド事件のトイデモ
--    class のリトマス試験「2 つ目の値が存在したら事故」を実演する。
--    同じ型に 2 つ目のインスタンスを宣言しても機構は黙って受け取り、
--    探索は（既定では）後に宣言された方を選ぶ——事故は静かに起きる。
--    TODO(P4): 本物の NatCast ダイヤモンド事件の語りは原稿側に置く
-- ============================================================

-- ANCHOR: diamond
namespace DiamondIncident

class Price (α : Type) where
  value : α → Nat

structure Coin where
  v : Nat

instance viaFace : Price Coin := ⟨fun c => c.v⟩
instance viaDouble : Price Coin := ⟨fun c => c.v + c.v⟩

-- どちらが選ばれているか？ 機構は後者（viaDouble）を黙って選ぶ
example : Price.value (⟨3⟩ : Coin) = 6 := rfl

end DiamondIncident
-- ANCHOR_END: diamond

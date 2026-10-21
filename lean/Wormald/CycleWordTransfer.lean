import Wormald.CycleLabelingFiber

/-! Exact transfer from labeled vertex cycles to balanced cyclic base words. -/

namespace Wormald.FiniteModel
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def BalancedBaseWord {d N : ℕ} (m : ℕ) (f : Fin N → Fin d) : Prop :=
  ∀ i, Fintype.card {a // f a = i} = m

def cyclicWordWeight {d N : ℕ} {R : Type*} [CommMonoid R]
    (B : Matrix (Fin d) (Fin d) R) (f : Fin N → Fin d) : R :=
  ∏ i, B (f i) (f (finRotate N i))

def balancedCycleWordSum {d N : ℕ} {R : Type*} [CommSemiring R]
    (B : Matrix (Fin d) (Fin d) R) (m : ℕ) : R :=
  ∑ f : Fin N → Fin d, if BalancedBaseWord m f then cyclicWordWeight B f else 0

theorem rootedOrder_block_weight {d m : ℕ} (B : Matrix (Fin d) (Fin d) ℝ)
    (e : Fin (Fintype.card (Fin d × Fin m)) ≃ (Fin d × Fin m)) :
    rootedOrderWeight (blockConstantMatrix B m) e =
      cyclicWordWeight B (fun a => (e a).1) := rfl

/-- The exact multiplicity `(m!)^d` comes from bijective vertex labelings,
not from an asymptotic approximation. -/
theorem rootedOrder_sum_blockConstant {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (m : ℕ) :
    (∑ e : Fin (Fintype.card (Fin d × Fin m)) ≃ (Fin d × Fin m),
      rootedOrderWeight (blockConstantMatrix B m) e) =
      (Nat.factorial m : ℝ) ^ d *
        balancedCycleWordSum (N := Fintype.card (Fin d × Fin m)) B m := by
  let π : (Fin (Fintype.card (Fin d × Fin m)) ≃ (Fin d × Fin m)) →
      (Fin (Fintype.card (Fin d × Fin m)) → Fin d) := fun e a => (e a).1
  calc
    _ = ∑ e, cyclicWordWeight B (π e) := by
      apply Finset.sum_congr rfl
      intro e _
      exact rootedOrder_block_weight B e
    _ = ∑ f, ∑ _e : labelingFiber (m := m) f, cyclicWordWeight B f :=
      (Fintype.sum_fiberwise' π (cyclicWordWeight B)).symm
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        labelingFiber_card_eq_ite, Nat.cast_ite, Nat.cast_pow, Nat.cast_zero]
      unfold balancedCycleWordSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      unfold BalancedBaseWord
      split_ifs <;> simp

/-- The original independent-model expectation is exactly the balanced
cyclic base-word weight, with the factorial labeling and rotation factors. -/
theorem expectedCycles_eq_balancedCycleWordSum {d : ℕ} (base : Orientation d)
    (m : ℕ) (hN : 3 ≤ d * m) :
    (expectedCycles base m : ℝ) = (Nat.factorial m : ℝ) ^ d / (d * m : ℕ) *
      balancedCycleWordSum (N := Fintype.card (Fin d × Fin m)) (weightedBase base) m := by
  rw [expectedCycles_eq_rootedOrderSum base m hN, rootedOrder_sum_blockConstant]
  ring

end
end Wormald.FiniteModel

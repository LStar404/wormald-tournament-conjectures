import Wormald.TiltedCycleTransfer
import Wormald.PartialPermutationLaplacian

namespace Wormald.FiniteModel
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem internalCycleArcSet_card {d m : ℕ} (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d) :
    (internalCycleArcSet σ i).card =
      (Finset.univ.filter (fun a : Fin m => (σ (i, a)).1 = i)).card := by
  have himage : (internalCycleArcSet σ i).image Prod.fst =
      Finset.univ.filter (fun a : Fin m => (σ (i, a)).1 = i) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨b, c⟩, he, hba⟩
      change b = a at hba
      subst b
      exact congrArg Prod.fst ((mem_internalCycleArcSet σ i a c).mp he)
    · intro ha
      exact ⟨(a, (σ (i, a)).2),
        (mem_internalCycleArcSet σ i a _).mpr (Prod.ext ha rfl), rfl⟩
  rw [← himage, Finset.card_image_of_injOn (internalCycleArcSet_source_injOn σ i)]

theorem independentCycle_row_product {d m : ℕ} (base : Orientation d)
    (σ : Equiv.Perm (Fin d × Fin m)) (hc : CrossBlockCycleCompatible base σ) (i : Fin d) :
    (∏ a : Fin m, blockConstantMatrix (weightedBase base) m (i, a) (σ (i, a))) =
      (1 / 2 : ℝ) ^ (internalCycleArcSet σ i).card := by
  have hentry (a : Fin m) :
      blockConstantMatrix (weightedBase base) m (i, a) (σ (i, a)) =
        if (σ (i, a)).1 = i then (1 / 2 : ℝ) else 1 := by
    by_cases hi : (σ (i, a)).1 = i
    · simp [blockConstantMatrix, weightedBase, hi]
    · have he := hc (i, a) (Ne.symm hi)
      simp [blockConstantMatrix, weightedBase, hi, Ne.symm hi, he]
  simp_rw [hentry]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  rw [internalCycleArcSet_card]

theorem independentCycle_product {d m : ℕ} (base : Orientation d)
    (σ : Equiv.Perm (Fin d × Fin m)) :
    (∏ v, blockConstantMatrix (weightedBase base) m v (σ v)) =
      if CrossBlockCycleCompatible base σ then
        ∏ i, (1 / 2 : ℝ) ^ (internalCycleArcSet σ i).card else 0 := by
  by_cases hc : CrossBlockCycleCompatible base σ
  · rw [ite_eq_left hc, Fintype.prod_prod_type]
    exact Finset.prod_congr rfl (fun i _ => independentCycle_row_product base σ hc i)
  · rw [ite_eq_right hc]
    obtain ⟨v, hv⟩ := not_forall.mp hc
    have hblock : v.1 ≠ (σ v).1 := by tauto
    have harc : arc base v.1 (σ v).1 ≠ true := by tauto
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [blockConstantMatrix, weightedBase, hblock, harc]

def independentTiltedBlockWeight {m : ℕ} (D : Finset (Fin m × Fin m)) : ℝ :=
  (1 / 2 : ℝ) ^ D.card * Real.exp ((internalInOutCount D : ℝ) / (m : ℝ))

theorem independentTiltedBlockWeight_pos {m : ℕ} (D : Finset (Fin m × Fin m)) :
    0 < independentTiltedBlockWeight D := by unfold independentTiltedBlockWeight; positivity

theorem internalJoinTilt_eq_product {d m : ℕ} (σ : Equiv.Perm (Fin d × Fin m)) :
    internalJoinTilt σ =
      ∏ i, Real.exp ((internalInOutCount (internalCycleArcSet σ i) : ℝ) / (m : ℝ)) := by
  rw [← Real.exp_sum]
  simp only [internalJoinTilt, Nat.cast_sum, Finset.sum_div]

theorem tiltedIndependentCycleSum_eq_internalWeights {d : ℕ}
    (base : Orientation d) (m : ℕ) :
    tiltedIndependentCycleSum base m =
      ∑ σ : Equiv.Perm (Fin d × Fin m),
        if SingleOrbit σ ∧ CrossBlockCycleCompatible base σ then
          ∏ i, independentTiltedBlockWeight (internalCycleArcSet σ i) else 0 := by
  unfold tiltedIndependentCycleSum
  apply Finset.sum_congr rfl
  intro σ _
  rw [independentCycle_product]
  by_cases ho : SingleOrbit σ <;> by_cases hc : CrossBlockCycleCompatible base σ <;>
    simp only [ho, hc, and_self, and_false, false_and, ite_true, ite_false, zero_mul]
  rw [internalJoinTilt_eq_product, ← Finset.prod_mul_distrib]
  rfl

end
end Wormald.FiniteModel

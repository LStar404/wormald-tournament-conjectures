import Wormald.BernoulliFiniteMGF
import Wormald.FiniteWeightedChernoff

namespace Wormald

noncomputable section
open scoped BigOperators

theorem pairedCentered_upper_tail_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    finiteTailMass (fun b : Fin N → Bool => bernoulliProductMass p b)
      (pairedCenteredValue p) (δ * (N : ℝ)) ≤ Real.exp (-2 * δ ^ 2 * (N : ℝ)) := by
  calc
    _ ≤ Real.exp (-(4 * δ) * (δ * (N : ℝ))) * pairedCenteredMGF p N (4 * δ) :=
      finiteTailMass_chernoff _ _ (bernoulliProductMass_nonneg p hp0 hp1) _ _ (by positivity)
    _ ≤ Real.exp (-(4 * δ) * (δ * (N : ℝ))) * Real.exp ((N : ℝ) * (4 * δ) ^ 2 / 8) :=
      mul_le_mul_of_nonneg_left (pairedCenteredMGF_le p hp0 hp1 N _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem pairedCentered_lower_tail_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    finiteTailMass (fun b : Fin N → Bool => bernoulliProductMass p b)
      (fun b => -pairedCenteredValue p b) (δ * (N : ℝ)) ≤ Real.exp (-2 * δ ^ 2 * (N : ℝ)) := by
  have hmgf : (∑ b : Fin N → Bool, bernoulliProductMass p b *
      Real.exp ((4 * δ) * -pairedCenteredValue p b)) = pairedCenteredMGF p N (-(4 * δ)) := by
    apply Finset.sum_congr rfl
    intro b _
    congr 2
    ring
  calc
    _ ≤ Real.exp (-(4 * δ) * (δ * (N : ℝ))) *
        ∑ b : Fin N → Bool, bernoulliProductMass p b * Real.exp ((4 * δ) * -pairedCenteredValue p b) :=
      finiteTailMass_chernoff _ _ (bernoulliProductMass_nonneg p hp0 hp1) _ _ (by positivity)
    _ = Real.exp (-(4 * δ) * (δ * (N : ℝ))) * pairedCenteredMGF p N (-(4 * δ)) := by rw [hmgf]
    _ ≤ Real.exp (-(4 * δ) * (δ * (N : ℝ))) * Real.exp ((N : ℝ) * (-(4 * δ)) ^ 2 / 8) :=
      mul_le_mul_of_nonneg_left (pairedCenteredMGF_le p hp0 hp1 N _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- A direct finite Hoeffding bound for the count of disjoint successful
adjacent holding pairs. The estimate includes all natural lengths. -/
theorem pairedCentered_abs_tail_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    finiteAbsTailMass (fun b : Fin N → Bool => bernoulliProductMass p b)
      (pairedCenteredValue p) (δ * (N : ℝ)) ≤ 2 * Real.exp (-2 * δ ^ 2 * (N : ℝ)) := by
  exact (finiteAbsTailMass_le_sum _ _ (bernoulliProductMass_nonneg p hp0 hp1) _).trans
    (by linarith [pairedCentered_upper_tail_le p hp0 hp1 N δ hδ,
      pairedCentered_lower_tail_le p hp0 hp1 N δ hδ])

end
end Wormald

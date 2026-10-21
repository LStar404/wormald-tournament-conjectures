import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real

/-! Gaussian tails with constants independent of the growing dimension.
The anchored estimate is exactly in the differences used by the quotient
Gaussian, and does not require an artificial independence premise. -/

namespace Wormald
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem standardNormal_hasSubgaussianMGF :
    HasSubgaussianMGF id 1 (gaussianReal 0 1) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by rw [mgf_id_gaussianReal]; simp

theorem hasSubgaussianMGF_of_standardNormal_law
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 1) μ) : HasSubgaussianMGF X 1 μ := by
  have h : HasSubgaussianMGF id 1 (μ.map X) := by
    rw [hX.map_eq]
    exact standardNormal_hasSubgaussianMGF
  simpa only [Function.id_comp] using
    (HasSubgaussianMGF.of_map (X := id) (Y := X) hX.aemeasurable h)

theorem subgaussian_abs_tail_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ) (R : ℝ) (hR : 0 ≤ R) :
    μ.real {ω | R ≤ |X ω|} ≤ 2 * Real.exp (-R ^ 2 / (2 * c)) := by
  have hset : {ω | R ≤ |X ω|} = {ω | R ≤ X ω} ∪ {ω | R ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      by_cases hx : 0 ≤ X ω
      · exact Or.inl (by simpa only [abs_of_nonneg hx] using h)
      · exact Or.inr (by simpa only [abs_of_nonpos (le_of_not_ge hx)] using h)
    · rintro (h | h)
      · exact h.trans (le_abs_self _)
      · exact h.trans (neg_le_abs _)
  rw [hset]
  have hright := hX.measure_ge_le hR
  have hleft := hX.neg.measure_ge_le hR
  exact (measureReal_union_le _ _).trans
    (by simpa only [two_mul, Pi.neg_apply] using add_le_add hright hleft)

theorem standardNormal_difference_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 1) μ) (hY : HasLaw Y (gaussianReal 0 1) μ) :
    HasSubgaussianMGF (fun ω => X ω - Y ω) 4 μ := by
  have h := (hasSubgaussianMGF_of_standardNormal_law hX).add
    (hasSubgaussianMGF_of_standardNormal_law hY).neg
  norm_num [NNReal.sqrt_one, sub_eq_add_neg] at h
  exact h

/-- The maximum of anchored differences has an exponential Gaussian tail,
uniformly in the number of coordinates. -/
theorem finiteGaussian_anchor_tail_le {n : ℕ} (j : Fin n) (R : ℝ) (hR : 0 ≤ R) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
      {x | ∃ i : Fin n, R ≤ |x i - x j|} ≤
        2 * n * Real.exp (-R ^ 2 / 8) := by
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  have hlaw (i : Fin n) : HasLaw (fun x : Fin n → ℝ => x i) (gaussianReal 0 1) μ := by
    exact ⟨(measurable_pi_apply i).aemeasurable,
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq⟩
  have htail (i : Fin n) : μ.real {x | R ≤ |x i - x j|} ≤
      2 * Real.exp (-R ^ 2 / 8) := by
    have h := subgaussian_abs_tail_le
      (standardNormal_difference_hasSubgaussianMGF (hlaw i) (hlaw j)) R hR
    norm_num at h
    exact h
  change μ.real _ ≤ _
  have hset : {x : Fin n → ℝ | ∃ i : Fin n, R ≤ |x i - x j|} =
      ⋃ i : Fin n, {x | R ≤ |x i - x j|} := by ext x; simp
  rw [hset]
  calc
    _ ≤ ∑ i : Fin n, μ.real {x | R ≤ |x i - x j|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, 2 * Real.exp (-R ^ 2 / 8) := Finset.sum_le_sum fun i _ => htail i
    _ = _ := by simp; ring

theorem finiteGaussian_scaled_anchor_tail_le {n : ℕ} (j : Fin n) (a : ℝ) (ha : 0 ≤ a) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
      {x | ∃ i : Fin n, Real.sqrt (n : ℝ) * a ≤ |x i - x j|} ≤
        2 * n * Real.exp (-(n : ℝ) * a ^ 2 / 8) := by
  have h := finiteGaussian_anchor_tail_le j (Real.sqrt (n : ℝ) * a) (by positivity)
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), neg_mul] using h

end
end Wormald

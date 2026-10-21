import Wormald.QuarticLawOfLargeNumbers
import Wormald.StandardNormalMoments
import Mathlib.Probability.Independence.InfinitePi

/-! The common quartic correction for an actual standard-normal product law.
The dimension grows with n; the proof uses a common countable product space,
then transfers the result to each finite Gaussian product exactly. -/

namespace Wormald
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Function

def standardNormalSequenceMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure standardNormalSequenceMeasure := by
  unfold standardNormalSequenceMeasure
  infer_instance

theorem standardNormalSequence_map_eval (i : ℕ) :
    standardNormalSequenceMeasure.map (fun ω => ω i) = gaussianReal 0 1 := by
  exact Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) i

theorem standardNormalSequence_iIndepFun :
    iIndepFun (fun i : ℕ => fun ω : ℕ → ℝ => ω i) standardNormalSequenceMeasure := by
  exact iIndepFun_infinitePi (X := fun _ : ℕ => id) (fun _ => measurable_id)

theorem standardNormalSequence_identDistrib (i : ℕ) :
    IdentDistrib (fun ω : ℕ → ℝ => ω i) (fun ω : ℕ → ℝ => ω 0)
      standardNormalSequenceMeasure standardNormalSequenceMeasure := by
  exact ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
    (standardNormalSequence_map_eval i).trans (standardNormalSequence_map_eval 0).symm⟩

theorem integrable_standardNormalSequence_pow (p : ℕ) :
    Integrable (fun ω : ℕ → ℝ => ω 0 ^ p) standardNormalSequenceMeasure := by
  have h : Integrable (fun x : ℝ => x ^ p)
      (standardNormalSequenceMeasure.map (fun ω => ω 0)) := by
    rw [standardNormalSequence_map_eval]
    exact integrable_standardNormal_pow p
  exact h.comp_measurable (measurable_pi_apply 0)

theorem integral_standardNormalSequence_pow (p : ℕ) :
    (∫ ω : ℕ → ℝ, ω 0 ^ p ∂standardNormalSequenceMeasure) = standardNormalMoment p := by
  calc
    _ = ∫ x : ℝ, x ^ p ∂standardNormalSequenceMeasure.map (fun ω => ω 0) :=
      (integral_map_of_stronglyMeasurable (μ := standardNormalSequenceMeasure)
        (measurable_pi_apply 0) (continuous_id.pow p).stronglyMeasurable).symm
    _ = standardNormalMoment p := by rw [standardNormalSequence_map_eval]; rfl

theorem tendsto_standardNormal_quartic_factor_sq :
    Tendsto (fun n => ∫ ω : ℕ → ℝ,
      (Real.exp (-normalizedCompleteQuartic (fun i ω => ω i) n ω) -
        Real.exp (-(1 / 2 : ℝ))) ^ 2 ∂standardNormalSequenceMeasure) atTop (𝓝 0) := by
  apply tendsto_integral_quartic_factor_sq (fun (i : ℕ) (ω : ℕ → ℝ) => ω i)
    (fun i => measurable_pi_apply i)
    (fun p _ => integrable_standardNormalSequence_pow p)
    (fun _ _ hij => standardNormalSequence_iIndepFun.indepFun hij)
    standardNormalSequence_identDistrib
  · simpa only [pow_one, standardNormalMoment_one] using integral_standardNormalSequence_pow 1
  · simpa only [standardNormalMoment_two] using integral_standardNormalSequence_pow 2
  · simpa only [standardNormalMoment_four] using integral_standardNormalSequence_pow 4

theorem standardNormalSequence_map_prefix (n : ℕ) :
    standardNormalSequenceMeasure.map (fun ω : ℕ → ℝ => fun i : Fin n => ω i) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  have hi : iIndepFun (fun i : Fin n => fun ω : ℕ → ℝ => ω i) standardNormalSequenceMeasure :=
    standardNormalSequence_iIndepFun.precomp Fin.val_injective
  rw [iIndepFun.map_fun_eq_pi_map
    (fun i : Fin n => (measurable_pi_apply (i : ℕ)).aemeasurable) hi]
  simp only [standardNormalSequence_map_eval]

/-- The finite-dimensional Gaussian product integral, with n itself tending
to infinity. This is not an application of a fixed-dimensional Laplace theorem. -/
theorem tendsto_finiteGaussian_quartic_factor_sq :
    Tendsto (fun n => ∫ x : Fin n → ℝ,
      (Real.exp (-(completeQuarticEnergy x / (12 * (n : ℝ) ^ 2))) -
        Real.exp (-(1 / 2 : ℝ))) ^ 2 ∂Measure.pi (fun _ => gaussianReal 0 1)) atTop (𝓝 0) := by
  apply tendsto_standardNormal_quartic_factor_sq.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    have hm : Measurable (fun ω : ℕ → ℝ => fun i : Fin n => ω i) :=
      Measurable.of_eval fun i => measurable_pi_apply (i : ℕ)
    rw [← standardNormalSequence_map_prefix n, integral_map hm.aemeasurable (by
      apply Continuous.aestronglyMeasurable
      unfold completeQuarticEnergy
      fun_prop)]
    rfl

end
end Wormald

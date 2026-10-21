import Wormald.GaussianQuarticIdentity
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The common complete-graph quartic factor converges in L². The probabilistic
input is only the ordinary iid law and its first four integrable moments. -/

namespace Wormald
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Function

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def normalizedCompleteQuartic (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  completeQuarticEnergy (fun i : Fin n => Z i ω) / (12 * (n : ℝ) ^ 2)

def empiricalPower (Z : ℕ → Ω → ℝ) (p n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, Z i ω ^ p) / n

omit [MeasurableSpace Ω] in
theorem normalizedCompleteQuartic_eq (Z : ℕ → Ω → ℝ) (n : ℕ) (hn : 0 < n) (ω : Ω) :
    normalizedCompleteQuartic Z n ω =
      (empiricalPower Z 4 n ω - 4 * empiricalPower Z 3 n ω * empiricalPower Z 1 n ω +
        3 * empiricalPower Z 2 n ω ^ 2) / 12 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hs (p : ℕ) : (∑ i : Fin n, Z i ω ^ p) = ∑ i ∈ Finset.range n, Z i ω ^ p := by
    exact Fin.sum_univ_eq_sum_range (fun i : ℕ => Z i ω ^ p) n
  have hs1 : (∑ i : Fin n, Z i ω) = ∑ i ∈ Finset.range n, Z i ω := by
    simpa only [pow_one] using hs 1
  simp only [normalizedCompleteQuartic, completeQuarticEnergy_eq, empiricalPower, pow_one,
    Fintype.card_fin, hs, hs1]
  field_simp

omit [MeasurableSpace Ω] in
theorem normalizedCompleteQuartic_nonneg (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ normalizedCompleteQuartic Z n ω := by
  unfold normalizedCompleteQuartic completeQuarticEnergy
  positivity

theorem ae_tendsto_normalizedCompleteQuartic (Z : ℕ → Ω → ℝ)
    (hint : ∀ p : ℕ, p ≤ 4 → Integrable (fun ω => Z 0 ω ^ p) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Z))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ)
    (hmean : ∫ ω, Z 0 ω ∂μ = 0) (hsecond : ∫ ω, Z 0 ω ^ 2 ∂μ = 1)
    (hfourth : ∫ ω, Z 0 ω ^ 4 ∂μ = 3) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => normalizedCompleteQuartic Z n ω) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hp (p : ℕ) (hp : p ≤ 4) : ∀ᵐ ω ∂μ,
      Tendsto (fun n => empiricalPower Z p n ω) atTop (𝓝 (∫ ω, Z 0 ω ^ p ∂μ)) :=
    strong_law_ae_real (fun i ω => Z i ω ^ p) (hint p hp)
      (fun i j hij => (hindep hij).comp (continuous_pow p).measurable (continuous_pow p).measurable)
      (fun i => (hident i).comp (continuous_pow p).measurable)
  filter_upwards [hp 1 (by omega), hp 2 (by omega), hp 3 (by omega), hp 4 (by omega)] with
    ω h1 h2 h3 h4
  simp only [pow_one, hmean, hsecond, hfourth] at h1 h2 h4
  have hlim := ((h4.sub ((h3.mul h1).const_mul 4)).add ((h2.pow 2).const_mul 3)).div_const 12
  norm_num at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa only [mul_assoc] using (normalizedCompleteQuartic_eq Z n hn ω).symm

theorem tendsto_integral_quartic_factor_sq [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (Z i))
    (hint : ∀ p : ℕ, p ≤ 4 → Integrable (fun ω => Z 0 ω ^ p) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Z))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ)
    (hmean : ∫ ω, Z 0 ω ∂μ = 0) (hsecond : ∫ ω, Z 0 ω ^ 2 ∂μ = 1)
    (hfourth : ∫ ω, Z 0 ω ^ 4 ∂μ = 3) :
    Tendsto (fun n => ∫ ω, (Real.exp (-normalizedCompleteQuartic Z n ω) -
      Real.exp (-(1 / 2 : ℝ))) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hmeasQ (n : ℕ) : Measurable (normalizedCompleteQuartic Z n) := by
    unfold normalizedCompleteQuartic completeQuarticEnergy
    fun_prop
  have hQ := ae_tendsto_normalizedCompleteQuartic Z hint hindep hident hmean hsecond hfourth
  let F : ℕ → Ω → ℝ := fun n ω => (Real.exp (-normalizedCompleteQuartic Z n ω) -
    Real.exp (-(1 / 2 : ℝ))) ^ 2
  have hmeasF (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    ((((hmeasQ n).neg.exp).sub_const _).pow_const 2).aestronglyMeasurable
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (F := F) (f := fun _ => 0)
    (fun _ : Ω => (4 : ℝ)) hmeasF (integrable_const 4)
    (fun n => ae_of_all _ (fun ω => by
      have he0 := Real.exp_pos (-normalizedCompleteQuartic Z n ω)
      have he1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (normalizedCompleteQuartic_nonneg Z n ω))
      have hc0 := Real.exp_pos (-(1 / 2 : ℝ))
      have hc1 : Real.exp (-(1 / 2 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith))
    (hQ.mono fun ω hω => by
      have h := ((Real.continuous_exp.tendsto _).comp hω.neg).sub_const
        (Real.exp (-(1 / 2 : ℝ)))
      simpa only [F, Function.comp_apply, sub_self, zero_pow (by norm_num : 2 ≠ 0)] using h.pow 2)
  simpa only [integral_zero] using hlim

end
end Wormald

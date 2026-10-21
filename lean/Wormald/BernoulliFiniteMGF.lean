import Wormald.HoldingFlags
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Bernoulli

namespace Wormald

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def bernoulliMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def bernoulliProductMass (p : ℝ) {N : ℕ} (b : Fin N → Bool) : ℝ :=
  ∏ t, bernoulliMass p (b t)

theorem bernoulliProductMass_cons (p : ℝ) {N : ℕ} (b : Bool) (bs : Fin N → Bool) :
    bernoulliProductMass p (Fin.cons b bs) = bernoulliMass p b * bernoulliProductMass p bs := by
  simp [bernoulliProductMass, Fin.prod_univ_succ]

theorem bernoulliProductMass_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {N : ℕ} (b : Fin N → Bool) : 0 ≤ bernoulliProductMass p b := by
  apply Finset.prod_nonneg
  intro t _
  unfold bernoulliMass
  split <;> linarith

def bernoulliCenteredMGF (p t : ℝ) : ℝ :=
  p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (t * (0 - p))

theorem bernoulliCenteredMGF_nonneg (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ bernoulliCenteredMGF p t := by
  unfold bernoulliCenteredMGF
  positivity

/-- Hoeffding's one-variable lemma, in the exact two-point finite-sum form. -/
theorem bernoulliCenteredMGF_le (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliCenteredMGF p t ≤ Real.exp (t ^ 2 / 8) := by
  let pp : unitInterval := ⟨p, hp0, hp1⟩
  let μ : Measure Bool := bernoulliMeasure true false pp
  let X : Bool → ℝ := fun b => if b then 1 else 0
  have hX : AEMeasurable X μ := (measurable_of_finite X).aemeasurable
  have hrange : ∀ᵐ b ∂μ, X b ∈ Set.Icc (0 : ℝ) 1 :=
    ae_of_all _ (fun b => by cases b <;> norm_num [X])
  have hmean : (∫ b, X b ∂μ) = p := by
    rw [show μ = bernoulliMeasure true false pp from rfl, integral_bernoulliMeasure]
    simp [X, pp]
  have hs := hasSubgaussianMGF_of_mem_Icc hX hrange
  have hh := hs.mgf_le t
  rw [ProbabilityTheory.mgf, hmean,
    show μ = bernoulliMeasure true false pp from rfl, integral_bernoulliMeasure] at hh
  norm_num [X, pp] at hh
  unfold bernoulliCenteredMGF
  convert hh using 1 <;> ring_nf

/-- Number of successful disjoint adjacent pairs, starting at positions 0,2,4,... . -/
def pairedSuccessCount : {N : ℕ} → (Fin N → Bool) → ℕ
  | 0, _ => 0
  | 1, _ => 0
  | _N + 2, b => (if b 0 && b 1 then 1 else 0) + pairedSuccessCount (Fin.tail (Fin.tail b))

def pairedCenteredValue (p : ℝ) {N : ℕ} (b : Fin N → Bool) : ℝ :=
  (pairedSuccessCount b : ℝ) - ((N / 2 : ℕ) : ℝ) * p ^ 2

def pairedCenteredMGF (p : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ b : Fin N → Bool, bernoulliProductMass p b * Real.exp (t * pairedCenteredValue p b)

theorem paired_mgf_integrand_cons_cons (p t : ℝ) {N : ℕ}
    (a b : Bool) (bs : Fin N → Bool) :
    bernoulliProductMass p (Fin.cons a (Fin.cons b bs)) *
      Real.exp (t * pairedCenteredValue p (Fin.cons a (Fin.cons b bs))) =
    (bernoulliMass p a * bernoulliMass p b *
      Real.exp (t * ((if a && b then (1 : ℝ) else 0) - p ^ 2))) *
        (bernoulliProductMass p bs * Real.exp (t * pairedCenteredValue p bs)) := by
  have hc : pairedCenteredValue p (Fin.cons a (Fin.cons b bs)) =
      ((if a && b then (1 : ℝ) else 0) - p ^ 2) + pairedCenteredValue p bs := by
    simp only [pairedCenteredValue, pairedSuccessCount, Fin.cons_zero, Fin.tail_cons]
    rw [show (N + 2) / 2 = N / 2 + 1 by omega]
    push_cast
    cases a <;> cases b <;> norm_num <;> ring
  rw [bernoulliProductMass_cons, bernoulliProductMass_cons, hc, mul_add, Real.exp_add]
  ring

theorem pairedCenteredMGF_add_two (p : ℝ) (N : ℕ) (t : ℝ) :
    pairedCenteredMGF p (N + 2) t = bernoulliCenteredMGF (p ^ 2) t * pairedCenteredMGF p N t := by
  unfold pairedCenteredMGF
  rw [sum_fin_succ_function]
  simp_rw [sum_fin_succ_function, paired_mgf_integrand_cons_cons, ← Finset.mul_sum]
  simp [bernoulliMass, bernoulliCenteredMGF]
  ring

theorem pairedCenteredMGF_eq_pow (p : ℝ) (N : ℕ) (t : ℝ) :
    pairedCenteredMGF p N t = bernoulliCenteredMGF (p ^ 2) t ^ (N / 2) := by
  induction N using Nat.twoStepInduction with
  | zero => simp [pairedCenteredMGF, pairedCenteredValue, pairedSuccessCount, bernoulliProductMass]
  | one =>
    unfold pairedCenteredMGF
    rw [sum_fin_succ_function]
    simp [bernoulliProductMass, pairedCenteredValue, pairedSuccessCount, bernoulliMass]
  | more N ih _ =>
    rw [pairedCenteredMGF_add_two, ih, show (N + 2) / 2 = N / 2 + 1 by omega, pow_succ]
    ring

/-- The disjoint adjacent pair count has the same centered MGF as a sum of
`floor(N/2)` independent Bernoulli(p²) variables. -/
theorem pairedCenteredMGF_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) (t : ℝ) :
    pairedCenteredMGF p N t ≤ Real.exp ((N : ℝ) * t ^ 2 / 8) := by
  have hp2 : p ^ 2 ≤ 1 := by nlinarith
  rw [pairedCenteredMGF_eq_pow]
  calc
    _ ≤ Real.exp (t ^ 2 / 8) ^ (N / 2) :=
      pow_le_pow_left₀ (bernoulliCenteredMGF_nonneg _ _ (sq_nonneg p) hp2)
        (bernoulliCenteredMGF_le _ _ (sq_nonneg p) hp2) _
    _ = Real.exp (((N / 2 : ℕ) : ℝ) * (t ^ 2 / 8)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hN : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.div_le_self N 2
      nlinarith [sq_nonneg t])

end
end Wormald

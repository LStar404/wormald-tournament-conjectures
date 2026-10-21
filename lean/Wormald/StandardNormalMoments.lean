import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The concrete standard-normal moments required by the quartic law of large
numbers. They are derived from Mathlib's proved Gaussian moment generating
function; no numerical moments are assumed. -/

namespace Wormald
noncomputable section
open MeasureTheory ProbabilityTheory

def standardNormalMoment (p : ℕ) : ℝ := ∫ x : ℝ, x ^ p ∂gaussianReal 0 1

theorem standardNormalMoment_eq_mgf_derivative (p : ℕ) :
    standardNormalMoment p = iteratedDeriv p (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
  simpa [standardNormalMoment, mgf_id_gaussianReal, Pi.pow_apply] using
    (iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 1) (by simp) p).symm

private theorem deriv_standardNormalMGF :
    deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) = fun t => t * Real.exp (t ^ 2 / 2) := by
  funext t
  rw [deriv_exp (by fun_prop)]
  simp only [deriv_div_const, deriv_pow_field, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

theorem standardNormalMoment_succ_two (p : ℕ) :
    standardNormalMoment (p + 2) = (p + 1 : ℝ) * standardNormalMoment p := by
  rw [standardNormalMoment_eq_mgf_derivative, standardNormalMoment_eq_mgf_derivative,
    show p + 2 = (p + 1) + 1 by omega, iteratedDeriv_succ', deriv_standardNormalMGF]
  change iteratedDeriv (p + 1) (id * (fun t : ℝ => Real.exp (t ^ 2 / 2))) 0 = _
  rw [iteratedDeriv_mul (by fun_prop) (by fun_prop), Finset.sum_eq_single 1]
  · simp [iteratedDeriv_id]
  · intro i _ hi
    simp [iteratedDeriv_id, hi]
  · intro h
    simp at h

@[simp] theorem standardNormalMoment_zero : standardNormalMoment 0 = 1 := by
  simp [standardNormalMoment]

@[simp] theorem standardNormalMoment_one : standardNormalMoment 1 = 0 := by
  simp [standardNormalMoment]

@[simp] theorem standardNormalMoment_two : standardNormalMoment 2 = 1 := by
  simpa using standardNormalMoment_succ_two 0

@[simp] theorem standardNormalMoment_four : standardNormalMoment 4 = 3 := by
  have h := standardNormalMoment_succ_two 2
  norm_num at h
  exact h

theorem integrable_standardNormal_pow (p : ℕ) :
    Integrable (fun x : ℝ => x ^ p) (gaussianReal 0 1) := by
  simpa only [id_eq] using integrable_pow_of_mem_interior_integrableExpSet
    (X := id) (μ := gaussianReal 0 1) (by simp) p

end
end Wormald

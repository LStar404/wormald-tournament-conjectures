import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.Algebra.MvPolynomial

/-! Exact extraction of multivariate polynomial coefficients by normalized
torus Fourier integrals. No asymptotic assertion is used here. -/

namespace Wormald
noncomputable section
open MeasureTheory
open scoped BigOperators

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def polynomialTorusEval (p : MvPolynomial ι ℂ) (x : UnitAddTorus ι) : ℂ :=
  MvPolynomial.eval (fun i => fourier 1 (x i)) p

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_polynomialTorusEval (p : MvPolynomial ι ℂ) :
    Continuous (polynomialTorusEval p) := by
  exact p.continuous_eval.comp (continuous_pi fun i =>
    (fourier (T := (1 : ℝ)) 1).continuous.comp (continuous_apply i))

theorem fourier_one_pow (k : ℕ) (x : UnitAddCircle) :
    fourier 1 x ^ k = fourier (k : ℤ) x := by
  induction k with
  | zero => simp only [pow_zero, Nat.cast_zero, fourier_zero]
  | succ k ih => rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, fourier_add]

omit [DecidableEq ι] in
theorem polynomialTorusEval_monomial (s : ι →₀ ℕ) (a : ℂ) (x : UnitAddTorus ι) :
    polynomialTorusEval (MvPolynomial.monomial s a) x =
      a * UnitAddTorus.mFourier (fun i => (s i : ℤ)) x := by
  simp only [polynomialTorusEval, MvPolynomial.eval_monomial, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [fourier_one_pow]

omit [DecidableEq ι] in
theorem integral_mFourier_mul (n m : ι → ℤ) :
    (∫ x : UnitAddTorus ι, UnitAddTorus.mFourier (-n) x *
      UnitAddTorus.mFourier m x) = if n = m then 1 else 0 := by
  simpa only [ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg, mul_comm] using
    (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := ι))) n m

theorem polynomial_coeff_eq_torus_integral (p : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    p.coeff s = ∫ x : UnitAddTorus ι,
      UnitAddTorus.mFourier (fun i => -(s i : ℤ)) x * polynomialTorusEval p x := by
  induction p using MvPolynomial.induction_on' with
  | monomial t a =>
    simp only [polynomialTorusEval_monomial]
    simp_rw [mul_left_comm _ a]
    rw [integral_const_mul]
    change _ = a * ∫ x : UnitAddTorus ι,
      UnitAddTorus.mFourier (-(fun i => (s i : ℤ))) x *
        UnitAddTorus.mFourier (fun i => (t i : ℤ)) x
    rw [integral_mFourier_mul]
    by_cases h : s = t
    · subst t
      simp [MvPolynomial.coeff_monomial]
    · have h' : (fun i => (s i : ℤ)) ≠ (fun i => (t i : ℤ)) := by
        intro he
        apply h
        ext i
        exact_mod_cast congrFun he i
      simp [MvPolynomial.coeff_monomial, Ne.symm h, h']
  | add p q hp hq =>
    change p.coeff s + q.coeff s = _
    rw [hp, hq, ← integral_add]
    · congr 1
      funext x
      simp [polynomialTorusEval, mul_add]
    · exact ((UnitAddTorus.mFourier _).continuous.mul
        (continuous_polynomialTorusEval p)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    · exact ((UnitAddTorus.mFourier _).continuous.mul
        (continuous_polynomialTorusEval q)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)

theorem polynomial_coeff_eq_cube_integral (p : MvPolynomial ι ℂ) (s : ι →₀ ℕ)
    (a : ι → ℝ) :
    p.coeff s = ∫ x : ι → ℝ in {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)},
      UnitAddTorus.mFourier (fun i => -(s i : ℤ)) (fun i => (x i : UnitAddCircle)) *
        polynomialTorusEval p (fun i => (x i : UnitAddCircle)) := by
  rw [polynomial_coeff_eq_torus_integral, UnitAddTorus.integral_preimage _ a]

end
end Wormald

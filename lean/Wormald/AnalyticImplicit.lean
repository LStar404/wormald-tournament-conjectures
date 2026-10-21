import Wormald.Elimination
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Analytic calculus for the original implicit function

This module develops genuine Fréchet derivative formulas for polynomial
evaluation and the explicit eliminated function. It does not introduce
the desired Hessian identity as an assumption.
-/

namespace Wormald

noncomputable section

open MvPolynomial Matrix Filter Topology
open scoped BigOperators

def evalPolynomialComplex {σ : Type*} (p : MvPolynomial σ ℚ) (x : σ → ℂ) : ℂ :=
  eval₂ (Rat.castHom ℂ) x p

def polynomialGradient {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (x : σ → ℂ) : (σ → ℂ) →L[ℂ] ℂ :=
  ∑ j, evalPolynomialComplex (pderiv j p) x • ContinuousLinearMap.proj j

/-- Algebraic partial differentiation of a multivariate polynomial agrees
with the actual complex Fréchet derivative of its evaluation. -/
theorem hasFDerivAt_evalPolynomialComplex {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (x : σ → ℂ) :
    HasFDerivAt (evalPolynomialComplex p) (polynomialGradient p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hfun : evalPolynomialComplex (C a : MvPolynomial σ ℚ) =
        (fun _ : σ → ℂ => (a : ℂ)) := by
      funext y
      simp [evalPolynomialComplex]
    have hgrad : polynomialGradient (C a : MvPolynomial σ ℚ) x = 0 := by
      ext v
      simp [polynomialGradient, evalPolynomialComplex]
    rw [hfun, hgrad]
    exact hasFDerivAt_const (𝕜 := ℂ) (a : ℂ) x
  | add p q hp hq =>
    have hfun : evalPolynomialComplex (p + q) =
        evalPolynomialComplex p + evalPolynomialComplex q := by
      funext y
      simp [evalPolynomialComplex]
    have hgrad : polynomialGradient (p + q) x =
        polynomialGradient p x + polynomialGradient q x := by
      ext v
      simp [polynomialGradient, evalPolynomialComplex, add_mul,
        Finset.sum_add_distrib]
    rw [hfun, hgrad]
    exact hp.add hq
  | mul_X p j hp =>
    have hj : HasFDerivAt (fun y : σ → ℂ => y j) (ContinuousLinearMap.proj j) x :=
      (ContinuousLinearMap.proj j : (σ → ℂ) →L[ℂ] ℂ).hasFDerivAt
    have hfun : evalPolynomialComplex (p * X j) =
        evalPolynomialComplex p * (fun y : σ → ℂ => y j) := by
      funext y
      simp [evalPolynomialComplex]
    have hgrad : polynomialGradient (p * X j) x =
        evalPolynomialComplex p x • ContinuousLinearMap.proj j +
          x j • polynomialGradient p x := by
      apply ContinuousLinearMap.ext
      intro v
      simp [polynomialGradient, evalPolynomialComplex,
        Pi.single_apply, apply_ite, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, eq_comm]
      ring_nf
    rw [hfun, hgrad]
    exact hp.mul hj

theorem fderiv_evalPolynomialComplex {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (x : σ → ℂ) :
    fderiv ℂ (evalPolynomialComplex p) x = polynomialGradient p x :=
  (hasFDerivAt_evalPolynomialComplex p x).fderiv

theorem polynomialGradient_apply_single {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (x : σ → ℂ) (j : σ) :
    polynomialGradient p x (Pi.single j 1) = evalPolynomialComplex (pderiv j p) x := by
  simp [polynomialGradient, Pi.single_apply, eq_comm]

/-- Polynomial evaluation is genuinely smooth, including after restriction
from complex to real scalars. -/
theorem contDiff_evalPolynomialComplex {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (r : WithTop ℕ∞) :
    ContDiff ℂ r (fun x : σ → ℂ => evalPolynomialComplex p x) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [evalPolynomialComplex] using (contDiff_const (c := (a : ℂ)))
  | add p q hp hq =>
    simpa [evalPolynomialComplex] using hp.add hq
  | mul_X p j hp =>
    have hj : ContDiff ℂ r (fun y : σ → ℂ => y j) :=
      (ContinuousLinearMap.proj j : (σ → ℂ) →L[ℂ] ℂ).contDiff
    simpa [evalPolynomialComplex] using hp.mul hj

theorem hasFDerivAt_evalPolynomialComplex_comp
    {σ E : Type*} [Fintype σ] [DecidableEq σ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : MvPolynomial σ ℚ) (f : E → σ → ℂ)
    (f' : E →L[ℝ] (σ → ℂ)) (x : E) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => evalPolynomialComplex p (f y))
      (((polynomialGradient p (f x)).restrictScalars ℝ).comp f') x :=
  ((hasFDerivAt_evalPolynomialComplex p (f x)).restrictScalars ℝ).comp x hf

/-- The actual directional chain rule for a polynomial composed with a
real differentiable vector map. -/
theorem fderiv_evalPolynomialComplex_comp_apply
    {σ E : Type*} [Fintype σ] [DecidableEq σ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : MvPolynomial σ ℚ) (f : E → σ → ℂ) (x v : E)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => evalPolynomialComplex p (f y)) x v =
      ∑ j, evalPolynomialComplex (pderiv j p) (f x) * (fderiv ℝ f x v) j := by
  rw [(hasFDerivAt_evalPolynomialComplex_comp p f _ x hf.hasFDerivAt).fderiv]
  simp [polynomialGradient]

/-- The full second directional chain rule, derived from actual polynomial
evaluation and ordinary twice differentiability of the inner vector map. -/
theorem second_fderiv_evalPolynomialComplex_comp_apply
    {σ E : Type*} [Fintype σ] [DecidableEq σ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : MvPolynomial σ ℚ) (f : E → σ → ℂ) (x v w : E)
    (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (fun y => fderiv ℝ (fun t => evalPolynomialComplex p (f t)) y v) x w =
      ∑ a : σ, ((∑ b : σ, evalPolynomialComplex (pderiv b (pderiv a p)) (f x) *
          (fderiv ℝ f x w) b) * (fderiv ℝ f x v) a +
        evalPolynomialComplex (pderiv a p) (f x) *
          (fderiv ℝ (fun y : E => fderiv ℝ f y v) x w) a) := by
  have hdf : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by norm_num)).mono (fun y hy => hy.differentiableAt (by norm_num))
  have hD : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hDc (a : σ) : DifferentiableAt ℝ (fun y => (fderiv ℝ f y v) a) x :=
    (ContinuousLinearMap.proj a : (σ → ℂ) →L[ℝ] ℂ).differentiableAt.comp x hD
  have hpoly (a : σ) :
      DifferentiableAt ℝ (fun y => evalPolynomialComplex (pderiv a p) (f y)) x :=
    (hasFDerivAt_evalPolynomialComplex_comp (pderiv a p) f _ x hdf.hasFDerivAt).differentiableAt
  have heq : (fun y => fderiv ℝ (fun t => evalPolynomialComplex p (f t)) y v) =ᶠ[𝓝 x]
      (fun y => ∑ a : σ, evalPolynomialComplex (pderiv a p) (f y) * (fderiv ℝ f y v) a) :=
    hnear.mono fun y hy => fderiv_evalPolynomialComplex_comp_apply p f y v hy
  rw [heq.fderiv_eq]
  have hsum := fderiv_fun_sum (u := Finset.univ) (fun a _ => (hpoly a).mul (hDc a))
  simp only [Pi.mul_apply] at hsum
  rw [hsum]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [fderiv_mul (hpoly a) (hDc a)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [fderiv_evalPolynomialComplex_comp_apply (pderiv a p) f x w hdf]
  have hproj := ((ContinuousLinearMap.proj a : (σ → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp x
    hD.hasFDerivAt).fderiv
  simp only [Function.comp_def, ContinuousLinearMap.proj_apply] at hproj
  rw [hproj]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  ring

theorem contDiff_appendLast {n : ℕ} (a : ℂ) (r : WithTop ℕ∞) :
    ContDiff ℂ r (fun y : Fin n → ℂ => appendLast y a) := by
  apply contDiff_pi.mpr
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simpa [appendLast] using (contDiff_const (c := a))
  · simpa [appendLast] using
      (contDiff_apply ℂ ℂ k : ContDiff ℂ r (fun y : Fin n → ℂ => y k))

theorem contDiff_eliminatedNumerator {n : ℕ} (T : Tournament (n + 1))
    (r : WithTop ℕ∞) : ContDiff ℂ r (eliminatedNumerator T) := by
  have heq : eliminatedNumerator T =
      (fun y => evalPolynomialComplex (definingPolynomial T.adjacency) (appendLast y 0)) := by
    funext y
    exact (originalDeterminant_eq_polynomial_eval T _).symm
  rw [heq]
  exact (contDiff_evalPolynomialComplex _ r).comp (contDiff_appendLast 0 r)

theorem contDiff_eliminatedCoefficient {n : ℕ} (T : Tournament (n + 1))
    (r : WithTop ℕ∞) : ContDiff ℂ r (eliminatedCoefficient T) := by
  have hOne : ContDiff ℂ r (fun y : Fin n → ℂ => originalDeterminant T (appendLast y 1)) := by
    have heq : (fun y : Fin n → ℂ => originalDeterminant T (appendLast y 1)) =
        (fun y => evalPolynomialComplex (definingPolynomial T.adjacency) (appendLast y 1)) := by
      funext y
      exact (originalDeterminant_eq_polynomial_eval T _).symm
    rw [heq]
    exact (contDiff_evalPolynomialComplex _ r).comp (contDiff_appendLast 1 r)
  exact hOne.sub (contDiff_eliminatedNumerator T r)

/-- The explicitly eliminated function is genuinely smooth wherever its
actual denominator is nonzero; no implicit derivative formula is assumed. -/
theorem contDiffAt_originalImplicitFunction {n : ℕ} (T : Tournament (n + 1))
    (y : Fin n → ℂ) (hcoeff : eliminatedCoefficient T y ≠ 0) (r : WithTop ℕ∞) :
    ContDiffAt ℂ r (originalImplicitFunction T) y := by
  exact ((contDiff_eliminatedNumerator T r).contDiffAt.neg).div
    (contDiff_eliminatedCoefficient T r).contDiffAt hcoeff

theorem originalImplicitFunction_at_critical {n : ℕ} (T : Tournament (n + 1))
    (z : ℂ) (hcritical : originalDeterminant T (fun _ => z) = 0)
    (hcoeff : eliminatedCoefficient T (fun _ => z) ≠ 0) :
    originalImplicitFunction T (fun _ => z) = z := by
  have ha : appendLast (fun _ : Fin n => z) z = (fun _ : Fin (n + 1) => z) := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [appendLast]
  have heq := originalDeterminant_affine_last T (fun _ => z) z
  rw [ha, hcritical] at heq
  unfold originalImplicitFunction
  apply (div_eq_iff hcoeff).mpr
  linear_combination heq

/-- Real directional differentiation of the actual principal complex log.
The slit-plane condition supplies precisely its analytic branch hypothesis. -/
theorem fderiv_clog_comp_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℂ) (x v : E) (hg : DifferentiableAt ℝ g x)
    (hslit : g x ∈ Complex.slitPlane) :
    fderiv ℝ (fun y => Complex.log (g y)) x v = fderiv ℝ g x v / g x := by
  have heq := ((Complex.hasStrictFDerivAt_log_real hslit).hasFDerivAt.comp x
    hg.hasFDerivAt).fderiv
  simp only [Function.comp_def] at heq
  rw [heq]
  simp [div_eq_inv_mul]

/-- The actual second real derivative of the original complex log branch.
No equations for the first or second derivative are premises. -/
theorem second_fderiv_clog_comp_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℂ) (x v w : E) (hg : ContDiffAt ℝ 2 g x)
    (hslit : g x ∈ Complex.slitPlane) :
    fderiv ℝ (fun y => fderiv ℝ (fun t => Complex.log (g t)) y v) x w =
      (fderiv ℝ (fun y => fderiv ℝ g y v) x w * g x -
        fderiv ℝ g x v * fderiv ℝ g x w) / g x ^ 2 := by
  have hdf : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fun y => fderiv ℝ g y v) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by norm_num)).mono (fun y hy => hy.differentiableAt (by norm_num))
  have hnearSlit : ∀ᶠ y in 𝓝 x, g y ∈ Complex.slitPlane :=
    hg.continuousAt.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hslit)
  have heq : (fun y => fderiv ℝ (fun t => Complex.log (g t)) y v) =ᶠ[𝓝 x]
      (fun y => (g y)⁻¹ * fderiv ℝ g y v) := by
    filter_upwards [hnear, hnearSlit] with y hy hs
    rw [fderiv_clog_comp_apply g y v hy hs, div_eq_inv_mul]
  have hne := Complex.slitPlane_ne_zero hslit
  have hinv := (hasFDerivAt_inv' (𝕜 := ℝ) hne).comp x hdf.hasFDerivAt
  have hproduct := (hinv.mul hD.hasFDerivAt).fderiv
  simp only [Function.comp_def, Pi.mul_def] at hproduct
  rw [heq.fderiv_eq, hproduct]
  simp only [_root_.add_apply, _root_.smul_apply,
    smul_eq_mul, ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply]
  field_simp
  ring

/-- Appending the actual eliminated coordinate commutes with Fréchet
differentiation. -/
theorem fderiv_appendLast_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (f : E → Fin n → ℂ) (g : E → ℂ) (x v : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => appendLast (f y) (g y)) x v =
      appendLast (fderiv ℝ f x v) (fderiv ℝ g x v) := by
  have hcomp (a : Fin (n + 1)) :
      DifferentiableAt ℝ (fun y => appendLast (f y) (g y) a) x := by
    refine Fin.lastCases ?_ (fun k => ?_) a
    · simpa [appendLast] using hg
    · simpa [appendLast] using (differentiableAt_pi.mp hf k)
  rw [fderiv_pi hcomp]
  ext a
  refine Fin.lastCases ?_ (fun k => ?_) a
  · simp [appendLast]
  · simp [appendLast, fderiv_apply hf k]

end
end Wormald

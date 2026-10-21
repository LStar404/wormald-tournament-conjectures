import Wormald.AnalyticJetBridge

/-! Actual real first and second derivatives of a polynomial in exponential
coordinates. The logarithmic jets are derived from ordinary calculus. -/

namespace Wormald
noncomputable section
open MvPolynomial
open Filter Topology
open scoped BigOperators

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def exponentialCoordinates (z : ℂ) (g : E → Fin n → ℂ) (y : E) : Fin n → ℂ :=
  fun a => z * Complex.exp (g y a)

theorem contDiffAt_exponentialCoordinates (z : ℂ) (g : E → Fin n → ℂ)
    (x : E) (r : WithTop ℕ∞) (hg : ContDiffAt ℝ r g x) :
    ContDiffAt ℝ r (exponentialCoordinates z g) x := by
  apply contDiffAt_pi.mpr
  intro a
  exact contDiffAt_const.mul ((contDiffAt_pi.mp hg a).cexp)

private theorem hasFDerivAt_exponentialCoordinate (z : ℂ) (g : E → Fin n → ℂ)
    (x : E) (hg : DifferentiableAt ℝ g x) (a : Fin n) :
    HasFDerivAt (fun y => exponentialCoordinates z g y a)
      ((z * Complex.exp (g x a)) •
        ((ContinuousLinearMap.proj a : (Fin n → ℂ) →L[ℝ] ℂ).comp (fderiv ℝ g x))) x := by
  have hproj := (ContinuousLinearMap.proj a : (Fin n → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp x
    hg.hasFDerivAt
  simpa only [exponentialCoordinates, smul_smul, Function.comp_def,
    ContinuousLinearMap.proj_apply] using hproj.cexp.const_mul z

theorem fderiv_exponentialCoordinates_apply (z : ℂ) (g : E → Fin n → ℂ)
    (x v : E) (hg : DifferentiableAt ℝ g x) (a : Fin n) :
    (fderiv ℝ (exponentialCoordinates z g) x v) a =
      z * Complex.exp (g x a) * (fderiv ℝ g x v) a := by
  have h := hasFDerivAt_pi.mpr (hasFDerivAt_exponentialCoordinate z g x hg)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.pi_apply, _root_.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

theorem second_fderiv_exponentialCoordinates_apply (z : ℂ) (g : E → Fin n → ℂ)
    (x v w : E) (hg : ContDiffAt ℝ 2 g x) (a : Fin n) :
    (fderiv ℝ (fun y => fderiv ℝ (exponentialCoordinates z g) y v) x w) a =
      z * Complex.exp (g x a) * ((fderiv ℝ g x v) a * (fderiv ℝ g x w) a +
        (fderiv ℝ (fun y => fderiv ℝ g y v) x w) a) := by
  have hdiff : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fun y => fderiv ℝ g y v) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hDc (b : Fin n) : DifferentiableAt ℝ (fun y => (fderiv ℝ g y v) b) x :=
    (ContinuousLinearMap.proj b : (Fin n → ℂ) →L[ℝ] ℂ).differentiableAt.comp x hD
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by norm_num)).mono (fun y hy => hy.differentiableAt (by norm_num))
  have heq : (fun y => fderiv ℝ (exponentialCoordinates z g) y v) =ᶠ[𝓝 x]
      (fun y b => z * Complex.exp (g y b) * (fderiv ℝ g y v) b) := by
    filter_upwards [hnear] with y hy
    funext b
    exact fderiv_exponentialCoordinates_apply z g y v hy b
  rw [heq.fderiv_eq]
  have hExp (b : Fin n) := hasFDerivAt_exponentialCoordinate z g x hdiff b
  have hprod (b : Fin n) : DifferentiableAt ℝ
      (fun y => z * Complex.exp (g y b) * (fderiv ℝ g y v) b) x :=
    (hExp b).differentiableAt.mul (hDc b)
  rw [fderiv_pi hprod]
  simp only [ContinuousLinearMap.pi_apply]
  have hprodder := ((hExp a).mul (hDc a).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => z * Complex.exp (g y a) * (fderiv ℝ g y v) a) x = _ at hprodder
  rw [hprodder]
  have hproj := ((ContinuousLinearMap.proj a : (Fin n → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp x
    hD.hasFDerivAt).fderiv
  simp only [Function.comp_def, ContinuousLinearMap.proj_apply] at hproj
  rw [hproj]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, exponentialCoordinates]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem exponentialCoordinates_at_zero (z : ℂ) (g : E → Fin n → ℂ) (x : E)
    (hzero : g x = 0) : exponentialCoordinates z g x = (fun _ => z) := by
  funext a
  simp [exponentialCoordinates, hzero]

theorem fderiv_evalPolynomial_exponentialCoordinates_zero
    (p : MvPolynomial (Fin n) ℚ) (z : ℚ) (g : E → Fin n → ℂ) (x v : E)
    (hg : DifferentiableAt ℝ g x) (hzero : g x = 0) :
    fderiv ℝ (fun y => evalPolynomialComplex p (exponentialCoordinates (z : ℂ) g y)) x v =
      ∑ a, (firstLogJet p z a : ℂ) * (fderiv ℝ g x v) a := by
  have hcoords : DifferentiableAt ℝ (exponentialCoordinates (z : ℂ) g) x :=
    (hasFDerivAt_pi.mpr (hasFDerivAt_exponentialCoordinate (z : ℂ) g x hg)).differentiableAt
  rw [fderiv_evalPolynomialComplex_comp_apply p _ x v hcoords,
    exponentialCoordinates_at_zero _ _ _ hzero]
  apply Finset.sum_congr rfl
  intro a _
  rw [fderiv_exponentialCoordinates_apply _ _ _ _ hg]
  simp only [hzero, Pi.zero_apply, Complex.exp_zero, mul_one, evalPolynomialComplex_ratCast,
    firstLogJet, Rat.cast_mul]
  ring

theorem second_fderiv_evalPolynomial_exponentialCoordinates_zero
    (p : MvPolynomial (Fin n) ℚ) (z : ℚ) (g : E → Fin n → ℂ) (x v w : E)
    (hg : ContDiffAt ℝ 2 g x) (hzero : g x = 0) :
    fderiv ℝ (fun y => fderiv ℝ
      (fun t => evalPolynomialComplex p (exponentialCoordinates (z : ℂ) g t)) y v) x w =
      (∑ a, ∑ b, (secondLogJet p z a b : ℂ) *
        (fderiv ℝ g x v) a * (fderiv ℝ g x w) b) +
      ∑ a, (firstLogJet p z a : ℂ) *
        (fderiv ℝ (fun y => fderiv ℝ g y v) x w) a := by
  have hdiff : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  rw [second_fderiv_evalPolynomialComplex_comp_apply p _ x v w
      (contDiffAt_exponentialCoordinates _ _ _ _ hg),
    exponentialCoordinates_at_zero _ _ _ hzero]
  simp_rw [fderiv_exponentialCoordinates_apply _ _ _ _ hdiff,
    second_fderiv_exponentialCoordinates_apply _ _ _ _ _ hg]
  simp only [hzero, Pi.zero_apply, Complex.exp_zero, mul_one, evalPolynomialComplex_ratCast]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hquad : ((∑ b, (eval (fun _ => z) (pderiv b (pderiv a p)) : ℂ) *
      ((z : ℂ) * (fderiv ℝ g x w) b)) * ((z : ℂ) * (fderiv ℝ g x v) a)) =
      ∑ b, ((z : ℂ) ^ 2 * (eval (fun _ => z) (pderiv b (pderiv a p)) : ℂ)) *
        (fderiv ℝ g x v) a * (fderiv ℝ g x w) b := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hquad]
  have hdiag (b : Fin n) : ((if a = b then firstLogJet p z a else 0 : ℚ) : ℂ) =
      if a = b then (firstLogJet p z a : ℂ) else 0 := by
    split_ifs <;> simp
  simp only [secondLogJet, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, hdiag]
  simp only [firstLogJet, Rat.cast_mul, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
  simp
  ring

end
end Wormald

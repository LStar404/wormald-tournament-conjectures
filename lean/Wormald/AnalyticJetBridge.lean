import Wormald.AnalyticImplicit
import Wormald.AngleCalculus
import Wormald.ImplicitAlgebra

/-! The genuine analytic implicit surface, in Wormald's original real
angle variables. Every differential equation below is derived from the
original defining determinant. -/

namespace Wormald

noncomputable section
open MvPolynomial Matrix Filter Topology
open scoped BigOperators

def angularImplicitValue {n : ℕ} (T : Tournament (n + 1)) (z : ℂ)
    (θ : Fin n → ℝ) : ℂ := originalImplicitFunction T (angleCoordinates z θ)

def angularImplicitSurface {n : ℕ} (T : Tournament (n + 1)) (z : ℂ)
    (θ : Fin n → ℝ) : Fin (n + 1) → ℂ :=
  appendLast (angleCoordinates z θ) (angularImplicitValue T z θ)

theorem contDiffAt_angularImplicitValue {n : ℕ} (T : Tournament (n + 1)) (z : ℂ)
    (hcoeff : eliminatedCoefficient T (fun _ => z) ≠ 0) (r : WithTop ℕ∞) :
    ContDiffAt ℝ r (angularImplicitValue T z) 0 := by
  have hh := (contDiffAt_originalImplicitFunction T (fun _ => z) hcoeff r).restrict_scalars ℝ
  have hh' : ContDiffAt ℝ r (originalImplicitFunction T) (angleCoordinates (n := n) z 0) := by
    simpa using hh
  change ContDiffAt ℝ r (fun θ => originalImplicitFunction T (angleCoordinates z θ)) 0
  simpa only [Function.comp_def] using
    hh'.comp 0 (contDiff_angleCoordinates z r).contDiffAt

theorem contDiffAt_angularImplicitSurface {n : ℕ} (T : Tournament (n + 1)) (z : ℂ)
    (hcoeff : eliminatedCoefficient T (fun _ => z) ≠ 0) (r : WithTop ℕ∞) :
    ContDiffAt ℝ r (angularImplicitSurface T z) 0 := by
  apply contDiffAt_pi.mpr
  intro a
  refine Fin.lastCases ?_ (fun k => ?_) a
  · simpa [angularImplicitSurface, appendLast] using contDiffAt_angularImplicitValue T z hcoeff r
  · simpa [angularImplicitSurface, appendLast] using
      (contDiffAt_pi.mp (contDiff_angleCoordinates z r).contDiffAt k)

theorem angularImplicitValue_zero {n : ℕ} (T : Tournament (n + 1)) (z : ℂ)
    (hcritical : originalDeterminant T (fun _ => z) = 0)
    (hcoeff : eliminatedCoefficient T (fun _ => z) ≠ 0) :
    angularImplicitValue T z 0 = z := by
  simpa [angularImplicitValue] using originalImplicitFunction_at_critical T z hcritical hcoeff

theorem angularImplicitSurface_zero {n : ℕ} (T : Tournament (n + 1)) (z : ℂ)
    (hcritical : originalDeterminant T (fun _ => z) = 0)
    (hcoeff : eliminatedCoefficient T (fun _ => z) ≠ 0) :
    angularImplicitSurface T z 0 = fun _ => z := by
  unfold angularImplicitSurface
  rw [angleCoordinates_zero, angularImplicitValue_zero T z hcritical hcoeff]
  funext a
  refine Fin.lastCases ?_ (fun k => ?_) a <;> simp [appendLast]

theorem angularImplicitSurface_solves_near_zero {n : ℕ}
    (T : Tournament (n + 1)) (z : ℂ)
    (hcoeff : eliminatedCoefficient T (fun _ => z) ≠ 0) :
    (fun θ : Fin n → ℝ => evalPolynomialComplex (definingPolynomial T.adjacency)
      (angularImplicitSurface T z θ)) =ᶠ[𝓝 0] (fun _ => 0) := by
  have hc : ContinuousAt (fun θ : Fin n → ℝ => eliminatedCoefficient T (angleCoordinates z θ)) 0 :=
    (contDiff_eliminatedCoefficient T 1).continuous.continuousAt.comp
      (contDiff_angleCoordinates z 1).continuous.continuousAt
  have hn : eliminatedCoefficient T (angleCoordinates (n := n) z 0) ≠ 0 := by
    simpa using hcoeff
  filter_upwards [hc.eventually_ne hn] with θ hθ
  change eval₂ (Rat.castHom ℂ) _ (definingPolynomial T.adjacency) = 0
  rw [originalDeterminant_eq_polynomial_eval]
  exact originalImplicitFunction_solves T (angleCoordinates z θ) hθ

theorem fderiv_angularImplicitSurface_zero_single {n : ℕ}
    (T : Tournament (n + 1)) (z : ℂ)
    (hcoeff : eliminatedCoefficient T (fun _ => z) ≠ 0) (j : Fin n) :
    fderiv ℝ (angularImplicitSurface T z) 0 (Pi.single j 1) =
      appendLast (Pi.single j (Complex.I * z))
        (fderiv ℝ (angularImplicitValue T z) 0 (Pi.single j 1)) := by
  change fderiv ℝ (fun θ => appendLast (angleCoordinates z θ)
    (angularImplicitValue T z θ)) 0 (Pi.single j 1) = _
  rw [fderiv_appendLast_apply _ _ _ _
    ((contDiff_angleCoordinates z 1).contDiffAt.differentiableAt (by norm_num))
    ((contDiffAt_angularImplicitValue T z hcoeff 1).differentiableAt (by norm_num)),
    fderiv_angleCoordinates_zero_single]

theorem fderiv_angularImplicitValue_zero_single {n : ℕ}
    (T : Tournament (n + 1)) (z r : ℂ)
    (hcritical : originalDeterminant T (fun _ => z) = 0)
    (hcoeff : eliminatedCoefficient T (fun _ => z) ≠ 0)
    (hgrad : ∀ a : Fin (n + 1),
      evalPolynomialComplex (pderiv a (definingPolynomial T.adjacency)) (fun _ => z) = r)
    (hr : r ≠ 0) (j : Fin n) :
    fderiv ℝ (angularImplicitValue T z) 0 (Pi.single j 1) = -Complex.I * z := by
  have hsolve := angularImplicitSurface_solves_near_zero T z hcoeff
  have hzero : fderiv ℝ (fun θ => evalPolynomialComplex (definingPolynomial T.adjacency)
      (angularImplicitSurface T z θ)) 0 = 0 := by
    simpa using hsolve.fderiv_eq (𝕜 := ℝ)
  have hchain := fderiv_evalPolynomialComplex_comp_apply (definingPolynomial T.adjacency)
    (angularImplicitSurface T z) 0 (Pi.single j 1)
    ((contDiffAt_angularImplicitSurface T z hcoeff 1).differentiableAt (by norm_num))
  rw [hzero, angularImplicitSurface_zero T z hcritical hcoeff,
    fderiv_angularImplicitSurface_zero_single T z hcoeff j] at hchain
  simp only [_root_.zero_apply, hgrad] at hchain
  rw [Fin.sum_univ_castSucc] at hchain
  simp [appendLast, Pi.single_apply, mul_ite] at hchain
  apply mul_left_cancel₀ hr
  linear_combination -hchain

theorem second_fderiv_angularImplicitSurface_zero_single {n : ℕ}
    (T : Tournament (n + 1)) (z : ℂ)
    (hcoeff : eliminatedCoefficient T (fun _ => z) ≠ 0) (j k : Fin n) :
    fderiv ℝ (fun θ => fderiv ℝ (angularImplicitSurface T z) θ (Pi.single j 1)) 0
      (Pi.single k 1) =
      appendLast (fun a => if a = j ∧ a = k then -z else 0)
        (fderiv ℝ (fun θ => fderiv ℝ (angularImplicitValue T z) θ (Pi.single j 1)) 0
          (Pi.single k 1)) := by
  have hH := contDiffAt_angularImplicitValue T z hcoeff 2
  have hA := (contDiff_angleCoordinates (n := n) z 2).contDiffAt (x := 0)
  have hnear : ∀ᶠ θ in 𝓝 (0 : Fin n → ℝ), DifferentiableAt ℝ (angularImplicitValue T z) θ :=
    (hH.eventually (by norm_num)).mono (fun θ hθ => hθ.differentiableAt (by norm_num))
  have heq : (fun θ => fderiv ℝ (angularImplicitSurface T z) θ (Pi.single j 1)) =ᶠ[𝓝 0]
      (fun θ => appendLast (fderiv ℝ (angleCoordinates z) θ (Pi.single j 1))
        (fderiv ℝ (angularImplicitValue T z) θ (Pi.single j 1))) := by
    filter_upwards [hnear] with θ hθ
    exact fderiv_appendLast_apply _ _ θ _
      ((contDiff_angleCoordinates z 1).differentiable (by norm_num) θ) hθ
  have hDA : DifferentiableAt ℝ (fun θ => fderiv ℝ (angleCoordinates z) θ (Pi.single j 1)) 0 :=
    ((hA.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hDH : DifferentiableAt ℝ (fun θ => fderiv ℝ (angularImplicitValue T z) θ (Pi.single j 1)) 0 :=
    ((hH.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  rw [heq.fderiv_eq, fderiv_appendLast_apply _ _ _ _ hDA hDH,
    second_fderiv_angleCoordinates_zero_single]

theorem angularImplicit_second_equation {n : ℕ}
    (T : Tournament (n + 1)) (z r : ℂ)
    (hcritical : originalDeterminant T (fun _ => z) = 0)
    (hcoeff : eliminatedCoefficient T (fun _ => z) ≠ 0)
    (hgrad : ∀ a : Fin (n + 1),
      evalPolynomialComplex (pderiv a (definingPolynomial T.adjacency)) (fun _ => z) = r)
    (hr : r ≠ 0) (j k : Fin n) :
    0 = -z ^ 2 *
      (evalPolynomialComplex (pderiv k.castSucc (pderiv j.castSucc (definingPolynomial T.adjacency))) (fun _ => z) -
       evalPolynomialComplex (pderiv (Fin.last n) (pderiv j.castSucc (definingPolynomial T.adjacency))) (fun _ => z) -
       evalPolynomialComplex (pderiv k.castSucc (pderiv (Fin.last n) (definingPolynomial T.adjacency))) (fun _ => z) +
       evalPolynomialComplex (pderiv (Fin.last n) (pderiv (Fin.last n) (definingPolynomial T.adjacency))) (fun _ => z)) +
      r * (fderiv ℝ (fun θ => fderiv ℝ (angularImplicitValue T z) θ (Pi.single j 1)) 0
        (Pi.single k 1) - if j = k then z else 0) := by
  have hsolve := angularImplicitSurface_solves_near_zero T z hcoeff
  have hsolveFirst : (fun θ => fderiv ℝ (fun t => evalPolynomialComplex (definingPolynomial T.adjacency)
      (angularImplicitSurface T z t)) θ (Pi.single j 1)) =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [hsolve.fderiv (𝕜 := ℝ)] with θ hθ
    simp [hθ]
  have hzero : fderiv ℝ (fun θ => fderiv ℝ (fun t => evalPolynomialComplex (definingPolynomial T.adjacency)
      (angularImplicitSurface T z t)) θ (Pi.single j 1)) 0 = 0 := by
    simpa using hsolveFirst.fderiv_eq (𝕜 := ℝ)
  have htangent (a : Fin n) : fderiv ℝ (angularImplicitSurface T z) 0 (Pi.single a 1) =
      appendLast (fun b => if b = a then Complex.I * z else 0) (-Complex.I * z) := by
    rw [fderiv_angularImplicitSurface_zero_single T z hcoeff a,
      fderiv_angularImplicitValue_zero_single T z r hcritical hcoeff hgrad hr a]
    congr 1
    funext b
    by_cases hb : b = a
    · subst b
      simp
    · simp [hb]
  have hchain := second_fderiv_evalPolynomialComplex_comp_apply (definingPolynomial T.adjacency)
    (angularImplicitSurface T z) 0 (Pi.single j 1) (Pi.single k 1)
    (contDiffAt_angularImplicitSurface T z hcoeff 2)
  rw [hzero, angularImplicitSurface_zero T z hcritical hcoeff, htangent j, htangent k,
    second_fderiv_angularImplicitSurface_zero_single T z hcoeff j k] at hchain
  simp only [_root_.zero_apply] at hchain
  rw [Finset.sum_add_distrib,
    implicit_second_tangent_sum z j k
      (fun a b => evalPolynomialComplex (pderiv b (pderiv a (definingPolynomial T.adjacency)))
        (fun _ => z))] at hchain
  simp only [hgrad] at hchain
  rw [implicit_acceleration_sum] at hchain
  exact hchain

/-- The original real-angle log Hessian, calculated from the original
implicit determinant and equal, nonzero first polynomial partials. -/
theorem angularImplicit_log_hessian_formula {n : ℕ}
    (T : Tournament (n + 1)) (z r : ℂ)
    (hcritical : originalDeterminant T (fun _ => z) = 0)
    (hcoeff : eliminatedCoefficient T (fun _ => z) ≠ 0)
    (hgrad : ∀ a : Fin (n + 1),
      evalPolynomialComplex (pderiv a (definingPolynomial T.adjacency)) (fun _ => z) = r)
    (hr : r ≠ 0) (hslit : z ∈ Complex.slitPlane) (j k : Fin n) :
    fderiv ℝ (fun θ => fderiv ℝ (fun t => Complex.log (angularImplicitValue T z t)) θ
      (Pi.single j 1)) 0 (Pi.single k 1) =
      z * (evalPolynomialComplex (pderiv k.castSucc (pderiv j.castSucc (definingPolynomial T.adjacency))) (fun _ => z) -
       evalPolynomialComplex (pderiv (Fin.last n) (pderiv j.castSucc (definingPolynomial T.adjacency))) (fun _ => z) -
       evalPolynomialComplex (pderiv k.castSucc (pderiv (Fin.last n) (definingPolynomial T.adjacency))) (fun _ => z) +
       evalPolynomialComplex (pderiv (Fin.last n) (pderiv (Fin.last n) (definingPolynomial T.adjacency))) (fun _ => z)) / r +
      (if j = k then 1 else 0) + 1 := by
  have hvalue := angularImplicitValue_zero T z hcritical hcoeff
  have hlog := second_fderiv_clog_comp_apply (angularImplicitValue T z) 0
    (Pi.single j 1) (Pi.single k 1) (contDiffAt_angularImplicitValue T z hcoeff 2)
    (by rw [hvalue]; exact hslit)
  rw [hvalue, fderiv_angularImplicitValue_zero_single T z r hcritical hcoeff hgrad hr j,
    fderiv_angularImplicitValue_zero_single T z r hcritical hcoeff hgrad hr k] at hlog
  have hI : (-Complex.I * z) * (-Complex.I * z) = -z ^ 2 := by
    ring_nf
    simp [Complex.I_sq]
  rw [hI] at hlog
  rw [hlog]
  have heq := angularImplicit_second_equation T z r hcritical hcoeff hgrad hr j k
  have hz := Complex.slitPlane_ne_zero hslit
  by_cases hjk : j = k
  · simp only [hjk, ite_true] at heq ⊢
    field_simp [hz, hr]
    linear_combination -heq
  · simp only [hjk, ite_false] at heq ⊢
    field_simp [hz, hr]
    linear_combination -heq

theorem evalPolynomialComplex_ratCast {σ : Type*} (K : MvPolynomial σ ℚ) (z : ℚ) :
    evalPolynomialComplex K (fun _ => (z : ℂ)) = (eval (fun _ => z) K : ℂ) := by
  induction K using MvPolynomial.induction_on with
  | C a => simp [evalPolynomialComplex]
  | add p q hp hq =>
    simpa [evalPolynomialComplex] using congrArg₂ (fun a b : ℂ => a + b) hp hq
  | mul_X p j hp =>
    simpa [evalPolynomialComplex] using congrArg (fun a : ℂ => a * (z : ℂ)) hp

theorem angularHessianJet_eq_implicit_formula {n : ℕ}
    (K : MvPolynomial (Fin (n + 1)) ℚ) (z r : ℚ) (hz : z ≠ 0) (hr : r ≠ 0)
    (hgrad : ∀ a, eval (fun _ => z) (pderiv a K) = r) (j k : Fin n) :
    angularHessianJet K z (Fin.last n) j.castSucc k.castSucc =
      z * (eval (fun _ => z) (pderiv k.castSucc (pderiv j.castSucc K)) -
        eval (fun _ => z) (pderiv (Fin.last n) (pderiv j.castSucc K)) -
        eval (fun _ => z) (pderiv k.castSucc (pderiv (Fin.last n) K)) +
        eval (fun _ => z) (pderiv (Fin.last n) (pderiv (Fin.last n) K))) / r +
      (if j = k then 1 else 0) + 1 := by
  have hjp : j.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last j).ne
  have hpk : Fin.last n ≠ k.castSucc := (Fin.castSucc_lt_last k).ne'
  by_cases hjk : j = k
  · simp [angularHessianJet, secondLogJet, firstLogJet, hgrad, hpk, hjk]
    field_simp
    ring
  · simp [angularHessianJet, secondLogJet, firstLogJet, hgrad, hjp, hpk, hjk]
    field_simp
    ring

/-- The original analytic Hessian agrees with the exact algebraic angular
jet, under only the actual critical-point, denominator and gradient facts.
No first- or second-derivative equation is assumed. -/
theorem analyticJetBridge_of_critical {n : ℕ} (T : Tournament (n + 1))
    (hcritical : originalDeterminant T (fun _ => 2 / ((n + 1 : ℕ) : ℂ)) = 0)
    (hcoeff : eliminatedCoefficient T (fun _ => 2 / ((n + 1 : ℕ) : ℂ)) ≠ 0)
    (hgrad : ∀ a : Fin (n + 1),
      eval (fun _ => 2 / ((n + 1 : ℕ) : ℚ)) (pderiv a (definingPolynomial T.adjacency)) =
      eval (fun _ => 2 / ((n + 1 : ℕ) : ℚ))
        (pderiv (Fin.last n) (definingPolynomial T.adjacency)))
    (hgradne : eval (fun _ => 2 / ((n + 1 : ℕ) : ℚ))
      (pderiv (Fin.last n) (definingPolynomial T.adjacency)) ≠ 0) :
    AnalyticJetBridge T := by
  let z : ℚ := 2 / ((n + 1 : ℕ) : ℚ)
  let r : ℚ := eval (fun _ => z) (pderiv (Fin.last n) (definingPolynomial T.adjacency))
  have hzpos : 0 < z := by dsimp [z]; positivity
  have hz : z ≠ 0 := ne_of_gt hzpos
  have hr : r ≠ 0 := hgradne
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hc : originalDeterminant T (fun _ => (z : ℂ)) = 0 := by
    simpa [z] using hcritical
  have hk : eliminatedCoefficient T (fun _ => (z : ℂ)) ≠ 0 := by
    simpa [z] using hcoeff
  have hg (a : Fin (n + 1)) :
      evalPolynomialComplex (pderiv a (definingPolynomial T.adjacency)) (fun _ => (z : ℂ)) =
        (r : ℂ) := by
    rw [evalPolynomialComplex_ratCast]
    exact_mod_cast hgrad a
  have hslit : (z : ℂ) ∈ Complex.slitPlane := by
    have hzr : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hzpos
    simpa using (Complex.ofReal_mem_slitPlane.mpr hzr)
  have hfun : originalAngularFunction T =
      (fun θ => Complex.log (angularImplicitValue T (z : ℂ) θ)) := by
    funext θ
    unfold originalAngularFunction angularImplicitValue
    apply congrArg Complex.log
    apply congrArg (originalImplicitFunction T)
    funext j
    simp [angleCoordinates, z]
  intro j k
  unfold originalAngularHessian
  rw [hfun, angularImplicit_log_hessian_formula T (z : ℂ) (r : ℂ) hc hk hg hrC hslit j k]
  change _ = (angularHessianJet (definingPolynomial T.adjacency) z (Fin.last n)
    j.castSucc k.castSucc : ℂ)
  rw [angularHessianJet_eq_implicit_formula (definingPolynomial T.adjacency) z r hz hr hgrad j k]
  push_cast
  simp only [evalPolynomialComplex_ratCast]
  by_cases hjk : j = k <;> simp [hjk]

#print axioms analyticJetBridge_of_critical

end
end Wormald

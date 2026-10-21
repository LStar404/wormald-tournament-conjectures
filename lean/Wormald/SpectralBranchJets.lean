import Wormald.LocalSpectralBranch
import Wormald.CenteredSpectralJet
import Wormald.ExponentialJetCalculus

namespace Wormald
noncomputable section
open scoped BigOperators Topology
open Matrix MvPolynomial Filter

/-- Real angles with the final angle fixed to zero, as an actual linear map. -/
def realAnchoredAngles (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℂ) :=
  ContinuousLinearMap.pi fun a => Fin.lastCases 0
    (fun j => Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)) a

theorem realAnchoredAngles_apply {n : ℕ} (θ : Fin n → ℝ) :
    realAnchoredAngles n θ = appendLast (fun j => (θ j : ℂ)) 0 := by
  ext a
  refine Fin.lastCases ?_ (fun j => ?_) a <;> simp [realAnchoredAngles, appendLast]

theorem realAnchoredAngles_single {n : ℕ} (j : Fin n) :
    realAnchoredAngles n (Pi.single j 1) = Pi.single j.castSucc 1 := by
  rw [realAnchoredAngles_apply]
  ext a
  refine Fin.lastCases ?_ (fun k => ?_) a
  · simp [appendLast, Pi.single_apply]
  · by_cases hk : k = j
    · subst k; simp [appendLast]
    · simp [appendLast, Pi.single_apply, hk]

def complexifyAngles (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun j => Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)

def Tournament.realLogSpectralBranch {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) (θ : Fin n → ℝ) : ℂ :=
  T.logSpectralBranch hT (complexifyAngles n θ)

@[simp] theorem Tournament.realLogSpectralBranch_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : T.realLogSpectralBranch hT 0 = 0 := by
  simp only [Tournament.realLogSpectralBranch, map_zero, T.logSpectralBranch_zero hT]

theorem Tournament.contDiffAt_realLogSpectralBranch {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : ContDiffAt ℝ 2 (T.realLogSpectralBranch hT) 0 := by
  have hs := (T.contDiffAt_logSpectralBranch hT).restrict_scalars ℝ
  have hs' : ContDiffAt ℝ 2 (T.logSpectralBranch hT) (complexifyAngles n 0) := by
    simpa only [map_zero] using hs
  exact hs'.comp 0 (complexifyAngles n).contDiff.contDiffAt

def Tournament.spectralLogCoordinates {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) (θ : Fin n → ℝ) : Fin (n + 1) → ℂ :=
  fun a => Complex.I * realAnchoredAngles n θ a - T.realLogSpectralBranch hT θ

@[simp] theorem Tournament.spectralLogCoordinates_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : T.spectralLogCoordinates hT 0 = 0 := by
  ext a
  simp [Tournament.spectralLogCoordinates]

theorem Tournament.contDiffAt_spectralLogCoordinates {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : ContDiffAt ℝ 2 (T.spectralLogCoordinates hT) 0 := by
  apply contDiffAt_pi.mpr
  intro a
  have hlin : ContDiff ℝ 2 (fun θ : Fin n → ℝ => realAnchoredAngles n θ a) :=
    ((ContinuousLinearMap.proj a).comp (realAnchoredAngles n)).contDiff
  exact (contDiffAt_const.mul hlin.contDiffAt).sub (T.contDiffAt_realLogSpectralBranch hT)

theorem Tournament.fderiv_spectralLogCoordinates_apply {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) (θ v : Fin n → ℝ)
    (hs : DifferentiableAt ℝ (T.realLogSpectralBranch hT) θ) (a : Fin (n + 1)) :
    (fderiv ℝ (T.spectralLogCoordinates hT) θ v) a =
      Complex.I * realAnchoredAngles n v a - fderiv ℝ (T.realLogSpectralBranch hT) θ v := by
  have hcoord (a : Fin (n + 1)) : HasFDerivAt
      (fun θ : Fin n → ℝ => Complex.I * realAnchoredAngles n θ a - T.realLogSpectralBranch hT θ)
      (Complex.I • ((ContinuousLinearMap.proj a).comp (realAnchoredAngles n)) -
        fderiv ℝ (T.realLogSpectralBranch hT) θ) θ :=
    (((ContinuousLinearMap.proj a).comp (realAnchoredAngles n)).hasFDerivAt.const_mul
      Complex.I).sub hs.hasFDerivAt
  have h := (hasFDerivAt_pi.mpr hcoord).fderiv
  rw [show fderiv ℝ (T.spectralLogCoordinates hT) θ = _ from h]
  simp

theorem Tournament.second_fderiv_spectralLogCoordinates_apply {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) (v w : Fin n → ℝ) (a : Fin (n + 1)) :
    (fderiv ℝ (fun θ => fderiv ℝ (T.spectralLogCoordinates hT) θ v) 0 w) a =
      -fderiv ℝ (fun θ => fderiv ℝ (T.realLogSpectralBranch hT) θ v) 0 w := by
  have hs := T.contDiffAt_realLogSpectralBranch hT
  have hnear : ∀ᶠ θ in 𝓝 0, DifferentiableAt ℝ (T.realLogSpectralBranch hT) θ :=
    (hs.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))
  have heq : (fun θ => fderiv ℝ (T.spectralLogCoordinates hT) θ v) =ᶠ[𝓝 0]
      (fun θ => fun a => Complex.I * realAnchoredAngles n v a -
        fderiv ℝ (T.realLogSpectralBranch hT) θ v) := by
    filter_upwards [hnear] with θ hθ
    funext a
    exact T.fderiv_spectralLogCoordinates_apply hT θ v hθ a
  have hds : DifferentiableAt ℝ
      (fun θ => fderiv ℝ (T.realLogSpectralBranch hT) θ v) 0 :=
    ((hs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  rw [heq.fderiv_eq]
  have hp := hasFDerivAt_pi.mpr (fun a : Fin (n + 1) =>
    hds.hasFDerivAt.const_sub (Complex.I * realAnchoredAngles n v a))
  rw [hp.fderiv]
  simp

theorem Tournament.spectralLogCoordinates_solves {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) :
    (fun θ : Fin n → ℝ => evalPolynomialComplex (definingPolynomial T.adjacency)
      (exponentialCoordinates (2 / ((n + 1 : ℕ) : ℚ) : ℚ)
        (T.spectralLogCoordinates hT) θ)) =ᶠ[𝓝 0] (fun _ => 0) := by
  have ht : Tendsto (complexifyAngles n) (𝓝 0) (𝓝 0) := by
    have h := (complexifyAngles n).continuous.continuousAt (x := (0 : Fin n → ℝ)) |>.tendsto
    rw [(complexifyAngles n).map_zero] at h
    exact h
  filter_upwards [ht.eventually (T.logSpectralBranch_solves hT)] with θ hθ
  have heq : exponentialCoordinates (2 / ((n + 1 : ℕ) : ℚ) : ℚ)
      (T.spectralLogCoordinates hT) θ =
      radialAngleCoordinates (2 / ((n + 1 : ℕ) : ℂ))
        (complexifyAngles n θ, T.realLogSpectralBranch hT θ) := by
    ext a
    simp only [exponentialCoordinates, Tournament.spectralLogCoordinates,
      radialAngleCoordinates, realAnchoredAngles_apply, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_natCast]
    rfl
  rw [heq]
  exact hθ

/-- The first derivative of the actual logarithmic eigenvalue is the mean phase. -/
theorem Tournament.fderiv_realLogSpectralBranch_zero_single {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) (j : Fin n) :
    fderiv ℝ (T.realLogSpectralBranch hT) 0 (Pi.single j 1) =
      Complex.I / ((n + 1 : ℕ) : ℂ) := by
  have hsolve := T.spectralLogCoordinates_solves hT
  have hzero : fderiv ℝ (fun θ => evalPolynomialComplex (definingPolynomial T.adjacency)
      (exponentialCoordinates (2 / ((n + 1 : ℕ) : ℚ) : ℚ)
        (T.spectralLogCoordinates hT) θ)) 0 = 0 := by
    simpa using hsolve.fderiv_eq (𝕜 := ℝ)
  have hg := T.contDiffAt_spectralLogCoordinates hT
  have hs := (T.contDiffAt_realLogSpectralBranch hT).differentiableAt (by norm_num)
  have hchain := fderiv_evalPolynomial_exponentialCoordinates_zero
    (definingPolynomial T.adjacency) (2 / ((n + 1 : ℕ) : ℚ))
    (T.spectralLogCoordinates hT) 0 (Pi.single j 1) (hg.differentiableAt (by norm_num))
    (T.spectralLogCoordinates_zero hT)
  rw [hzero] at hchain
  simp only [_root_.zero_apply, firstLogJet_cast_critical T hT (Nat.succ_ne_zero n)] at hchain
  simp_rw [T.fderiv_spectralLogCoordinates_apply hT 0 (Pi.single j 1) hs,
    realAnchoredAngles_single] at hchain
  simp only [Pi.single_apply, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hchain
  have hd : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hr : -T.criticalDet / ((n + 1 : ℕ) : ℂ) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr T.criticalDet_ne_zero) hd
  apply (eq_div_iff hd).mpr
  apply mul_left_cancel₀ hr
  linear_combination hchain

theorem Tournament.fderiv_spectralLogCoordinates_zero_single {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) (j : Fin n) :
    fderiv ℝ (T.spectralLogCoordinates hT) 0 (Pi.single j 1) =
      fun a => Complex.I * centeredBasis j.castSucc a := by
  ext a
  rw [T.fderiv_spectralLogCoordinates_apply hT 0 (Pi.single j 1)
    ((T.contDiffAt_realLogSpectralBranch hT).differentiableAt (by norm_num)),
    realAnchoredAngles_single, T.fderiv_realLogSpectralBranch_zero_single hT j]
  simp only [Pi.single_apply, centeredBasis]
  ring

/-- The actual second derivative gives the anchored covariance kernel. -/
theorem Tournament.second_fderiv_realLogSpectralBranch_zero_single {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) (j k : Fin n) :
    fderiv ℝ (fun θ => fderiv ℝ (T.realLogSpectralBranch hT) θ (Pi.single j 1)) 0
      (Pi.single k 1) =
      -(T.complexResolventCore j.castSucc k.castSucc - 1 / ((n + 1 : ℕ) : ℂ)) /
        ((n + 1 : ℕ) : ℂ) := by
  have hsolve := T.spectralLogCoordinates_solves hT
  have hsolveFirst : (fun θ => fderiv ℝ (fun t => evalPolynomialComplex
      (definingPolynomial T.adjacency) (exponentialCoordinates
        (2 / ((n + 1 : ℕ) : ℚ) : ℚ) (T.spectralLogCoordinates hT) t)) θ
          (Pi.single j 1)) =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [hsolve.fderiv (𝕜 := ℝ)] with θ hθ
    have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℂ => L (Pi.single j 1)) hθ
    simpa using h
  have hzero : fderiv ℝ (fun θ => fderiv ℝ (fun t => evalPolynomialComplex
      (definingPolynomial T.adjacency) (exponentialCoordinates
        (2 / ((n + 1 : ℕ) : ℚ) : ℚ) (T.spectralLogCoordinates hT) t)) θ
          (Pi.single j 1)) 0 = 0 := by
    simpa using hsolveFirst.fderiv_eq (𝕜 := ℝ)
  have hchain := second_fderiv_evalPolynomial_exponentialCoordinates_zero
    (definingPolynomial T.adjacency) (2 / ((n + 1 : ℕ) : ℚ))
    (T.spectralLogCoordinates hT) 0 (Pi.single j 1) (Pi.single k 1)
    (T.contDiffAt_spectralLogCoordinates hT) (T.spectralLogCoordinates_zero hT)
  rw [hzero, T.fderiv_spectralLogCoordinates_zero_single hT j,
    T.fderiv_spectralLogCoordinates_zero_single hT k] at hchain
  simp_rw [T.second_fderiv_spectralLogCoordinates_apply hT] at hchain
  let d : ℂ := ((n + 1 : ℕ) : ℂ)
  let u := fderiv ℝ (fun θ => fderiv ℝ (T.realLogSpectralBranch hT) θ (Pi.single j 1))
    0 (Pi.single k 1)
  have hquad : (∑ a, ∑ b,
      (secondLogJet (definingPolynomial T.adjacency) (2 / ((n + 1 : ℕ) : ℚ)) a b : ℂ) *
      (Complex.I * centeredBasis j.castSucc a) * (Complex.I * centeredBasis k.castSucc b)) =
      T.criticalDet / d * (T.complexResolventCore j.castSucc k.castSucc - 1 / d) := by
    rw [← T.secondLogJet_centered hT (Nat.succ_ne_zero n) j.castSucc k.castSucc]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hacc : (∑ a : Fin (n + 1),
      (firstLogJet (definingPolynomial T.adjacency) (2 / ((n + 1 : ℕ) : ℚ)) a : ℂ) * -u) =
      T.criticalDet * u := by
    simp only [firstLogJet_cast_critical T hT (Nat.succ_ne_zero n), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hd : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
  rw [hquad, hacc] at hchain
  simp only [_root_.zero_apply] at hchain
  apply mul_left_cancel₀ T.criticalDet_ne_zero
  linear_combination -hchain

end
end Wormald

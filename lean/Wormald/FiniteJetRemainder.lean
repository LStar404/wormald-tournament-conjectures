import Wormald.SecondOrderRemainder
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Coordinate checks of a genuine C² function determine its full second
derivative and hence its multivariate quadratic remainder. -/

namespace Wormald
noncomputable section
open Filter Topology
open scoped BigOperators

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuousLinearMap_eq_zero_of_single (L : (Fin n → ℝ) →L[ℝ] F)
    (hL : ∀ j, L (Pi.single j 1) = 0) : L = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ j, v j • Pi.single j 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, hL, smul_zero, Finset.sum_const_zero, _root_.zero_apply]

theorem second_fderiv_eq_zero_of_single (f : (Fin n → ℝ) → F)
    (hf : ContDiffAt ℝ 2 f 0)
    (hsecond : ∀ j k, fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) 0
      (Pi.single k 1) = 0) : fderiv ℝ (fderiv ℝ f) 0 = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  apply continuousLinearMap_eq_zero_of_single
  intro k
  apply continuousLinearMap_eq_zero_of_single
  intro j
  have heq := fderiv_clm_apply hd
    (differentiableAt_const (c := Pi.single j (1 : ℝ)))
  have h := hsecond j k
  rw [heq] at h
  simpa using h

theorem isLittleO_norm_sq_of_zero_coordinate_jets (f : (Fin n → ℝ) → F)
    (hf : ContDiffAt ℝ 2 f 0) (hzero : f 0 = 0)
    (hfirst : fderiv ℝ f 0 = 0)
    (hsecond : ∀ j k, fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) 0
      (Pi.single k 1) = 0) :
    f =o[𝓝 0] (fun y => ‖y‖ ^ 2) :=
  isLittleO_norm_sq_of_zero_second_jet f hf hzero hfirst
    (second_fderiv_eq_zero_of_single f hf hsecond)

end
end Wormald

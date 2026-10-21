import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! A multivariate second-order Taylor remainder derived from the derivative
remainder and the mean-value inequality on a small convex ball. -/

namespace Wormald
noncomputable section
open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isLittleO_norm_sq_of_zero_second_jet (f : E → F)
    (hf : ContDiffAt ℝ 2 f 0) (hzero : f 0 = 0)
    (hfirst : fderiv ℝ f 0 = 0) (hsecond : fderiv ℝ (fderiv ℝ f) 0 = 0) :
    f =o[𝓝 (0 : E)] (fun y => ‖y‖ ^ 2) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hl : (fderiv ℝ f) =o[𝓝 (0 : E)] (fun y => ‖y‖) := by
    rw [Asymptotics.isLittleO_norm_right]
    simpa only [hfirst, hsecond, sub_zero, _root_.zero_apply] using
      hd.hasFDerivAt.isLittleO
  have hdiff : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ f y :=
    (hf.eventually (by norm_num)).mono fun _ hy => hy.differentiableAt (by norm_num)
  obtain ⟨ε, hε, hεdiff⟩ := Metric.mem_nhds_iff.mp hdiff
  have hh := (convex_ball (0 : E) ε).isLittleO_pow_succ (n := 1)
    (Metric.mem_ball_self hε)
    (fun y hy => (hεdiff hy).hasFDerivAt.hasFDerivWithinAt)
    (by simpa only [sub_zero, pow_one] using hl.mono nhdsWithin_le_nhds)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds (0 : E) hε)] at hh
  simpa only [hzero, sub_zero] using hh

end
end Wormald

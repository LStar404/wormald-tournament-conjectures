import Wormald.GaussianCentralWindow
import Wormald.CentralGaussianRadius

namespace Wormald
noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology

def quarticFactorSquareError (m : ℕ) : ℝ :=
  ∫ x : Fin m → ℝ, (gaussianQuarticFactor m x - Real.exp (-(1 / 2 : ℝ))) ^ 2
    ∂Measure.pi (fun _ => gaussianReal 0 1)

theorem quarticFactorSquareError_nonneg (m : ℕ) : 0 ≤ quarticFactorSquareError m :=
  integral_nonneg fun _ => sq_nonneg _

theorem tendsto_quarticFactorSquareError :
    Tendsto quarticFactorSquareError atTop (𝓝 0) := tendsto_finiteGaussian_quartic_factor_sq

theorem memLp_graphGaussianWeight_centralScale {m : ℕ} (hm : 16 ≤ m)
    (G : GaussianGraphData m) :
    MemLp (graphGaussianWeight G (1 / (m : ℝ))) 2
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hm16 : 16 ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  exact memLp_graphGaussianWeight G _ (by positivity)
    (by rw [mul_one_div, div_lt_one hm0]; linarith)

theorem graphQuarticWeight_L2_le {m : ℕ} (hm : 16 ≤ m) (G : GaussianGraphData m) :
    (∫ x, ‖graphQuarticWeight G x‖ ^ 2 ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      Real.exp 4 := by
  have hw := memLp_graphGaussianWeight_centralScale hm G
  have hq := memLp_graphQuarticWeight hm G
  apply le_trans _ (graphGaussianWeight_L2_le hm G)
  apply integral_mono
    ((memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mp hq)
    ((memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw)
  intro x
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_graphQuarticWeight_le G x) 2

theorem norm_integral_graphQuarticWeight_mean_error {m : ℕ} (hm : 16 ≤ m)
    (G : GaussianGraphData m) :
    ‖(∫ x, graphQuarticWeight G x ∂Measure.pi (fun _ => gaussianReal 0 1)) -
      (Real.exp (-(1 / 2 : ℝ)) * Real.exp (graphGaussianLogFactor G (1 / (m : ℝ))) : ℂ)‖ ≤
        Real.sqrt (Real.exp 4) * Real.sqrt (quarticFactorSquareError m) := by
  have hw := memLp_graphGaussianWeight_centralScale hm G
  have hwi := hw.integrable (by norm_num)
  have hqi := (memLp_graphQuarticWeight hm G).integrable (by norm_num)
  have hm16 : 16 ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have heq : (∫ x, graphGaussianWeight G (1 / (m : ℝ)) x *
      ((gaussianQuarticFactor m x - Real.exp (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      (∫ x, graphQuarticWeight G x ∂Measure.pi (fun _ => gaussianReal 0 1)) -
        (Real.exp (-(1 / 2 : ℝ)) * Real.exp (graphGaussianLogFactor G (1 / (m : ℝ))) : ℂ) := by
    simp only [Complex.ofReal_sub, mul_sub]
    change (∫ x, graphQuarticWeight G x -
      graphGaussianWeight G (1 / (m : ℝ)) x * (Real.exp (-(1 / 2 : ℝ)) : ℂ)
        ∂Measure.pi (fun _ => gaussianReal 0 1)) = _
    rw [integral_sub hqi (hwi.mul_const _), integral_mul_const,
      integral_graphGaussianWeight G _ (by positivity)
        (by rw [mul_one_div, div_lt_one hm0]; linarith)]
    push_cast
    ring
  rw [← heq]
  exact norm_integral_graph_quartic_error_le hm G

theorem norm_integral_graphQuarticWeight_outside_le {m : ℕ} (hm : 16 ≤ m)
    (G : GaussianGraphData m) (j : Fin m) :
    ‖∫ x in (gaussianCentralWindow j (centralGaussianRadius m))ᶜ,
      graphQuarticWeight G x ∂Measure.pi (fun _ => gaussianReal 0 1)‖ ≤
        Real.sqrt (Real.exp 4) * Real.sqrt (centralGaussianTail m) := by
  have h := norm_setIntegral_le_sqrt_L2 (memLp_graphQuarticWeight hm G)
    (gaussianCentralWindow j (centralGaussianRadius m))ᶜ
  exact h.trans (mul_le_mul
    (Real.sqrt_le_sqrt (graphQuarticWeight_L2_le hm G))
    (Real.sqrt_le_sqrt (gaussianCentralWindow_compl_measure_le j _ (centralGaussianRadius_nonneg m)))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end
end Wormald

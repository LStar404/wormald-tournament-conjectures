import Wormald.GaussianQuarticMean

namespace Wormald
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem graph_joinCount_le_edgeCount {m : ℕ} (G : GaussianGraphData m) :
    G.joinCount ≤ G.edgeCount := by
  have hp : 0 ≤ G.imbalance ⬝ᵥ G.imbalance :=
    Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  rw [G.imbalance_square] at hp
  have hcast : (G.joinCount : ℝ) ≤ G.edgeCount := by linarith
  exact_mod_cast hcast

theorem norm_integral_graphGaussianWeight_main_error_le {m : ℕ}
    (hm : 16 ≤ m) (G : GaussianGraphData m) :
    ‖(∫ x, graphGaussianWeight G (1 / (m : ℝ)) x ∂Measure.pi (fun _ => gaussianReal 0 1)) -
      (Real.exp (G.joinCount / (m : ℝ)) : ℂ)‖ ≤ Real.exp 1 * (32 / (m : ℝ)) := by
  have hm16 : 16 ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have hj : (G.joinCount : ℝ) ≤ m := by
    exact_mod_cast (graph_joinCount_le_edgeCount G).trans G.edges_le
  have hle : Real.exp (G.joinCount / (m : ℝ)) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr ((div_le_one hm0).mpr hj)
  rw [integral_graphGaussianWeight G _ (by positivity)
    (by rw [mul_one_div, div_lt_one hm0]; linarith),
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hid : Real.exp (graphGaussianLogFactor G (1 / (m : ℝ))) -
      Real.exp (G.joinCount / (m : ℝ)) =
      Real.exp (G.joinCount / (m : ℝ)) *
        (Real.exp (graphGaussianLogFactor G (1 / (m : ℝ)) - G.joinCount / (m : ℝ)) - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    congr 1
    ring
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul hle (graphGaussian_relative_error_le hm G) (abs_nonneg _) (Real.exp_pos _).le

end
end Wormald

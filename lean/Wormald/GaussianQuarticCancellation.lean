import Wormald.GaussianQuarticConcentration
import Wormald.GaussianGraphFourierIntegral
import Wormald.WeightedL2Cancellation

/-! The quartic factor is common to the numerator and denominator. Its
Gaussian L² concentration cancels it uniformly for every allowed graph,
including the complex endpoint phase. -/

namespace Wormald
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology

def gaussianQuarticFactor (m : ℕ) (x : Fin m → ℝ) : ℝ :=
  Real.exp (-(completeQuarticEnergy x / (12 * (m : ℝ) ^ 2)))

theorem continuous_gaussianQuarticFactor (m : ℕ) : Continuous (gaussianQuarticFactor m) := by
  unfold gaussianQuarticFactor completeQuarticEnergy
  fun_prop

theorem gaussianQuarticFactor_mem_unitInterval (m : ℕ) (x : Fin m → ℝ) :
    gaussianQuarticFactor m x ∈ Set.Icc 0 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    unfold completeQuarticEnergy
    apply neg_nonpos.mpr
    positivity

theorem memLp_gaussianQuarticError (m : ℕ) :
    MemLp (fun x => gaussianQuarticFactor m x - Real.exp (-(1 / 2 : ℝ))) 2
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  apply MemLp.of_bound ((continuous_gaussianQuarticFactor m).sub continuous_const).aestronglyMeasurable 2
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    dsimp only [Pi.sub_apply]
    have hq := gaussianQuarticFactor_mem_unitInterval m x
    have hc0 := Real.exp_pos (-(1 / 2 : ℝ))
    have hc1 : Real.exp (-(1 / 2 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    exact abs_le.mpr ⟨by linarith [hq.1], by linarith [hq.2]⟩

/-- A single error bound works for all graph data at the same dimension. -/
theorem norm_integral_graph_quartic_error_le {m : ℕ} (hmNat : 16 ≤ m)
    (G : GaussianGraphData m) :
    ‖∫ x, graphGaussianWeight G (1 / (m : ℝ)) x *
      ((gaussianQuarticFactor m x - Real.exp (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        ∂Measure.pi (fun _ => gaussianReal 0 1)‖ ≤
      Real.sqrt (Real.exp 4) * Real.sqrt
        (∫ x, (gaussianQuarticFactor m x - Real.exp (-(1 / 2 : ℝ))) ^ 2
          ∂Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hm16 : 16 ≤ (m : ℝ) := by exact_mod_cast hmNat
  have hm : 0 < (m : ℝ) := by linarith
  have hw := memLp_graphGaussianWeight G (1 / (m : ℝ)) (by positivity)
    (show 8 * (1 / (m : ℝ)) < 1 by
      rw [mul_one_div, div_lt_one hm]
      linarith)
  exact (norm_integral_mul_real_le_sqrt hw (memLp_gaussianQuarticError m)).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (graphGaussianWeight_L2_le hmNat G))
      (Real.sqrt_nonneg _))

/-- The spaces may grow and the graph may change arbitrarily with m. The
conclusion is thus a uniform error estimate, not a fixed-graph asymptotic. -/
theorem tendsto_graph_quartic_error (G : (m : ℕ) → GaussianGraphData m) :
    Tendsto (fun m => ∫ x, graphGaussianWeight (G m) (1 / (m : ℝ)) x *
      ((gaussianQuarticFactor m x - Real.exp (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        ∂Measure.pi (fun _ => gaussianReal 0 1)) atTop (𝓝 0) := by
  apply tendsto_integral_mul_real_of_L2
    (fun m => Measure.pi (fun _ : Fin m => gaussianReal 0 1))
    (fun m => graphGaussianWeight (G m) (1 / (m : ℝ)))
    (fun m x => gaussianQuarticFactor m x - Real.exp (-(1 / 2 : ℝ)))
    ?_ (Eventually.of_forall memLp_gaussianQuarticError) (Real.exp 4) ?_
    tendsto_finiteGaussian_quartic_factor_sq
  · filter_upwards [eventually_ge_atTop 16] with m hmNat
    have hm16 : 16 ≤ (m : ℝ) := by exact_mod_cast hmNat
    have hm : 0 < (m : ℝ) := by linarith
    exact memLp_graphGaussianWeight (G m) _ (by positivity) (by
      rw [mul_one_div, div_lt_one hm]
      linarith)
  · filter_upwards [eventually_ge_atTop 16] with m hmNat
    exact graphGaussianWeight_L2_le hmNat (G m)

end
end Wormald

import Wormald.GaussianProductTail
import Wormald.RegularScaledExpansion
import Wormald.WeightedL2Domination

namespace Wormald
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

def gaussianCentralWindow {m : ℕ} (j : Fin m) (r : ℝ) : Set (Fin m → ℝ) :=
  {x | ∀ i, |(Real.sqrt (m : ℝ))⁻¹ * (x i - x j)| ≤ r / 2}

theorem measurableSet_gaussianCentralWindow {m : ℕ} (j : Fin m) (r : ℝ) :
    MeasurableSet (gaussianCentralWindow j r) := by
  unfold gaussianCentralWindow
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun _ => (isClosed_le (by fun_prop) continuous_const).measurableSet

theorem gaussianCentralWindow_pair_bound {m : ℕ} (j : Fin m) (r : ℝ)
    (x : Fin m → ℝ) (hx : x ∈ gaussianCentralWindow j r) (a b : Fin m) :
    |(Real.sqrt (m : ℝ))⁻¹ * x a - (Real.sqrt (m : ℝ))⁻¹ * x b| ≤ r := by
  calc
    _ = |(Real.sqrt (m : ℝ))⁻¹ * (x a - x j) -
      (Real.sqrt (m : ℝ))⁻¹ * (x b - x j)| := by congr 1; ring
    _ ≤ |(Real.sqrt (m : ℝ))⁻¹ * (x a - x j)| +
      |(Real.sqrt (m : ℝ))⁻¹ * (x b - x j)| := abs_sub _ _
    _ ≤ r := by linarith [hx a, hx b]

theorem gaussianCentralWindow_compl_measure_le {m : ℕ} (j : Fin m)
    (r : ℝ) (hr : 0 ≤ r) :
    (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).real (gaussianCentralWindow j r)ᶜ ≤
      2 * m * Real.exp (-(m : ℝ) * r ^ 2 / 32) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Fin.pos j
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm
  have hsubset : (gaussianCentralWindow j r)ᶜ ⊆
      {x : Fin m → ℝ | ∃ i, Real.sqrt (m : ℝ) * (r / 2) ≤ |x i - x j|} := by
    intro x hx
    have hex : ∃ i, r / 2 < |(Real.sqrt (m : ℝ))⁻¹ * (x i - x j)| := by
      simpa only [Set.mem_compl_iff, gaussianCentralWindow, Set.mem_ofPred_eq,
        not_forall, not_le] using hx
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, ?_⟩
    rw [abs_mul, abs_inv, abs_of_pos hs, inv_mul_eq_div] at hi
    have hh := (lt_div_iff₀ hs).mp hi
    nlinarith
  calc
    _ ≤ (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).real
        {x : Fin m → ℝ | ∃ i, Real.sqrt (m : ℝ) * (r / 2) ≤ |x i - x j|} :=
      measureReal_mono hsubset
    _ ≤ 2 * m * Real.exp (-(m : ℝ) * (r / 2) ^ 2 / 8) :=
      finiteGaussian_scaled_anchor_tail_le j (r / 2) (by positivity)
    _ = _ := by congr 2; ring

def graphQuarticWeight {m : ℕ} (G : GaussianGraphData m) (x : Fin m → ℝ) : ℂ :=
  graphGaussianWeight G (1 / (m : ℝ)) x * (gaussianQuarticFactor m x : ℂ)

theorem continuous_graphQuarticWeight {m : ℕ} (G : GaussianGraphData m) :
    Continuous (graphQuarticWeight G) :=
  (continuous_graphGaussianWeight G _).mul
    (Complex.continuous_ofReal.comp (continuous_gaussianQuarticFactor m))

theorem norm_graphQuarticWeight_le {m : ℕ} (G : GaussianGraphData m) (x : Fin m → ℝ) :
    ‖graphQuarticWeight G x‖ ≤ ‖graphGaussianWeight G (1 / (m : ℝ)) x‖ := by
  rw [graphQuarticWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gaussianQuarticFactor_mem_unitInterval m x).1]
  exact mul_le_of_le_one_right (norm_nonneg _) (gaussianQuarticFactor_mem_unitInterval m x).2

theorem memLp_graphQuarticWeight {m : ℕ} (hmNat : 16 ≤ m) (G : GaussianGraphData m) :
    MemLp (graphQuarticWeight G) 2 (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hm16 : 16 ≤ (m : ℝ) := by exact_mod_cast hmNat
  have hm : 0 < (m : ℝ) := by linarith
  have hw := memLp_graphGaussianWeight G (1 / (m : ℝ)) (by positivity)
    (by rw [mul_one_div, div_lt_one hm]; linarith)
  exact hw.of_le (continuous_graphQuarticWeight G).aestronglyMeasurable
    (Eventually.of_forall (norm_graphQuarticWeight_le G))

end
end Wormald

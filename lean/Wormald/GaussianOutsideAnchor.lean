import Wormald.MeasurableGaussianBoxAnchor
import Wormald.GoodClusterGaussianVolume
import Wormald.GaussianCentralWindow
import Wormald.CentralGaussianRadius

namespace Wormald
noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem setIntegral_norm_le_sqrt_L2 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {w : Ω → ℂ}
    (hw : MemLp w 2 μ) (A : Set Ω) :
    (∫ x in A, ‖w x‖ ∂μ) ≤
      Real.sqrt (∫ x, ‖w x‖ ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using (hw.restrict A).norm)
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 (μ.restrict A)))
  have h' : (∫ x in A, ‖w x‖ ∂μ) ≤
      Real.sqrt (∫ x in A, ‖w x‖ ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_one, mul_one,
      Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
      measureReal_def, Measure.restrict_apply_univ, ← Real.sqrt_eq_rpow] using h
  have hsq : (∫ x in A, ‖w x‖ ^ 2 ∂μ) ≤ ∫ x, ‖w x‖ ^ 2 ∂μ :=
    integral_mono_measure μ.restrict_le_self (Eventually.of_forall fun _ => sq_nonneg _)
      ((memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw)
  exact h'.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _))

theorem scaledAnchorDifference_mem_closedBall {n : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (x : Fin (n + 2) → ℝ) :
    scaledAnchorDifference x ∈ Metric.closedBall 0 (r / 2) ↔
      x ∈ gaussianCentralWindow (Fin.last (n + 1)) r := by
  simp only [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (show 0 ≤ r / 2 by positivity), scaledAnchorDifference,
    Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, anchorDifference,
    gaussianCentralWindow, Set.mem_ofPred_eq]
  constructor
  · intro h i
    refine Fin.lastCases ?_ (fun j => h j) i
    simp only [sub_self, mul_zero, abs_zero]
    positivity
  · intro h j
    exact h j.castSucc

theorem graphQuadraticWeight_central_outside_le {m : ℕ} (hm : 16 ≤ m)
    (G : GaussianGraphData m) (j : Fin m) (r : ℝ) (hr : 0 ≤ r) :
    (∫ x in (gaussianCentralWindow j r)ᶜ, graphQuadraticWeight G (1 / (m : ℝ)) x
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      Real.exp 2 * Real.sqrt (2 * m * Real.exp (-(m : ℝ) * r ^ 2 / 32)) := by
  have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hw := memLp_graphGaussianWeight G (1 / (m : ℝ)) (by positivity) (by
    rw [show 8 * (1 / (m : ℝ)) = 8 / m by ring]
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < m)).mpr
    linarith)
  have hbound := setIntegral_norm_le_sqrt_L2 hw (gaussianCentralWindow j r)ᶜ
  simp_rw [norm_graphGaussianWeight] at hbound
  have hL2 := graphGaussianWeight_L2_le hm G
  simp_rw [norm_graphGaussianWeight] at hL2
  have htail := gaussianCentralWindow_compl_measure_le j r hr
  have hsqrt : Real.sqrt (Real.exp 4) = Real.exp 2 := by
    have heq : Real.exp 4 = Real.exp 2 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hbound.trans (by
    have hh := mul_le_mul (Real.sqrt_le_sqrt hL2) (Real.sqrt_le_sqrt htail)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    simpa only [hsqrt] using hh)

theorem integral_anchoredGraphGaussian_outside_le {n : ℕ} (hn : 16 ≤ n + 2)
    (G : GaussianGraphData (n + 2)) (h1 : G.laplacian *ᵥ (fun _ => 1) = 0)
    (r : ℝ) (hr : 0 ≤ r) :
    (∫ y : Fin (n + 1) → ℝ in (Metric.closedBall 0 (r / 2))ᶜ,
      matrixGaussian (anchoredGraphPrecision G) y) ≤
      Real.exp 2 * Real.sqrt (2 * (n + 2) * Real.exp (-((n + 2 : ℕ) : ℝ) * r ^ 2 / 32)) *
        quotientGaussianVolume (n + 2) := by
  let A : Set (Fin (n + 1) → ℝ) := (Metric.closedBall 0 (r / 2))ᶜ
  let F : (Fin (n + 1) → ℝ) → ℝ := A.indicator (anchoredGraphQuadraticFactor G)
  have hA : MeasurableSet A := Metric.isClosed_closedBall.measurableSet.compl
  have hpoint (x : Fin (n + 2) → ℝ) : F (scaledAnchorDifference x) =
      (gaussianCentralWindow (Fin.last (n + 1)) r)ᶜ.indicator
        (graphQuadraticWeight G (1 / ((n + 2 : ℕ) : ℝ))) x := by
    have hx : scaledAnchorDifference x ∈ A ↔ x ∈ (gaussianCentralWindow (Fin.last (n + 1)) r)ᶜ := by
      exact not_congr (scaledAnchorDifference_mem_closedBall r hr x)
    by_cases hxa : scaledAnchorDifference x ∈ A
    · simp only [F, Set.indicator_of_mem hxa, Set.indicator_of_mem (hx.mp hxa),
        graphQuadraticFactor_scaledAnchor G h1]
    · simp only [F, Set.indicator_of_notMem hxa, Set.indicator_of_notMem (hx.not.mp hxa)]
  have hmR : (16 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hn
  have hw := memLp_graphGaussianWeight G (1 / ((n + 2 : ℕ) : ℝ)) (by positivity) (by
    rw [show 8 * (1 / ((n + 2 : ℕ) : ℝ)) = 8 / ((n + 2 : ℕ) : ℝ) by ring]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n + 2 : ℕ))).mpr
    linarith)
  have hreal : Integrable (graphQuadraticWeight G (1 / ((n + 2 : ℕ) : ℝ)))
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
    simpa only [norm_graphGaussianWeight] using hw.norm.integrable (by norm_num)
  have hFi : Integrable (fun x : Fin (n + 2) → ℝ => F (scaledAnchorDifference x))
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
    simp_rw [hpoint]
    exact hreal.indicator (measurableSet_gaussianCentralWindow _ _).compl
  have htransport := integral_standardNormalProduct_scaledAnchorDifference F hFi
  simp_rw [hpoint, integral_indicator (measurableSet_gaussianCentralWindow _ _).compl] at htransport
  have hint : (∫ y, matrixGaussian (completeQuotientPrecision n) y * F y) =
      ∫ y in A, matrixGaussian (anchoredGraphPrecision G) y := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      by_cases hy : y ∈ A
      · simp only [F, Set.indicator_of_mem hy, matrixGaussian_anchoredGraphPrecision]
      · simp only [F, Set.indicator_of_notMem hy, mul_zero]
  simp only [smul_eq_mul] at htransport
  rw [hint] at htransport
  have hbound := graphQuadraticWeight_central_outside_le hn G (Fin.last (n + 1)) r hr
  rw [htransport] at hbound
  have hV := quotientGaussianVolume_pos (show 2 ≤ n + 2 by omega)
  have hh := mul_le_mul_of_nonneg_left hbound hV.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul, mul_comm, A,
    Nat.cast_add, Nat.cast_ofNat] using hh

theorem goodClusterGaussian_cube_outside_le {n : ℕ} (hn : 16 ≤ n + 2)
    (G : GaussianGraphData (n + 2)) (h1 : G.laplacian *ᵥ (fun _ => 1) = 0)
    (r : ℝ) (hr : 0 ≤ r) :
    (∫ x : Fin (n + 2) → ℝ in Metric.closedBall 0 (3 / 16 : ℝ),
      ((Metric.closedBall 0 (r / 2))ᶜ.indicator (matrixGaussian (anchoredGraphPrecision G)))
        (Real.pi • anchorDifference x)) ≤
      (3 / 8 : ℝ) * Real.exp 2 *
        Real.sqrt (2 * ((n + 2 : ℕ) : ℝ) * Real.exp (-((n + 2 : ℕ) : ℝ) * r ^ 2 / 32)) *
          quotientGaussianVolume (n + 2) / Real.pi ^ (n + 1) := by
  let A : Set (Fin (n + 1) → ℝ) := (Metric.closedBall 0 (r / 2))ᶜ
  let F : (Fin (n + 1) → ℝ) → ℝ := A.indicator (matrixGaussian (anchoredGraphPrecision G))
  have hA : MeasurableSet A := Metric.isClosed_closedBall.measurableSet.compl
  have hp := anchoredGraphPrecision_posDef (by omega) G h1
  have hG : Continuous (matrixGaussian (anchoredGraphPrecision G)) := by
    unfold matrixGaussian dotProduct Matrix.mulVec
    fun_prop
  have hF : Measurable F := hG.measurable.indicator hA
  have hF0 (y) : 0 ≤ F y := Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) y
  have hFbound (y) : ‖F y‖ ≤ matrixGaussian (anchoredGraphPrecision G) y := by
    by_cases hy : y ∈ A
    · simp only [F, Set.indicator_of_mem hy, Real.norm_eq_abs, matrixGaussian,
        abs_of_pos (Real.exp_pos _), le_refl]
    · simp only [F, Set.indicator_of_notMem hy, norm_zero, matrixGaussian]
      exact (Real.exp_pos _).le
  have hFi : Integrable F := (integrable_matrixGaussian _ hp).indicator hA
  have hmap : Continuous (fun x : Fin (n + 2) → ℝ => Real.pi • anchorDifference x) := by
    exact (continuous_anchorDifference (n + 1)).const_smul Real.pi
  have hFbox : IntegrableOn (fun x : Fin (n + 2) → ℝ => F (Real.pi • anchorDifference x))
      (Metric.closedBall 0 (3 / 16 : ℝ)) := by
    exact ((hG.comp hmap).continuousOn.integrableOn_compact (isCompact_closedBall 0 _)).mono'
      ((hF.comp hmap.measurable).aestronglyMeasurable) (Eventually.of_forall fun x => hFbound _)
  have hbox := integral_closedBall_scaled_anchorDifference_le_of_integrableOn
    (3 / 16 : ℝ) (by norm_num) Real.pi Real.pi_pos F hF0 hFi hFbox
  have htail := integral_anchoredGraphGaussian_outside_le hn G h1 r hr
  rw [← integral_indicator hA] at htail
  have hcoef : 0 ≤ 2 * (3 / 16 : ℝ) / Real.pi ^ (n + 1) := by positivity
  have hh := hbox.trans (mul_le_mul_of_nonneg_left htail hcoef)
  convert hh using 1
  push_cast
  ring

end
end Wormald

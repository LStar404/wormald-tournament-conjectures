import Wormald.GaussianOutsideAnchor
import Wormald.GoodClusterKernelVolume

namespace Wormald
noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

local instance allGoodCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance allGoodCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def circleAnchorWindow {m : ℕ} (j : Fin m) (r : ℝ) : Set (UnitAddTorus (Fin m)) :=
  {x | ∀ i, dist (x i) (x j) ≤ r}

theorem measurableSet_circleAnchorWindow {m : ℕ} (j : Fin m) (r : ℝ) :
    MeasurableSet (circleAnchorWindow j r) := by
  unfold circleAnchorWindow
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun _ => (isClosed_le (by fun_prop) continuous_const).measurableSet

theorem circleAnchorWindow_lift_iff {n : ℕ} (j : Fin 16) (r : ℝ) (hr : 0 ≤ r)
    (x : UnitAddTorus (Fin (n + 1))) (hx : x ∈ circleClusterWindow j (3 / 16 : ℝ)) :
    x ∈ circleAnchorWindow (Fin.last n) (r / (2 * Real.pi)) ↔
      Real.pi • anchorDifference (fun i => circleCenteredLift j (x i)) ∈
        Metric.closedBall 0 (r / 2) := by
  have hgood (i : Fin (n + 1)) : i ∈ circleGood x j :=
    (mem_circleGood x j i).mpr (hx i)
  simp only [circleAnchorWindow, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (show 0 ≤ r / 2 by positivity), Pi.smul_apply, smul_eq_mul,
    anchorDifference, Real.norm_eq_abs]
  constructor
  · intro h i
    have hi := h i.castSucc
    rw [circleGood_lift_distance x j (hgood _) (hgood _)] at hi
    rw [abs_mul, abs_of_pos Real.pi_pos]
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp hi
    nlinarith
  · intro h i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [dist_self]
      positivity
    · rw [circleGood_lift_distance x j (hgood _) (hgood _)]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
      have hk := h k
      rw [abs_mul, abs_of_pos Real.pi_pos] at hk
      nlinarith

namespace FiniteModel

theorem norm_normalizedRegularTorusIntegrand_allGood_le {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hm : Odd m) (j : Fin 16)
    (x : UnitAddTorus (Fin m)) (hx : x ∈ circleClusterWindow j (3 / 16 : ℝ)) :
    ‖normalizedRegularTorusIntegrand D x‖ ≤
      freeEdgeGaussian D (fun i => circleCenteredLift j (x i)) := by
  have hgood (i : Fin m) : i ∈ circleGood x j := (mem_circleGood x j i).mpr (hx i)
  apply (norm_normalizedRegularTorusIntegrand_le D hm x).trans
  calc
    _ ≤ ∏ e ∈ freeCosineEdges D,
        Real.exp (-((Real.pi * (circleCenteredLift j (x e.1.1) -
          circleCenteredLift j (x e.1.2))) ^ 2 / 2)) :=
      Finset.prod_le_prod₀ (fun _ _ => circleCosineKernel_nonneg _ _)
        (fun _ _ => circleCosineKernel_good_gaussian x j (hgood _) (hgood _))
    _ = _ := by
      rw [← Real.exp_sum]
      unfold freeEdgeGaussian
      congr 1
      simp only [← neg_div, ← Finset.sum_div, Finset.sum_neg_distrib]

theorem integral_freeEdgeGaussian_cube_outside_le {n : ℕ} (hm : 16 ≤ n + 2)
    (D : Finset (Fin (n + 2) × Fin (n + 2))) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hs : Set.InjOn (Prod.fst : Fin (n + 2) × Fin (n + 2) → Fin (n + 2)) D)
    (ht : Set.InjOn (Prod.snd : Fin (n + 2) × Fin (n + 2) → Fin (n + 2)) D) (r : ℝ) (hr : 0 ≤ r) :
    (∫ x : Fin (n + 2) → ℝ in Metric.closedBall 0 (3 / 16 : ℝ),
      if ‖Real.pi • anchorDifference x‖ ≤ r / 2 then
        0 else freeEdgeGaussian D x) ≤
      (3 / 8 : ℝ) * Real.exp 2 *
        Real.sqrt (2 * ((n + 2 : ℕ) : ℝ) * Real.exp (-((n + 2 : ℕ) : ℝ) * r ^ 2 / 32)) *
          quotientGaussianVolume (n + 2) / Real.pi ^ (n + 1) := by
  simp_rw [freeEdgeGaussian_eq_anchored D hD hs ht]
  have h := goodClusterGaussian_cube_outside_le hm
    (partialPermutationGaussianGraphData D (no_opposite_arc_ne D hD) hs ht)
    (partialLaplacian_mulVec_one D) r hr
  convert h using 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [Set.indicator_apply, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right]
      split_ifs <;> simp_all

theorem integral_normalizedRegularTorusIntegrand_allGood_outside_le {n : ℕ}
    (hm : 16 ≤ n + 2) (hmOdd : Odd (n + 2))
    (D : Finset (Fin (n + 2) × Fin (n + 2))) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hs : Set.InjOn (Prod.fst : Fin (n + 2) × Fin (n + 2) → Fin (n + 2)) D)
    (ht : Set.InjOn (Prod.snd : Fin (n + 2) × Fin (n + 2) → Fin (n + 2)) D)
    (j : Fin 16) (r : ℝ) (hr : 0 ≤ r) :
    (∫ x : UnitAddTorus (Fin (n + 2)) in
      circleClusterWindow j (3 / 16 : ℝ) \ circleAnchorWindow (Fin.last (n + 1)) (r / (2 * Real.pi)),
        ‖normalizedRegularTorusIntegrand D x‖) ≤
      (3 / 8 : ℝ) * Real.exp 2 *
        Real.sqrt (2 * ((n + 2 : ℕ) : ℝ) * Real.exp (-((n + 2 : ℕ) : ℝ) * r ^ 2 / 32)) *
          quotientGaussianVolume (n + 2) / Real.pi ^ (n + 1) := by
  let f : (Fin (n + 2) → ℝ) → ℝ := fun y =>
    if ‖Real.pi • anchorDifference y‖ ≤ r / 2 then 0 else freeEdgeGaussian D y
  have hmap : Continuous (fun y : Fin (n + 2) → ℝ => Real.pi • anchorDifference y) :=
    (continuous_anchorDifference (n + 1)).const_smul Real.pi
  have hf : Measurable f := Measurable.ite
    (isClosed_le hmap.norm continuous_const).measurableSet measurable_const
    (continuous_freeEdgeGaussian D).measurable
  have hF0 (y) : 0 ≤ f y := by dsimp [f]; split_ifs; exact le_rfl; exact freeEdgeGaussian_nonneg _ _
  have hF1 (y) : ‖f y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 y)]
    dsimp [f]
    split_ifs
    · norm_num
    · exact freeEdgeGaussian_le_one D y
  let lift : UnitAddTorus (Fin (n + 2)) → (Fin (n + 2) → ℝ) :=
    fun x i => circleCenteredLift j (x i)
  have hlift : Measurable lift := measurable_pi_iff.mpr
    (fun i => (measurable_circleCenteredLift j).comp (measurable_pi_apply i))
  have hfi : Integrable (fun x => f (lift x)) :=
    (integrable_const (1 : ℝ)).mono' (hf.comp hlift).aestronglyMeasurable
      (Eventually.of_forall fun x => hF1 (lift x))
  let A := circleAnchorWindow (Fin.last (n + 1)) (r / (2 * Real.pi))
  let W : Set (UnitAddTorus (Fin (n + 2))) := circleClusterWindow j (3 / 16 : ℝ)
  have hA : MeasurableSet A := measurableSet_circleAnchorWindow _ _
  have hW : MeasurableSet W := measurableSet_circleClusterWindow _ _
  have hrew : (∫ x in W \ A, ‖normalizedRegularTorusIntegrand D x‖) =
      ∫ x in W, Aᶜ.indicator (fun x => ‖normalizedRegularTorusIntegrand D x‖) x := by
    rw [setIntegral_indicator hA.compl, Set.sdiff_eq_compl_inter, Set.inter_comm]
  change (∫ x in W \ A, ‖normalizedRegularTorusIntegrand D x‖) ≤ _
  rw [hrew]
  have hbound : (∫ x in W, Aᶜ.indicator (fun x => ‖normalizedRegularTorusIntegrand D x‖) x) ≤
      ∫ x in W, f (lift x) := by
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => norm_nonneg _) x)
      hfi.integrableOn
    filter_upwards [ae_restrict_mem hW] with x hx
    have hiff := circleAnchorWindow_lift_iff j r hr x hx
    by_cases hxa : x ∈ A
    · have hin : ‖Real.pi • anchorDifference (lift x)‖ ≤ r / 2 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hiff.mp hxa
      have hnot : x ∉ Aᶜ := not_not.mpr hxa
      simp only [Set.indicator_of_notMem hnot, f, ite_eq_left hin, le_refl]
    · have hout : ¬ ‖Real.pi • anchorDifference (lift x)‖ ≤ r / 2 := by
        intro h
        exact hxa (hiff.mpr (by simpa only [Metric.mem_closedBall, dist_zero_right] using h))
      rw [Set.indicator_of_mem hxa,
        show f (lift x) = freeEdgeGaussian D (lift x) from ite_eq_right hout]
      exact norm_normalizedRegularTorusIntegrand_allGood_le D hmOdd j x hx
  apply hbound.trans
  rw [show (fun x => f (lift x)) = (fun x => f (fun i => circleCenteredLift j (x i))) from rfl,
    integral_circleClusterWindow_lift j (3 / 16 : ℝ) (by norm_num) (by norm_num)]
  exact integral_freeEdgeGaussian_cube_outside_le hm D hD hs ht r hr

end FiniteModel
end
end Wormald

import Wormald.GoodClusterCoordinates
import Wormald.RegularFourierAnchoring

/-! A circle window narrower than a semicircle is exactly a real cube in the
centered lift. This removes the good-cluster angular coordinates without any
boundary convention or volume approximation. -/

namespace Wormald
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

local instance circleLiftIntegralMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance circleLiftIntegralProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance circleLiftIntegralAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

theorem measurable_circleCenteredLift (j : Fin 16) : Measurable (circleCenteredLift j) := by
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIoc 1 (-(1 / 2 : ℝ))).measurable.comp
      (measurable_id.sub_const (circleGridCenter j)))

def circleClusterWindow {n : ℕ} (j : Fin 16) (r : ℝ) : Set (UnitAddTorus (Fin n)) :=
  {x | ∀ i, dist (x i) (circleGridCenter j) ≤ r}

theorem measurableSet_circleClusterWindow {n : ℕ} (j : Fin 16) (r : ℝ) :
    MeasurableSet (circleClusterWindow (n := n) j r) := by
  simpa only [circleClusterWindow, Set.ofPred_forall] using
    (MeasurableSet.iInter (fun i : Fin n => measurableSet_le
      ((measurable_pi_apply i : Measurable (fun x : UnitAddTorus (Fin n) => x i)).dist
        (measurable_const : Measurable (fun _ : UnitAddTorus (Fin n) => circleGridCenter j)))
      (measurable_const : Measurable (fun _ : UnitAddTorus (Fin n) => r))))

theorem circleCenteredLift_coe_add_center (j : Fin 16) {y : ℝ}
    (hy : y ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :
    circleCenteredLift j ((y : UnitAddCircle) + circleGridCenter j) = y := by
  unfold circleCenteredLift
  simp only [add_sub_cancel_right]
  exact AddCircle.equivIoc_coe_of_mem (by convert hy using 1; norm_num)

theorem closedBall_subset_centeredUnitCube (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hrhalf : r < 1 / 2) :
    Metric.closedBall (0 : Fin n → ℝ) r ⊆ centeredUnitCube n := by
  intro y hy i
  have hcoord := (pi_norm_le_iff_of_nonneg hr).mp (by simpa only [Metric.mem_closedBall,
    dist_zero_right] using hy) i
  rw [Real.norm_eq_abs, abs_le] at hcoord
  constructor <;> linarith

/-- The normalized circle integral over a good window is exactly the real
cube integral of the centered lift, including the zero-dimensional case. -/
theorem integral_circleClusterWindow_lift {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (j : Fin 16) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r < 1 / 2) (f : (Fin n → ℝ) → E) :
    (∫ x : UnitAddTorus (Fin n) in circleClusterWindow j r,
      f (fun i => circleCenteredLift j (x i))) =
      ∫ y : Fin n → ℝ in Metric.closedBall 0 r, f y := by
  let H : UnitAddTorus (Fin n) → E := (circleClusterWindow j r).indicator
    (fun x => f (fun i => circleCenteredLift j (x i)))
  have hunit : MeasurableSet (centeredUnitCube n) := by
    simpa only [centeredUnitCube, Set.ofPred_forall, Set.preimage] using
      (MeasurableSet.iInter (fun i : Fin n =>
        (measurableSet_Ioc : MeasurableSet (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))).preimage
          (measurable_pi_apply i)))
  have hwindow := measurableSet_circleClusterWindow (n := n) j r
  rw [← integral_indicator hwindow]
  change (∫ x : UnitAddTorus (Fin n), H x) = _
  calc
    _ = ∫ x : UnitAddTorus (Fin n), H (fun i => x i + circleGridCenter j) :=
      (integral_add_right_eq_self H (fun _ => circleGridCenter j)).symm
    _ = ∫ y : Fin n → ℝ in centeredUnitCube n,
        H (fun i => (y i : UnitAddCircle) + circleGridCenter j) := by
      rw [UnitAddTorus.integral_preimage _ (fun _ => -(1 / 2 : ℝ))]
      congr 1
      ext y
      norm_num [centeredUnitCube]
    _ = ∫ y : Fin n → ℝ in centeredUnitCube n, (Metric.closedBall 0 r).indicator f y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hunit] with y hy
      have hlift : (fun i => circleCenteredLift j ((y i : UnitAddCircle) + circleGridCenter j)) = y :=
        funext fun i => circleCenteredLift_coe_add_center j (hy i)
      have hmem : (fun i => (y i : UnitAddCircle) + circleGridCenter j) ∈ circleClusterWindow j r ↔
          y ∈ Metric.closedBall 0 r := by
        simp only [circleClusterWindow, Set.mem_ofPred_eq, Metric.mem_closedBall,
          dist_zero_right, pi_norm_le_iff_of_nonneg hr, Real.norm_eq_abs]
        apply forall_congr'
        intro i
        rw [← circleCenteredLift_abs_eq_dist]
        rw [congrFun hlift i]
      by_cases hball : y ∈ Metric.closedBall (0 : Fin n → ℝ) r
      · simp only [H, Set.indicator_of_mem (hmem.mpr hball), Set.indicator_of_mem hball, hlift]
      · simp only [H, Set.indicator_of_notMem (hmem.not.mpr hball), Set.indicator_of_notMem hball]
    _ = _ := by
      rw [setIntegral_indicator measurableSet_closedBall,
        Set.inter_eq_right.mpr (closedBall_subset_centeredUnitCube n hr hrhalf)]

end
end Wormald

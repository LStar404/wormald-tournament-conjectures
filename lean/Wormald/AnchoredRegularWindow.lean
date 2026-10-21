import Wormald.AllGoodClusterTail
import Wormald.PhysicalGaussianQuotientVolume

namespace Wormald
noncomputable section
open MeasureTheory
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable

local instance anchoredWindowCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance anchoredWindowCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance anchoredWindowCircleAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

theorem integral_torus_eq_anchored_last_of_integrable {n : ℕ}
    (f : UnitAddTorus (Fin (n + 1)) → ℂ) (hf : Integrable f)
    (hinv : ∀ x c, f (fun i => x i + c) = f x) :
    (∫ x : UnitAddTorus (Fin (n + 1)), f x) =
      ∫ y : UnitAddTorus (Fin n), f (Fin.snoc y 0) := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle)
    (Fin.last n)).symm
  have hints : Integrable (fun p : UnitAddCircle × UnitAddTorus (Fin n) =>
      f (Fin.snoc p.2 p.1)) := by
    simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv_last, Fin.snocEquiv, Equiv.coe_fn_mk] using hp.integrable_comp_of_integrable hf
  have hinner (t : UnitAddCircle) :
      (∫ y : UnitAddTorus (Fin n), f (Fin.snoc y t)) =
        ∫ y : UnitAddTorus (Fin n), f (Fin.snoc y 0) := by
    have hpoint (y : UnitAddTorus (Fin n)) :
        f (Fin.snoc y t) = f (Fin.snoc (fun i => y i + -t) 0) := by
      have heq : (fun i => (Fin.snoc y t : Fin (n + 1) → UnitAddCircle) i + -t) =
          Fin.snoc (fun i => y i + -t) 0 := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      simpa only [heq] using (hinv (Fin.snoc y t) (-t)).symm
    calc
      _ = ∫ y : UnitAddTorus (Fin n), f (Fin.snoc (fun i => y i + -t) 0) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = _ := integral_add_right_eq_self (fun y : UnitAddTorus (Fin n) => f (Fin.snoc y 0))
        (fun _ => -t)
  calc
    _ = ∫ p : UnitAddCircle × UnitAddTorus (Fin n), f (Fin.snoc p.2 p.1) := by
      rw [← hp.integral_comp']
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last]
      rfl
    _ = ∫ t : UnitAddCircle, ∫ y : UnitAddTorus (Fin n), f (Fin.snoc y t) := integral_prod _ hints
    _ = _ := by simp_rw [hinner]; simp

theorem circleAnchorWindow_add_const {m : ℕ} (a : Fin m) (R : ℝ)
    (x : UnitAddTorus (Fin m)) (c : UnitAddCircle) :
    (fun i => x i + c) ∈ circleAnchorWindow a R ↔ x ∈ circleAnchorWindow a R := by
  simp only [circleAnchorWindow, Set.mem_ofPred_eq, dist_add_right]

theorem circleAnchorWindow_snoc_iff {n : ℕ} (R : ℝ) (hR : 0 ≤ R)
    (y : UnitAddTorus (Fin n)) :
    Fin.snoc y 0 ∈ circleAnchorWindow (Fin.last n) R ↔
      y ∈ circleClusterWindow (0 : Fin 16) R := by
  constructor
  · intro h i
    simpa [circleGridCenter] using h i.castSucc
  · intro h i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last, dist_self] using hR
    · simpa [circleGridCenter] using h j

namespace FiniteModel

theorem integral_circleAnchorWindow_eq_lifted_cube {n : ℕ}
    (D : Finset (Fin (n + 1) × Fin (n + 1))) (hm : Odd (n + 1))
    (R : ℝ) (hR0 : 0 ≤ R) (hRhalf : R < 1 / 2) :
    (∫ x : UnitAddTorus (Fin (n + 1)) in circleAnchorWindow (Fin.last n) R,
      normalizedRegularTorusIntegrand D x) =
        ∫ y : Fin n → ℝ in Metric.closedBall 0 R,
          normalizedRegularIntegrand D (Fin.snoc y 0) := by
  let A := circleAnchorWindow (Fin.last n) R
  let H : UnitAddTorus (Fin (n + 1)) → ℂ := A.indicator (normalizedRegularTorusIntegrand D)
  have hA : MeasurableSet A := measurableSet_circleAnchorWindow _ _
  have hH : Integrable H :=
    ((continuous_normalizedRegularTorusIntegrand D).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).indicator hA
  have hinv (x : UnitAddTorus (Fin (n + 1))) (c : UnitAddCircle) :
      H (fun i => x i + c) = H x := by
    have hmem := circleAnchorWindow_add_const (Fin.last n) R x c
    by_cases hx : x ∈ A
    · have htrans : (fun i => x i + c) ∈ A := hmem.mpr hx
      simp only [H, Set.indicator_of_mem hx, Set.indicator_of_mem htrans,
        normalizedRegularTorusIntegrand_add_const D hm]
    · have htrans : (fun i => x i + c) ∉ A := hmem.not.mpr hx
      simp only [H, Set.indicator_of_notMem hx, Set.indicator_of_notMem htrans]
  rw [← integral_indicator hA]
  change (∫ x, H x) = _
  rw [integral_torus_eq_anchored_last_of_integrable H hH hinv]
  calc
    _ = ∫ y : UnitAddTorus (Fin n) in circleClusterWindow (0 : Fin 16) R,
        normalizedRegularTorusIntegrand D (Fin.snoc y 0) := by
      rw [← integral_indicator (measurableSet_circleClusterWindow _ _)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        have hmem := circleAnchorWindow_snoc_iff R hR0 y
        by_cases hy : y ∈ circleClusterWindow (0 : Fin 16) R
        · have hsy : Fin.snoc y 0 ∈ A := hmem.mpr hy
          simp only [H, Set.indicator_of_mem hy, Set.indicator_of_mem hsy]
        · have hsy : Fin.snoc y 0 ∉ A := hmem.not.mpr hy
          simp only [H, Set.indicator_of_notMem hy, Set.indicator_of_notMem hsy]
    _ = ∫ y : UnitAddTorus (Fin n) in circleClusterWindow (0 : Fin 16) R,
        normalizedRegularIntegrand D (Fin.snoc (fun i => circleCenteredLift 0 (y i)) 0) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        have heq : (fun i => (((Fin.snoc (fun j => circleCenteredLift 0 (y j)) (0 : ℝ) : Fin (n + 1) → ℝ) i : ℝ) : UnitAddCircle)) =
            Fin.snoc y 0 := by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simp
          · simp [circleCenteredLift_coe, circleGridCenter]
        dsimp only
        rw [← heq, normalizedRegularTorusIntegrand_coe D hm]
    _ = _ := integral_circleClusterWindow_lift 0 R hR0 hRhalf
      (fun y => normalizedRegularIntegrand D (Fin.snoc y 0))

theorem integral_circleAnchorWindow_eq_physical {n : ℕ}
    (D : Finset (Fin (n + 1) × Fin (n + 1))) (hm : Odd (n + 1))
    (r : ℝ) (hr : 0 ≤ r) (hrpi : r < Real.pi) :
    (∫ x : UnitAddTorus (Fin (n + 1)) in
      circleAnchorWindow (Fin.last n) (r / (2 * Real.pi)), normalizedRegularTorusIntegrand D x) =
      (Real.pi ^ n)⁻¹ • ∫ θ : Fin n → ℝ in Metric.closedBall 0 (r / 2),
        normalizedRegularPhysicalIntegrand D (Fin.snoc θ 0) := by
  have hR0 : 0 ≤ r / (2 * Real.pi) := by positivity
  have hRh : r / (2 * Real.pi) < 1 / 2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
    linarith
  rw [integral_circleAnchorWindow_eq_lifted_cube D hm _ hR0 hRh]
  let F : (Fin n → ℝ) → ℂ := fun θ => normalizedRegularPhysicalIntegrand D (Fin.snoc θ 0)
  have hfun (y : Fin n → ℝ) : normalizedRegularIntegrand D (Fin.snoc y 0) = F (Real.pi • y) := by
    unfold F normalizedRegularPhysicalIntegrand
    congr 1
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [Pi.smul_apply, smul_eq_mul, Real.pi_ne_zero]
  simp_rw [hfun]
  rw [Measure.setIntegral_comp_smul_of_pos volume F _ Real.pi_pos]
  simp only [Module.finrank_pi, Fintype.card_fin]
  have hset : Real.pi • Metric.closedBall (0 : Fin n → ℝ) (r / (2 * Real.pi)) =
      Metric.closedBall 0 (r / 2) := by
    rw [smul_closedBall' Real.pi_ne_zero]
    simp only [smul_zero, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    congr 1
    field_simp
  rw [hset]

theorem integral_circleAnchorWindow_div_volume_eq_physical {n : ℕ}
    (D : Finset (Fin (n + 1) × Fin (n + 1))) (hm : Odd (n + 1))
    (r : ℝ) (hr : 0 ≤ r) (hrpi : r < Real.pi) :
    (∫ x : UnitAddTorus (Fin (n + 1)) in
      circleAnchorWindow (Fin.last n) (r / (2 * Real.pi)), normalizedRegularTorusIntegrand D x) /
        (physicalGaussianQuotientVolume (n + 1) : ℂ) =
      (∫ θ : Fin n → ℝ in Metric.closedBall 0 (r / 2),
        normalizedRegularPhysicalIntegrand D (Fin.snoc θ 0)) /
          (quotientGaussianVolume (n + 1) : ℂ) := by
  have hpi : (Real.pi : ℂ) ^ n ≠ 0 := by exact_mod_cast pow_ne_zero n Real.pi_ne_zero
  rw [integral_circleAnchorWindow_eq_physical D hm r hr hrpi]
  simp only [physicalGaussianQuotientVolume, Nat.add_sub_cancel,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.real_smul, Complex.ofReal_inv]
  field_simp

end FiniteModel
end
end Wormald

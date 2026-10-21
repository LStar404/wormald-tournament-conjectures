import Wormald.GoodClusterKernelVolume
import Wormald.CircleClusterCells
import Wormald.ClusterGeometricDecay

/-! The actual Fourier integrand on each cluster cell. The outlier
coordinates integrate to one under probability Haar measure; only the
exact good-cluster Gaussian quotient volume remains. -/

namespace Wormald.FiniteModel
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

local instance goodCellCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance goodCellCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem partialPermutation_neighbor_card_le_two {m : ℕ} (D : Finset (Fin m × Fin m))
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D) (u : Fin m) (C : Finset (Fin m)) :
    (C.filter (fun v => (u, v) ∈ D ∨ (v, u) ∈ D)).card ≤ 2 := by
  have hs1 : (C.filter (fun v => (u, v) ∈ D)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact congrArg Prod.snd (hs (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 rfl)
  have ht1 : (C.filter (fun v => (v, u) ∈ D)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact congrArg Prod.fst (ht (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 rfl)
  rw [Finset.filter_or]
  exact (Finset.card_union_le _ _).trans (by omega)

def circleWindowGaussian {m : ℕ} (D : Finset (Fin m × Fin m)) (j : Fin 16)
    (x : UnitAddTorus (Fin m)) : ℝ :=
  (circleClusterWindow j (3 / 16 : ℝ)).indicator
    (fun y => freeEdgeGaussian D (fun i => circleCenteredLift j (y i))) x

theorem measurable_circleWindowGaussian {m : ℕ} (D : Finset (Fin m × Fin m)) (j : Fin 16) :
    Measurable (circleWindowGaussian D j) := by
  apply Measurable.indicator _ (measurableSet_circleClusterWindow j _)
  exact (continuous_freeEdgeGaussian D).measurable.comp
    (Measurable.of_eval fun i => (measurable_circleCenteredLift j).comp (measurable_pi_apply i))

theorem circleWindowGaussian_nonneg {m : ℕ} (D : Finset (Fin m × Fin m))
    (j : Fin 16) (x : UnitAddTorus (Fin m)) : 0 ≤ circleWindowGaussian D j x :=
  Set.indicator_nonneg (fun _ _ => freeEdgeGaussian_nonneg D _) x

theorem circleWindowGaussian_le_one {m : ℕ} (D : Finset (Fin m × Fin m))
    (j : Fin 16) (x : UnitAddTorus (Fin m)) : circleWindowGaussian D j x ≤ 1 := by
  by_cases hx : x ∈ circleClusterWindow j (3 / 16 : ℝ)
  · simpa only [circleWindowGaussian, Set.indicator_of_mem hx] using freeEdgeGaussian_le_one D _
  · simp only [circleWindowGaussian, Set.indicator_of_notMem hx, zero_le_one]

theorem integrable_circleWindowGaussian {m : ℕ} (D : Finset (Fin m × Fin m)) (j : Fin 16) :
    Integrable (circleWindowGaussian D j) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_circleWindowGaussian D j).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (circleWindowGaussian_nonneg D j x)]
    exact circleWindowGaussian_le_one D j x

theorem circleClusterCell_good_eq_compl {m : ℕ} {j : Fin 16} {O : Finset (Fin m)}
    {x : UnitAddTorus (Fin m)} (hx : x ∈ circleClusterCell j O) : circleGood x j = Oᶜ := by
  rw [← hx.2]
  simp [circleOutliers, ← Finset.compl_eq_univ_sdiff]

theorem goodFreeGaussian_reindex {m : ℕ} (D : Finset (Fin m × Fin m))
    (G : Finset (Fin m)) (j : Fin 16) (x : UnitAddTorus (Fin m)) :
    Real.exp (-(∑ e ∈ goodFreeCosineEdges D G,
      (Real.pi * (circleCenteredLift j (x e.1.1) - circleCenteredLift j (x e.1.2))) ^ 2) / 2) =
      freeEdgeGaussian (restrictedArcSet D G)
        (fun i => circleCenteredLift j (goodCircleCoordinates G x i)) := by
  have h := sum_goodFreeCosineEdges_reindex D G (fun i => Real.pi * circleCenteredLift j (x i))
  simp only [← mul_sub] at h
  exact congrArg (fun s : ℝ => Real.exp (-s / 2)) h

theorem normalizedRegularIntegrand_cell_pointwise {m : ℕ} (D : Finset (Fin m × Fin m))
    (hm : Odd m) (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D)
    (j : Fin 16) (O : Finset (Fin m)) (x : UnitAddTorus (Fin m)) :
    (circleClusterCell j O).indicator (fun y => ‖normalizedRegularTorusIntegrand D y‖) x ≤
      (circleSeparationRatio ^ (m / 16 - 2)) ^ O.card *
        circleWindowGaussian (restrictedArcSet D Oᶜ) j (goodCircleCoordinates Oᶜ x) := by
  have hq : 0 ≤ (circleSeparationRatio ^ (m / 16 - 2)) ^ O.card :=
    pow_nonneg (pow_nonneg circleSeparationRatio_pos.le _) _
  by_cases hx : x ∈ circleClusterCell j O
  · rw [Set.indicator_of_mem hx]
    have hG := circleClusterCell_good_eq_compl hx
    have hwindow : goodCircleCoordinates Oᶜ x ∈ circleClusterWindow j (3 / 16 : ℝ) := by
      intro i
      apply circleClusterCell_good_constraints hx
      exact Finset.mem_compl.mp (goodVertex_mem Oᶜ i)
    have hbound := normalizedRegularTorusIntegrand_cluster_bound D hm x j
      (fun u _ => partialPermutation_neighbor_card_le_two D hs ht u (circleCore x j))
    rw [hx.2, hG, goodFreeGaussian_reindex D Oᶜ j x] at hbound
    refine hbound.trans ?_
    rw [circleWindowGaussian, Set.indicator_of_mem hwindow]
    exact mul_le_mul_of_nonneg_right
      (cluster_separation_power_le circleSeparationRatio_pos.le circleSeparationRatio_lt_one.le
        m (circleCore x j).card O.card hx.1) (freeEdgeGaussian_nonneg _ _)
  · rw [Set.indicator_of_notMem hx]
    exact mul_nonneg hq (circleWindowGaussian_nonneg _ _ _)

/-- The quantitative bound on one actual cluster cell. No additional root
or anchor choice is charged for an outlier containing the original anchor. -/
theorem integral_normalizedRegularIntegrand_cell_le {m : ℕ} (D : Finset (Fin m × Fin m))
    (hm : Odd m) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D)
    (j : Fin 16) (O : Finset (Fin m)) (hG : 16 ≤ Oᶜ.card) :
    (∫ x : UnitAddTorus (Fin m) in circleClusterCell j O, ‖normalizedRegularTorusIntegrand D x‖) ≤
      (circleSeparationRatio ^ (m / 16 - 2)) ^ O.card *
        ((3 / 8 : ℝ) * Real.exp 2 * quotientGaussianVolume Oᶜ.card / Real.pi ^ (Oᶜ.card - 1)) := by
  have hstrong := (measurable_circleWindowGaussian (restrictedArcSet D Oᶜ) j).stronglyMeasurable
  have hi := (measurePreserving_goodCircleCoordinates Oᶜ).integrable_comp_of_integrable
    (integrable_circleWindowGaussian (restrictedArcSet D Oᶜ) j)
  rw [← integral_indicator (measurableSet_circleClusterCell j O)]
  calc
    _ ≤ ∫ x : UnitAddTorus (Fin m), (circleSeparationRatio ^ (m / 16 - 2)) ^ O.card *
        circleWindowGaussian (restrictedArcSet D Oᶜ) j (goodCircleCoordinates Oᶜ x) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => norm_nonneg _) x
      · exact hi.const_mul _
      · exact Filter.Eventually.of_forall (normalizedRegularIntegrand_cell_pointwise D hm hs ht j O)
    _ = (circleSeparationRatio ^ (m / 16 - 2)) ^ O.card *
        ∫ y : UnitAddTorus (Fin Oᶜ.card), circleWindowGaussian (restrictedArcSet D Oᶜ) j y := by
      rw [integral_const_mul, integral_goodCircleCoordinates Oᶜ _ hstrong]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _
        (pow_nonneg (pow_nonneg circleSeparationRatio_pos.le _) _)
      change (∫ y, (circleClusterWindow j (3 / 16 : ℝ)).indicator
        (fun z => freeEdgeGaussian (restrictedArcSet D Oᶜ) (fun i => circleCenteredLift j (z i))) y) ≤ _
      rw [integral_indicator (measurableSet_circleClusterWindow j _)]
      exact integral_circleWindow_freeEdgeGaussian_le hG _ (restrictedArcSet_no_opposite D Oᶜ hD)
        (restrictedArcSet_source_injOn D Oᶜ hs) (restrictedArcSet_target_injOn D Oᶜ ht) j

end
end Wormald.FiniteModel

import Wormald.OutlierClusterTail

/-! The noncentral region with at least one outlier is an actual measurable
subset of the original torus. Its norm integral is bounded by the already
proved cluster-cell sum, uniformly over all partial permutations. -/

namespace Wormald.FiniteModel
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

local instance outlierRegionCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance outlierRegionCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def outlierClusterRegion (m : ℕ) : Set (UnitAddTorus (Fin m)) :=
  ⋃ p : Fin 16 × Finset (Fin m), if p.2 = ∅ then ∅ else circleClusterCell p.1 p.2

theorem measurableSet_outlierClusterRegion (m : ℕ) : MeasurableSet (outlierClusterRegion m) := by
  apply MeasurableSet.iUnion
  intro p
  split
  · exact MeasurableSet.empty
  · exact measurableSet_circleClusterCell _ _

theorem integral_outlierClusterRegion_le {m : ℕ} (D : Finset (Fin m × Fin m)) :
    (∫ x : UnitAddTorus (Fin m) in outlierClusterRegion m,
      ‖normalizedRegularTorusIntegrand D x‖) ≤ outlierClusterTail D := by
  let f : UnitAddTorus (Fin m) → ℝ := fun x => ‖normalizedRegularTorusIntegrand D x‖
  let H (p : Fin 16 × Finset (Fin m)) : UnitAddTorus (Fin m) → ℝ :=
    if p.2 = ∅ then 0 else (circleClusterCell p.1 p.2).indicator f
  have hf : Integrable f := (continuous_normalizedRegularTorusIntegrand D).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hH (p) : Integrable (H p) := by
    unfold H
    split
    · exact integrable_const (0 : ℝ)
    · exact hf.indicator (measurableSet_circleClusterCell _ _)
  have hH0 (p) (x) : 0 ≤ H p x := by
    unfold H
    split
    · exact le_rfl
    · exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) x
  rw [← integral_indicator (measurableSet_outlierClusterRegion m)]
  calc
    _ ≤ ∫ x : UnitAddTorus (Fin m), ∑ p : Fin 16 × Finset (Fin m), H p x := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => norm_nonneg _) x
      · exact integrable_finsetSum _ (fun p _ => hH p)
      · exact Filter.Eventually.of_forall fun x => by
          by_cases hx : x ∈ outlierClusterRegion m
          · obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
            have hp0 : p.2 ≠ ∅ := by intro h; simp [h] at hp
            have hcell : x ∈ circleClusterCell p.1 p.2 := by simpa only [ite_eq_right hp0] using hp
            rw [Set.indicator_of_mem hx]
            have heq : H p x = f x := by simp only [H, ite_eq_right hp0, Set.indicator_of_mem hcell]
            change f x ≤ ∑ p : Fin 16 × Finset (Fin m), H p x
            rw [← heq]
            exact Finset.single_le_sum (fun q _ => hH0 q x) (Finset.mem_univ p)
          · rw [Set.indicator_of_notMem hx]
            exact Finset.sum_nonneg fun p _ => hH0 p x
    _ = outlierClusterTail D := by
      rw [integral_finsetSum _ (fun p _ => hH p), Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro O _
      by_cases hO : O = ∅
      · subst O
        simp [H]
      · simp only [H, ite_eq_right hO, integral_indicator (measurableSet_circleClusterCell j O), f]

theorem outlierClusterRegion_uniform_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ D : Finset (Fin m × Fin m), Odd m →
      (∀ u v, (u, v) ∈ D → (v, u) ∉ D) →
      Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D →
      Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D →
      (∫ x : UnitAddTorus (Fin m) in outlierClusterRegion m, ‖normalizedRegularTorusIntegrand D x‖) /
        physicalGaussianQuotientVolume m < ε := by
  filter_upwards [eventually_ge_atTop 2, outlierClusterTail_uniform_small ε hε]
    with m hm htail D hodd hD hs ht
  exact (div_le_div_of_nonneg_right (integral_outlierClusterRegion_le D)
    (physicalGaussianQuotientVolume_pos hm).le).trans_lt (htail D hodd hD hs ht)

theorem tendsto_outlierClusterRegion {a : ℕ → ℕ} (ha : Tendsto a atTop atTop)
    (D : ∀ k, Finset (Fin (a k) × Fin (a k))) (hm : ∀ k, Odd (a k))
    (hD : ∀ k u v, (u, v) ∈ D k → (v, u) ∉ D k)
    (hs : ∀ k, Set.InjOn (Prod.fst : Fin (a k) × Fin (a k) → Fin (a k)) (D k))
    (ht : ∀ k, Set.InjOn (Prod.snd : Fin (a k) × Fin (a k) → Fin (a k)) (D k)) :
    Tendsto (fun k => (∫ x : UnitAddTorus (Fin (a k)) in outlierClusterRegion (a k),
      ‖normalizedRegularTorusIntegrand (D k) x‖) / physicalGaussianQuotientVolume (a k))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [ha.eventually (eventually_ge_atTop 2)] with k hk
    exact div_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (physicalGaussianQuotientVolume_pos hk).le
  · filter_upwards [ha.eventually (eventually_ge_atTop 2)] with k hk
    exact div_le_div_of_nonneg_right (integral_outlierClusterRegion_le (D k))
      (physicalGaussianQuotientVolume_pos hk).le
  · exact tendsto_outlierClusterTail ha D hm hD hs ht

end
end Wormald.FiniteModel

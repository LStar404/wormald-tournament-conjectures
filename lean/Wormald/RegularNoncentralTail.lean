import Wormald.OutlierClusterRegion
import Wormald.AllGoodRegionTail

/-! The complete noncentral tail of the original regular-degree Fourier
integrand. Every configuration is covered either by an outlier cell or by
an all-good window. Both actual norm integrals vanish uniformly. -/

namespace Wormald.FiniteModel
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

local instance noncentralTailCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance noncentralTailCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem circleAnchorWindow_compl_subset_clusters {m : ℕ} (a : Fin m) (r : ℝ) :
    (circleAnchorWindow a (r / (2 * Real.pi)))ᶜ ⊆
      outlierClusterRegion m ∪ allGoodOutsideRegion a r := by
  intro x hx
  obtain ⟨j, hj⟩ := exists_dense_circleCore x
  let O := circleOutliers x j
  have hcell : x ∈ circleClusterCell j O := ⟨hj, rfl⟩
  by_cases hO : O = ∅
  · apply Or.inr
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_, hx⟩
    intro i
    have hi : i ∉ O := by rw [hO]; exact Finset.notMem_empty i
    exact circleClusterCell_good_constraints hcell i hi
  · apply Or.inl
    exact Set.mem_iUnion.mpr ⟨(j, O), by simpa only [ite_eq_right hO] using hcell⟩

theorem integral_circleAnchorWindow_compl_le_clusters {m : ℕ}
    (D : Finset (Fin m × Fin m)) (a : Fin m) (r : ℝ) :
    (∫ x : UnitAddTorus (Fin m) in (circleAnchorWindow a (r / (2 * Real.pi)))ᶜ,
      ‖normalizedRegularTorusIntegrand D x‖) ≤
      (∫ x : UnitAddTorus (Fin m) in outlierClusterRegion m, ‖normalizedRegularTorusIntegrand D x‖) +
      (∫ x : UnitAddTorus (Fin m) in allGoodOutsideRegion a r, ‖normalizedRegularTorusIntegrand D x‖) := by
  let f : UnitAddTorus (Fin m) → ℝ := fun x => ‖normalizedRegularTorusIntegrand D x‖
  let A := (circleAnchorWindow a (r / (2 * Real.pi)))ᶜ
  let B := outlierClusterRegion m
  let C := allGoodOutsideRegion a r
  have hA : MeasurableSet A := (measurableSet_circleAnchorWindow _ _).compl
  have hB : MeasurableSet B := measurableSet_outlierClusterRegion m
  have hC : MeasurableSet C := measurableSet_allGoodOutsideRegion a r
  have hf : Integrable f := (continuous_normalizedRegularTorusIntegrand D).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  change (∫ x in A, f x) ≤ (∫ x in B, f x) + ∫ x in C, f x
  rw [← integral_indicator hA, ← integral_indicator hB, ← integral_indicator hC,
    ← integral_add (hf.indicator hB) (hf.indicator hC)]
  apply integral_mono (hf.indicator hA) ((hf.indicator hB).add (hf.indicator hC))
  intro x
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    simp only [Pi.add_apply]
    rcases circleAnchorWindow_compl_subset_clusters a r hx with h | h
    · change x ∈ B at h
      rw [Set.indicator_of_mem h]
      exact le_add_of_nonneg_right (Set.indicator_nonneg (fun _ _ => norm_nonneg _) x)
    · change x ∈ C at h
      rw [Set.indicator_of_mem h]
      exact le_add_of_nonneg_left (Set.indicator_nonneg (fun _ _ => norm_nonneg _) x)
  · rw [Set.indicator_of_notMem hx]
    simp only [Pi.add_apply]
    exact add_nonneg (Set.indicator_nonneg (fun _ _ => norm_nonneg _) x)
      (Set.indicator_nonneg (fun _ _ => norm_nonneg _) x)

def regularNoncentralError (m : ℕ) : ℝ := outlierClusterTailBound m + allGoodClusterTailBound m

theorem regularNoncentralError_nonneg (m : ℕ) : 0 ≤ regularNoncentralError m := by
  unfold regularNoncentralError outlierClusterTailBound allGoodClusterTailBound
  apply add_nonneg
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun r _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (clusterRemovalBase_nonneg m) _)
  · positivity

theorem tendsto_regularNoncentralError : Tendsto regularNoncentralError atTop (𝓝 0) := by
  change Tendsto (fun m => outlierClusterTailBound m + allGoodClusterTailBound m) atTop (𝓝 0)
  simpa only [add_zero] using tendsto_outlierClusterTailBound.add tendsto_allGoodClusterTailBound

theorem integral_regularNoncentral_norm_div_volume_le {m : ℕ} (hmLarge : 256 ≤ m)
    (D : Finset (Fin m × Fin m)) (hm : Odd m)
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D)
    (a : Fin m) (ha : a.val = m - 1) :
    (∫ x : UnitAddTorus (Fin m) in
      (circleAnchorWindow a (centralGaussianRadius m / (2 * Real.pi)))ᶜ,
        ‖normalizedRegularTorusIntegrand D x‖) / physicalGaussianQuotientVolume m ≤
      regularNoncentralError m := by
  have hV := (physicalGaussianQuotientVolume_pos (show 2 ≤ m by omega)).le
  have hout := (div_le_div_of_nonneg_right (integral_outlierClusterRegion_le D) hV).trans
    (outlierClusterTail_div_volume_le hmLarge D hm hD hs ht)
  have hgood := allGoodOutsideRegion_div_volume_le (show 16 ≤ m by omega) D hm hD hs ht a ha
  calc
    _ ≤ ((∫ x : UnitAddTorus (Fin m) in outlierClusterRegion m, ‖normalizedRegularTorusIntegrand D x‖) +
        (∫ x : UnitAddTorus (Fin m) in allGoodOutsideRegion a (centralGaussianRadius m),
          ‖normalizedRegularTorusIntegrand D x‖)) / physicalGaussianQuotientVolume m :=
      div_le_div_of_nonneg_right (integral_circleAnchorWindow_compl_le_clusters D a _) hV
    _ = _ := add_div _ _ _
    _ ≤ regularNoncentralError m := add_le_add hout hgood

theorem norm_regularNoncentralIntegral_div_volume_le {m : ℕ} (hmLarge : 256 ≤ m)
    (D : Finset (Fin m × Fin m)) (hm : Odd m)
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D)
    (a : Fin m) (ha : a.val = m - 1) :
    ‖(∫ x : UnitAddTorus (Fin m) in
      (circleAnchorWindow a (centralGaussianRadius m / (2 * Real.pi)))ᶜ,
        normalizedRegularTorusIntegrand D x) / (physicalGaussianQuotientVolume m : ℂ)‖ ≤
      regularNoncentralError m := by
  have hV := physicalGaussianQuotientVolume_pos (show 2 ≤ m by omega)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV]
  exact (div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) hV.le).trans
    (integral_regularNoncentral_norm_div_volume_le hmLarge D hm hD hs ht a ha)

theorem regularNoncentral_uniform_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ D : Finset (Fin m × Fin m), Odd m →
      (∀ u v, (u, v) ∈ D → (v, u) ∉ D) →
      Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D →
      Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D →
      ∀ a : Fin m, a.val = m - 1 →
      (∫ x : UnitAddTorus (Fin m) in
        (circleAnchorWindow a (centralGaussianRadius m / (2 * Real.pi)))ᶜ,
          ‖normalizedRegularTorusIntegrand D x‖) / physicalGaussianQuotientVolume m < ε := by
  filter_upwards [eventually_ge_atTop 256, tendsto_regularNoncentralError.eventually_lt_const hε]
    with m hm hsmall D hodd hD hs ht a ha
  exact (integral_regularNoncentral_norm_div_volume_le hm D hodd hD hs ht a ha).trans_lt hsmall

end
end Wormald.FiniteModel

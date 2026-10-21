import Wormald.AllGoodClusterTail
import Wormald.PhysicalGaussianQuotientVolume
import Wormald.CircleClusterCells

namespace Wormald.FiniteModel
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

local instance allGoodRegionCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance allGoodRegionCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def allGoodOutsideRegion {m : ℕ} (a : Fin m) (r : ℝ) : Set (UnitAddTorus (Fin m)) :=
  ⋃ j : Fin 16, circleClusterWindow j (3 / 16 : ℝ) \ circleAnchorWindow a (r / (2 * Real.pi))

theorem measurableSet_allGoodOutsideRegion {m : ℕ} (a : Fin m) (r : ℝ) :
    MeasurableSet (allGoodOutsideRegion a r) :=
  MeasurableSet.iUnion fun j => (measurableSet_circleClusterWindow j _).diff
    (measurableSet_circleAnchorWindow _ _)

theorem integral_allGoodOutsideRegion_le_sum {m : ℕ} (D : Finset (Fin m × Fin m))
    (a : Fin m) (r : ℝ) :
    (∫ x : UnitAddTorus (Fin m) in allGoodOutsideRegion a r,
      ‖normalizedRegularTorusIntegrand D x‖) ≤
        ∑ j : Fin 16, ∫ x in circleClusterWindow j (3 / 16 : ℝ) \
          circleAnchorWindow a (r / (2 * Real.pi)), ‖normalizedRegularTorusIntegrand D x‖ := by
  let f : UnitAddTorus (Fin m) → ℝ := fun x => ‖normalizedRegularTorusIntegrand D x‖
  let A (j : Fin 16) := circleClusterWindow j (3 / 16 : ℝ) \
    circleAnchorWindow a (r / (2 * Real.pi))
  have hA (j) : MeasurableSet (A j) := (measurableSet_circleClusterWindow j _).diff
    (measurableSet_circleAnchorWindow _ _)
  have hf : Integrable f := (continuous_normalizedRegularTorusIntegrand D).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  rw [← integral_indicator (measurableSet_allGoodOutsideRegion a r)]
  calc
    _ ≤ ∫ x : UnitAddTorus (Fin m), ∑ j : Fin 16, (A j).indicator f x := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => norm_nonneg _) x
      · exact integrable_finsetSum _ (fun j _ => hf.indicator (hA j))
      · exact Eventually.of_forall fun x => by
          by_cases hx : x ∈ allGoodOutsideRegion a r
          · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
            rw [Set.indicator_of_mem hx]
            change f x ≤ _
            rw [← Set.indicator_of_mem hj f]
            exact Finset.single_le_sum
              (f := fun k : Fin 16 => (A k).indicator f x)
              (fun k _ => Set.indicator_nonneg (fun y _ => show 0 ≤ f y from norm_nonneg _) x)
              (Finset.mem_univ j)
          · rw [Set.indicator_of_notMem hx]
            exact Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) x
    _ = _ := by
      rw [integral_finsetSum _ (fun j _ => hf.indicator (hA j))]
      exact Finset.sum_congr rfl fun j _ => integral_indicator (hA j)

def allGoodClusterTailBound (m : ℕ) : ℝ := 6 * Real.exp 2 * Real.sqrt (centralGaussianTail m)

theorem tendsto_allGoodClusterTailBound : Tendsto allGoodClusterTailBound atTop (𝓝 0) := by
  change Tendsto (fun m => allGoodClusterTailBound m) atTop (𝓝 0)
  have h := (Real.continuous_sqrt.tendsto 0).comp tendsto_centralGaussianTail
  simpa only [allGoodClusterTailBound, Real.sqrt_zero, mul_zero, Function.comp_def] using
    h.const_mul (6 * Real.exp 2)

theorem allGoodOutsideRegion_div_volume_le {m : ℕ} (hm : 16 ≤ m)
    (D : Finset (Fin m × Fin m)) (hmOdd : Odd m)
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D)
    (a : Fin m) (ha : a.val = m - 1) :
    (∫ x : UnitAddTorus (Fin m) in allGoodOutsideRegion a (centralGaussianRadius m),
      ‖normalizedRegularTorusIntegrand D x‖) / physicalGaussianQuotientVolume m ≤
        allGoodClusterTailBound m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have ha' : a = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
  subst a
  have hV := physicalGaussianQuotientVolume_pos (show 2 ≤ n + 2 by omega)
  apply (div_le_iff₀ hV).mpr
  calc
    _ ≤ ∑ j : Fin 16, ∫ x in circleClusterWindow j (3 / 16 : ℝ) \
        circleAnchorWindow (Fin.last (n + 1)) (centralGaussianRadius (n + 2) / (2 * Real.pi)),
          ‖normalizedRegularTorusIntegrand D x‖ := integral_allGoodOutsideRegion_le_sum _ _ _
    _ ≤ ∑ _j : Fin 16, (3 / 8 : ℝ) * Real.exp 2 *
        Real.sqrt (2 * ((n + 2 : ℕ) : ℝ) * Real.exp (-((n + 2 : ℕ) : ℝ) *
          centralGaussianRadius (n + 2) ^ 2 / 32)) *
            quotientGaussianVolume (n + 2) / Real.pi ^ (n + 1) :=
      Finset.sum_le_sum fun j _ => integral_normalizedRegularTorusIntegrand_allGood_outside_le
        hm hmOdd D hD hs ht j _ (centralGaussianRadius_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        allGoodClusterTailBound, centralGaussianTail, physicalGaussianQuotientVolume,
        show n + 2 - 1 = n + 1 by omega]
      ring

theorem allGoodOutsideRegion_uniform_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ D : Finset (Fin m × Fin m), Odd m →
      (∀ u v, (u, v) ∈ D → (v, u) ∉ D) →
      Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D →
      Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D →
      ∀ a : Fin m, a.val = m - 1 →
      (∫ x : UnitAddTorus (Fin m) in allGoodOutsideRegion a (centralGaussianRadius m),
        ‖normalizedRegularTorusIntegrand D x‖) / physicalGaussianQuotientVolume m < ε := by
  filter_upwards [eventually_ge_atTop 16, tendsto_allGoodClusterTailBound.eventually_lt_const hε]
    with m hm hbound D hodd hD hs ht a ha
  exact (allGoodOutsideRegion_div_volume_le hm D hodd hD hs ht a ha).trans_lt hbound

end
end Wormald.FiniteModel

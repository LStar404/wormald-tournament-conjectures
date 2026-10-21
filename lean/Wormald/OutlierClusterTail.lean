import Wormald.GoodClusterCellBound
import Wormald.PhysicalGaussianQuotientVolume
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Uniform disappearance of the genuine cluster cells with at least one
outlier, relative to the exact complete-graph Gaussian normalization. -/

namespace Wormald.FiniteModel
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

local instance outlierTailCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance outlierTailCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def clusterRemovalBase (m : ℕ) : ℝ :=
  Real.sqrt (Real.pi * Real.exp 1 / 2) * Real.sqrt (m : ℝ) * circleSeparationRatio ^ (m / 16 - 2)

theorem clusterRemovalBase_nonneg (m : ℕ) : 0 ≤ clusterRemovalBase m :=
  mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (pow_nonneg circleSeparationRatio_pos.le _)

theorem integral_normalizedRegularIntegrand_cell_div_volume_le {m : ℕ} (hmLarge : 256 ≤ m)
    (D : Finset (Fin m × Fin m)) (hm : Odd m)
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D)
    (j : Fin 16) (O : Finset (Fin m)) :
    (∫ x : UnitAddTorus (Fin m) in circleClusterCell j O, ‖normalizedRegularTorusIntegrand D x‖) /
        physicalGaussianQuotientVolume m ≤
      ((3 / 8 : ℝ) * Real.exp 2) * clusterRemovalBase m ^ O.card := by
  have hm2 : 2 ≤ m := by omega
  have hV := physicalGaussianQuotientVolume_pos hm2
  by_cases hG : 16 ≤ Oᶜ.card
  · have hgm : Oᶜ.card ≤ m := by simpa only [Fintype.card_fin] using Finset.card_le_univ Oᶜ
    have hcard : m - Oᶜ.card = O.card := by
      have h := Finset.card_add_card_compl O
      simp only [Fintype.card_fin] at h
      omega
    have hc := integral_normalizedRegularIntegrand_cell_le D hm hD hs ht j O hG
    have hratio := physicalGaussianQuotientVolume_ratio_le (show 2 ≤ Oᶜ.card by omega) hgm
    rw [hcard] at hratio
    calc
      _ ≤ ((circleSeparationRatio ^ (m / 16 - 2)) ^ O.card *
          ((3 / 8 : ℝ) * Real.exp 2 * physicalGaussianQuotientVolume Oᶜ.card)) /
            physicalGaussianQuotientVolume m := by
        apply div_le_div_of_nonneg_right _ hV.le
        convert hc using 1; simp only [physicalGaussianQuotientVolume]; ring
      _ = ((3 / 8 : ℝ) * Real.exp 2) * (circleSeparationRatio ^ (m / 16 - 2)) ^ O.card *
          (physicalGaussianQuotientVolume Oᶜ.card / physicalGaussianQuotientVolume m) := by ring
      _ ≤ ((3 / 8 : ℝ) * Real.exp 2) * (circleSeparationRatio ^ (m / 16 - 2)) ^ O.card *
          (Real.sqrt (Real.pi * Real.exp 1 / 2) * Real.sqrt (m : ℝ)) ^ O.card := by
        exact mul_le_mul_of_nonneg_left hratio
          (mul_nonneg (by positivity) (pow_nonneg (pow_nonneg circleSeparationRatio_pos.le _) _))
      _ = _ := by rw [clusterRemovalBase, mul_pow]; ring
  · have hcell : circleClusterCell j O = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hgood := (circleClusterCell_good_card hx).2
      rw [circleClusterCell_good_eq_compl hx] at hgood
      omega
    rw [hcell, setIntegral_empty, zero_div]
    exact mul_nonneg (by positivity) (pow_nonneg (clusterRemovalBase_nonneg m) _)

theorem sum_nonempty_finsets_card_pow (m : ℕ) (A : ℝ) :
    (∑ O : Finset (Fin m), if O = ∅ then 0 else A ^ O.card) =
      ∑ r ∈ Icc 1 m, (m.choose r : ℝ) * A ^ r := by
  let f : ℕ → ℝ := fun k => if k = 0 then 0 else A ^ k
  have hpow : (Finset.univ : Finset (Finset (Fin m))) = (Finset.univ : Finset (Fin m)).powerset := by
    ext O
    simp only [Finset.mem_univ, Finset.mem_powerset, Finset.subset_univ, iff_self]
  calc
    _ = ∑ O : Finset (Fin m), f O.card := by simp only [f, Finset.card_eq_zero]
    _ = ∑ r ∈ range (m + 1), (m.choose r : ℝ) * f r := by
      rw [hpow, sum_powerset]
      simp_rw [sum_powersetCard]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ r ∈ Icc 1 m, (m.choose r : ℝ) * f r := by
      symm
      apply Finset.sum_subset
      · intro r hr
        simp only [mem_Icc] at hr
        exact mem_range.mpr (by omega)
      · intro r hr hnot
        have hr0 : r = 0 := by simp only [mem_range] at hr; simp only [mem_Icc, not_and] at hnot; omega
        simp only [hr0, f, ite_eq_left rfl, mul_zero]
    _ = _ := Finset.sum_congr rfl fun r hr => by
      have hr0 : r ≠ 0 := by have := (mem_Icc.mp hr).1; omega
      simp only [f, ite_eq_right hr0]

def outlierClusterTail {m : ℕ} (D : Finset (Fin m × Fin m)) : ℝ :=
  ∑ j : Fin 16, ∑ O : Finset (Fin m), if O = ∅ then 0 else
    ∫ x : UnitAddTorus (Fin m) in circleClusterCell j O, ‖normalizedRegularTorusIntegrand D x‖

theorem outlierClusterTail_nonneg {m : ℕ} (D : Finset (Fin m × Fin m)) :
    0 ≤ outlierClusterTail D := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro O _
  split
  · exact le_rfl
  · exact integral_nonneg fun _ => norm_nonneg _

theorem outlierClusterTail_div_volume_le {m : ℕ} (hmLarge : 256 ≤ m)
    (D : Finset (Fin m × Fin m)) (hm : Odd m)
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D) :
    outlierClusterTail D / physicalGaussianQuotientVolume m ≤
      (16 : ℝ) * ((3 / 8 : ℝ) * Real.exp 2) *
        ∑ r ∈ Icc 1 m, (m.choose r : ℝ) * clusterRemovalBase m ^ r := by
  unfold outlierClusterTail
  simp_rw [Finset.sum_div]
  calc
    _ ≤ ∑ _j : Fin 16, ∑ O : Finset (Fin m),
        ((3 / 8 : ℝ) * Real.exp 2) * (if O = ∅ then 0 else clusterRemovalBase m ^ O.card) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro O _
      split_ifs with hO
      · simp only [zero_div, mul_zero, le_refl]
      · exact integral_normalizedRegularIntegrand_cell_div_volume_le hmLarge D hm hD hs ht j O
    _ = _ := by
      simp_rw [← Finset.mul_sum, sum_nonempty_finsets_card_pow]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

def outlierClusterTailBound (m : ℕ) : ℝ :=
  (16 : ℝ) * ((3 / 8 : ℝ) * Real.exp 2) *
    ∑ r ∈ Icc 1 m, (m.choose r : ℝ) * clusterRemovalBase m ^ r

theorem tendsto_outlierClusterTailBound : Tendsto outlierClusterTailBound atTop (𝓝 0) := by
  change Tendsto (fun m => outlierClusterTailBound m) atTop (𝓝 0)
  have h := (tendsto_actual_circle_cluster_tail (Real.sqrt (Real.pi * Real.exp 1 / 2))
    (Real.sqrt_nonneg _)).const_mul ((16 : ℝ) * ((3 / 8 : ℝ) * Real.exp 2))
  simpa only [outlierClusterTailBound, clusterRemovalBase, mul_zero] using h

/-- The estimate is uniform over all prescribed partial permutations, even
when their number of edges grows linearly with the number of vertices. -/
theorem outlierClusterTail_uniform_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ D : Finset (Fin m × Fin m), Odd m →
      (∀ u v, (u, v) ∈ D → (v, u) ∉ D) →
      Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D →
      Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D →
      outlierClusterTail D / physicalGaussianQuotientVolume m < ε := by
  filter_upwards [eventually_ge_atTop 256, tendsto_outlierClusterTailBound.eventually_lt_const hε]
    with m hm hbound D hodd hD hs ht
  exact (outlierClusterTail_div_volume_le hm D hodd hD hs ht).trans_lt hbound

theorem tendsto_outlierClusterTail {a : ℕ → ℕ} (ha : Tendsto a atTop atTop)
    (D : ∀ k, Finset (Fin (a k) × Fin (a k))) (hm : ∀ k, Odd (a k))
    (hD : ∀ k u v, (u, v) ∈ D k → (v, u) ∉ D k)
    (hs : ∀ k, Set.InjOn (Prod.fst : Fin (a k) × Fin (a k) → Fin (a k)) (D k))
    (ht : ∀ k, Set.InjOn (Prod.snd : Fin (a k) × Fin (a k) → Fin (a k)) (D k)) :
    Tendsto (fun k => outlierClusterTail (D k) / physicalGaussianQuotientVolume (a k))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [ha.eventually (eventually_ge_atTop 2)] with k hk
    exact div_nonneg (outlierClusterTail_nonneg _) (physicalGaussianQuotientVolume_pos hk).le
  · filter_upwards [ha.eventually (eventually_ge_atTop 256)] with k hk
    exact outlierClusterTail_div_volume_le hk (D k) (hm k) (hD k) (hs k) (ht k)
  · exact tendsto_outlierClusterTailBound.comp ha

end
end Wormald.FiniteModel

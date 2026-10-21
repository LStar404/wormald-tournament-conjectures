import Wormald.CircleClusterCover
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Measurable cells for the finite circle-cluster cover. A cell fixes the
grid center and the exact outlier subset; overlapping cores require only
an integral upper bound, never a disjointness claim. -/

namespace Wormald
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem measurable_circleCore {m : ℕ} (j : Fin 16) :
    Measurable (fun x : Fin m → UnitAddCircle => circleCore x j) := by
  rw [measurable_finset_iff]
  intro i
  simp only [mem_circleCore]
  exact measurableSet_setOfPred.mp
    (isClosed_le ((continuous_apply i).dist continuous_const) continuous_const).measurableSet

theorem measurable_circleOutliers {m : ℕ} (j : Fin 16) :
    Measurable (fun x : Fin m → UnitAddCircle => circleOutliers x j) := by
  rw [measurable_finset_iff]
  intro i
  simp only [mem_circleOutliers]
  exact measurableSet_setOfPred.mp
    (isOpen_lt continuous_const ((continuous_apply i).dist continuous_const)).measurableSet

def circleClusterCell {m : ℕ} (j : Fin 16) (O : Finset (Fin m)) :
    Set (Fin m → UnitAddCircle) := {x | m ≤ 16 * (circleCore x j).card ∧ circleOutliers x j = O}

theorem measurableSet_circleClusterCell {m : ℕ} (j : Fin 16) (O : Finset (Fin m)) :
    MeasurableSet (circleClusterCell j O) := by
  have hcard : Measurable (fun x : Fin m → UnitAddCircle => (circleCore x j).card) :=
    (measurable_of_countable Finset.card).comp (measurable_circleCore j)
  exact (measurableSet_le measurable_const (measurable_const.mul hcard)).inter
    (measurableSet_eq_fun (measurable_circleOutliers j) measurable_const)

theorem circleClusterCell_cover (m : ℕ) :
    (⋃ j : Fin 16, ⋃ O : Finset (Fin m), circleClusterCell j O) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨j, hj⟩ := exists_dense_circleCore x
  exact ⟨j, circleOutliers x j, hj, rfl⟩

theorem circleClusterCell_good_card {m : ℕ} {j : Fin 16} {O : Finset (Fin m)}
    {x : Fin m → UnitAddCircle} (hx : x ∈ circleClusterCell j O) :
    (circleGood x j).card + O.card = m ∧ m ≤ 16 * (circleGood x j).card := by
  exact ⟨by simpa only [hx.2] using circleGood_card_add_outliers x j,
    dense_circleGood_card x j hx.1⟩

theorem circleClusterCell_good_constraints {m : ℕ} {j : Fin 16} {O : Finset (Fin m)}
    {x : Fin m → UnitAddCircle} (hx : x ∈ circleClusterCell j O) :
    ∀ i ∉ O, dist (x i) (circleGridCenter j) ≤ 3 / 16 := by
  intro i hi
  rw [← hx.2, mem_circleOutliers, not_lt] at hi
  exact hi

/-- The covering step for any nonnegative integrable function. The sum
has exactly sixteen center choices and one choice of the outlier subset. -/
theorem integral_le_sum_circleClusterCells {m : ℕ}
    (μ : Measure (Fin m → UnitAddCircle)) (f : (Fin m → UnitAddCircle) → ℝ)
    (hf : Integrable f μ) (hnonneg : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂μ) ≤ ∑ p : Fin 16 × Finset (Fin m),
      ∫ x in circleClusterCell p.1 p.2, f x ∂μ := by
  have hints (p : Fin 16 × Finset (Fin m)) :
      Integrable ((circleClusterCell p.1 p.2).indicator f) μ :=
    hf.indicator (measurableSet_circleClusterCell p.1 p.2)
  calc
    _ ≤ ∫ x, ∑ p : Fin 16 × Finset (Fin m), (circleClusterCell p.1 p.2).indicator f x ∂μ := by
      apply integral_mono hf (integrable_finsetSum _ (fun p _ => hints p))
      intro x
      obtain ⟨j, hj⟩ := exists_dense_circleCore x
      let p : Fin 16 × Finset (Fin m) := (j, circleOutliers x j)
      have hp : x ∈ circleClusterCell p.1 p.2 := ⟨hj, rfl⟩
      calc
        _ = (circleClusterCell p.1 p.2).indicator f x := (Set.indicator_of_mem hp f).symm
        _ ≤ _ := Finset.single_le_sum
          (f := fun q : Fin 16 × Finset (Fin m) => (circleClusterCell q.1 q.2).indicator f x)
          (fun q _ => Set.indicator_nonneg (fun x _ => hnonneg x) x)
          (Finset.mem_univ p)
    _ = ∑ p : Fin 16 × Finset (Fin m), ∫ x, (circleClusterCell p.1 p.2).indicator f x ∂μ :=
      integral_finsetSum _ (fun p _ => hints p)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      exact integral_indicator (measurableSet_circleClusterCell p.1 p.2)

end
end Wormald

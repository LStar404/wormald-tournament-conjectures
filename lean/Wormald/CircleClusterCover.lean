import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-! A finite circle-cluster decomposition for the high-dimensional regular
tournament Fourier integral. Sixteen closed core balls cover the circle.
A dense core and its enlarged good ball separate every outlier from every
core point. Closed balls avoid boundary exceptions and overlap costs only
the fixed number of centers. -/

namespace Wormald
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def circleGridCenter (j : Fin 16) : UnitAddCircle := ((j.val : ℝ) / 16 : ℝ)

theorem circle_dist_coe_le (a b : ℝ) :
    dist (a : UnitAddCircle) (b : UnitAddCircle) ≤ |a - b| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  exact QuotientAddGroup.norm_mk_le_norm

theorem circle_grid_cover (z : UnitAddCircle) :
    ∃ j : Fin 16, dist z (circleGridCenter j) ≤ (1 / 16 : ℝ) := by
  obtain ⟨y, hy, rfl⟩ := AddCircle.eq_coe_Ico z
  have hnonneg : 0 ≤ 16 * y := mul_nonneg (by norm_num) hy.1
  have hj : ⌊16 * y⌋₊ < 16 := (Nat.floor_lt hnonneg).mpr (by norm_num at hy ⊢; linarith)
  refine ⟨⟨⌊16 * y⌋₊, hj⟩, (circle_dist_coe_le y (⌊16 * y⌋₊ / 16)).trans ?_⟩
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one (16 * y)
  rw [abs_of_nonneg (by linarith : 0 ≤ y - (⌊16 * y⌋₊ : ℝ) / 16)]
  linarith

def circleCore {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16) : Finset (Fin m) :=
  Finset.univ.filter (fun i => dist (x i) (circleGridCenter j) ≤ 1 / 16)

def circleGood {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16) : Finset (Fin m) :=
  Finset.univ.filter (fun i => dist (x i) (circleGridCenter j) ≤ 3 / 16)

def circleOutliers {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16) : Finset (Fin m) :=
  Finset.univ \ circleGood x j

@[simp] theorem mem_circleCore {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16) (i : Fin m) :
    i ∈ circleCore x j ↔ dist (x i) (circleGridCenter j) ≤ 1 / 16 := by
  simp only [circleCore, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_circleGood {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16) (i : Fin m) :
    i ∈ circleGood x j ↔ dist (x i) (circleGridCenter j) ≤ 3 / 16 := by
  simp only [circleGood, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_circleOutliers {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16) (i : Fin m) :
    i ∈ circleOutliers x j ↔ 3 / 16 < dist (x i) (circleGridCenter j) := by
  simp only [circleOutliers, Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_circleGood, not_le]

theorem circleCore_subset_good {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16) :
    circleCore x j ⊆ circleGood x j := by
  intro i hi
  rw [mem_circleCore] at hi
  rw [mem_circleGood]
  linarith

theorem circle_core_cover {m : ℕ} (x : Fin m → UnitAddCircle) (i : Fin m) :
    ∃ j : Fin 16, i ∈ circleCore x j := by
  simpa only [mem_circleCore] using circle_grid_cover (x i)

/-- At least one of the sixteen cores contains a sixteenth of the vertices.
The integer inequality avoids a floor or ceiling convention. -/
theorem exists_dense_circleCore {m : ℕ} (x : Fin m → UnitAddCircle) :
    ∃ j : Fin 16, m ≤ 16 * (circleCore x j).card := by
  have hcount : m ≤ ∑ j : Fin 16, (circleCore x j).card := by
    calc
      m = ∑ _i : Fin m, 1 := by simp
      _ ≤ ∑ i : Fin m, ∑ j : Fin 16, if i ∈ circleCore x j then 1 else 0 := by
        apply Finset.sum_le_sum
        intro i _
        obtain ⟨j, hj⟩ := circle_core_cover x i
        exact (by simpa only [hj, ite_true] using
          (Finset.single_le_sum (f := fun j => if i ∈ circleCore x j then (1 : ℕ) else 0)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)))
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.card_filter]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin 16 => (circleCore x j).card) (by simp)
  refine ⟨j, hcount.trans ?_⟩
  calc
    _ ≤ ∑ _k : Fin 16, (circleCore x j).card :=
      Finset.sum_le_sum (fun k hk => hj k hk)
    _ = _ := by simp

theorem dense_circleGood_card {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16)
    (hj : m ≤ 16 * (circleCore x j).card) :
    m ≤ 16 * (circleGood x j).card :=
  hj.trans (Nat.mul_le_mul_left _ (Finset.card_le_card (circleCore_subset_good x j)))

theorem circleGood_card_add_outliers {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16) :
    (circleGood x j).card + (circleOutliers x j).card = m := by
  simpa [circleOutliers, Finset.compl_eq_univ_sdiff] using
    Finset.card_add_card_compl (circleGood x j)

theorem circleCore_outlier_separation {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16)
    {u v : Fin m} (hu : u ∈ circleOutliers x j) (hv : v ∈ circleCore x j) :
    (1 / 8 : ℝ) < dist (x u) (x v) := by
  rw [mem_circleOutliers] at hu
  rw [mem_circleCore] at hv
  have htri := dist_triangle (x u) (x v) (circleGridCenter j)
  linarith

/-- A single real lift around the selected grid center, including all
circle boundary cases. -/
def circleCenteredLift (j : Fin 16) (z : UnitAddCircle) : ℝ :=
  (AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) (z - circleGridCenter j)).1

theorem circleCenteredLift_coe (j : Fin 16) (z : UnitAddCircle) :
    (circleCenteredLift j z : UnitAddCircle) = z - circleGridCenter j :=
  AddCircle.coe_equivIoc

theorem circleCenteredLift_abs_le_half (j : Fin 16) (z : UnitAddCircle) :
    |circleCenteredLift j z| ≤ (1 / 2 : ℝ) := by
  have h := (AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) (z - circleGridCenter j)).2
  unfold circleCenteredLift
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

theorem circleCenteredLift_abs_eq_dist (j : Fin 16) (z : UnitAddCircle) :
    |circleCenteredLift j z| = dist z (circleGridCenter j) := by
  rw [dist_eq_norm, ← circleCenteredLift_coe j z]
  symm
  exact (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num : (1 : ℝ) ≠ 0)).mpr
    (by simpa only [abs_one] using circleCenteredLift_abs_le_half j z)

theorem circleCenteredLift_good_bound {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16)
    {i : Fin m} (hi : i ∈ circleGood x j) : |circleCenteredLift j (x i)| ≤ 3 / 16 := by
  rw [circleCenteredLift_abs_eq_dist]
  exact (mem_circleGood x j i).mp hi

theorem circleGood_lift_distance {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16)
    {u v : Fin m} (hu : u ∈ circleGood x j) (hv : v ∈ circleGood x j) :
    dist (x u) (x v) = |circleCenteredLift j (x u) - circleCenteredLift j (x v)| := by
  have hbound : |circleCenteredLift j (x u) - circleCenteredLift j (x v)| ≤ 3 / 8 := by
    have hh := abs_sub (circleCenteredLift j (x u)) (circleCenteredLift j (x v))
    linarith [circleCenteredLift_good_bound x j hu, circleCenteredLift_good_bound x j hv]
  have hcoe : ((circleCenteredLift j (x u) - circleCenteredLift j (x v) : ℝ) : UnitAddCircle) =
      x u - x v := by
    rw [QuotientAddGroup.mk_sub, circleCenteredLift_coe, circleCenteredLift_coe]
    abel
  rw [dist_eq_norm, ← hcoe]
  exact (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num : (1 : ℝ) ≠ 0)).mpr
    (by norm_num; linarith)

/-- Choosing an exact outlier subset costs at most m^r possibilities. The
additional cover over grid centers has the fixed factor sixteen. -/
theorem circle_outlier_choices_le (m r : ℕ) :
    16 * ((Finset.univ : Finset (Fin m)).powersetCard r).card ≤ 16 * m ^ r := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact Nat.mul_le_mul_left _ (Nat.choose_le_pow m r)

/-- After deleting at most Δ core neighbors per outlier, there remain at
least r(c−Δ) separated cross pairs. -/
theorem available_core_pairs_card_lower {α : Type*} [DecidableEq α]
    (O C : Finset α) (p : α → α → Prop) (Δ : ℕ)
    (hdeleted : ∀ u ∈ O, (C.filter (fun v => ¬ p u v)).card ≤ Δ) :
    O.card * (C.card - Δ) ≤ ((O ×ˢ C).filter (fun uv => p uv.1 uv.2)).card := by
  have hrows : ((O ×ˢ C).filter (fun uv => p uv.1 uv.2)).card =
      ∑ u ∈ O, (C.filter (p u)).card := by
    simp only [Finset.card_filter, Finset.sum_product]
  rw [hrows]
  calc
    _ = ∑ _u ∈ O, (C.card - Δ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u hu
      have hparts := Finset.card_filter_add_card_filter_not (s := C) (p u)
      have hdel := hdeleted u hu
      omega

end
end Wormald

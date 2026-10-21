import Wormald.CircleClusterEdges
import Wormald.CosineTaylorBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! A well-defined positive cosine kernel on the unit circle and the exact
finite extraction of separated core–outlier cosine factors. -/

namespace Wormald
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def circleCosineKernel (z w : UnitAddCircle) : ℝ := Real.cos (Real.pi * dist z w)

theorem unitCircle_dist_le_half (z w : UnitAddCircle) : dist z w ≤ (1 / 2 : ℝ) := by
  simpa only [dist_eq_norm, abs_one] using
    (AddCircle.norm_le_half_period 1 (x := z - w) (by norm_num : (1 : ℝ) ≠ 0))

theorem circleCosineKernel_nonneg (z w : UnitAddCircle) : 0 ≤ circleCosineKernel z w := by
  unfold circleCosineKernel
  apply Real.cos_nonneg_of_mem_Icc
  have hp := Real.pi_pos
  constructor
  · nlinarith [dist_nonneg (x := z) (y := w)]
  · nlinarith [unitCircle_dist_le_half z w]

theorem circleCosineKernel_le_one (z w : UnitAddCircle) : circleCosineKernel z w ≤ 1 :=
  Real.cos_le_one _

theorem abs_cos_pi_mul_eq_circle_norm (t : ℝ) :
    |Real.cos (Real.pi * t)| = Real.cos (Real.pi * ‖(t : UnitAddCircle)‖) := by
  rw [UnitAddCircle.norm_eq]
  have hfrac := abs_sub_round t
  have hsign : |(-1 : ℝ) ^ round t| = 1 := by
    simpa only [Real.cos_int_mul_pi] using Real.abs_cos_int_mul_pi (round t)
  have hnonneg : 0 ≤ Real.cos (Real.pi * (t - round t)) := by
    apply Real.cos_nonneg_of_mem_Icc
    rw [abs_le] at hfrac
    have hp := Real.pi_pos
    constructor <;> nlinarith [hfrac.1, hfrac.2]
  calc
    _ = |Real.cos (Real.pi * t - round t * Real.pi)| := by
      rw [Real.cos_sub_int_mul_pi, abs_mul, hsign, one_mul]
    _ = Real.cos (Real.pi * (t - round t)) := by
      rw [show Real.pi * t - round t * Real.pi = Real.pi * (t - round t) by ring,
        abs_of_nonneg hnonneg]
    _ = _ := by rw [show Real.pi * |t - round t| = |Real.pi * (t - round t)| by
        rw [abs_mul, abs_of_pos Real.pi_pos], Real.cos_abs]

theorem abs_cos_pi_sub_eq_circleKernel (a b : ℝ) :
    |Real.cos (Real.pi * (a - b))| = circleCosineKernel (a : UnitAddCircle) (b : UnitAddCircle) := by
  unfold circleCosineKernel
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  exact abs_cos_pi_mul_eq_circle_norm (a - b)

def circleSeparationRatio : ℝ := Real.cos (Real.pi / 8)

theorem circleSeparationRatio_pos : 0 < circleSeparationRatio := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

theorem circleSeparationRatio_lt_one : circleSeparationRatio < 1 := by
  have h := Real.strictAntiOn_cos (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by
      constructor <;> linarith [Real.pi_pos])
    (show Real.pi / 8 ∈ Set.Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos])
    (show (0 : ℝ) < Real.pi / 8 by linarith [Real.pi_pos])
  simpa only [Real.cos_zero, circleSeparationRatio] using h

theorem circleCosineKernel_le_separationRatio {z w : UnitAddCircle}
    (hfar : (1 / 8 : ℝ) ≤ dist z w) :
    circleCosineKernel z w ≤ circleSeparationRatio := by
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · linarith [Real.pi_pos]
  · nlinarith [unitCircle_dist_le_half z w, Real.pi_pos]
  · nlinarith [Real.pi_pos]

theorem circleCosineKernel_good_lifts {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16)
    {u v : Fin m} (hu : u ∈ circleGood x j) (hv : v ∈ circleGood x j) :
    circleCosineKernel (x u) (x v) =
      Real.cos (Real.pi * (circleCenteredLift j (x u) - circleCenteredLift j (x v))) := by
  unfold circleCosineKernel
  rw [circleGood_lift_distance x j hu hv]
  rw [show Real.pi * |circleCenteredLift j (x u) - circleCenteredLift j (x v)| =
      |Real.pi * (circleCenteredLift j (x u) - circleCenteredLift j (x v))| by
    rw [abs_mul, abs_of_pos Real.pi_pos], Real.cos_abs]

theorem circleCosineKernel_good_gaussian {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16)
    {u v : Fin m} (hu : u ∈ circleGood x j) (hv : v ∈ circleGood x j) :
    circleCosineKernel (x u) (x v) ≤
      Real.exp (-((Real.pi * (circleCenteredLift j (x u) - circleCenteredLift j (x v))) ^ 2 / 2)) := by
  have hdiff : |circleCenteredLift j (x u) - circleCenteredLift j (x v)| ≤ (1 / 2 : ℝ) := by
    rw [← circleGood_lift_distance x j hu hv]
    exact unitCircle_dist_le_half _ _
  have hangle : |Real.pi * (circleCenteredLift j (x u) - circleCenteredLift j (x v))| ≤
      Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  rw [circleCosineKernel_good_lifts x j hu hv]
  exact (le_abs_self _).trans (abs_cos_le_exp_neg_half_sq _ hangle)

theorem product_extract_separated_factors {α : Type*} [DecidableEq α]
    (E S G : Finset α) (f : α → ℝ) (q : ℝ)
    (hS : S ⊆ E) (hG : G ⊆ E) (hdisj : Disjoint S G)
    (h0 : ∀ i ∈ E, 0 ≤ f i) (h1 : ∀ i ∈ E, f i ≤ 1) (hsep : ∀ i ∈ S, f i ≤ q) :
    (∏ i ∈ E, f i) ≤ q ^ S.card * ∏ i ∈ G, f i := by
  have hsubset : S ∪ G ⊆ E := Finset.union_subset hS hG
  calc
    _ ≤ ∏ i ∈ S ∪ G, f i := Finset.prod_le_prod_of_subset_of_le_one₀ hsubset h0
      (fun i hi _ => h1 i hi)
    _ = (∏ i ∈ S, f i) * ∏ i ∈ G, f i := Finset.prod_union hdisj
    _ ≤ (∏ _i ∈ S, q) * ∏ i ∈ G, f i := mul_le_mul_of_nonneg_right
      (Finset.prod_le_prod₀ (fun i hi => h0 i (hS hi)) hsep)
      (Finset.prod_nonneg fun i hi => h0 i (hG hi))
    _ = _ := by rw [Finset.prod_const]

namespace FiniteModel

def freeCosineEdges {m : ℕ} (D : Finset (Fin m × Fin m)) : Finset (Edge m) :=
  Finset.univ.filter (fun e => (e.1.1, e.1.2) ∉ D ∧ (e.1.2, e.1.1) ∉ D)

def goodFreeCosineEdges {m : ℕ} (D : Finset (Fin m × Fin m)) (G : Finset (Fin m)) :
    Finset (Edge m) := (freeCosineEdges D).filter (fun e => e.1.1 ∈ G ∧ e.1.2 ∈ G)

theorem selectedCrossEdges_subset_free {m : ℕ} (D : Finset (Fin m × Fin m))
    (O C : Finset (Fin m)) (hd : Disjoint O C) :
    selectedCrossEdges O C hd (fun u v => (u, v) ∉ D ∧ (v, u) ∉ D) ⊆ freeCosineEdges D := by
  intro e he
  obtain ⟨u, _, v, _, hp, heq⟩ := selectedCrossEdges_witness _ _ _ _ he
  simp only [freeCosineEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases heq with h | h
  · simpa only [h] using hp
  · simpa only [h, and_comm] using hp

theorem selectedCrossEdges_disjoint_good {m : ℕ} (D : Finset (Fin m × Fin m))
    (O C G : Finset (Fin m)) (hd : Disjoint O C) (hOG : Disjoint O G) :
    Disjoint (selectedCrossEdges O C hd (fun u v => (u, v) ∉ D ∧ (v, u) ∉ D))
      (goodFreeCosineEdges D G) := by
  apply Finset.disjoint_left.mpr
  intro e he hg
  obtain ⟨u, hu, v, _, _, heq⟩ := selectedCrossEdges_witness _ _ _ _ he
  have hgood := (Finset.mem_filter.mp hg).2
  rcases heq with h | h
  · rw [h] at hgood
    exact Finset.disjoint_left.mp hOG hu hgood.1
  · rw [h] at hgood
    exact Finset.disjoint_left.mp hOG hu hgood.2

theorem freeCosineProduct_cluster_bound {m : ℕ} (D : Finset (Fin m × Fin m))
    (x : Fin m → UnitAddCircle) (j : Fin 16)
    (hdeleted : ∀ u ∈ circleOutliers x j,
      ((circleCore x j).filter (fun v => (u, v) ∈ D ∨ (v, u) ∈ D)).card ≤ 2) :
    (∏ e ∈ freeCosineEdges D, circleCosineKernel (x e.1.1) (x e.1.2)) ≤
      circleSeparationRatio ^ ((circleOutliers x j).card * ((circleCore x j).card - 2)) *
        ∏ e ∈ goodFreeCosineEdges D (circleGood x j), circleCosineKernel (x e.1.1) (x e.1.2) := by
  let S := selectedCrossEdges (circleOutliers x j) (circleCore x j)
    (circleOutliers_disjoint_core x j) (fun u v => (u, v) ∉ D ∧ (v, u) ∉ D)
  have hOG : Disjoint (circleOutliers x j) (circleGood x j) := by
    apply Finset.disjoint_left.mpr
    intro i ho hg
    have hfar := (mem_circleOutliers x j i).mp ho
    exact not_lt_of_ge ((mem_circleGood x j i).mp hg) hfar
  have hcard : (circleOutliers x j).card * ((circleCore x j).card - 2) ≤ S.card := by
    apply selectedCrossEdges_card_lower _ _ _ _ 2
    intro u hu
    simpa only [not_and_or, not_not] using hdeleted u hu
  have hprod := product_extract_separated_factors (freeCosineEdges D) S
    (goodFreeCosineEdges D (circleGood x j))
    (fun e => circleCosineKernel (x e.1.1) (x e.1.2)) circleSeparationRatio
    (selectedCrossEdges_subset_free D _ _ _) (Finset.filter_subset _ _)
    (selectedCrossEdges_disjoint_good D _ _ _ _ hOG)
    (fun e _ => circleCosineKernel_nonneg _ _) (fun e _ => circleCosineKernel_le_one _ _)
    (fun e he => circleCosineKernel_le_separationRatio
      (selectedCrossEdges_circle_separation x j _ he).le)
  refine hprod.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact pow_le_pow_of_le_one circleSeparationRatio_pos.le circleSeparationRatio_lt_one.le hcard
  · exact Finset.prod_nonneg (fun e _ => circleCosineKernel_nonneg _ _)

theorem goodFreeCosineProduct_gaussian_bound {m : ℕ} (D : Finset (Fin m × Fin m))
    (x : Fin m → UnitAddCircle) (j : Fin 16) :
    (∏ e ∈ goodFreeCosineEdges D (circleGood x j), circleCosineKernel (x e.1.1) (x e.1.2)) ≤
      Real.exp (-(∑ e ∈ goodFreeCosineEdges D (circleGood x j),
        (Real.pi * (circleCenteredLift j (x e.1.1) - circleCenteredLift j (x e.1.2))) ^ 2) / 2) := by
  calc
    _ ≤ ∏ e ∈ goodFreeCosineEdges D (circleGood x j),
        Real.exp (-((Real.pi * (circleCenteredLift j (x e.1.1) - circleCenteredLift j (x e.1.2))) ^ 2 / 2)) := by
      apply Finset.prod_le_prod₀ (fun e _ => circleCosineKernel_nonneg _ _)
      intro e he
      have hg := (Finset.mem_filter.mp he).2
      exact circleCosineKernel_good_gaussian x j hg.1 hg.2
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [← neg_div, ← Finset.sum_div, Finset.sum_neg_distrib]

theorem freeCosineProduct_cluster_gaussian_bound {m : ℕ} (D : Finset (Fin m × Fin m))
    (x : Fin m → UnitAddCircle) (j : Fin 16)
    (hdeleted : ∀ u ∈ circleOutliers x j,
      ((circleCore x j).filter (fun v => (u, v) ∈ D ∨ (v, u) ∈ D)).card ≤ 2) :
    (∏ e ∈ freeCosineEdges D, circleCosineKernel (x e.1.1) (x e.1.2)) ≤
      circleSeparationRatio ^ ((circleOutliers x j).card * ((circleCore x j).card - 2)) *
        Real.exp (-(∑ e ∈ goodFreeCosineEdges D (circleGood x j),
          (Real.pi * (circleCenteredLift j (x e.1.1) - circleCenteredLift j (x e.1.2))) ^ 2) / 2) :=
  (freeCosineProduct_cluster_bound D x j hdeleted).trans
    (mul_le_mul_of_nonneg_left (goodFreeCosineProduct_gaussian_bound D x j)
      (pow_nonneg circleSeparationRatio_pos.le _))

theorem internalCycleCosineProduct_cluster_gaussian_bound {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d) (x : Fin m → UnitAddCircle) (j : Fin 16) :
    (∏ e ∈ freeCosineEdges (internalCycleArcSet σ i), circleCosineKernel (x e.1.1) (x e.1.2)) ≤
      circleSeparationRatio ^ ((circleOutliers x j).card * ((circleCore x j).card - 2)) *
        Real.exp (-(∑ e ∈ goodFreeCosineEdges (internalCycleArcSet σ i) (circleGood x j),
          (Real.pi * (circleCenteredLift j (x e.1.1) - circleCenteredLift j (x e.1.2))) ^ 2) / 2) :=
  freeCosineProduct_cluster_gaussian_bound _ x j
    (fun u _ => internalCycleArcSet_neighbor_card_le_two σ i u (circleCore x j))

end FiniteModel
end
end Wormald

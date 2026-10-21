import Wormald.CosineTaylorBounds

/-! A uniform local expansion with deleted edges. The constants depend only
on the number of all edges and deleted edges, not on their arrangement. -/

namespace Wormald
noncomputable section
open scoped BigOperators

theorem deleted_cosine_log_error {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (ht : t ⊆ s) (x : ι → ℝ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hx : ∀ i ∈ s, |x i| ≤ r) :
    |(∑ i ∈ s \ t, Real.log (Real.cos (x i))) +
      (∑ i ∈ s, x i ^ 2) / 2 + (∑ i ∈ s, x i ^ 4) / 12 -
        (∑ i ∈ t, x i ^ 2) / 2| ≤ s.card * r ^ 6 + 2 * t.card * r ^ 4 := by
  have hs := cosine_quartic_error_le_card_mul_radius s x r hr hr1 hx
  have hdel := cosine_quadratic_error_le_card_mul_radius t x r hr hr1
    (fun i hi => hx i (ht hi))
  have hsum : (∑ i ∈ s \ t, Real.log (Real.cos (x i))) =
      (∑ i ∈ s, Real.log (Real.cos (x i))) - ∑ i ∈ t, Real.log (Real.cos (x i)) := by
    exact eq_sub_iff_add_eq.mpr (Finset.sum_sdiff ht)
  have hid : (∑ i ∈ s \ t, Real.log (Real.cos (x i))) +
      (∑ i ∈ s, x i ^ 2) / 2 + (∑ i ∈ s, x i ^ 4) / 12 -
        (∑ i ∈ t, x i ^ 2) / 2 =
      (∑ i ∈ s, (Real.log (Real.cos (x i)) + x i ^ 2 / 2 + x i ^ 4 / 12)) -
        ∑ i ∈ t, (Real.log (Real.cos (x i)) + x i ^ 2 / 2) := by
    rw [hsum]
    simp only [Finset.sum_add_distrib, ← Finset.sum_div]
    ring
  rw [hid]
  exact (abs_sub _ _).trans (add_le_add hs hdel)

theorem exists_deleted_cosine_product_error {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (ht : t ⊆ s) (x : ι → ℝ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hx : ∀ i ∈ s, |x i| ≤ r) :
    ∃ e : ℝ, |e| ≤ s.card * r ^ 6 + 2 * t.card * r ^ 4 ∧
      (∏ i ∈ s \ t, Real.cos (x i)) = Real.exp
        (-(∑ i ∈ s, x i ^ 2) / 2 - (∑ i ∈ s, x i ^ 4) / 12 +
          (∑ i ∈ t, x i ^ 2) / 2 + e) := by
  let e : ℝ := (∑ i ∈ s \ t, Real.log (Real.cos (x i))) +
      (∑ i ∈ s, x i ^ 2) / 2 + (∑ i ∈ s, x i ^ 4) / 12 -
        (∑ i ∈ t, x i ^ 2) / 2
  refine ⟨e, deleted_cosine_log_error s t ht x r hr hr1 hx, ?_⟩
  have he : -(∑ i ∈ s, x i ^ 2) / 2 - (∑ i ∈ s, x i ^ 4) / 12 +
      (∑ i ∈ t, x i ^ 2) / 2 + e = ∑ i ∈ s \ t, Real.log (Real.cos (x i)) := by
    dsimp [e]
    ring
  rw [he, Real.exp_sum]
  exact Finset.prod_congr rfl fun i hi =>
    (Real.exp_log (cos_pos_of_abs_le_one (x i) ((hx i (Finset.mem_sdiff.mp hi).1).trans hr1))).symm

end
end Wormald

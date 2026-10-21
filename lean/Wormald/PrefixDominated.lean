import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Prefix domination and the squared-norm equality criterion

Abel summation is proved by removing the smallest weight. The squared-norm
comparison and its strict equality criterion then need only finite algebra,
so no positive-part integrals are needed.
-/

namespace Wormald
noncomputable section
open scoped BigOperators

def prefixSum {n : ℕ} (x : Fin n → ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < r), x j

def PrefixDominated {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∀ r : ℕ, r ≤ n → prefixSum x r ≤ prefixSum y r

@[simp] theorem prefixSum_zero {n : ℕ} (x : Fin n → ℝ) : prefixSum x 0 = 0 := by
  simp [prefixSum]

theorem prefixSum_succ {n : ℕ} (x : Fin n → ℝ) (r : ℕ) (hr : r < n) :
    prefixSum x (r + 1) = prefixSum x r + x ⟨r, hr⟩ := by
  have hfilter : Finset.univ.filter (fun j : Fin n => j.val < r + 1) =
      insert ⟨r, hr⟩ (Finset.univ.filter (fun j : Fin n => j.val < r)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  unfold prefixSum
  rw [hfilter, Finset.sum_insert (by simp)]
  ring

theorem prefixSum_castSucc {n : ℕ} (x : Fin (n + 1) → ℝ) (r : ℕ) (hr : r ≤ n) :
    prefixSum x r = prefixSum (fun j : Fin n => x j.castSucc) r := by
  unfold prefixSum
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  have hlast : ¬n < r := by omega
  simp [hlast]

@[simp] theorem prefixSum_full {n : ℕ} (x : Fin n → ℝ) :
    prefixSum x n = ∑ j, x j := by
  unfold prefixSum
  have hfilter : Finset.univ.filter (fun j : Fin n => j.val < n) = Finset.univ := by
    ext j
    simp
  rw [hfilter]

theorem PrefixDominated.castSucc {n : ℕ} {x y : Fin (n + 1) → ℝ}
    (hxy : PrefixDominated x y) :
    PrefixDominated (fun j : Fin n => x j.castSucc) (fun j : Fin n => y j.castSucc) := by
  intro r hr
  rw [← prefixSum_castSucc x r hr, ← prefixSum_castSucc y r hr]
  exact hxy r (by omega)

/-- Nonnegative decreasing weights preserve prefix domination. -/
theorem prefixDominated_weighted_sum_le {n : ℕ} (x y w : Fin n → ℝ)
    (hxy : PrefixDominated x y) (hw : Antitone w) (hw0 : ∀ j, 0 ≤ w j) :
    (∑ j, w j * x j) ≤ ∑ j, w j * y j := by
  induction n with
  | zero => simp
  | succ n ih =>
    let w' : Fin n → ℝ := fun j => w j.castSucc - w (Fin.last n)
    have hw' : Antitone w' := by
      intro i j hij
      exact sub_le_sub_right (hw (Fin.castSucc_le_castSucc_iff.mpr hij)) _
    have hw0' : ∀ j, 0 ≤ w' j := by
      intro j
      exact sub_nonneg.mpr (hw (Fin.castSucc_lt_last j).le)
    have hind := ih (fun j : Fin n => x j.castSucc) (fun j : Fin n => y j.castSucc)
      w' hxy.castSucc hw' hw0'
    dsimp [w'] at hind
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at hind
    have hfull : (∑ j, x j) ≤ ∑ j, y j := by
      simpa using hxy (n + 1) le_rfl
    have hlast := mul_le_mul_of_nonneg_left hfull (hw0 (Fin.last n))
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hlast ⊢
    nlinarith

/-- A short algebraic weak-majorization norm comparison. -/
theorem PrefixDominated.sum_sq_le {n : ℕ} (x y : Fin n → ℝ)
    (hxy : PrefixDominated x y) (hx : Antitone x) (hy : Antitone y)
    (hx0 : ∀ j, 0 ≤ x j) (hy0 : ∀ j, 0 ≤ y j) :
    (∑ j, x j ^ 2) ≤ ∑ j, y j ^ 2 := by
  have h := prefixDominated_weighted_sum_le x y (fun j => x j + y j) hxy
    (fun i j hij => add_le_add (hx hij) (hy hij)) (fun j => add_nonneg (hx0 j) (hy0 j))
  have hxsum : (∑ j, (x j + y j) * x j) =
      (∑ j, x j ^ 2) + ∑ j, x j * y j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hysum : (∑ j, (x j + y j) * y j) =
      (∑ j, x j * y j) + ∑ j, y j ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hxsum, hysum] at h
  linarith

/-- Equal squared norms under prefix domination force vector equality.
This replaces the positive-part integral and its equality analysis. -/
theorem PrefixDominated.eq_of_sum_sq_eq {n : ℕ} (x y : Fin n → ℝ)
    (hxy : PrefixDominated x y) (hx : Antitone x) (hx0 : ∀ j, 0 ≤ x j)
    (heq : (∑ j, x j ^ 2) = ∑ j, y j ^ 2) : x = y := by
  have hcross := prefixDominated_weighted_sum_le x y x hxy hx hx0
  simp only [← pow_two] at hcross
  have hsumsq : (∑ j, (y j - x j) ^ 2) =
      (∑ j, y j ^ 2) + (∑ j, x j ^ 2) - 2 * ∑ j, x j * y j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hle : (∑ j, (y j - x j) ^ 2) ≤ 0 := by
    rw [hsumsq]
    linarith
  have hzero : (∑ j, (y j - x j) ^ 2) = 0 :=
    le_antisymm hle (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  funext j
  have hj : (y j - x j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (y k - x k))).mp hzero
      j (Finset.mem_univ j)
  nlinarith [sq_nonneg (y j - x j)]

end
end Wormald

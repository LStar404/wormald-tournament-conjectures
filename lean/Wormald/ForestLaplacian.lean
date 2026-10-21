import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-! Incidence matrices for arbitrary subsets of one directed spanning path.
This represents every path forest after relabeling, with constants independent
of its size and of the number of components. -/

namespace Wormald
noncomputable section
open Matrix
open scoped BigOperators

def pathIncidence {n : ℕ} (k : Fin n) : Fin (n + 1) → ℝ :=
  Pi.single k.castSucc 1 - Pi.single k.succ 1

def forestLaplacian {n : ℕ} (S : Finset (Fin n)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  ∑ k ∈ S, Matrix.vecMulVec (pathIncidence k) (pathIncidence k)

def forestImbalance {n : ℕ} (S : Finset (Fin n)) : Fin (n + 1) → ℝ :=
  ∑ k ∈ S, pathIncidence k

@[simp] theorem pathIncidence_dotProduct {n : ℕ} (k : Fin n) (x : Fin (n + 1) → ℝ) :
    pathIncidence k ⬝ᵥ x = x k.castSucc - x k.succ := by
  simp [pathIncidence, sub_dotProduct]

@[simp] theorem dotProduct_pathIncidence {n : ℕ} (k : Fin n) (x : Fin (n + 1) → ℝ) :
    x ⬝ᵥ pathIncidence k = x k.castSucc - x k.succ := by
  rw [dotProduct_comm, pathIncidence_dotProduct]

@[simp] theorem pathIncidence_square {n : ℕ} (k : Fin n) :
    pathIncidence k ⬝ᵥ pathIncidence k = 2 := by
  have hne : k.castSucc ≠ k.succ := by intro h; have := congrArg Fin.val h; simp at this
  rw [pathIncidence_dotProduct]
  norm_num [pathIncidence, hne, hne.symm]

@[simp] theorem sum_pathIncidence {n : ℕ} (k : Fin n) :
    ∑ i, pathIncidence k i = 0 := by
  simp [pathIncidence, Finset.sum_sub_distrib]

@[simp] theorem trace_forestLaplacian {n : ℕ} (S : Finset (Fin n)) :
    (forestLaplacian S).trace = 2 * S.card := by
  simp only [forestLaplacian, Matrix.trace_sum, Matrix.trace_vecMulVec,
    pathIncidence_square, Finset.sum_const, nsmul_eq_mul]
  ring

theorem forestLaplacian_symmetric {n : ℕ} (S : Finset (Fin n)) :
    (forestLaplacian S).transpose = forestLaplacian S := by
  simp [forestLaplacian, Matrix.transpose_sum, Matrix.transpose_vecMulVec]

theorem forestLaplacian_quadratic {n : ℕ} (S : Finset (Fin n))
    (x : Fin (n + 1) → ℝ) :
    x ⬝ᵥ (forestLaplacian S *ᵥ x) =
      ∑ k ∈ S, (x k.castSucc - x k.succ) ^ 2 := by
  simp only [forestLaplacian, Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dotProduct_mulVec, Matrix.vecMul_vecMulVec, smul_dotProduct, smul_eq_mul,
    dotProduct_pathIncidence, pathIncidence_dotProduct, pow_two]

theorem forestLaplacian_quadratic_nonneg {n : ℕ} (S : Finset (Fin n))
    (x : Fin (n + 1) → ℝ) : 0 ≤ x ⬝ᵥ (forestLaplacian S *ᵥ x) := by
  rw [forestLaplacian_quadratic]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Every vertex of a path forest meets at most two edges; consequently its
Laplacian has Euclidean operator bound four, uniformly in the forest. -/
theorem forestLaplacian_quadratic_le_four {n : ℕ} (S : Finset (Fin n))
    (x : Fin (n + 1) → ℝ) :
    x ⬝ᵥ (forestLaplacian S *ᵥ x) ≤ 4 * (x ⬝ᵥ x) := by
  rw [forestLaplacian_quadratic]
  have hsource : (∑ k : Fin n, x k.castSucc ^ 2) ≤ ∑ i, x i ^ 2 := by
    rw [Fin.sum_univ_castSucc (fun i : Fin (n + 1) => x i ^ 2)]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have htarget : (∑ k : Fin n, x k.succ ^ 2) ≤ ∑ i, x i ^ 2 := by
    rw [Fin.sum_univ_succ (fun i : Fin (n + 1) => x i ^ 2)]
    exact le_add_of_nonneg_left (sq_nonneg _)
  calc
    _ ≤ ∑ k ∈ S, (2 * x k.castSucc ^ 2 + 2 * x k.succ ^ 2) :=
      Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (x k.castSucc + x k.succ)]
    _ ≤ ∑ k : Fin n, (2 * x k.castSucc ^ 2 + 2 * x k.succ ^ 2) :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => by positivity
    _ = 2 * (∑ k : Fin n, x k.castSucc ^ 2) + 2 * (∑ k : Fin n, x k.succ ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by simp only [dotProduct, ← pow_two]; linarith

theorem posDef_one_sub_smul_forestLaplacian {n : ℕ} (S : Finset (Fin n))
    (r : ℝ) (hr : 0 ≤ r) (hr4 : 4 * r < 1) :
    (1 - r • forestLaplacian S).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSymm]
    change (1 - r • forestLaplacian S).transpose = 1 - r • forestLaplacian S
    simp [Matrix.transpose_sub, Matrix.transpose_smul, forestLaplacian_symmetric]
  · intro x hx
    have hp : 0 < x ⬝ᵥ x := by
      simpa only [star_trivial] using (dotProduct_star_self_pos_iff (v := x)).mpr hx
    have henergy := forestLaplacian_quadratic_le_four S x
    have hmul := mul_le_mul_of_nonneg_left henergy hr
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
    nlinarith [mul_pos (sub_pos.mpr hr4) hp]

def pathSelected {n : ℕ} (S : Finset (Fin n)) (k : Fin n) : ℝ := if k ∈ S then 1 else 0

def pathOutgoing {n : ℕ} (S : Finset (Fin n)) : Fin (n + 1) → ℝ :=
  Fin.snoc (pathSelected S) 0

def pathIncoming {n : ℕ} (S : Finset (Fin n)) : Fin (n + 1) → ℝ :=
  Fin.cons 0 (pathSelected S)

theorem forestImbalance_eq_out_sub_in {n : ℕ} (S : Finset (Fin n)) :
    forestImbalance S = pathOutgoing S - pathIncoming S := by
  unfold forestImbalance pathIncidence
  rw [Finset.sum_sub_distrib]
  congr 1
  · ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [pathOutgoing, Fin.castSucc_ne_last]
    · simp [pathOutgoing, pathSelected, Finset.sum_apply, Pi.single_apply]
  · ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [pathIncoming, Fin.succ_ne_zero]
    · simp [pathIncoming, pathSelected, Finset.sum_apply, Pi.single_apply]

theorem pathOutgoing_zero_or_one {n : ℕ} (S : Finset (Fin n)) (i : Fin (n + 1)) :
    pathOutgoing S i = 0 ∨ pathOutgoing S i = 1 := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [pathOutgoing]
  · by_cases hk : k ∈ S <;> simp [pathOutgoing, pathSelected, hk]

theorem pathIncoming_zero_or_one {n : ℕ} (S : Finset (Fin n)) (i : Fin (n + 1)) :
    pathIncoming S i = 0 ∨ pathIncoming S i = 1 := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [pathIncoming]
  · by_cases hk : k ∈ S <;> simp [pathIncoming, pathSelected, hk]

def forestJoinCount {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin (n + 1) => pathOutgoing S i = 1 ∧ pathIncoming S i = 1).card

theorem pathOutgoing_dot_self {n : ℕ} (S : Finset (Fin n)) :
    pathOutgoing S ⬝ᵥ pathOutgoing S = S.card := by
  simp only [dotProduct]
  rw [Fin.sum_univ_castSucc]
  simp [pathOutgoing, pathSelected]

theorem pathIncoming_dot_self {n : ℕ} (S : Finset (Fin n)) :
    pathIncoming S ⬝ᵥ pathIncoming S = S.card := by
  simp only [dotProduct]
  rw [Fin.sum_univ_succ]
  simp [pathIncoming, pathSelected]

theorem pathOutgoing_dot_incoming {n : ℕ} (S : Finset (Fin n)) :
    pathOutgoing S ⬝ᵥ pathIncoming S = forestJoinCount S := by
  have hterm (i : Fin (n + 1)) : pathOutgoing S i * pathIncoming S i =
      if pathOutgoing S i = 1 ∧ pathIncoming S i = 1 then 1 else 0 := by
    rcases pathOutgoing_zero_or_one S i with h | h <;>
      rcases pathIncoming_zero_or_one S i with h' | h' <;> simp [h, h']
  simp only [dotProduct, hterm, forestJoinCount]
  simp

/-- Every nontrivial path has two imbalanced endpoints; the number of such
paths is |S| minus the number of consecutive selected edge pairs. -/
theorem forestImbalance_square {n : ℕ} (S : Finset (Fin n)) :
    forestImbalance S ⬝ᵥ forestImbalance S = 2 * (S.card : ℝ) - 2 * forestJoinCount S := by
  rw [forestImbalance_eq_out_sub_in, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    pathOutgoing_dot_self, pathIncoming_dot_self, pathOutgoing_dot_incoming,
    dotProduct_comm (pathIncoming S) (pathOutgoing S), pathOutgoing_dot_incoming]
  ring

@[simp] theorem sum_forestImbalance {n : ℕ} (S : Finset (Fin n)) :
    ∑ i, forestImbalance S i = 0 := by
  simp only [forestImbalance, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp

end
end Wormald

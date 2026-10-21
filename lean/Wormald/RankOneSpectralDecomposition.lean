import Wormald.CarouselDeterminant
import Mathlib.LinearAlgebra.Matrix.Trace

/-! A normalized pair of right and left eigenvectors gives an actual rank-one
projector. Removing it splits every positive trace power exactly. -/

namespace Wormald
noncomputable section
open scoped BigOperators
open Matrix

def rankOneProjection {ι K : Type*} [Fintype ι] [Field K] (r l : ι → K) : Matrix ι ι K :=
  (l ⬝ᵥ r)⁻¹ • Matrix.vecMulVec r l

theorem rankOneProjection_idempotent {ι K : Type*} [Fintype ι] [Field K]
    (r l : ι → K) (hn : l ⬝ᵥ r ≠ 0) :
    rankOneProjection r l * rankOneProjection r l = rankOneProjection r l := by
  simp only [rankOneProjection, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
  congr 1
  field_simp

theorem rankOneProjection_trace {ι K : Type*} [Fintype ι] [Field K]
    (r l : ι → K) (hn : l ⬝ᵥ r ≠ 0) : (rankOneProjection r l).trace = 1 := by
  simp only [rankOneProjection, Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul]
  rw [dotProduct_comm r l]
  exact inv_mul_cancel₀ hn

theorem mul_rankOneProjection {ι K : Type*} [Fintype ι] [Field K]
    (A : Matrix ι ι K) (r l : ι → K) (lam : K) (hr : A *ᵥ r = lam • r) :
    A * rankOneProjection r l = lam • rankOneProjection r l := by
  simp only [rankOneProjection, Matrix.mul_smul, Matrix.mul_vecMulVec, hr,
    Matrix.smul_vecMulVec, smul_smul]
  rw [mul_comm]

theorem rankOneProjection_mul {ι K : Type*} [Fintype ι] [Field K]
    (A : Matrix ι ι K) (r l : ι → K) (lam : K) (hl : l ᵥ* A = lam • l) :
    rankOneProjection r l * A = lam • rankOneProjection r l := by
  simp only [rankOneProjection, Matrix.smul_mul, Matrix.vecMulVec_mul, hl,
    Matrix.vecMulVec_smul, smul_smul]
  rw [mul_comm]

/-- Exact decomposition at every positive power; the residual is the actual
matrix obtained by subtracting the eigenprojector. -/
theorem pow_eq_rankOne_add_residual {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (A : Matrix ι ι K) (r l : ι → K) (lam : K) (hn : l ⬝ᵥ r ≠ 0)
    (hr : A *ᵥ r = lam • r) (hl : l ᵥ* A = lam • l) (N : ℕ) (hN : 0 < N) :
    A ^ N = lam ^ N • rankOneProjection r l +
      (A - lam • rankOneProjection r l) ^ N := by
  let P := rankOneProjection r l
  let R := A - lam • P
  have hP : P * P = P := rankOneProjection_idempotent r l hn
  have hAP : A * P = lam • P := mul_rankOneProjection A r l lam hr
  have hPA : P * A = lam • P := rankOneProjection_mul A r l lam hl
  have hPR : P * R = 0 := by
    dsimp [R]
    rw [mul_sub, Matrix.mul_smul, hP, hPA, sub_self]
  have hRP : R * P = 0 := by
    dsimp [R]
    rw [sub_mul, Matrix.smul_mul, hP, hAP, sub_self]
  have hRpowP : ∀ k, R ^ (k + 1) * P = 0 := by
    intro k
    rw [pow_succ, Matrix.mul_assoc, hRP, mul_zero]
  have hA : A = lam • P + R := by dsimp [R]; abel
  have hpow : ∀ k, A ^ (k + 1) = lam ^ (k + 1) • P + R ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa only [Nat.zero_add, pow_one] using hA
    | succ k ih =>
      rw [pow_succ, ih, hA, add_mul, mul_add, mul_add,
        Matrix.smul_mul, Matrix.mul_smul, hP, Matrix.mul_smul, hRpowP,
        smul_zero, Matrix.smul_mul, hPR, smul_zero, add_zero, zero_add,
        smul_smul, ← pow_succ, ← pow_succ]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  exact hpow k

theorem trace_pow_eq_rankOne_add_residual {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (A : Matrix ι ι K) (r l : ι → K) (lam : K) (hn : l ⬝ᵥ r ≠ 0)
    (hr : A *ᵥ r = lam • r) (hl : l ᵥ* A = lam • l) (N : ℕ) (hN : 0 < N) :
    (A ^ N).trace = lam ^ N + ((A - lam • rankOneProjection r l) ^ N).trace := by
  rw [pow_eq_rankOne_add_residual A r l lam hn hr hl N hN,
    Matrix.trace_add, Matrix.trace_smul, rankOneProjection_trace r l hn, smul_eq_mul, mul_one]

end
end Wormald

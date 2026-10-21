import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-! Exact two-coordinate determinant expansion at a corank-one critical point.
This finite identity avoids differentiating a matrix inverse analytically. -/

namespace Wormald

open Matrix

section
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

theorem det_lowRank_update (D U : Matrix ι ι R) (F : Matrix ι (Fin 3) R)
    (G : Matrix (Fin 3) ι R) (hDU : D * U = 1) :
    (D + F * G).det = D.det * (1 + G * U * F).det := by
  have hf : D + F * G = D * (1 + (U * F) * G) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc D,
      ← Matrix.mul_assoc D, hDU, Matrix.one_mul]
  rw [hf, Matrix.det_mul, Matrix.det_one_add_mul_comm]
  simp only [Matrix.mul_assoc]

/-- `r` is the reciprocal dimension, `β` the common sum of the two transformed
columns. The result remains valid over a polynomial coefficient ring. -/
theorem det_twoColumn_critical_expansion
    (D U : Matrix ι ι R) (v w : ι → R) (r β a b : R) (j k : ι)
    (hDU : D * U = 1)
    (hr : r * (Fintype.card ι : R) = 1)
    (hU : U *ᵥ (fun _ => 1) = (fun _ => 1))
    (hv : ∑ i, (U *ᵥ v) i = β) (hw : ∑ i, (U *ᵥ w) i = β) :
    (Matrix.of (fun i l => D i l - r -
      a * v i * (if l = j then 1 else 0) -
      b * w i * (if l = k then 1 else 0))).det =
    D.det * (-(r * β) * (a + b) + r * β * a * b *
      ((U *ᵥ v) j + (U *ᵥ w) k - (U *ᵥ w) j - (U *ᵥ v) k)) := by
  let F : Matrix ι (Fin 3) R := Matrix.of fun i => ![1, v i, w i]
  let G : Matrix (Fin 3) ι R := Matrix.of fun s l =>
    ![-r, -a * (if l = j then 1 else 0), -b * (if l = k then 1 else 0)] s
  have hUF0 (i : ι) : (U * F) i 0 = 1 := by
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, F] using congrFun hU i
  have hUF1 (i : ι) : (U * F) i 1 = (U *ᵥ v) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, F]
  have hUF2 (i : ι) : (U * F) i 2 = (U *ᵥ w) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, F]
  have hbig : Matrix.of (fun i l => D i l - r -
      a * v i * (if l = j then 1 else 0) -
      b * w i * (if l = k then 1 else 0)) = D + F * G := by
    ext i l
    simp [Matrix.mul_apply, Fin.sum_univ_succ, F, G]
    split_ifs <;> ring
  have hr' : (Fintype.card ι : R) * r = 1 := by simpa only [mul_comm] using hr
  have hsmall : 1 + G * U * F =
      !![0, -(r * β), -(r * β);
        -a, 1 - a * (U *ᵥ v) j, -a * (U *ᵥ w) j;
        -b, -b * (U *ᵥ v) k, 1 - b * (U *ᵥ w) k] := by
    rw [Matrix.mul_assoc]
    ext s t
    change (if s = t then 1 else 0) + ∑ i, G s i * (U * F) i t = _
    fin_cases s <;> fin_cases t <;>
      simp [G, hUF0, hUF1, hUF2,
        ← Finset.mul_sum, hv, hw, hr', mul_ite, sub_eq_add_neg]
  rw [hbig, det_lowRank_update D U F G hDU, hsmall, Matrix.det_fin_three]
  simp
  ring

end
end Wormald

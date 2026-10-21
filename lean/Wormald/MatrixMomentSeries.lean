import Wormald.MomentSeries
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-! The scalar odd-moment series applied to an actual positive symmetric
matrix D with I-D positive definite. No spectral or logarithmic identity is
assumed: diagonalization is supplied by Mathlib's real spectral theorem. -/

namespace Wormald
noncomputable section
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_unitary_conjugate (U : Matrix.unitaryGroup ι ℝ) (M : Matrix ι ι ℝ) :
    (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U M).det = M.det := by
  have hdet : (U : Matrix ι ι ℝ).det * (star (U : Matrix ι ι ℝ)).det = 1 := by
    rw [← Matrix.det_mul]
    simp
  simp only [Unitary.conjStarAlgAut_apply, Matrix.det_mul]
  calc
    _ = M.det * ((U : Matrix ι ι ℝ).det * (star (U : Matrix ι ι ℝ)).det) := by ring
    _ = M.det := by rw [hdet, mul_one]

theorem trace_unitary_conjugate (U : Matrix.unitaryGroup ι ℝ) (M : Matrix ι ι ℝ) :
    (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U M).trace = M.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

theorem trace_pow_eq_sum_eigenvalues (D : Matrix ι ι ℝ) (hD : D.IsHermitian) (k : ℕ) :
    (D ^ k).trace = ∑ i, hD.eigenvalues i ^ k := by
  have hdiag : Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star hD.eigenvectorUnitary) D =
      Matrix.diagonal hD.eigenvalues := by
    simpa using hD.conjStarAlgAut_star_eigenvectorUnitary
  rw [← trace_unitary_conjugate (star hD.eigenvectorUnitary) (D ^ k), map_pow, hdiag,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

theorem det_one_add_eq_prod_eigenvalues (D : Matrix ι ι ℝ) (hD : D.IsHermitian) :
    (1 + D).det = ∏ i, (1 + hD.eigenvalues i) := by
  have hdiag : Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star hD.eigenvectorUnitary) D =
      Matrix.diagonal hD.eigenvalues := by
    simpa using hD.conjStarAlgAut_star_eigenvectorUnitary
  rw [← det_unitary_conjugate (star hD.eigenvectorUnitary) (1 + D), map_add, map_one, hdiag]
  have hadd : (1 : Matrix ι ι ℝ) + Matrix.diagonal hD.eigenvalues =
      Matrix.diagonal (fun i => 1 + hD.eigenvalues i) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hadd, Matrix.det_diagonal]

theorem det_one_sub_eq_prod_eigenvalues (D : Matrix ι ι ℝ) (hD : D.IsHermitian) :
    (1 - D).det = ∏ i, (1 - hD.eigenvalues i) := by
  have hdiag : Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star hD.eigenvectorUnitary) D =
      Matrix.diagonal hD.eigenvalues := by
    simpa using hD.conjStarAlgAut_star_eigenvectorUnitary
  rw [← det_unitary_conjugate (star hD.eigenvectorUnitary) (1 - D), map_sub, map_one, hdiag]
  have hsub : (1 : Matrix ι ι ℝ) - Matrix.diagonal hD.eigenvalues =
      Matrix.diagonal (fun i => 1 - hD.eigenvalues i) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hsub, Matrix.det_diagonal]

theorem eigenvalues_lt_one_of_posDef_one_sub (D : Matrix ι ι ℝ)
    (hD : D.IsHermitian) (hminus : (1 - D).PosDef) (i : ι) : hD.eigenvalues i < 1 := by
  let U := hD.eigenvectorUnitary
  have hinj : Function.Injective (U : Matrix ι ι ℝ).mulVec := by
    apply Function.LeftInverse.injective (g := (star (U : Matrix ι ι ℝ)).mulVec)
    intro x
    rw [Matrix.mulVec_mulVec, Unitary.coe_star_mul_self, Matrix.one_mulVec]
  have hp := hminus.conjTranspose_mul_mul_same hinj
  have hdiag : Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star U) D =
      Matrix.diagonal hD.eigenvalues := by
    simpa [U] using hD.conjStarAlgAut_star_eigenvectorUnitary
  have htrans : (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star U) (1 - D)).PosDef := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using hp
  rw [map_sub, map_one, hdiag] at htrans
  have hsub : (1 : Matrix ι ι ℝ) - Matrix.diagonal hD.eigenvalues =
      Matrix.diagonal (fun j => 1 - hD.eigenvalues j) := by
    ext j k
    by_cases hjk : j = k <;> simp [hjk]
  rw [hsub] at htrans
  exact sub_pos.mp ((Matrix.posDef_diagonal_iff.mp htrans) i)

theorem hasSum_trace_odd_pow_logdet (D : Matrix ι ι ℝ)
    (hD : D.PosSemidef) (hminus : (1 - D).PosDef) :
    HasSum (fun r : ℕ => (D ^ (2 * r + 1)).trace / ((2 * r + 1 : ℕ) : ℝ))
      ((Real.log (1 + D).det - Real.log (1 - D).det) / 2) := by
  have he0 (i : ι) : 0 ≤ hD.1.eigenvalues i := hD.eigenvalues_nonneg i
  have he1 (i : ι) : hD.1.eigenvalues i < 1 :=
    eigenvalues_lt_one_of_posDef_one_sub D hD.1 hminus i
  have hseries := hasSum_oddSpectralMoment hD.1.eigenvalues
    (fun i => by rw [abs_of_nonneg (he0 i)]; exact he1 i)
  have hlogplus : Real.log (1 + D).det = ∑ i, Real.log (1 + hD.1.eigenvalues i) := by
    rw [det_one_add_eq_prod_eigenvalues D hD.1,
      Real.log_prod (fun i _ => ne_of_gt (by linarith [he0 i]))]
  have hlogminus : Real.log (1 - D).det = ∑ i, Real.log (1 - hD.1.eigenvalues i) := by
    rw [det_one_sub_eq_prod_eigenvalues D hD.1,
      Real.log_prod (fun i _ => ne_of_gt (sub_pos.mpr (he1 i)))]
  simpa only [oddSpectralMoment, trace_pow_eq_sum_eigenvalues D hD.1,
    hlogplus, hlogminus] using hseries

end
end Wormald

import Wormald.AnalyticTarget

/-! Exact last-coordinate elimination for Wormald's original determinant.
Only nonvanishing of the explicitly defined coefficient is assumed. Analytic
existence and derivative theorems are separate from this polynomial identity. -/

namespace Wormald

noncomputable section

open Matrix MvPolynomial

theorem originalDeterminant_eq_polynomial_eval {d : ℕ}
    (T : Tournament d) (y : Fin d → ℂ) :
    eval₂ (Rat.castHom ℂ) y (definingPolynomial T.adjacency) =
      originalDeterminant T y := by
  change (eval₂Hom (Rat.castHom ℂ) y) (definingMatrix T.adjacency).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [definingMatrix, originalMatrix, h]

theorem originalDeterminant_affine_last {n : ℕ}
    (T : Tournament (n + 1)) (y : Fin n → ℂ) (t : ℂ) :
    originalDeterminant T (appendLast y t) =
      eliminatedNumerator T y + t * eliminatedCoefficient T y := by
  let M₀ := originalMatrix T (appendLast y 0)
  let b : Fin (n + 1) → ℂ := fun i =>
    -((T.adjacency i (Fin.last n) : ℂ) + if i = Fin.last n then (1 / 2 : ℂ) else 0)
  have hM (a : ℂ) : originalMatrix T (appendLast y a) =
      Matrix.updateCol M₀ (Fin.last n) ((fun i => M₀ i (Fin.last n)) + a • b) := by
    ext i j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [Matrix.updateCol, M₀, originalMatrix, appendLast, b]
      ring
    · simp [Matrix.updateCol, M₀, originalMatrix, appendLast]
  have hdet (a : ℂ) : originalDeterminant T (appendLast y a) =
      M₀.det + a * (Matrix.updateCol M₀ (Fin.last n) b).det := by
    unfold originalDeterminant
    rw [hM, Matrix.det_updateCol_add, Matrix.det_updateCol_smul]
    simp
  have hcoef : eliminatedCoefficient T y = (Matrix.updateCol M₀ (Fin.last n) b).det := by
    simp [eliminatedCoefficient, eliminatedNumerator, hdet]
  rw [hdet, hcoef]
  rfl

theorem originalImplicitFunction_solves {n : ℕ}
    (T : Tournament (n + 1)) (y : Fin n → ℂ)
    (hcoeff : eliminatedCoefficient T y ≠ 0) :
    originalDeterminant T (appendLast y (originalImplicitFunction T y)) = 0 := by
  rw [originalDeterminant_affine_last]
  unfold originalImplicitFunction
  field_simp
  ring

end
end Wormald

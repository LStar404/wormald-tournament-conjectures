import Wormald.CriticalPoint
import Wormald.TwoColumnDeterminant
import Wormald.AlgebraicJets

namespace Wormald

open Matrix MvPolynomial

noncomputable section

def criticalRestriction {d : ℕ} (T : Tournament d) (j k : Fin d) :
    MvPolynomial (Fin 2) ℂ :=
  eval₂ (C.comp (Rat.castHom ℂ))
    (twoCoordinateSubstitution (fun _ => 2 / (d : ℂ)) j k)
    (definingPolynomial T.adjacency)

def Tournament.criticalColumn {d : ℕ} (T : Tournament d) (j : Fin d) : Fin d → ℂ :=
  fun i => (T.adjacency i j : ℂ) + if i = j then (1 / 2 : ℂ) else 0

theorem criticalRestriction_formula {d : ℕ} (T : Tournament d) (hT : T.Regular)
    (hd : d ≠ 0) (j k : Fin d) :
    criticalRestriction T j k =
      C T.criticalDet *
        (-C (1 / 2) * (X 0 + X 1) + C (1 / 2) * X 0 * X 1 *
          (C ((T.criticalResolvent *ᵥ T.criticalColumn j) j) +
           C ((T.criticalResolvent *ᵥ T.criticalColumn k) k) -
           C ((T.criticalResolvent *ᵥ T.criticalColumn k) j) -
           C ((T.criticalResolvent *ᵥ T.criticalColumn j) k))) := by
  let D := 1 - T.complexNormalizedSign
  let U := T.criticalResolvent
  let Dp : Matrix (Fin d) (Fin d) (MvPolynomial (Fin 2) ℂ) := C.mapMatrix D
  let Up : Matrix (Fin d) (Fin d) (MvPolynomial (Fin 2) ℂ) := C.mapMatrix U
  let v := T.criticalColumn j
  let w := T.criticalColumn k
  let vp : Fin d → MvPolynomial (Fin 2) ℂ := fun i => C (v i)
  let wp : Fin d → MvPolynomial (Fin 2) ℂ := fun i => C (w i)
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hDU : Dp * Up = 1 := by
    change (C.mapMatrix D) * (C.mapMatrix U) = 1
    rw [← map_mul, T.inverse_mul_criticalResolvent, map_one]
  have hUp : Up *ᵥ (fun _ => 1) = (fun _ => 1) := by
    funext i
    have h := congrArg (C : ℂ →+* MvPolynomial (Fin 2) ℂ)
      (congrFun (T.criticalResolvent_mulVec_one hT) i)
    simpa [Up, U, Matrix.mulVec, dotProduct] using h
  have hvecv : Up *ᵥ vp = fun i => C ((U *ᵥ v) i) := by
    funext i
    simp only [Up, vp, Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply,
      Matrix.map_apply, map_sum, map_mul]
  have hvecw : Up *ᵥ wp = fun i => C ((U *ᵥ w) i) := by
    funext i
    simp only [Up, wp, Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply,
      Matrix.map_apply, map_sum, map_mul]
  have hsum (p : Fin d) : ∑ i, (U *ᵥ T.criticalColumn p) i = (d : ℂ) / 2 := by
    calc
      ∑ i, (U *ᵥ T.criticalColumn p) i =
          (fun _ => 1) ⬝ᵥ (U *ᵥ T.criticalColumn p) := by simp [dotProduct]
      _ = ((fun _ => 1) ᵥ* U) ⬝ᵥ T.criticalColumn p := Matrix.dotProduct_mulVec _ _ _
      _ = (fun _ => 1) ⬝ᵥ T.criticalColumn p := by
        rw [T.one_vecMul_criticalResolvent hT]
      _ = (d : ℂ) / 2 := by
        simpa [dotProduct, Tournament.criticalColumn] using T.critical_column_sum hT hd p
  have hvp : ∑ i, (Up *ᵥ vp) i = C ((d : ℂ) / 2) := by
    rw [hvecv, ← map_sum]
    exact congrArg C (hsum j)
  have hwp : ∑ i, (Up *ᵥ wp) i = C ((d : ℂ) / 2) := by
    rw [hvecw, ← map_sum]
    exact congrArg C (hsum k)
  have hr : C (1 / (d : ℂ)) * (Fintype.card (Fin d) : MvPolynomial (Fin 2) ℂ) = 1 := by
    simp only [Fintype.card_fin]
    rw [← map_natCast C d, ← map_mul]
    simp [hdC]
  have hbase (i l : Fin d) :
      (if i = l then (1 : ℂ) else 0) -
        ((T.adjacency i l : ℂ) + if i = l then (1 / 2 : ℂ) else 0) * (2 / (d : ℂ)) =
      D i l - 1 / (d : ℂ) := by
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i l)
      (originalMatrix_update_critical T hd j (2 / (d : ℂ)))
    simpa [Function.update_eq_self, originalMatrix, D] using h
  have hmatrix :
      (eval₂Hom (C.comp (Rat.castHom ℂ))
        (twoCoordinateSubstitution (fun _ => 2 / (d : ℂ)) j k)).mapMatrix
        (definingMatrix T.adjacency) =
      Matrix.of (fun i l => Dp i l - C (1 / (d : ℂ)) -
        X 0 * vp i * (if l = j then 1 else 0) -
        X 1 * wp i * (if l = k then 1 else 0)) := by
    apply Matrix.ext
    intro i l
    have hjterm :
        C ((T.adjacency i l : ℂ) + if i = l then (1 / 2 : ℂ) else 0) *
          (if l = j then X 0 else 0) = X 0 * vp i * (if l = j then 1 else 0) := by
      by_cases h : l = j
      · subst l
        simp [vp, v, Tournament.criticalColumn, mul_comm]
      · simp [h]
    have hkterm :
        C ((T.adjacency i l : ℂ) + if i = l then (1 / 2 : ℂ) else 0) *
          (if l = k then X 1 else 0) = X 1 * wp i * (if l = k then 1 else 0) := by
      by_cases h : l = k
      · subst l
        simp [wp, w, Tournament.criticalColumn, mul_comm]
      · simp [h]
    have hb := congrArg (C : ℂ →+* MvPolynomial (Fin 2) ℂ) (hbase i l)
    simp only [map_sub, map_mul] at hb
    have hcast : (Rat.castHom ℂ) (T.adjacency i l + if i = l then (1 / 2 : ℚ) else 0) =
        (T.adjacency i l : ℂ) + if i = l then (1 / 2 : ℂ) else 0 := by
      by_cases hil : i = l <;> norm_num [map_add, hil]
    simp only [definingMatrix, RingHom.mapMatrix_apply, Matrix.map_apply,
      coe_eval₂Hom, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X,
      RingHom.comp_apply, twoCoordinateSubstitution, Matrix.of_apply]
    rw [hcast]
    rw [mul_add, mul_add, hjterm, hkterm]
    by_cases hil : i = l <;> simp [hil, Dp] at hb ⊢ <;> linear_combination hb
  unfold criticalRestriction definingPolynomial
  change (eval₂Hom (C.comp (Rat.castHom ℂ))
    (twoCoordinateSubstitution (fun _ => 2 / (d : ℂ)) j k))
      (definingMatrix T.adjacency).det = _
  rw [RingHom.map_det, hmatrix]
  rw [det_twoColumn_critical_expansion Dp Up vp wp
    (C (1 / (d : ℂ))) (C ((d : ℂ) / 2)) (X 0) (X 1) j k hDU hr hUp hvp hwp]
  have hdet : Dp.det = C T.criticalDet := (C.map_det D).symm
  have hhalf : C (1 / (d : ℂ)) * C ((d : ℂ) / 2) =
      (C (1 / 2) : MvPolynomial (Fin 2) ℂ) := by
    rw [← map_mul]
    congr 1
    field_simp
  rw [hdet, hhalf, hvecv, hvecw]

/-- Every actual first polynomial partial has the same nonzero value. -/
theorem eval_first_pderiv_critical {d : ℕ} (T : Tournament d) (hT : T.Regular)
    (hd : d ≠ 0) (j : Fin d) :
    eval₂ (Rat.castHom ℂ) (fun _ => 2 / (d : ℂ))
      (pderiv j (definingPolynomial T.adjacency)) = -T.criticalDet / 2 := by
  have h := congrArg (fun p : MvPolynomial (Fin 2) ℂ =>
    eval (fun _ => 0) (pderiv 0 p)) (criticalRestriction_formula T hT hd j j)
  unfold criticalRestriction at h
  rw [pderiv_zero_twoCoordinate_eval₂, eval_zero_twoCoordinate_eval₂] at h
  simpa [pderiv_mul, div_eq_mul_inv] using h

/-- The exact mixed partials of the original determinant at its critical point. -/
theorem eval_second_pderiv_critical {d : ℕ} (T : Tournament d) (hT : T.Regular)
    (hd : d ≠ 0) (j k : Fin d) :
    eval₂ (Rat.castHom ℂ) (fun _ => 2 / (d : ℂ))
      (pderiv k (pderiv j (definingPolynomial T.adjacency))) =
      T.criticalDet / 2 *
        ((T.criticalResolvent *ᵥ T.criticalColumn j) j +
         (T.criticalResolvent *ᵥ T.criticalColumn k) k -
         (T.criticalResolvent *ᵥ T.criticalColumn k) j -
         (T.criticalResolvent *ᵥ T.criticalColumn j) k) := by
  have h := congrArg (fun p : MvPolynomial (Fin 2) ℂ =>
    eval (fun _ => 0) (pderiv 1 (pderiv 0 p)))
      (criticalRestriction_formula T hT hd j k)
  unfold criticalRestriction at h
  rw [eval_mixed_twoCoordinate_eval₂] at h
  simpa [pderiv_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

end
end Wormald

import Wormald.CriticalPoint

/-! Exact correspondence between the complex resolvent and the real positive
matrix core used to define the finite candidate Hessian. -/

open Matrix

namespace Wormald

noncomputable section

theorem mapMatrix_nonsing_inv_of_isUnit {m R S : Type*}
    [Fintype m] [DecidableEq m] [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix m m R) (hA : IsUnit A.det) :
    f.mapMatrix A⁻¹ = (f.mapMatrix A)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← map_mul, Matrix.nonsing_inv_mul _ hA, map_one]

theorem isUnit_det_one_sub_real_skew {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℝ) (hC : C.transpose = -C) : IsUnit (1 - C).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [det_one_sub_eq_det_one_add C hC]
  intro hz
  have hp := (posDef_one_sub_square C hC).det_pos
  rw [det_one_sub_square C hC, hz] at hp
  norm_num at hp

/-- The symmetric resolvent sum is exactly the rational positive matrix core. -/
theorem real_resolvent_sum {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℝ) (hC : C.transpose = -C) :
    (1 - C)⁻¹ + ((1 - C)⁻¹).transpose - 1 =
      (1 + C * C) * (1 - C * C)⁻¹ := by
  let U := (1 - C)⁻¹
  let V := (1 + C)⁻¹
  let W := (1 - C * C)⁻¹
  have hminus := isUnit_det_one_sub_real_skew C hC
  have hplus : IsUnit (1 + C).det := by
    rw [← det_one_sub_eq_det_one_add C hC]
    exact hminus
  have hsquare : IsUnit (1 - C * C).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (posDef_one_sub_square C hC).isUnit
  have hU : U * (1 - C) = 1 := Matrix.nonsing_inv_mul _ hminus
  have hUr : (1 - C) * U = 1 := Matrix.mul_nonsing_inv _ hminus
  have hV : V * (1 + C) = 1 := Matrix.nonsing_inv_mul _ hplus
  have hW : (1 - C * C) * W = 1 := Matrix.mul_nonsing_inv _ hsquare
  have hUC : U * C = U - 1 := by
    have hh : U - U * C = 1 := by simpa only [mul_sub, mul_one] using hU
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hh).symm
  have hh := hessian_core_identity C U V W hC hU hUr hV hW
  rw [hUC, Matrix.transpose_sub, Matrix.transpose_one] at hh
  change U + U.transpose - 1 = _
  calc
    U + U.transpose - 1 = 1 + (U - 1) + (U.transpose - 1) := by noncomm_ring
    _ = (1 + C * C) * W := hh

theorem Tournament.complexNormalizedSign_eq_realMap {d : ℕ} (T : Tournament d) :
    T.complexNormalizedSign = Complex.ofRealHom.mapMatrix T.realNormalizedSign := by
  ext i j
  simp [Tournament.complexNormalizedSign, Tournament.realNormalizedSign]

theorem Tournament.criticalResolvent_eq_realMap {d : ℕ} (T : Tournament d) :
    T.criticalResolvent = Complex.ofRealHom.mapMatrix ((1 - T.realNormalizedSign)⁻¹) := by
  rw [mapMatrix_nonsing_inv_of_isUnit Complex.ofRealHom _
    (isUnit_det_one_sub_real_skew T.realNormalizedSign T.realNormalizedSign_skew)]
  unfold Tournament.criticalResolvent
  congr 1
  rw [map_sub, map_one, ← T.complexNormalizedSign_eq_realMap]

/-- This is the exact real/complex core correspondence required after the
polynomial mixed-derivative calculation. -/
theorem Tournament.criticalResolvent_sum_eq_realCore {d : ℕ} (T : Tournament d) :
    T.criticalResolvent + T.criticalResolvent.transpose - 1 =
      Complex.ofRealHom.mapMatrix
        ((1 + T.realNormalizedSign * T.realNormalizedSign) *
          (1 - T.realNormalizedSign * T.realNormalizedSign)⁻¹) := by
  rw [T.criticalResolvent_eq_realMap]
  have hh := congrArg Complex.ofRealHom.mapMatrix
    (real_resolvent_sum T.realNormalizedSign T.realNormalizedSign_skew)
  have htranspose (A : Matrix (Fin d) (Fin d) ℝ) :
      Complex.ofRealHom.mapMatrix A.transpose =
        (Complex.ofRealHom.mapMatrix A).transpose := rfl
  simpa only [map_add, map_sub, map_one, htranspose] using hh

end
end Wormald

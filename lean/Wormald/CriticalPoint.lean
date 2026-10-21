import Wormald.Elimination
import Wormald.RegularCandidate
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! The actual critical point and nonzero last-coordinate coefficient of
Wormald's defining determinant. These are finite identities, independent of
any analytic Hessian correspondence. -/

open Matrix
open scoped BigOperators

namespace Wormald

noncomputable section

def Tournament.complexNormalizedSign {d : ℕ} (T : Tournament d) :
    Matrix (Fin d) (Fin d) ℂ := T.normalizedSign.map (Rat.castHom ℂ)

def Tournament.constantProjection {d : ℕ} (_T : Tournament d) :
    Matrix (Fin d) (Fin d) ℂ := Matrix.of fun _ _ => 1 / (d : ℂ)

def Tournament.criticalTransition {d : ℕ} (T : Tournament d) :
    Matrix (Fin d) (Fin d) ℂ := T.constantProjection + T.complexNormalizedSign

def Tournament.criticalResolvent {d : ℕ} (T : Tournament d) :
    Matrix (Fin d) (Fin d) ℂ := (1 - T.complexNormalizedSign)⁻¹

def Tournament.criticalDet {d : ℕ} (T : Tournament d) : ℂ :=
  (1 - T.complexNormalizedSign).det

theorem Tournament.normalizedSign_skew {d : ℕ} (T : Tournament d) :
    T.normalizedSign.transpose = -T.normalizedSign := by
  ext i j
  change T.sign j i / (d : ℚ) = -(T.sign i j / (d : ℚ))
  have hij : T.sign j i = -T.sign i j := congrFun (congrFun T.sign_skew i) j
  rw [hij, neg_div]

theorem Tournament.complexNormalizedSign_skew {d : ℕ} (T : Tournament d) :
    T.complexNormalizedSign.transpose = -T.complexNormalizedSign := by
  change (T.normalizedSign.map (Rat.castHom ℂ)).transpose =
    -(T.normalizedSign.map (Rat.castHom ℂ))
  rw [← Matrix.transpose_map, T.normalizedSign_skew]
  ext i j
  simp

theorem Tournament.complexNormalizedSign_mulVec_one {d : ℕ} (T : Tournament d)
    (hT : T.Regular) : T.complexNormalizedSign *ᵥ (fun _ => 1) = 0 := by
  have hrat (i : Fin d) : ∑ j, T.normalizedSign i j = 0 := by
    simp only [Tournament.normalizedSign, ← Finset.sum_div, T.sign_row_sum hT,
      zero_div]
  funext i
  change (∑ j, (T.normalizedSign i j : ℂ) * 1) = 0
  simp only [mul_one]
  exact_mod_cast hrat i

theorem Tournament.one_vecMul_complexNormalizedSign {d : ℕ} (T : Tournament d)
    (hT : T.Regular) : (fun _ => 1) ᵥ* T.complexNormalizedSign = 0 := by
  rw [← Matrix.mulVec_transpose, T.complexNormalizedSign_skew, Matrix.neg_mulVec,
    T.complexNormalizedSign_mulVec_one hT, neg_zero]

/-- A rational skew matrix has no eigenvalue 1, by the real positive-definite
identity `I-C²=I+CᵀC`. -/
theorem det_one_sub_rational_skew_ne_zero {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℚ) (hC : C.transpose = -C) : (1 - C).det ≠ 0 := by
  let Cr := C.map (Rat.castHom ℝ)
  have hCr : Cr.transpose = -Cr := by
    change (C.map (Rat.castHom ℝ)).transpose = -(C.map (Rat.castHom ℝ))
    rw [← Matrix.transpose_map, hC]
    ext i j
    simp
  have hplus : (1 + Cr).det ≠ 0 := by
    intro hz
    have hp := (posDef_one_sub_square Cr hCr).det_pos
    rw [det_one_sub_square Cr hCr, hz] at hp
    norm_num at hp
  have hminus : (1 - Cr).det ≠ 0 := by
    rw [det_one_sub_eq_det_one_add Cr hCr]
    exact hplus
  have htransport : ((1 - C).det : ℝ) = (1 - Cr).det := by
    change (Rat.castHom ℝ) (1 - C).det = _
    rw [RingHom.map_det]
    change (((Rat.castHom ℝ).mapMatrix) (1 - C)).det = _
    rw [map_sub, map_one]
    rfl
  intro hz
  apply hminus
  rw [← htransport, hz, Rat.cast_zero]

theorem Tournament.criticalDet_eq_ratCast {d : ℕ} (T : Tournament d) :
    T.criticalDet = ((1 - T.normalizedSign).det : ℂ) := by
  symm
  change (Rat.castHom ℂ) (1 - T.normalizedSign).det = _
  rw [RingHom.map_det]
  change (((Rat.castHom ℂ).mapMatrix) (1 - T.normalizedSign)).det = _
  rw [map_sub, map_one]
  rfl

theorem Tournament.criticalDet_ne_zero {d : ℕ} (T : Tournament d) :
    T.criticalDet ≠ 0 := by
  rw [T.criticalDet_eq_ratCast]
  exact_mod_cast det_one_sub_rational_skew_ne_zero T.normalizedSign T.normalizedSign_skew

theorem det_critical_rankTwo {m : Type*} [Fintype m] [DecidableEq m]
    {R : Type*} [Field R] [CharZero R]
    (D : Matrix m m R) (hD : IsUnit D.det)
    (hd : (Fintype.card m : R) ≠ 0)
    (hu : D *ᵥ (fun _ => 1) = (fun _ => 1))
    (hul : (fun _ => 1) ᵥ* D = (fun _ => 1))
    (v : m → R) (hv : ∑ i, v i = (Fintype.card m : R) / 2)
    (p : m) (z t : R) :
    (Matrix.of fun i j => D i j - 1 / (Fintype.card m : R) -
      (t - z) * v i * (if j = p then 1 else 0)).det = D.det * ((z - t) / 2) := by
  let U : Matrix m (Fin 2) R := Matrix.of fun i j => if j = 0 then 1 else v i
  let V : Matrix (Fin 2) m R := Matrix.of fun j i =>
    if j = 0 then -1 / (Fintype.card m : R) else
      -(t - z) * (if i = p then 1 else 0)
  have hinvu : D⁻¹ *ᵥ (fun _ => 1) = (fun _ => 1) := by
    calc
      D⁻¹ *ᵥ (fun _ => 1) = D⁻¹ *ᵥ (D *ᵥ (fun _ => 1)) := by rw [hu]
      _ = (fun _ => 1) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hD, Matrix.one_mulVec]
  have hinvul : (fun _ => 1) ᵥ* D⁻¹ = (fun _ => 1) := by
    calc
      (fun _ => 1) ᵥ* D⁻¹ = ((fun _ => 1) ᵥ* D) ᵥ* D⁻¹ := by rw [hul]
      _ = (fun _ => 1) := by
        rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hD, Matrix.vecMul_one]
  have hsuminv : ∑ i, (D⁻¹ *ᵥ v) i = (Fintype.card m : R) / 2 := by
    calc
      ∑ i, (D⁻¹ *ᵥ v) i = (fun _ => 1) ⬝ᵥ (D⁻¹ *ᵥ v) := by simp [dotProduct]
      _ = ((fun _ => 1) ᵥ* D⁻¹) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
      _ = (fun _ => 1) ⬝ᵥ v := by rw [hinvul]
      _ = (Fintype.card m : R) / 2 := by simpa [dotProduct] using hv
  have hu0 (i : m) : (D⁻¹ * U) i 0 = 1 := by
    simpa [U, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hinvu i
  have hu1 (i : m) : (D⁻¹ * U) i 1 = (D⁻¹ *ᵥ v) i := by
    simp [U, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  let S : Matrix (Fin 2) (Fin 2) R := 1 + V * (D⁻¹ * U)
  have h00 : S 0 0 = 0 := by
    change (1 : Matrix (Fin 2) (Fin 2) R) 0 0 + ∑ i, V 0 i * (D⁻¹ * U) i 0 = 0
    simp only [Matrix.one_apply_eq, V, Matrix.of_apply, hu0, mul_one, ↓reduceIte]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have h01 : S 0 1 = -1 / 2 := by
    change (1 : Matrix (Fin 2) (Fin 2) R) 0 1 + ∑ i, V 0 i * (D⁻¹ * U) i 1 = -1 / 2
    simp only [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), V,
      Matrix.of_apply, hu1, zero_add, ↓reduceIte, ← Finset.mul_sum, hsuminv]
    field_simp
  have h10 : S 1 0 = -(t - z) := by
    change (1 : Matrix (Fin 2) (Fin 2) R) 1 0 + ∑ i, V 1 i * (D⁻¹ * U) i 0 = -(t - z)
    simp [V, hu0]
  have hS : S.det = (z - t) / 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10]
    ring
  have hM : (Matrix.of fun i j => D i j - 1 / (Fintype.card m : R) -
      (t - z) * v i * (if j = p then 1 else 0)) = D + U * V := by
    ext i j
    by_cases hj : j = p <;>
      simp [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, U, V, hj] <;> ring
  rw [hM, Matrix.det_add_mul U V hD, Matrix.mul_assoc]
  exact congrArg (D.det * ·) hS

/-- The transition matrix is exactly Wormald's scaled adjacency matrix. -/
theorem Tournament.criticalTransition_entry {d : ℕ} (T : Tournament d)
    (hd : d ≠ 0) (i j : Fin d) :
    T.criticalTransition i j =
      ((T.adjacency i j : ℂ) + if i = j then (1 / 2 : ℂ) else 0) * (2 / (d : ℂ)) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  by_cases hij : i = j <;>
    simp [Tournament.criticalTransition, Tournament.constantProjection,
      Tournament.complexNormalizedSign, Tournament.normalizedSign, Tournament.sign, hij] <;>
    field_simp <;> ring

/-- Varying one original variable is a two-column perturbation of `I-C`. -/
theorem originalMatrix_update_critical {d : ℕ} (T : Tournament d) (hd : d ≠ 0)
    (p : Fin d) (t : ℂ) :
    originalMatrix T (Function.update (fun _ => 2 / (d : ℂ)) p t) =
      Matrix.of (fun i j => (1 - T.complexNormalizedSign) i j - 1 / (d : ℂ) -
        (t - 2 / (d : ℂ)) *
          ((T.adjacency i p : ℂ) + if i = p then (1 / 2 : ℂ) else 0) *
          (if j = p then 1 else 0)) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  ext i j
  by_cases hj : j = p
  · subst j
    by_cases hij : i = p <;>
      simp [originalMatrix, Tournament.complexNormalizedSign, Tournament.normalizedSign,
        Tournament.sign, Matrix.one_apply, hij] <;> field_simp <;> ring
  · by_cases hij : i = j <;>
      simp [originalMatrix, Tournament.complexNormalizedSign, Tournament.normalizedSign,
        Tournament.sign, Matrix.one_apply, hij, hj] <;> field_simp <;> ring

theorem Tournament.critical_column_sum {d : ℕ} (T : Tournament d)
    (hT : T.Regular) (hd : d ≠ 0) (p : Fin d) :
    (∑ i, ((T.adjacency i p : ℂ) + if i = p then (1 / 2 : ℂ) else 0)) = (d : ℂ) / 2 := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hcol : ∑ i, T.complexNormalizedSign i p = 0 := by
    simpa [Matrix.vecMul, dotProduct] using
      congrFun (T.one_vecMul_complexNormalizedSign hT) p
  have hP : ∑ i, T.criticalTransition i p = 1 := by
    simp [Tournament.criticalTransition, Tournament.constantProjection,
      Finset.sum_add_distrib, hcol, hdC]
  simp only [T.criticalTransition_entry hd, ← Finset.sum_mul] at hP
  apply mul_right_cancel₀ (show (2 / (d : ℂ)) ≠ 0 by exact div_ne_zero (by norm_num) hdC)
  rw [hP]
  field_simp

/-- The original determinant along any single critical coordinate is exactly
affine with the same nonzero slope. -/
theorem originalDeterminant_update_critical {d : ℕ} (T : Tournament d)
    (hT : T.Regular) (hd : d ≠ 0) (p : Fin d) (t : ℂ) :
    originalDeterminant T (Function.update (fun _ => 2 / (d : ℂ)) p t) =
      T.criticalDet * ((2 / (d : ℂ) - t) / 2) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hD : IsUnit (1 - T.complexNormalizedSign).det :=
    isUnit_iff_ne_zero.mpr T.criticalDet_ne_zero
  have hu : (1 - T.complexNormalizedSign) *ᵥ (fun _ => 1) = (fun _ => 1) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, T.complexNormalizedSign_mulVec_one hT,
      sub_zero]
  have hul : (fun _ => 1) ᵥ* (1 - T.complexNormalizedSign) = (fun _ => 1) := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, T.one_vecMul_complexNormalizedSign hT,
      sub_zero]
  unfold originalDeterminant
  rw [originalMatrix_update_critical T hd]
  simpa only [Fintype.card_fin, Tournament.criticalDet] using
    det_critical_rankTwo (1 - T.complexNormalizedSign) hD
      (by simpa only [Fintype.card_fin] using hdC) hu hul
      (fun i => (T.adjacency i p : ℂ) + if i = p then (1 / 2 : ℂ) else 0)
      (by simpa only [Fintype.card_fin] using T.critical_column_sum hT hd p)
      p (2 / (d : ℂ)) t

theorem appendLast_constant_eq_update {n : ℕ} (z t : ℂ) :
    appendLast (fun _ : Fin n => z) t =
      Function.update (fun _ : Fin (n + 1) => z) (Fin.last n) t := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [appendLast]
  · simp [appendLast, (Fin.castSucc_lt_last j).ne]

/-- The original determinant really vanishes at Wormald's critical point. -/
theorem originalDeterminant_critical {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) :
    originalDeterminant T (fun _ => 2 / ((n + 1 : ℕ) : ℂ)) = 0 := by
  have h := originalDeterminant_update_critical T hT (Nat.succ_ne_zero n)
    (Fin.last n) (2 / ((n + 1 : ℕ) : ℂ))
  simpa only [Function.update_eq_self, sub_self, zero_div, mul_zero] using h

theorem eliminatedNumerator_critical {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) :
    eliminatedNumerator T (fun _ => 2 / ((n + 1 : ℕ) : ℂ)) =
      T.criticalDet / ((n + 1 : ℕ) : ℂ) := by
  unfold eliminatedNumerator
  rw [appendLast_constant_eq_update,
    originalDeterminant_update_critical T hT (Nat.succ_ne_zero n)]
  ring

/-- The genuine eliminated last-coordinate coefficient is `-det(I-C)/2`. -/
theorem eliminatedCoefficient_critical {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) :
    eliminatedCoefficient T (fun _ => 2 / ((n + 1 : ℕ) : ℂ)) =
      -T.criticalDet / 2 := by
  unfold eliminatedCoefficient eliminatedNumerator
  rw [appendLast_constant_eq_update, appendLast_constant_eq_update,
    originalDeterminant_update_critical T hT (Nat.succ_ne_zero n),
    originalDeterminant_update_critical T hT (Nat.succ_ne_zero n)]
  ring

theorem eliminatedCoefficient_critical_ne_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) :
    eliminatedCoefficient T (fun _ => 2 / ((n + 1 : ℕ) : ℂ)) ≠ 0 := by
  rw [eliminatedCoefficient_critical T hT]
  exact div_ne_zero (neg_ne_zero.mpr T.criticalDet_ne_zero) (by norm_num)

/-- The explicitly defined elimination function has the required critical value. -/
theorem originalImplicitFunction_critical {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) :
    originalImplicitFunction T (fun _ => 2 / ((n + 1 : ℕ) : ℂ)) =
      2 / ((n + 1 : ℕ) : ℂ) := by
  unfold originalImplicitFunction
  rw [eliminatedNumerator_critical T hT, eliminatedCoefficient_critical T hT]
  field_simp [T.criticalDet_ne_zero]

theorem Tournament.criticalResolvent_mul_inverse {d : ℕ} (T : Tournament d) :
    T.criticalResolvent * (1 - T.complexNormalizedSign) = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr T.criticalDet_ne_zero)

theorem Tournament.inverse_mul_criticalResolvent {d : ℕ} (T : Tournament d) :
    (1 - T.complexNormalizedSign) * T.criticalResolvent = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr T.criticalDet_ne_zero)

theorem Tournament.criticalResolvent_mulVec_one {d : ℕ} (T : Tournament d)
    (hT : T.Regular) : T.criticalResolvent *ᵥ (fun _ => 1) = (fun _ => 1) := by
  have hD : (1 - T.complexNormalizedSign) *ᵥ (fun _ => 1) = (fun _ => 1) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, T.complexNormalizedSign_mulVec_one hT,
      sub_zero]
  calc
    T.criticalResolvent *ᵥ (fun _ => 1) =
        T.criticalResolvent *ᵥ ((1 - T.complexNormalizedSign) *ᵥ (fun _ => 1)) := by rw [hD]
    _ = (fun _ => 1) := by
      rw [Matrix.mulVec_mulVec, T.criticalResolvent_mul_inverse, Matrix.one_mulVec]

theorem Tournament.one_vecMul_criticalResolvent {d : ℕ} (T : Tournament d)
    (hT : T.Regular) : (fun _ => 1) ᵥ* T.criticalResolvent = (fun _ => 1) := by
  have hD : (fun _ => 1) ᵥ* (1 - T.complexNormalizedSign) = (fun _ => 1) := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, T.one_vecMul_complexNormalizedSign hT,
      sub_zero]
  calc
    (fun _ => 1) ᵥ* T.criticalResolvent =
        ((fun _ => 1) ᵥ* (1 - T.complexNormalizedSign)) ᵥ* T.criticalResolvent := by rw [hD]
    _ = (fun _ => 1) := by
      rw [Matrix.vecMul_vecMul, T.inverse_mul_criticalResolvent, Matrix.vecMul_one]

/-- The finite resolvent identity used in the mixed-coordinate determinant. -/
theorem Tournament.criticalResolvent_mul_criticalTransition {d : ℕ} (T : Tournament d)
    (hT : T.Regular) :
    T.criticalResolvent * T.criticalTransition =
      T.criticalResolvent - 1 + T.constantProjection := by
  have hUP0 : T.criticalResolvent * T.constantProjection = T.constantProjection := by
    ext i j
    change (∑ k, T.criticalResolvent i k * (1 / (d : ℂ))) = 1 / (d : ℂ)
    rw [← Finset.sum_mul]
    have hs : ∑ k, T.criticalResolvent i k = 1 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun (T.criticalResolvent_mulVec_one hT) i
    rw [hs, one_mul]
  have hUC : T.criticalResolvent * T.complexNormalizedSign = T.criticalResolvent - 1 := by
    have hh : T.criticalResolvent - T.criticalResolvent * T.complexNormalizedSign = 1 := by
      simpa only [mul_sub, mul_one] using T.criticalResolvent_mul_inverse
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hh).symm
  rw [Tournament.criticalTransition, mul_add, hUP0, hUC, add_comm]

end
end Wormald


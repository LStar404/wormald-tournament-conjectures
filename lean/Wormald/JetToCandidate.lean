import Wormald.CriticalResolvent
import Wormald.CriticalJets

/-! Coordinate entries and the final finite algebraic Hessian correspondence. -/

open Matrix MvPolynomial
open scoped BigOperators

namespace Wormald

noncomputable section

theorem coordinateCompression_entry {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j k : Fin n) :
    ((coordinateEmbedding n).transpose * Q * coordinateEmbedding n) j k =
      Q j.castSucc k.castSucc - Q j.castSucc (Fin.last n) -
        Q (Fin.last n) k.castSucc + Q (Fin.last n) (Fin.last n) := by
  have hlast (a : Fin n) : coordinateEmbedding n (Fin.last n) a = -1 := by
    simp [coordinateEmbedding, (Fin.castSucc_lt_last a).ne']
  have hcast (a b : Fin n) : coordinateEmbedding n a.castSucc b =
      if a = b then 1 else 0 := by simp [coordinateEmbedding]
  have hleft (a : Fin n) (b : Fin (n + 1)) :
      ((coordinateEmbedding n).transpose * Q) a b =
        Q a.castSucc b - Q (Fin.last n) b := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [Fin.sum_univ_castSucc]
    simp [hcast, hlast, ite_mul]
    ring
  simp only [Matrix.mul_apply, hleft]
  rw [Fin.sum_univ_castSucc]
  simp [hcast, hlast, mul_ite]
  ring

theorem Tournament.candidateHessian_complex_entry {n : ℕ}
    (T : Tournament (n + 1)) (j k : Fin n) :
    (Complex.ofRealHom.mapMatrix T.candidateHessian) j k =
      (T.criticalResolvent + T.criticalResolvent.transpose - 1) j.castSucc k.castSucc -
      (T.criticalResolvent + T.criticalResolvent.transpose - 1) j.castSucc (Fin.last n) -
      (T.criticalResolvent + T.criticalResolvent.transpose - 1) (Fin.last n) k.castSucc +
      (T.criticalResolvent + T.criticalResolvent.transpose - 1) (Fin.last n) (Fin.last n) := by
  let Q := (1 + T.realNormalizedSign * T.realNormalizedSign) *
    (1 - T.realNormalizedSign * T.realNormalizedSign)⁻¹
  have hentry (a b : Fin (n + 1)) :
      (Q a b : ℂ) = (T.criticalResolvent + T.criticalResolvent.transpose - 1) a b := by
    exact (congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M a b)
      T.criticalResolvent_sum_eq_realCore).symm
  change ((((coordinateEmbedding n).transpose * Q * coordinateEmbedding n) j k : ℝ) : ℂ) = _
  rw [coordinateCompression_entry]
  push_cast
  rw [hentry, hentry, hentry, hentry]

theorem ratCast_eval_complex {d : ℕ} (K : MvPolynomial (Fin d) ℚ) (z : ℚ) :
    (eval (fun _ => z) K : ℂ) = eval₂ (Rat.castHom ℂ) (fun _ => (z : ℂ)) K := by
  induction K using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem Tournament.criticalResolvent_criticalColumn_entry {d : ℕ}
    (T : Tournament d) (hT : T.Regular) (hd : d ≠ 0) (i j : Fin d) :
    (T.criticalResolvent *ᵥ T.criticalColumn j) i = (d : ℂ) / 2 *
      (T.criticalResolvent i j - (if i = j then 1 else 0) + 1 / (d : ℂ)) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hcol (k : Fin d) : T.criticalTransition k j =
      T.criticalColumn j k * (2 / (d : ℂ)) := T.criticalTransition_entry hd k j
  have hentry : (T.criticalResolvent * T.criticalTransition) i j =
      (T.criticalResolvent *ᵥ T.criticalColumn j) i * (2 / (d : ℂ)) := by
    simp only [Matrix.mul_apply, hcol, Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    exact (mul_assoc _ _ _).symm
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j)
    (T.criticalResolvent_mul_criticalTransition hT)
  rw [hentry] at h
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Tournament.constantProjection, Matrix.of_apply] at h
  apply mul_right_cancel₀ (show (2 / (d : ℂ)) ≠ 0 from div_ne_zero (by norm_num) hdC)
  rw [h]
  field_simp

theorem firstLogJet_cast_critical {d : ℕ} (T : Tournament d) (hT : T.Regular)
    (hd : d ≠ 0) (j : Fin d) :
    (firstLogJet (definingPolynomial T.adjacency) (2 / (d : ℚ)) j : ℂ) =
      -T.criticalDet / (d : ℂ) := by
  simp only [firstLogJet, Rat.cast_mul, ratCast_eval_complex]
  push_cast
  rw [eval_first_pderiv_critical T hT hd j]
  ring

theorem secondLogJet_cast_critical {d : ℕ} (T : Tournament d) (hT : T.Regular)
    (hd : d ≠ 0) (j k : Fin d) :
    (secondLogJet (definingPolynomial T.adjacency) (2 / (d : ℚ)) j k : ℂ) =
      T.criticalDet / (d : ℂ) *
        (T.criticalResolvent j j + T.criticalResolvent k k -
          T.criticalResolvent j k - T.criticalResolvent k j - 2 +
          (if j = k then 1 else 0)) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hdelta : ((if j = k then
        firstLogJet (definingPolynomial T.adjacency) (2 / (d : ℚ)) j else 0 : ℚ) : ℂ) =
      if j = k then -T.criticalDet / (d : ℂ) else 0 := by
    split_ifs <;> simp [firstLogJet_cast_critical T hT hd]
  simp only [secondLogJet, Rat.cast_add, Rat.cast_mul, Rat.cast_pow]
  rw [ratCast_eval_complex, hdelta]
  push_cast
  rw [eval_second_pderiv_critical T hT hd j k]
  simp only [T.criticalResolvent_criticalColumn_entry hT hd]
  by_cases hjk : j = k
  · subst k
    simp
    ring
  · simp [hjk, Ne.symm hjk]
    field_simp
    ring

/-- The actual polynomial implicit jet is exactly the finite positive Hessian
candidate, for every regular tournament and the prescribed eliminated coordinate. -/
theorem angularHessianJet_eq_candidate {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) (j k : Fin n) :
    (angularHessianJet (definingPolynomial T.adjacency)
      (2 / ((n + 1 : ℕ) : ℚ)) (Fin.last n) j.castSucc k.castSucc : ℂ) =
      (Complex.ofRealHom.mapMatrix T.candidateHessian) j k := by
  have hdC : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hq : T.criticalDet ≠ 0 := T.criticalDet_ne_zero
  have hjp : j.castSucc ≠ Fin.last n := Fin.castSucc_ne_last j
  have hkp : k.castSucc ≠ Fin.last n := Fin.castSucc_ne_last k
  simp only [angularHessianJet, Rat.cast_div, Rat.cast_add, Rat.cast_sub]
  rw [secondLogJet_cast_critical T hT (Nat.succ_ne_zero n),
    secondLogJet_cast_critical T hT (Nat.succ_ne_zero n),
    secondLogJet_cast_critical T hT (Nat.succ_ne_zero n),
    secondLogJet_cast_critical T hT (Nat.succ_ne_zero n),
    firstLogJet_cast_critical T hT (Nat.succ_ne_zero n),
    T.candidateHessian_complex_entry]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply, Matrix.one_apply]
  by_cases hjk : j = k
  · subst k
    simp [hjp, Ne.symm hjp]
    field_simp
    ring
  · simp [hjk, hjp, Ne.symm hkp]
    field_simp
    ring

end
end Wormald

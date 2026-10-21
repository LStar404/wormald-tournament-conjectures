import Wormald.MatrixMomentSeries
import Wormald.SpectralConstant

/-! The actual tournament determinant ratio is represented by the positive
odd-power Frobenius moment series used in the extremal proof. -/

namespace Wormald
noncomputable section
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def frobeniusSq (M : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

omit [DecidableEq ι] in
theorem trace_transpose_mul_self_eq_frobeniusSq (M : Matrix ι ι ℝ) :
    (M.transpose * M).trace = frobeniusSq M := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    frobeniusSq, pow_two]
  exact Finset.sum_comm

omit [DecidableEq ι] in
theorem neg_skew_square_eq_gram (C : Matrix ι ι ℝ) (hC : C.transpose = -C) :
    -(C * C) = C.transpose * C := by rw [hC, neg_mul]

theorem trace_neg_skew_square_pow (C : Matrix ι ι ℝ)
    (hC : C.transpose = -C) (k : ℕ) :
    ((-(C * C)) ^ k).trace = frobeniusSq (C ^ k) := by
  have hcomm : Commute C.transpose C := by
    rw [hC]
    change (-C) * C = C * (-C)
    noncomm_ring
  rw [neg_skew_square_eq_gram C hC, hcomm.mul_pow,
    ← Matrix.transpose_pow, trace_transpose_mul_self_eq_frobeniusSq]

omit [DecidableEq ι] in
theorem posSemidef_neg_skew_square (C : Matrix ι ι ℝ)
    (hC : C.transpose = -C) : (-(C * C)).PosSemidef := by
  rw [neg_skew_square_eq_gram C hC]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self C

theorem Tournament.spectralRatio_re_pos {d : ℕ} (T : Tournament d) (hd : d ≠ 0) :
    0 < T.spectralRatio.re := by
  obtain ⟨q, hq, heq⟩ := T.spectralRatio_positive_rational hd
  rw [heq]
  simpa only [Complex.ratCast_re] using (show (0 : ℝ) < q by exact_mod_cast hq)

theorem Tournament.spectralRatio_re_sq {d : ℕ} (T : Tournament d) (hd : d ≠ 0) :
    T.spectralRatio.re ^ 2 =
      (1 - T.realNormalizedSign * T.realNormalizedSign).det /
        (1 + T.realNormalizedSign * T.realNormalizedSign).det := by
  obtain ⟨q, _, heq⟩ := T.spectralRatio_positive_rational hd
  have hsq := T.spectralRatio_sq
  rw [heq] at hsq
  have hplus : 1 + T.complexNormalizedSign * T.complexNormalizedSign =
      Complex.ofRealHom.mapMatrix (1 + T.realNormalizedSign * T.realNormalizedSign) := by
    rw [map_add, map_one, map_mul, ← T.complexNormalizedSign_eq_realMap]
  have hminus : 1 - T.complexNormalizedSign * T.complexNormalizedSign =
      Complex.ofRealHom.mapMatrix (1 - T.realNormalizedSign * T.realNormalizedSign) := by
    rw [map_sub, map_one, map_mul, ← T.complexNormalizedSign_eq_realMap]
  rw [hplus, hminus, ← Complex.ofRealHom.map_det, ← Complex.ofRealHom.map_det] at hsq
  rw [heq]
  simp only [Complex.ratCast_re]
  apply Complex.ofRealHom.injective
  simp only [map_pow, map_div₀]
  simpa using hsq

theorem Tournament.log_spectralRatio_re {d : ℕ} (T : Tournament d) (hd : d ≠ 0) :
    Real.log T.spectralRatio.re =
      (Real.log (1 - T.realNormalizedSign * T.realNormalizedSign).det -
        Real.log (1 + T.realNormalizedSign * T.realNormalizedSign).det) / 2 := by
  have hp := (T.posDef_one_add_realNormalizedSign_square hd).det_pos
  have hm := (posDef_one_sub_square T.realNormalizedSign T.realNormalizedSign_skew).det_pos
  have hlog := congrArg Real.log (T.spectralRatio_re_sq hd)
  rw [Real.log_pow, Real.log_div hm.ne' hp.ne'] at hlog
  norm_num at hlog
  linarith

/-- The complete log-determinant/moment-series identity for the literal
normalized tournament sign matrix. Regularity is not needed for this identity. -/
theorem Tournament.hasSum_frobenius_odd_log_spectralRatio {d : ℕ}
    (T : Tournament d) (hd : d ≠ 0) :
    HasSum (fun r : ℕ => frobeniusSq (T.realNormalizedSign ^ (2 * r + 1)) /
      ((2 * r + 1 : ℕ) : ℝ)) (Real.log T.spectralRatio.re) := by
  have hminus : (1 - (-(T.realNormalizedSign * T.realNormalizedSign))).PosDef := by
    simpa only [sub_neg_eq_add] using T.posDef_one_add_realNormalizedSign_square hd
  have h := hasSum_trace_odd_pow_logdet (-(T.realNormalizedSign * T.realNormalizedSign))
    (posSemidef_neg_skew_square T.realNormalizedSign T.realNormalizedSign_skew) hminus
  rw [T.log_spectralRatio_re hd]
  simpa only [trace_neg_skew_square_pow T.realNormalizedSign T.realNormalizedSign_skew,
    sub_eq_add_neg, sub_neg_eq_add, neg_neg] using h

end
end Wormald

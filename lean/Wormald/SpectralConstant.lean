import Wormald.CriticalResolvent
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue

/-! The actual determinant ratio has the positive rational sign required by
the manuscript. Positivity is proved along a continuous nonvanishing matrix
path, without assuming a spectral decomposition or selecting a square root. -/

open Matrix
open scoped BigOperators

namespace Wormald

noncomputable section

private theorem positive_endpoint_of_nonzero (g : ℝ → ℝ) (hg : Continuous g)
    (hzero : g 0 = 1) (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ≠ 0) : 0 < g 1 := by
  by_contra hpos
  have hle : g 1 ≤ 0 := le_of_not_gt hpos
  have hz : (0 : ℝ) ∈ Set.Icc (g 1) (g 0) := by rw [hzero]; exact ⟨hle, by norm_num⟩
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hg.continuousOn hz
  exact hne t ht hgt

private theorem smul_skew {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℝ) (hC : C.transpose = -C) (t : ℝ) :
    (t • C).transpose = -(t • C) := by simp [hC]

/-- Every real skew resolvent has a positive real determinant. -/
theorem det_one_add_real_skew_pos {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℝ) (hC : C.transpose = -C) : 0 < (1 + C).det := by
  let g : ℝ → ℝ := fun t => (1 + t • C).det
  have hg : Continuous g := by
    apply Continuous.matrix_det
    fun_prop
  have hzero : g 0 = 1 := by simp [g]
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ≠ 0 := by
    intro t _
    change (1 + t • C).det ≠ 0
    rw [← det_one_sub_eq_det_one_add (t • C) (smul_skew C hC t)]
    exact (isUnit_det_one_sub_real_skew (t • C) (smul_skew C hC t)).ne_zero
  simpa [g] using positive_endpoint_of_nonzero g hg hzero hne

private def complexSkewPencil {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℝ) (t : ℝ) : Matrix m m ℂ :=
  1 + Complex.I • (Complex.ofRealHom.mapMatrix (t • C))

private theorem complexSkewPencil_hermitian {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℝ) (hC : C.transpose = -C) (t : ℝ) :
    (complexSkewPencil C t).conjTranspose = complexSkewPencil C t := by
  ext i j
  have hij : C j i = -C i j := congrFun (congrFun hC i) j
  by_cases h : i = j
  · subst j
    have hii : C i i = 0 := by linarith
    simp [complexSkewPencil, Matrix.conjTranspose_apply, Matrix.smul_apply, hii]
  · simp [complexSkewPencil, Matrix.conjTranspose_apply,
      Matrix.smul_apply, hij, h, eq_comm]

private theorem complexSkewPencil_im_zero {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℝ) (hC : C.transpose = -C) (t : ℝ) :
    (complexSkewPencil C t).det.im = 0 := by
  have hh : (complexSkewPencil C t).det = star (complexSkewPencil C t).det := by
    simpa only [complexSkewPencil_hermitian C hC t] using
      Matrix.det_conjTranspose (complexSkewPencil C t)
  have hi := congrArg Complex.im hh
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

private theorem complexSkewPencil_square {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℝ) (hC : C.transpose = -C) (t : ℝ) :
    (((1 + (t • C) * (t • C)).det : ℝ) : ℂ) =
      (complexSkewPencil C t).det ^ 2 := by
  let Ct := Complex.ofRealHom.mapMatrix (t • C)
  have hCt : Ct.transpose = -Ct := by
    change ((t • C).map Complex.ofRealHom).transpose = -((t • C).map Complex.ofRealHom)
    rw [← Matrix.transpose_map, smul_skew C hC t]
    ext i j
    simp
  change Complex.ofRealHom (1 + (t • C) * (t • C)).det = _
  rw [RingHom.map_det]
  change (Complex.ofRealHom.mapMatrix (1 + (t • C) * (t • C))).det = _
  rw [map_add, map_one, map_mul]
  exact det_one_add_square Ct hCt Complex.I Complex.I_mul_I

private theorem smul_frobenius_lt_one {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℝ) (hF : (∑ i, ∑ j, C i j ^ 2) < 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i, ∑ j, (t • C) i j ^ 2) < 1 := by
  have hF0 : 0 ≤ ∑ i, ∑ j, C i j ^ 2 := by positivity
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hsum : (∑ i, ∑ j, (t • C) i j ^ 2) =
      t ^ 2 * (∑ i, ∑ j, C i j ^ 2) := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [hsum]
  nlinarith

/-- The determinant `det(I+iC)` has strictly positive real part when the
entry-square bound is below one. Its imaginary part is exactly zero. -/
theorem det_one_add_I_real_skew_pos {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℝ) (hC : C.transpose = -C)
    (hF : (∑ i, ∑ j, C i j ^ 2) < 1) :
    0 < (1 + Complex.I • Complex.ofRealHom.mapMatrix C).det.re ∧
      (1 + Complex.I • Complex.ofRealHom.mapMatrix C).det.im = 0 := by
  let g : ℝ → ℝ := fun t => (complexSkewPencil C t).det.re
  have hmatrix : Continuous (complexSkewPencil C) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [complexSkewPencil, Matrix.add_apply, Matrix.smul_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul]
    change Continuous (fun a : ℝ => (1 : Matrix m m ℂ) i j +
      Complex.I * ((a * C i j : ℝ) : ℂ))
    exact continuous_const.add (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)))
  have hg : Continuous g := Complex.continuous_re.comp hmatrix.matrix_det
  have hzero : g 0 = 1 := by simp [g, complexSkewPencil]
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ≠ 0 := by
    intro t ht hz
    have hpos := (posDef_one_add_square_of_frobenius (t • C)
      (smul_skew C hC t) (smul_frobenius_lt_one C hF t ht)).det_pos
    have him := complexSkewPencil_im_zero C hC t
    have hdetzero : (complexSkewPencil C t).det = 0 := by
      apply Complex.ext
      · exact hz
      · exact him
    have hsq := complexSkewPencil_square C hC t
    rw [hdetzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
    have : (1 + (t • C) * (t • C)).det = 0 := by exact_mod_cast hsq
    exact (ne_of_gt hpos) this
  constructor
  · simpa [g, complexSkewPencil] using positive_endpoint_of_nonzero g hg hzero hne
  · simpa [complexSkewPencil] using complexSkewPencil_im_zero C hC 1

/-- The literal complex determinant descends to a rational number, rather
than merely having a rational square. -/
theorem det_one_add_I_rational {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℚ) (hC : C.transpose = -C) :
    ∃ q : ℚ, (1 + Complex.I • C.map (Rat.castHom ℂ)).det = (q : ℂ) := by
  let Cc := C.map (Rat.castHom ℂ)
  have hCc : Cc.transpose = -Cc := by
    change (C.map (Rat.castHom ℂ)).transpose = -(C.map (Rat.castHom ℂ))
    rw [← Matrix.transpose_map, hC]
    ext i j
    simp
  obtain ⟨q, hq⟩ := det_one_add_square_rational C hC
  have hmap : (1 + Cc * Cc).det = (q : ℂ) ^ 2 := by
    calc
      (1 + Cc * Cc).det = (Rat.castHom ℂ) (1 + C * C).det := by
        rw [RingHom.map_det]
        change (1 + Cc * Cc).det = ((Rat.castHom ℂ).mapMatrix (1 + C * C)).det
        rw [map_add, map_one, map_mul]
        rfl
      _ = (q : ℂ) ^ 2 := by rw [hq, map_pow]; rfl
  have hs := (det_one_add_square Cc hCc Complex.I Complex.I_mul_I).symm.trans hmap
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with heq | heq
  · exact ⟨q, heq⟩
  · refine ⟨-q, ?_⟩
    simpa only [Rat.cast_neg] using heq

def Tournament.spectralNumerator {d : ℕ} (T : Tournament d) : ℂ :=
  (1 + T.complexNormalizedSign).det

def Tournament.spectralDenominator {d : ℕ} (T : Tournament d) : ℂ :=
  (1 + Complex.I • T.complexNormalizedSign).det

def Tournament.spectralRatio {d : ℕ} (T : Tournament d) : ℂ :=
  T.spectralNumerator / T.spectralDenominator

theorem Tournament.spectralNumerator_positive_rational {d : ℕ} (T : Tournament d) :
    ∃ q : ℚ, 0 < q ∧ T.spectralNumerator = (q : ℂ) := by
  let q := (1 + T.normalizedSign).det
  have hreal : (q : ℝ) = (1 + T.realNormalizedSign).det := by
    change (Rat.castHom ℝ) (1 + T.normalizedSign).det = _
    rw [RingHom.map_det]
    change ((Rat.castHom ℝ).mapMatrix (1 + T.normalizedSign)).det = _
    rw [map_add, map_one]
    rfl
  have hq : 0 < q := by
    have hh : (0 : ℝ) < q := by
      rw [hreal]
      exact det_one_add_real_skew_pos T.realNormalizedSign T.realNormalizedSign_skew
    exact_mod_cast hh
  refine ⟨q, hq, ?_⟩
  symm
  change (Rat.castHom ℂ) (1 + T.normalizedSign).det = _
  rw [RingHom.map_det]
  change ((Rat.castHom ℂ).mapMatrix (1 + T.normalizedSign)).det = _
  rw [map_add, map_one]
  rfl

theorem Tournament.spectralDenominator_positive_rational {d : ℕ} (T : Tournament d)
    (hd : d ≠ 0) :
    ∃ q : ℚ, 0 < q ∧ T.spectralDenominator = (q : ℂ) := by
  obtain ⟨q, hq⟩ := det_one_add_I_rational T.normalizedSign T.normalizedSign_skew
  have hpos : 0 < T.spectralDenominator.re := by
    have hh := (det_one_add_I_real_skew_pos T.realNormalizedSign
      T.realNormalizedSign_skew (T.realNormalizedSign_energy_lt_one hd)).1
    simpa only [Tournament.spectralDenominator, T.complexNormalizedSign_eq_realMap] using hh
  have hq' : T.spectralDenominator = (q : ℂ) := hq
  refine ⟨q, ?_, hq'⟩
  rw [hq'] at hpos
  exact_mod_cast hpos

/-- Wormald's actual spectral determinant quotient is a strictly positive
rational number. This conclusion uses its literal determinant definition. -/
theorem Tournament.spectralRatio_positive_rational {d : ℕ} (T : Tournament d)
    (hd : d ≠ 0) :
    ∃ q : ℚ, 0 < q ∧ T.spectralRatio = (q : ℂ) := by
  obtain ⟨a, ha, hnum⟩ := T.spectralNumerator_positive_rational
  obtain ⟨b, hb, hden⟩ := T.spectralDenominator_positive_rational hd
  refine ⟨a / b, div_pos ha hb, ?_⟩
  rw [Tournament.spectralRatio, hnum, hden, Rat.cast_div]

/-- The literal spectral ratio has the determinant quotient prescribed by
the Hessian formula, including when interpreted over complex scalars. -/
theorem Tournament.spectralRatio_sq {d : ℕ} (T : Tournament d) :
    T.spectralRatio ^ 2 =
      (1 - T.complexNormalizedSign * T.complexNormalizedSign).det /
        (1 + T.complexNormalizedSign * T.complexNormalizedSign).det := by
  unfold Tournament.spectralRatio Tournament.spectralNumerator Tournament.spectralDenominator
  rw [div_pow, ← det_one_sub_square T.complexNormalizedSign T.complexNormalizedSign_skew,
    ← det_one_add_square T.complexNormalizedSign T.complexNormalizedSign_skew
      Complex.I Complex.I_mul_I]

/-- The positive rational spectral ratio is the square root of the actual
finite candidate Hessian quotient. -/
theorem Tournament.spectralRatio_sq_eq_candidate {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    T.spectralRatio ^ 2 = ((n : ℂ) + 1) / (T.candidateHessian.det : ℂ) := by
  let C := T.realNormalizedSign
  let Cc := T.complexNormalizedSign
  have hplus : (((1 + C * C).det : ℝ) : ℂ) = (1 + Cc * Cc).det := by
    change Complex.ofRealHom (1 + C * C).det = _
    rw [RingHom.map_det]
    change (Complex.ofRealHom.mapMatrix (1 + C * C)).det = _
    rw [map_add, map_one, map_mul, ← T.complexNormalizedSign_eq_realMap]
  have hminus : (((1 - C * C).det : ℝ) : ℂ) = (1 - Cc * Cc).det := by
    change Complex.ofRealHom (1 - C * C).det = _
    rw [RingHom.map_det]
    change (Complex.ofRealHom.mapMatrix (1 - C * C)).det = _
    rw [map_sub, map_one, map_mul, ← T.complexNormalizedSign_eq_realMap]
  have hH : (T.candidateHessian.det : ℂ) = ((n : ℂ) + 1) *
      (1 + Cc * Cc).det / (1 - Cc * Cc).det := by
    have hh := congrArg Complex.ofRealHom (T.candidateHessian_det_formula hT)
    simp only [map_div₀, map_mul, map_add, map_natCast, map_one] at hh
    change (T.candidateHessian.det : ℂ) = ((n : ℂ) + 1) *
      (((1 + C * C).det : ℝ) : ℂ) / (((1 - C * C).det : ℝ) : ℂ) at hh
    rw [hplus, hminus] at hh
    exact hh
  have hd : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity)
  have haR : (1 + C * C).det ≠ 0 :=
    ne_of_gt (T.posDef_one_add_realNormalizedSign_square (Nat.succ_ne_zero n)).det_pos
  have hbR : (1 - C * C).det ≠ 0 :=
    ne_of_gt (posDef_one_sub_square C T.realNormalizedSign_skew).det_pos
  have ha : (1 + Cc * Cc).det ≠ 0 := by
    rw [← hplus]
    exact_mod_cast haR
  have hb : (1 - Cc * Cc).det ≠ 0 := by
    rw [← hminus]
    exact_mod_cast hbR
  rw [T.spectralRatio_sq, hH]
  change (1 - Cc * Cc).det / (1 + Cc * Cc).det = _
  field_simp

theorem Tournament.spectralRatio_re_sqrt_candidate {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    T.spectralRatio.re = Real.sqrt (((n : ℝ) + 1) / T.candidateHessian.det) := by
  obtain ⟨q, hq, heq⟩ := T.spectralRatio_positive_rational (Nat.succ_ne_zero n)
  have hsq := T.spectralRatio_sq_eq_candidate hT
  rw [heq] at hsq
  have hreal : (q : ℝ) ^ 2 = ((n : ℝ) + 1) / T.candidateHessian.det := by
    exact_mod_cast hsq
  rw [heq]
  simp only [Complex.ratCast_re]
  rw [← hreal, Real.sqrt_sq_eq_abs, abs_of_pos (show (0 : ℝ) < q by exact_mod_cast hq)]

end
end Wormald

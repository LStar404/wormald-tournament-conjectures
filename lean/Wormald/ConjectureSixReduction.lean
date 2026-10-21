import Wormald.RegularCandidate
import Wormald.AnalyticTarget

/-!
# The finite conclusion and analytic reduction for Conjecture 6

All finite positivity and rational-square conclusions below are proved for the
actual regular tournament matrix. The only premise of the final reduction is
the precise original-analytic-Hessian = candidate-matrix equality. That premise
is stated as a proposition, not introduced as an axiom or proved by a placeholder.
The following module `ConjectureSixProof` proves that premise and the original
unconditional conjecture from the actual analytic definitions.
-/

namespace Wormald

noncomputable section

open Matrix

private theorem real_det_transport {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℚ) (s : ℚ) :
    (((1 + s • (C * C)).det : ℚ) : ℝ) =
      (1 + (s : ℝ) • (C.map (Rat.castHom ℝ) * C.map (Rat.castHom ℝ))).det := by
  change (Rat.castHom ℝ) (1 + s • (C * C)).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;>
    simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, h]

/-- The complete rational-square conclusion for the finite candidate Hessian. -/
theorem Tournament.candidateHessian_rational_square {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    ∃ q : ℚ, ((n : ℝ) + 1) / T.candidateHessian.det = (q : ℝ) ^ 2 := by
  have hskew : T.normalizedSign.transpose = -T.normalizedSign := by
    ext i j
    change T.sign j i / ((n + 1 : ℕ) : ℚ) = -(T.sign i j / ((n + 1 : ℕ) : ℚ))
    have h := congrFun (congrFun T.sign_skew i) j
    change T.sign j i = -T.sign i j at h
    rw [h, neg_div]
  obtain ⟨q, hq⟩ := det_quotient_rational_square T.normalizedSign hskew
  have hc : T.normalizedSign.map (Rat.castHom ℝ) = T.realNormalizedSign := by
    ext i j
    rfl
  have hp : (((1 + T.normalizedSign * T.normalizedSign).det : ℚ) : ℝ) =
      (1 + T.realNormalizedSign * T.realNormalizedSign).det := by
    simpa only [Rat.cast_one, one_smul, hc] using real_det_transport T.normalizedSign 1
  have hm : (((1 - T.normalizedSign * T.normalizedSign).det : ℚ) : ℝ) =
      (1 - T.realNormalizedSign * T.realNormalizedSign).det := by
    simpa only [Rat.cast_neg, Rat.cast_one, neg_one_smul, sub_eq_add_neg, hc] using
      real_det_transport T.normalizedSign (-1)
  have hqr : (1 - T.realNormalizedSign * T.realNormalizedSign).det /
      (1 + T.realNormalizedSign * T.realNormalizedSign).det = (q : ℝ) ^ 2 := by
    have h := congrArg (Rat.castHom ℝ) hq
    simp only [map_div₀, map_pow] at h
    change (((1 - T.normalizedSign * T.normalizedSign).det : ℚ) : ℝ) /
      (((1 + T.normalizedSign * T.normalizedSign).det : ℚ) : ℝ) = (q : ℝ) ^ 2 at h
    rw [hp, hm] at h
    exact h
  refine ⟨q, ?_⟩
  have hd : (n : ℝ) + 1 ≠ 0 := by positivity
  have ha : (1 + T.realNormalizedSign * T.realNormalizedSign).det ≠ 0 :=
    ne_of_gt (T.posDef_one_add_realNormalizedSign_square (Nat.succ_ne_zero n)).det_pos
  have hb : (1 - T.realNormalizedSign * T.realNormalizedSign).det ≠ 0 :=
    ne_of_gt (posDef_one_sub_square T.realNormalizedSign T.realNormalizedSign_skew).det_pos
  calc
    ((n : ℝ) + 1) / T.candidateHessian.det =
        (1 - T.realNormalizedSign * T.realNormalizedSign).det /
          (1 + T.realNormalizedSign * T.realNormalizedSign).det := by
      rw [T.candidateHessian_det_formula hT]
      field_simp
    _ = (q : ℝ) ^ 2 := hqr

/-- The analytic equality for exactly the original angular function. This Prop
is proved by `analyticCandidateCorrespondence` in `ConjectureSixProof`. -/
def AnalyticCandidateCorrespondence : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (T : Tournament (n + 1)), T.Regular →
    originalAngularHessian T = (Complex.ofRealHom.mapMatrix T.candidateHessian)

/-- Once the original analytic correspondence is proved, every remaining
conclusion in Wormald's original Conjecture 6 follows from the checked finite core.
The hypothesis is discharged in `ConjectureSixProof`. -/
theorem conjectureSix_of_analytic_correspondence
    (hbridge : AnalyticCandidateCorrespondence) : ConjectureSix := by
  intro n hn T hT
  have hdet : (originalAngularHessian T).det = (T.candidateHessian.det : ℂ) := by
    rw [hbridge n hn T hT]
    exact (Complex.ofRealHom.map_det T.candidateHessian).symm
  constructor
  · rw [hdet]
    exact_mod_cast ne_of_gt T.candidateHessian_det_pos
  · obtain ⟨q, hq⟩ := T.candidateHessian_rational_square hT
    refine ⟨q, ?_⟩
    rw [hdet]
    exact_mod_cast hq

end
end Wormald

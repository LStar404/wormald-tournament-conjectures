import Wormald.JetToCandidate

/-! Centering the actual second logarithmic polynomial jet removes its
one-coordinate terms. The remaining bilinear form is exactly the resolvent
core minus the constant projection. -/

namespace Wormald
noncomputable section
open scoped BigOperators
open Matrix

def centeredBasis {d : ℕ} (j : Fin d) : Fin d → ℂ :=
  fun a => (if a = j then 1 else 0) - 1 / (d : ℂ)

theorem sum_mul_centeredBasis {d : ℕ} (f : Fin d → ℂ) (j : Fin d) :
    (∑ a, f a * centeredBasis j a) = f j - (∑ a, f a) / (d : ℂ) := by
  simp [centeredBasis, mul_sub, Finset.sum_sub_distrib, mul_ite,
    div_eq_mul_inv, ← Finset.sum_mul]

theorem sum_centeredBasis {d : ℕ} (hd : d ≠ 0) (j : Fin d) :
    (∑ a, centeredBasis j a) = 0 := by
  have h := sum_mul_centeredBasis (fun _ : Fin d => 1) j
  simpa [hd] using h

theorem centeredBasis_bilinear {d : ℕ} (hd : d ≠ 0)
    (Q : Matrix (Fin d) (Fin d) ℂ)
    (hrow : ∀ a, ∑ b, Q a b = 1) (hcol : ∀ b, ∑ a, Q a b = 1)
    (j k : Fin d) :
    (∑ a, (∑ b, Q a b * centeredBasis k b) * centeredBasis j a) =
      Q j k - 1 / (d : ℂ) := by
  simp_rw [sum_mul_centeredBasis, hrow]
  simp only [Finset.sum_sub_distrib, hcol, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  field_simp
  ring

private theorem zero_sum_bilinear_rank_terms {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℂ) (r p q : Fin d → ℂ)
    (hp : ∑ a, p a = 0) (hq : ∑ a, q a = 0) :
    (∑ a, (∑ b, (r a + r b - 2 - Q a b) * p b) * q a) =
      -(∑ a, (∑ b, Q a b * p b) * q a) := by
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hp, hq, mul_zero,
    zero_add, zero_sub, sub_zero]

def Tournament.complexResolventCore {d : ℕ} (T : Tournament d) :
    Matrix (Fin d) (Fin d) ℂ := T.criticalResolvent + T.criticalResolvent.transpose - 1

theorem Tournament.complexResolventCore_row_sum {d : ℕ} (T : Tournament d)
    (hT : T.Regular) (_hd : d ≠ 0) (i : Fin d) :
    (∑ j, T.complexResolventCore i j) = 1 := by
  have hr : ∀ i, ∑ j, T.criticalResolvent i j = 1 := by
    intro i
    simpa [Matrix.mulVec, dotProduct] using congrFun (T.criticalResolvent_mulVec_one hT) i
  have hc : ∀ j, ∑ i, T.criticalResolvent i j = 1 := by
    intro j
    simpa [Matrix.vecMul, dotProduct] using congrFun (T.one_vecMul_criticalResolvent hT) j
  simp [Tournament.complexResolventCore, Matrix.add_apply, Matrix.sub_apply,
    Matrix.transpose_apply, Matrix.one_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hr, hc]

theorem Tournament.complexResolventCore_col_sum {d : ℕ} (T : Tournament d)
    (hT : T.Regular) (hd : d ≠ 0) (j : Fin d) :
    (∑ i, T.complexResolventCore i j) = 1 := by
  have hsym : T.complexResolventCore.transpose = T.complexResolventCore := by
    simp [Tournament.complexResolventCore, add_comm]
  have h := T.complexResolventCore_row_sum hT hd j
  have he : ∀ i, T.complexResolventCore i j = T.complexResolventCore j i := by
    intro i
    exact congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M j i) hsym
  simpa only [he] using h

/-- The genuine polynomial second jet on centered phase directions equals
the covariance kernel, including its normalization by the vertex count. -/
theorem Tournament.secondLogJet_centered {d : ℕ} (T : Tournament d)
    (hT : T.Regular) (hd : d ≠ 0) (j k : Fin d) :
    (∑ a, (∑ b, (secondLogJet (definingPolynomial T.adjacency) (2 / (d : ℚ)) a b : ℂ) *
      (Complex.I * centeredBasis k b)) * (Complex.I * centeredBasis j a)) =
      T.criticalDet / (d : ℂ) * (T.complexResolventCore j k - 1 / (d : ℂ)) := by
  have hp : (∑ a, Complex.I * centeredBasis k a) = 0 := by
    rw [← Finset.mul_sum, sum_centeredBasis hd k, mul_zero]
  have hq : (∑ a, Complex.I * centeredBasis j a) = 0 := by
    rw [← Finset.mul_sum, sum_centeredBasis hd j, mul_zero]
  have hentry : ∀ a b,
      (secondLogJet (definingPolynomial T.adjacency) (2 / (d : ℚ)) a b : ℂ) =
      T.criticalDet / (d : ℂ) * (T.criticalResolvent a a + T.criticalResolvent b b -
        2 - T.complexResolventCore a b) := by
    intro a b
    rw [secondLogJet_cast_critical T hT hd]
    simp only [Tournament.complexResolventCore, Matrix.add_apply, Matrix.sub_apply,
      Matrix.transpose_apply, Matrix.one_apply]
    ring
  simp_rw [hentry]
  have hfactor : (∑ a, (∑ b, T.criticalDet / (d : ℂ) *
      (T.criticalResolvent a a + T.criticalResolvent b b - 2 - T.complexResolventCore a b) *
      (Complex.I * centeredBasis k b)) * (Complex.I * centeredBasis j a)) =
      T.criticalDet / (d : ℂ) *
      (∑ a, (∑ b, (T.criticalResolvent a a + T.criticalResolvent b b - 2 -
        T.complexResolventCore a b) * (Complex.I * centeredBasis k b)) *
          (Complex.I * centeredBasis j a)) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hfactor, zero_sum_bilinear_rank_terms _ (fun a => T.criticalResolvent a a) _ _ hp hq]
  have hI : -(∑ a, (∑ b, T.complexResolventCore a b * (Complex.I * centeredBasis k b)) *
      (Complex.I * centeredBasis j a)) =
      ∑ a, (∑ b, T.complexResolventCore a b * centeredBasis k b) * centeredBasis j a := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    have hsq := Complex.I_sq
    linear_combination -T.complexResolventCore a b * centeredBasis k b * centeredBasis j a * hsq
  rw [hI, centeredBasis_bilinear hd _
    (T.complexResolventCore_row_sum hT hd) (T.complexResolventCore_col_sum hT hd)]

end
end Wormald

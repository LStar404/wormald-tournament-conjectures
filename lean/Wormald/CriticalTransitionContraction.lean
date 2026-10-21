import Wormald.CriticalPoint

namespace Wormald

noncomputable section
open Matrix Finset

/-- The actual Euclidean squared energy on finite complex vectors. -/
def complexEnergy {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

theorem complexEnergy_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ complexEnergy x :=
  Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (x i))

theorem complexEnergy_eq_zero_iff {n : ℕ} (x : Fin n → ℂ) :
    complexEnergy x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    exact Complex.normSq_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (x j))).mp h i (by simp))
  · intro h
    simp [complexEnergy, h]

theorem complexEnergy_pos {n : ℕ} (x : Fin n → ℂ) (hx : x ≠ 0) : 0 < complexEnergy x :=
  lt_of_le_of_ne (complexEnergy_nonneg x) (Ne.symm (fun h => hx ((complexEnergy_eq_zero_iff x).mp h)))

theorem complexEnergy_eq_re_im {n : ℕ} (x : Fin n → ℂ) :
    complexEnergy x = (∑ i, (x i).re ^ 2) + ∑ i, (x i).im ^ 2 := by
  simp [complexEnergy, Complex.normSq_apply, pow_two, Finset.sum_add_distrib]

theorem Tournament.complexNormalizedSign_mulVec_re {n : ℕ} (T : Tournament n) (x : Fin n → ℂ) :
    (fun i => ((T.complexNormalizedSign *ᵥ x) i).re) =
      T.realNormalizedSign *ᵥ (fun i => (x i).re) := by
  funext i
  change (∑ j, (T.normalizedSign i j : ℂ) * x j).re = _
  simp [Tournament.realNormalizedSign, Matrix.mulVec, dotProduct, Complex.mul_re]

theorem Tournament.complexNormalizedSign_mulVec_im {n : ℕ} (T : Tournament n) (x : Fin n → ℂ) :
    (fun i => ((T.complexNormalizedSign *ᵥ x) i).im) =
      T.realNormalizedSign *ᵥ (fun i => (x i).im) := by
  funext i
  change (∑ j, (T.normalizedSign i j : ℂ) * x j).im = _
  simp [Tournament.realNormalizedSign, Matrix.mulVec, dotProduct, Complex.mul_im]

/-- The real Frobenius estimate applies to both real and imaginary parts. -/
theorem Tournament.complexNormalizedSign_energy_le {n : ℕ} (T : Tournament n) (x : Fin n → ℂ) :
    complexEnergy (T.complexNormalizedSign *ᵥ x) ≤
      (∑ i, ∑ j, T.realNormalizedSign i j ^ 2) * complexEnergy x := by
  have hR := mulVec_square_le_frobenius T.realNormalizedSign (fun i => (x i).re)
  have hI := mulVec_square_le_frobenius T.realNormalizedSign (fun i => (x i).im)
  simp only [dotProduct, ← pow_two] at hR hI
  rw [complexEnergy_eq_re_im, complexEnergy_eq_re_im]
  change (∑ i, (fun k => (T.complexNormalizedSign *ᵥ x) k |>.re) i ^ 2) +
      (∑ i, (fun k => (T.complexNormalizedSign *ᵥ x) k |>.im) i ^ 2) ≤ _
  rw [T.complexNormalizedSign_mulVec_re, T.complexNormalizedSign_mulVec_im]
  nlinarith

theorem Tournament.complexNormalizedSign_energy_lt {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (x : Fin n → ℂ) (hx : x ≠ 0) :
    complexEnergy (T.complexNormalizedSign *ᵥ x) < complexEnergy x := by
  have hF := T.realNormalizedSign_energy_lt_one hn
  have hxpos := complexEnergy_pos x hx
  exact (T.complexNormalizedSign_energy_le x).trans_lt (by nlinarith)

theorem Tournament.constantProjection_mulVec {n : ℕ} (T : Tournament n) (x : Fin n → ℂ) :
    T.constantProjection *ᵥ x = (fun _ => (1 / (n : ℂ)) * ∑ j, x j) := by
  funext i
  simp [Tournament.constantProjection, Matrix.mulVec, dotProduct, ← Finset.mul_sum]

theorem Tournament.criticalTransition_mulVec_of_sum_eq_zero {n : ℕ} (T : Tournament n)
    (x : Fin n → ℂ) (hx : ∑ i, x i = 0) :
    T.criticalTransition *ᵥ x = T.complexNormalizedSign *ᵥ x := by
  rw [Tournament.criticalTransition, Matrix.add_mulVec, T.constantProjection_mulVec, hx]
  have hz : (fun _ : Fin n => (0 : ℂ)) = 0 := rfl
  simp only [mul_zero, hz, zero_add]

/-- A genuine strict spectral gap on the constant-orthogonal subspace, derived
from the actual tournament energy. No contraction assumption is introduced. -/
theorem Tournament.criticalTransition_energy_lt_of_sum_eq_zero {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) (x : Fin n → ℂ)
    (hsum : ∑ i, x i = 0) (hx : x ≠ 0) :
    complexEnergy (T.criticalTransition *ᵥ x) < complexEnergy x := by
  rw [T.criticalTransition_mulVec_of_sum_eq_zero x hsum]
  exact T.complexNormalizedSign_energy_lt hn x hx

end
end Wormald

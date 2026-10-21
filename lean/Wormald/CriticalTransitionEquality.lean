import Wormald.CriticalTransitionContraction

namespace Wormald

noncomputable section
open Matrix Finset

theorem complexEnergy_const_add {n : ℕ} (a : ℂ) (x : Fin n → ℂ)
    (hsum : ∑ i, x i = 0) :
    complexEnergy (fun i => a + x i) = (n : ℝ) * Complex.normSq a + complexEnergy x := by
  have hR : (∑ i, (x i).re) = 0 := by simpa using congrArg Complex.re hsum
  have hI : (∑ i, (x i).im) = 0 := by simpa using congrArg Complex.im hsum
  have hcross : (∑ i, (a * (starRingEnd ℂ) (x i)).re) = 0 := by
    change (∑ i, (a * star (x i)).re) = 0
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
      mul_neg, sub_neg_eq_add, Finset.sum_add_distrib, ← Finset.mul_sum, hR, hI,
      mul_zero, zero_add]
  simp only [complexEnergy, Complex.normSq_add, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, hcross, mul_zero, add_zero]

def complexMean {n : ℕ} (x : Fin n → ℂ) : ℂ := (∑ i, x i) / (n : ℂ)
def complexCentered {n : ℕ} (x : Fin n → ℂ) : Fin n → ℂ := fun i => x i - complexMean x

theorem complexCentered_sum {n : ℕ} (hn : n ≠ 0) (x : Fin n → ℂ) :
    (∑ i, complexCentered x i) = 0 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [complexCentered, complexMean, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem complexMean_repr {n : ℕ} (x : Fin n → ℂ) :
    x = (fun _ => complexMean x) + complexCentered x := by
  funext i
  simp [complexCentered]

theorem Tournament.complexNormalizedSign_mulVec_const {n : ℕ} (T : Tournament n)
    (hT : T.Regular) (a : ℂ) : T.complexNormalizedSign *ᵥ (fun _ => a) = 0 := by
  have hconst : (fun _ : Fin n => a) = a • (fun _ => (1 : ℂ)) := by funext i; simp
  rw [hconst, Matrix.mulVec_smul, T.complexNormalizedSign_mulVec_one hT, smul_zero]

theorem Tournament.criticalTransition_mulVec_const {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (a : ℂ) :
    T.criticalTransition *ᵥ (fun _ => a) = (fun _ => a) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Tournament.criticalTransition, Matrix.add_mulVec,
    T.complexNormalizedSign_mulVec_const hT, add_zero, T.constantProjection_mulVec]
  funext i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem Tournament.sum_complexNormalizedSign_mulVec {n : ℕ} (T : Tournament n)
    (hT : T.Regular) (x : Fin n → ℂ) :
    (∑ i, (T.complexNormalizedSign *ᵥ x) i) = 0 := by
  have hcol : ∀ j, ∑ i, T.complexNormalizedSign i j = 0 := by
    intro j
    have h := congrFun (T.one_vecMul_complexNormalizedSign hT) j
    simpa [Matrix.vecMul, dotProduct] using h
  change (∑ i, ∑ j, T.complexNormalizedSign i j * x j) = 0
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcol, zero_mul]
  simp

theorem Tournament.criticalTransition_mean_decomposition {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (x : Fin n → ℂ) :
    T.criticalTransition *ᵥ x =
      (fun _ => complexMean x) + T.complexNormalizedSign *ᵥ complexCentered x := by
  calc
    _ = T.criticalTransition *ᵥ ((fun _ => complexMean x) + complexCentered x) :=
      congrArg (fun y => T.criticalTransition *ᵥ y) (complexMean_repr x)
    _ = _ := by
      rw [Matrix.mulVec_add, T.criticalTransition_mulVec_const hn hT,
        T.criticalTransition_mulVec_of_sum_eq_zero _ (complexCentered_sum hn x)]

theorem Tournament.criticalTransition_energy_decomposition {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (x : Fin n → ℂ) :
    complexEnergy x = (n : ℝ) * Complex.normSq (complexMean x) + complexEnergy (complexCentered x) ∧
    complexEnergy (T.criticalTransition *ᵥ x) = (n : ℝ) * Complex.normSq (complexMean x) +
      complexEnergy (T.complexNormalizedSign *ᵥ complexCentered x) := by
  constructor
  · calc
      _ = complexEnergy ((fun _ => complexMean x) + complexCentered x) :=
        congrArg complexEnergy (complexMean_repr x)
      _ = _ := complexEnergy_const_add _ _ (complexCentered_sum hn x)
  · rw [T.criticalTransition_mean_decomposition hn hT x]
    exact complexEnergy_const_add _ _ (T.sum_complexNormalizedSign_mulVec hT _)

/-- The actual critical transition never increases Euclidean energy. -/
theorem Tournament.criticalTransition_energy_le {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (x : Fin n → ℂ) :
    complexEnergy (T.criticalTransition *ᵥ x) ≤ complexEnergy x := by
  have hdecomp := T.criticalTransition_energy_decomposition hn hT x
  have hC : complexEnergy (T.complexNormalizedSign *ᵥ complexCentered x) ≤ complexEnergy (complexCentered x) := by
    by_cases hx : complexCentered x = 0
    · simp [hx, complexEnergy]
    · exact (T.complexNormalizedSign_energy_lt hn _ hx).le
  linarith [hdecomp.1, hdecomp.2]

theorem Tournament.criticalTransition_energy_lt_of_not_constant {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (x : Fin n → ℂ)
    (hx : ¬∃ a : ℂ, x = fun _ => a) :
    complexEnergy (T.criticalTransition *ᵥ x) < complexEnergy x := by
  have hcenter : complexCentered x ≠ 0 := by
    intro h
    apply hx
    exact ⟨complexMean x, by simpa only [h, add_zero] using complexMean_repr x⟩
  have hdecomp := T.criticalTransition_energy_decomposition hn hT x
  have hC := T.complexNormalizedSign_energy_lt hn _ hcenter
  linarith [hdecomp.1, hdecomp.2]

/-- Equality occurs precisely in the constant direction. -/
theorem Tournament.criticalTransition_energy_eq_iff_constant {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (x : Fin n → ℂ) :
    complexEnergy (T.criticalTransition *ᵥ x) = complexEnergy x ↔ ∃ a : ℂ, x = fun _ => a := by
  constructor
  · intro heq
    by_contra h
    exact (ne_of_lt (T.criticalTransition_energy_lt_of_not_constant hn hT x h)) heq
  · rintro ⟨a, rfl⟩
    rw [T.criticalTransition_mulVec_const hn hT a]

end
end Wormald

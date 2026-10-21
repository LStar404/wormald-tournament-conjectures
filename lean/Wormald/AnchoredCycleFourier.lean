import Wormald.ExactCycleFourier

namespace Wormald

noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The last torus coordinate is exactly zero. -/
def anchoredTorus {d : ℕ} (x : UnitAddTorus (Fin d)) : UnitAddTorus (Fin (d + 1)) :=
  Fin.snoc x 0

def anchoredFourierPhase {d : ℕ} (x : UnitAddTorus (Fin d)) : Fin (d + 1) → ℂ :=
  fun i => fourier 1 (anchoredTorus x i)

@[simp] theorem anchoredFourierPhase_last {d : ℕ} (x : UnitAddTorus (Fin d)) :
    anchoredFourierPhase x (Fin.last d) = 1 := by
  simp [anchoredFourierPhase, anchoredTorus]

@[simp] theorem anchoredFourierPhase_castSucc {d : ℕ} (x : UnitAddTorus (Fin d)) (i : Fin d) :
    anchoredFourierPhase x i.castSucc = fourier 1 (x i) := by
  simp [anchoredFourierPhase, anchoredTorus]

theorem anchored_polynomial_monomial {d : ℕ} (s : Fin (d + 1) →₀ ℕ)
    (a : ℂ) (x : UnitAddTorus (Fin d)) :
    MvPolynomial.eval (anchoredFourierPhase x) (MvPolynomial.monomial s a) =
      a * UnitAddTorus.mFourier (fun i : Fin d => (s i.castSucc : ℤ)) x := by
  have h := polynomialTorusEval_monomial s a (anchoredTorus x)
  change MvPolynomial.eval (anchoredFourierPhase x) (MvPolynomial.monomial s a) = _ at h
  rw [h]
  congr 1
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [Fin.prod_univ_castSucc]
  simp [anchoredTorus]

namespace FiniteModel

theorem anchored_eval₂_monomial {d : ℕ} (s : Fin (d + 1) →₀ ℕ)
    (a : ℝ) (x : UnitAddTorus (Fin d)) :
    MvPolynomial.eval₂ Complex.ofRealHom (anchoredFourierPhase x) (MvPolynomial.monomial s a) =
      (a : ℂ) * UnitAddTorus.mFourier (fun i : Fin d => (s i.castSucc : ℤ)) x := by
  rw [MvPolynomial.eval₂_monomial]
  change (a : ℂ) * s.prod (fun i e => anchoredFourierPhase x i ^ e) = _
  simpa only [MvPolynomial.eval_monomial] using anchored_polynomial_monomial s (a : ℂ) x

theorem wordMultiplicity_sum {d N : ℕ} (f : Fin N → Fin d) :
    (∑ i : Fin d, wordMultiplicity f i) = N := by
  simp only [wordMultiplicity, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp

/-- At total length (d+1)m, balancing the first d coordinates forces the last
coordinate to have the same count. This is the exact reason one phase is redundant. -/
theorem wordMultiplicity_castSucc_eq_iff_balanced {d m : ℕ}
    (f : Fin ((d + 1) * m) → Fin (d + 1)) :
    (∀ i : Fin d, wordMultiplicity f i.castSucc = m) ↔ BalancedBaseWord m f := by
  constructor
  · intro hfirst
    have htotal := wordMultiplicity_sum f
    rw [Fin.sum_univ_castSucc] at htotal
    simp only [hfirst, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_id, Nat.add_mul, Nat.one_mul] at htotal
    have hlast : wordMultiplicity f (Fin.last d) = m := by omega
    intro i
    rw [← wordMultiplicity_apply]
    exact Fin.lastCases hlast (fun j => hfirst j) i
  · intro h i
    rw [wordMultiplicity_apply]
    exact h i.castSucc

theorem integral_anchored_word_character {d m : ℕ}
    (f : Fin ((d + 1) * m) → Fin (d + 1)) :
    (∫ x : UnitAddTorus (Fin d),
      UnitAddTorus.mFourier (fun _ => -(m : ℤ)) x *
        UnitAddTorus.mFourier (fun i => (wordMultiplicity f i.castSucc : ℤ)) x) =
      if BalancedBaseWord m f then 1 else 0 := by
  have h := integral_mFourier_mul (fun _ : Fin d => (m : ℤ))
    (fun i : Fin d => (wordMultiplicity f i.castSucc : ℤ))
  change (∫ x : UnitAddTorus (Fin d),
      UnitAddTorus.mFourier (fun _ => -(m : ℤ)) x *
        UnitAddTorus.mFourier (fun i => (wordMultiplicity f i.castSucc : ℤ)) x) = _ at h
  rw [h]
  have hiff : ((fun _ : Fin d => (m : ℤ)) =
      (fun i : Fin d => (wordMultiplicity f i.castSucc : ℤ))) ↔ BalancedBaseWord m f := by
    rw [← wordMultiplicity_castSucc_eq_iff_balanced]
    constructor
    · intro h i
      exact_mod_cast (congrFun h i).symm
    · intro h
      funext i
      exact_mod_cast (h i).symm
  simp only [hiff]

theorem trace_anchored_phase_eq_word_characters {d m : ℕ}
    (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hN : 0 < (d + 1) * m)
    (x : UnitAddTorus (Fin d)) :
    ((B.map Complex.ofRealHom * Matrix.diagonal (anchoredFourierPhase x)) ^ ((d + 1) * m)).trace =
      ∑ f : Fin ((d + 1) * m) → Fin (d + 1), ((cyclicWordWeight B f : ℝ) : ℂ) *
        UnitAddTorus.mFourier (fun i => (wordMultiplicity f i.castSucc : ℤ)) x := by
  rw [← eval₂_trace_variableMatrix_pow, trace_variableMatrix_pow_eq B hN, MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro f hf
  exact anchored_eval₂_monomial _ _ x

/-- Exact balanced-word extraction in d coordinates for a matrix on d+1
vertices. The fixed total length forces the omitted occupation count. -/
theorem integral_anchored_trace_eq_balancedWordSum {d m : ℕ}
    (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hN : 0 < (d + 1) * m) :
    (∫ x : UnitAddTorus (Fin d), UnitAddTorus.mFourier (fun _ => -(m : ℤ)) x *
      ((B.map Complex.ofRealHom * Matrix.diagonal (anchoredFourierPhase x)) ^ ((d + 1) * m)).trace) =
      ((balancedCycleWordSum (N := (d + 1) * m) B m : ℝ) : ℂ) := by
  let g := fun (f : Fin ((d + 1) * m) → Fin (d + 1)) (x : UnitAddTorus (Fin d)) =>
    ((cyclicWordWeight B f : ℝ) : ℂ) * (UnitAddTorus.mFourier (fun _ => -(m : ℤ)) x *
      UnitAddTorus.mFourier (fun i => (wordMultiplicity f i.castSucc : ℤ)) x)
  have hg : ∀ f, Integrable (g f) := by
    intro f
    exact (continuous_const.mul ((UnitAddTorus.mFourier _).continuous.mul
      (UnitAddTorus.mFourier _).continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ x : UnitAddTorus (Fin d), ∑ f, g f x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [trace_anchored_phase_eq_word_characters B hN x, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f hf
        dsimp [g]
        ring)
    _ = ∑ f, ∫ x : UnitAddTorus (Fin d), g f x := integral_finsetSum _ (fun f _ => hg f)
    _ = ∑ f : Fin ((d + 1) * m) → Fin (d + 1),
        if BalancedBaseWord m f then ((cyclicWordWeight B f : ℝ) : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      dsimp [g]
      rw [integral_const_mul, integral_anchored_word_character]
      split_ifs <;> simp
    _ = _ := by
      simp only [balancedCycleWordSum, Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro f hf
      split_ifs <;> simp

/-- The original normalized independent Hamilton-cycle expectation is exactly
the anchored (one-fewer-dimensional) Fourier integral. -/
theorem normalizedExpectedCycles_eq_anchoredFourierIntegral {d : ℕ}
    (base : Orientation (d + 1)) (m : ℕ) (hN : 3 ≤ (d + 1) * m) :
    (normalizedExpectedCycles base m : ℂ) = (factorialPrefactor (d + 1) m : ℂ) *
      ∫ x : UnitAddTorus (Fin d), UnitAddTorus.mFourier (fun _ => -(m : ℤ)) x *
        (((markovBase base).map Complex.ofRealHom *
          Matrix.diagonal (anchoredFourierPhase x)) ^ ((d + 1) * m)).trace := by
  rw [normalizedExpectedCycles_eq_markovWordSum base m hN, Complex.ofReal_mul,
    integral_anchored_trace_eq_balancedWordSum _ (by omega)]
  congr 2
  simp only [Fintype.card_prod, Fintype.card_fin]

end FiniteModel
end
end Wormald


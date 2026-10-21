import Wormald.CycleWordTransfer
import Wormald.MeanPermanentDegree
import Wormald.FactorialPrefactor
import Wormald.ConjectureOneReduction

/-! The exact independent mean in Markov occupation normalization.
For regular bases the normalized weighted base is a genuine stochastic matrix.
All identities below are finite; no local limit theorem is assumed. -/

namespace Wormald.FiniteModel
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cyclicWordWeight_smul {d N : ℕ} {R : Type*} [CommSemiring R]
    (c : R) (B : Matrix (Fin d) (Fin d) R) (f : Fin N → Fin d) :
    cyclicWordWeight (c • B) f = c ^ N * cyclicWordWeight B f := by
  simp only [cyclicWordWeight, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem balancedCycleWordSum_smul {d N : ℕ} {R : Type*} [CommSemiring R]
    (c : R) (B : Matrix (Fin d) (Fin d) R) (m : ℕ) :
    balancedCycleWordSum (N := N) (c • B) m = c ^ N * balancedCycleWordSum (N := N) B m := by
  simp only [balancedCycleWordSum, cyclicWordWeight_smul, Finset.mul_sum, mul_ite, mul_zero]

def markovBase {d : ℕ} (base : Orientation d) : Matrix (Fin d) (Fin d) ℝ :=
  (2 / (d : ℝ)) • weightedBase base

theorem markovBase_nonneg {d : ℕ} (base : Orientation d) :
    ∀ i j, 0 ≤ markovBase base i j := by
  intro i j
  exact mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg d)) (weightedBase_nonneg base i j)

theorem weightedBase_eq_smul_markovBase {d : ℕ} (base : Orientation d) (hd : d ≠ 0) :
    weightedBase base = ((d : ℝ) / 2) • markovBase base := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  ext i j
  simp only [markovBase, Matrix.smul_apply, smul_eq_mul]
  field_simp

theorem markovBase_rowSum {d : ℕ} (base : Orientation d) (hd : d ≠ 0)
    (hregular : (toTournament base).Regular) (i : Fin d) :
    (∑ j, markovBase base i j) = 1 := by
  have hdeg : (toTournament base).degreeFactor i = 1 :=
    ((toTournament base).degreeFactor_eq_one_iff hd).mpr hregular i
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  simp only [markovBase, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [weightedBase_rowSum_eq_degreeFactor base hd, hdeg]
  field_simp

theorem weightedBase_add_reverse {d : ℕ} (base : Orientation d) (i j : Fin d) :
    weightedBase base i j + weightedBase base j i = 1 := by
  by_cases hij : i = j
  · subst j
    norm_num [weightedBase]
  · simp only [weightedBase, ite_eq_right hij, ite_eq_right (Ne.symm hij),
      arc_reverse base i j hij]
    cases arc base j i <;> norm_num

theorem markovBase_add_reverse {d : ℕ} (base : Orientation d) (i j : Fin d) :
    markovBase base i j + markovBase base j i = 2 / (d : ℝ) := by
  simp only [markovBase, Matrix.smul_apply, smul_eq_mul]
  rw [← mul_add, weightedBase_add_reverse, mul_one]

theorem markovBase_colSum {d : ℕ} (base : Orientation d) (hd : d ≠ 0)
    (hregular : (toTournament base).Regular) (i : Fin d) :
    (∑ j, markovBase base j i) = 1 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hsum : (∑ j, (markovBase base i j + markovBase base j i)) = 2 := by
    simp only [markovBase_add_reverse, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [Finset.sum_add_distrib, markovBase_rowSum base hd hregular i] at hsum
  linarith

theorem markovBase_self {d : ℕ} (base : Orientation d) (i : Fin d) :
    markovBase base i i = 1 / (d : ℝ) := by
  simp only [markovBase, Matrix.smul_apply, smul_eq_mul, weightedBase,
    ite_true]
  ring

/-- An exact finite identity: the actual normalized independent expectation
is a Stirling prefactor times a balanced cyclic occupation sum. -/
theorem normalizedExpectedCycles_eq_markovWordSum {d : ℕ} (base : Orientation d)
    (m : ℕ) (hN : 3 ≤ d * m) :
    normalizedExpectedCycles base m = factorialPrefactor d m *
      balancedCycleWordSum (N := Fintype.card (Fin d × Fin m)) (markovBase base) m := by
  have hd : d ≠ 0 := by
    intro h
    simp [h] at hN
  have hNne : d * m ≠ 0 := by omega
  have hfac : ((d * m : ℕ) : ℝ) * (Nat.factorial (d * m - 1) : ℝ) =
      (Nat.factorial (d * m) : ℝ) := by
    exact_mod_cast Nat.mul_factorial_pred hNne
  have hNreal : ((d * m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hNne
  have hpredfac : (Nat.factorial (d * m - 1) : ℝ) ≠ 0 := by positivity
  have hNfac : (Nat.factorial (d * m) : ℝ) ≠ 0 := by positivity
  have htwo : (2 : ℝ) ^ (d * m) ≠ 0 := by positivity
  unfold normalizedExpectedCycles
  rw [expectedCycles_eq_balancedCycleWordSum base m hN,
    weightedBase_eq_smul_markovBase base hd, balancedCycleWordSum_smul]
  simp only [Fintype.card_prod, Fintype.card_fin]
  unfold cycleNormalizer factorialPrefactor
  rw [div_pow]
  field_simp
  rw [← hfac]
  ring

end
end Wormald.FiniteModel

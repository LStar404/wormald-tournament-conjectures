import Wormald.MeanPermanentDegree
import Wormald.FactorialPrefactor
import Wormald.ConjectureOneReduction

/-!
# Actual nonregular independent-model asymptotics

The finite independent mean is controlled by its true edge law, then by
the block permanent, the strict degree product, and Stirling's estimate.
No asymptotic formula for regular bases is assumed here.
-/

namespace Wormald.FiniteModel
noncomputable section
open Filter Topology
open scoped BigOperators

theorem expectedCycles_nonneg {d : ℕ} (base : Orientation d) (m : ℕ) :
    (0 : ℝ) ≤ (expectedCycles base m : ℝ) := by
  unfold expectedCycles uniformMean
  push_cast
  positivity

theorem normalizedExpectedCycles_nonneg {d : ℕ} (base : Orientation d) (m : ℕ) :
    0 ≤ normalizedExpectedCycles base m :=
  div_nonneg (expectedCycles_nonneg base m) (cycleNormalizer_pos _).le

theorem factorialDegree_bound_normalized {d : ℕ} (base : Orientation d)
    (hd : 0 < d) (m : ℕ) (hm : 0 < m) :
    normalizedExpectedCycles base m ≤
      (d : ℝ) * ((m : ℝ) * factorialPrefactor d m *
        (∏ i, (toTournament base).degreeFactor i) ^ m) := by
  have hN : d * m ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hd hm)
  have hfac : ((d * m : ℕ) : ℝ) * (Nat.factorial (d * m - 1) : ℝ) =
      (Nat.factorial (d * m) : ℝ) := by
    exact_mod_cast Nat.mul_factorial_pred hN
  have hNfac : (Nat.factorial (d * m) : ℝ) ≠ 0 := by positivity
  have hpredfac : (Nat.factorial (d * m - 1) : ℝ) ≠ 0 := by positivity
  have htwo : (2 : ℝ) ^ (d * m) ≠ 0 := by positivity
  have hbound := div_le_div_of_nonneg_right
    (expectedCycles_le_factorial_degreeProduct base (Nat.ne_of_gt hd) m)
    (cycleNormalizer_pos (d * m)).le
  unfold normalizedExpectedCycles
  apply hbound.trans_eq
  unfold cycleNormalizer factorialPrefactor
  rw [div_pow]
  push_cast at hfac ⊢
  field_simp
  rw [← hfac]
  ring

/-- The normalized expected Hamilton-cycle count tends to zero for every
fixed nonregular base, for the original independent internal-block law. -/
theorem tendsto_normalizedExpectedCycles_nonregular {d : ℕ} (base : Orientation d)
    (hd : 0 < d) (hnreg : ¬ (toTournament base).Regular) :
    Tendsto (normalizedExpectedCycles base) atTop (𝓝 0) := by
  let r : ℝ := ∏ i, (toTournament base).degreeFactor i
  have hr : 0 ≤ r := (Finset.prod_pos (fun i _ =>
    (toTournament base).degreeFactor_pos (Nat.ne_of_gt hd) i)).le
  have hr1 : r < 1 := (toTournament base).degreeProduct_lt_one (Nat.ne_of_gt hd) hnreg
  have hlimit := (tendsto_factorialPrefactor_mul_pow d 1 hd r hr hr1).const_mul (d : ℝ)
  simp only [pow_one, mul_zero] at hlimit
  apply squeeze_zero'
  · exact Eventually.of_forall (normalizedExpectedCycles_nonneg base)
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact factorialDegree_bound_normalized base hd m (by omega)
  · exact hlimit

end
end Wormald.FiniteModel

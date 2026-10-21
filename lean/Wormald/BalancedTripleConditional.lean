import Wormald.BalancedTripleConcentration
import Wormald.ActualRegularCyclesLimit
import Wormald.SkewMomentSeries

namespace Wormald

noncomputable section
open Filter
open scoped BigOperators Topology

theorem factorialPrefactor_pos (d m : ℕ) (hd : 0 < d) : 0 < factorialPrefactor d m := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold factorialPrefactor
  positivity

theorem balancedTripleTailMass_nonneg {n L : ℕ} (T : Tournament n) (m : ℕ) (ε : ℝ) :
    0 ≤ balancedTripleTailMass (L := L) T m ε := by
  apply Finset.sum_nonneg
  intro f _
  split_ifs
  · exact Finset.prod_nonneg (fun _ _ => T.realCriticalTransition_nonneg _ _)
  · exact le_rfl

namespace FiniteModel

def balancedOccupationMass {d : ℕ} (base : Orientation d) (m : ℕ) : ℝ :=
  balancedCycleWordSum (N := Fintype.card (Fin d × Fin m))
    (toTournament base).realCriticalTransition m

def balancedTripleBadFraction {d : ℕ} (base : Orientation d) (ε : ℝ) (m : ℕ) : ℝ :=
  balancedTripleTailMass (L := Fintype.card (Fin d × Fin m)) (toTournament base) m ε /
    balancedOccupationMass base m

theorem normalizedExpectedCycles_eq_prefactor_mul_occupation {d : ℕ}
    (base : Orientation d) (m : ℕ) (hN : 3 ≤ d * m) :
    normalizedExpectedCycles base m = factorialPrefactor d m * balancedOccupationMass base m := by
  simpa only [balancedOccupationMass, markovBase_eq_realCriticalTransition] using
    normalizedExpectedCycles_eq_markovWordSum base m hN

theorem tendsto_prefactor_mul_balancedTripleTailMass {d : ℕ} (hd : 3 ≤ d)
    (base : Orientation d) (hT : (toTournament base).Regular) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m : ℕ => factorialPrefactor d m *
      balancedTripleTailMass (L := Fintype.card (Fin d × Fin m)) (toTournament base) m ε)
      atTop (𝓝 0) := by
  let q : ℝ := Real.exp (-ε ^ 2 / 8)
  have hq0 : 0 ≤ q := Real.exp_nonneg _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hε])
  have hlim : Tendsto (fun m : ℕ => 8 * (factorialPrefactor d m * q ^ m)) atTop (𝓝 0) := by
    have hh := tendsto_factorialPrefactor_mul_pow d 0 (by omega) q hq0 hq1
    simpa only [pow_zero, one_mul, mul_zero] using hh.const_mul 8
  have hNat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ m : ℕ in atTop, 4 / ε ≤ (m : ℝ) :=
    hNat.eventually (eventually_ge_atTop (4 / ε))
  apply squeeze_zero' (Eventually.of_forall (fun m =>
    mul_nonneg (factorialPrefactor_pos d m (by omega)).le
      (balancedTripleTailMass_nonneg _ m ε))) _ hlim
  filter_upwards [eventually_ge_atTop 3, hlarge] with m hm hmscale
  let L := Fintype.card (Fin d × Fin m)
  have hL : L = d * m := by simp [L, Fintype.card_prod]
  have hdm : 3 * m ≤ d * m := Nat.mul_le_mul_right m hd
  have hL3 : 3 ≤ L := by rw [hL]; omega
  have hLm : m ≤ L - 2 := by rw [hL]; omega
  have hLm' : m ≤ L := by omega
  have hmr : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLm'
  have hscale : 4 ≤ ε * (L : ℝ) := by
    have hh := (div_le_iff₀ hε).mp hmscale
    nlinarith
  have hb := (toTournament base).balancedTripleTailMass_le (by omega) hT hL3 m ε hε.le hscale
  have hgeom : Real.exp (-ε ^ 2 * ((L - 2 : ℕ) : ℝ) / 8) ≤ q ^ m := by
    change _ ≤ Real.exp (-ε ^ 2 / 8) ^ m
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hh : (m : ℝ) ≤ ((L - 2 : ℕ) : ℝ) := by exact_mod_cast hLm
    nlinarith [sq_nonneg ε]
  have hbad : balancedTripleTailMass (L := L) (toTournament base) m ε ≤ 8 * q ^ m :=
    hb.trans (mul_le_mul_of_nonneg_left hgeom (by norm_num))
  calc
    _ ≤ factorialPrefactor d m * (8 * q ^ m) :=
      mul_le_mul_of_nonneg_left hbad (factorialPrefactor_pos d m (by omega)).le
    _ = _ := by ring

/-- The balanced cyclic law has actual exponential concentration. Its
conditioning cost is controlled by the already proved genuine counting limit
and factorial normalization, rather than assumed as a probability bound. -/
theorem tendsto_balancedTripleBadFraction {d : ℕ} (hd : 3 ≤ d)
    (base : Orientation d) (hT : (toTournament base).Regular) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (balancedTripleBadFraction base ε) atTop (𝓝 0) := by
  have hnum := tendsto_prefactor_mul_balancedTripleTailMass hd base hT ε hε
  have hmean := tendsto_normalizedExpectedCycles_regular hd base hT
  have hp : 0 < (toTournament base).spectralRatio.re :=
    (toTournament base).spectralRatio_re_pos (by omega)
  have hh := hnum.div hmean hp.ne'
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 3] with m hm
  have hN : 3 ≤ d * m := by
    have hmul := Nat.mul_le_mul_right m hd
    omega
  change (factorialPrefactor d m *
      balancedTripleTailMass (L := Fintype.card (Fin d × Fin m)) (toTournament base) m ε) /
      normalizedExpectedCycles base m =
    balancedTripleTailMass (L := Fintype.card (Fin d × Fin m)) (toTournament base) m ε /
      balancedOccupationMass base m
  rw [normalizedExpectedCycles_eq_prefactor_mul_occupation base m hN]
  exact mul_div_mul_left _ _ (factorialPrefactor_pos d m (by omega)).ne'

end FiniteModel
end
end Wormald

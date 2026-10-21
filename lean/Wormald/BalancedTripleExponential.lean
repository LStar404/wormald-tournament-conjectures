import Wormald.BalancedTripleConditional
import Wormald.FiniteWeightedAverages

namespace Wormald

noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

theorem cyclicTripleCount_le {V : Type*} [DecidableEq V] {L : ℕ} (f : Fin L → V) :
    cyclicTripleCount f ≤ L := by
  calc
    _ ≤ ∑ _t : Fin L, (1 : ℕ) := Finset.sum_le_sum (fun t _ => by
      unfold cyclicTripleIndicator
      split_ifs <;> omega)
    _ = _ := by simp

namespace FiniteModel

def balancedWordWeight {d : ℕ} (base : Orientation d) (m : ℕ)
    (f : Fin (Fintype.card (Fin d × Fin m)) → Fin d) : ℝ :=
  if BalancedBaseWord m f then cyclicWordWeight (toTournament base).realCriticalTransition f else 0

def normalizedTripleValue {d : ℕ} (m : ℕ)
    (f : Fin (Fintype.card (Fin d × Fin m)) → Fin d) : ℝ :=
  (cyclicTripleCount f : ℝ) / (m : ℝ)

def balancedTripleExponentialMean {d : ℕ} (base : Orientation d) (m : ℕ) : ℝ :=
  finiteWeightedAverage (balancedWordWeight base m) (fun f => Real.exp (normalizedTripleValue m f))

theorem balancedWordWeight_nonneg {d : ℕ} (base : Orientation d) (m : ℕ)
    (f : Fin (Fintype.card (Fin d × Fin m)) → Fin d) : 0 ≤ balancedWordWeight base m f := by
  unfold balancedWordWeight
  split_ifs
  · exact Finset.prod_nonneg (fun _ _ => (toTournament base).realCriticalTransition_nonneg _ _)
  · exact le_rfl

@[simp] theorem sum_balancedWordWeight {d : ℕ} (base : Orientation d) (m : ℕ) :
    (∑ f, balancedWordWeight base m f) = balancedOccupationMass base m := rfl

theorem eventually_balancedOccupationMass_pos {d : ℕ} (hd : 3 ≤ d)
    (base : Orientation d) (hT : (toTournament base).Regular) :
    ∀ᶠ m : ℕ in atTop, 0 < balancedOccupationMass base m := by
  have hp := (toTournament base).spectralRatio_re_pos (by omega)
  have hpos := (tendsto_normalizedExpectedCycles_regular hd base hT).eventually (eventually_gt_nhds hp)
  filter_upwards [hpos, eventually_ge_atTop 3] with m hm hm3
  have hN : 3 ≤ d * m := by have hh := Nat.mul_le_mul_right m hd; omega
  rw [normalizedExpectedCycles_eq_prefactor_mul_occupation base m hN] at hm
  exact (mul_pos_iff_of_pos_left (factorialPrefactor_pos d m (by omega))).mp hm

theorem triple_bad_iff {d : ℕ} (hd : d ≠ 0) (m : ℕ) (hm : 0 < m) (δ : ℝ)
    (f : Fin (Fintype.card (Fin d × Fin m)) → Fin d) :
    (δ / (d : ℝ)) * (Fintype.card (Fin d × Fin m) : ℝ) ≤
        |(cyclicTripleCount f : ℝ) - (Fintype.card (Fin d × Fin m) : ℝ) * (1 / (d : ℝ)) ^ 2| ↔
      δ ≤ |normalizedTripleValue m f - 1 / (d : ℝ)| := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : (Fintype.card (Fin d × Fin m) : ℝ) = (d : ℝ) * (m : ℝ) := by simp
  have hc : (cyclicTripleCount f : ℝ) - (Fintype.card (Fin d × Fin m) : ℝ) * (1 / (d : ℝ)) ^ 2 =
      (m : ℝ) * (normalizedTripleValue m f - 1 / (d : ℝ)) := by
    rw [hL]
    unfold normalizedTripleValue
    field_simp [hdR, hmR.ne']
  have ht : (δ / (d : ℝ)) * (Fintype.card (Fin d × Fin m) : ℝ) = (m : ℝ) * δ := by
    rw [hL]
    field_simp
  rw [ht, hc, abs_mul, abs_of_pos hmR]
  exact mul_le_mul_iff_right₀ hmR

theorem tendsto_balancedTripleMetricBadFraction {d : ℕ} (hd : 3 ≤ d)
    (base : Orientation d) (hT : (toTournament base).Regular) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun m : ℕ =>
      finiteAbsTailMass (balancedWordWeight base m) (fun f => normalizedTripleValue m f - 1 / (d : ℝ)) δ /
        ∑ f, balancedWordWeight base m f) atTop (𝓝 0) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hh := tendsto_balancedTripleBadFraction hd base hT (δ / (d : ℝ)) (div_pos hδ hdR)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  rw [sum_balancedWordWeight]
  change balancedTripleTailMass (L := Fintype.card (Fin d × Fin m)) (toTournament base) m (δ / (d : ℝ)) /
      balancedOccupationMass base m = _
  congr 1
  unfold balancedTripleTailMass finiteAbsTailMass balancedWordWeight
  apply Finset.sum_congr rfl
  intro f _
  simp only [triple_bad_iff (by omega) m hm δ f]
  by_cases hb : BalancedBaseWord m f <;> simp [hb]

theorem normalizedTripleValue_mem_Icc {d : ℕ} (m : ℕ) (hm : 0 < m)
    (f : Fin (Fintype.card (Fin d × Fin m)) → Fin d) :
    normalizedTripleValue m f ∈ Set.Icc 0 (d : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hmR.le
  · apply (div_le_iff₀ hmR).mpr
    have hb : (cyclicTripleCount f : ℝ) ≤ (Fintype.card (Fin d × Fin m) : ℝ) :=
      by exact_mod_cast cyclicTripleCount_le f
    simpa using hb

/-- The positive exponential correction in the original regular model has
the required actual balanced-word mean limit. -/
theorem tendsto_balancedTripleExponentialMean {d : ℕ} (hd : 3 ≤ d)
    (base : Orientation d) (hT : (toTournament base).Regular) :
    Tendsto (balancedTripleExponentialMean base) atTop (𝓝 (Real.exp (1 / (d : ℝ)))) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have href : 1 / (d : ℝ) ≤ (d : ℝ) := by
    have hp : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hdR
    apply (div_le_iff₀ hp).mpr
    nlinarith
  apply tendsto_finiteWeightedAverage_of_concentration
    (fun m => balancedWordWeight base m) (fun m => normalizedTripleValue (d := d) m)
    (1 / (d : ℝ)) Real.exp (Real.exp (d : ℝ)) (balancedWordWeight_nonneg base)
    ((eventually_balancedOccupationMass_pos hd base hT).mono (fun m hm => by simpa using hm))
  · filter_upwards [eventually_gt_atTop 0] with m hm f
    have hx := normalizedTripleValue_mem_Icc m hm f
    have heX := Real.exp_le_exp.mpr hx.2
    have heC := Real.exp_le_exp.mpr href
    exact abs_sub_le_iff.mpr ⟨by linarith [Real.exp_nonneg (1 / (d : ℝ))],
      by linarith [Real.exp_nonneg (normalizedTripleValue m f)]⟩
  · exact Real.continuous_exp.continuousAt
  · exact tendsto_balancedTripleMetricBadFraction hd base hT

end FiniteModel
end
end Wormald

import Wormald.InternalCycleWeights
import Wormald.ConjectureTwoReduction
import Wormald.CarouselConstantBridge

/-! A finite, faithful reduction of Conjecture 2 to the uniform
regular-containment estimate. The sole analytic input concerns actual finite
arc-set probabilities; `UniformRegularTorusProof` and `ConjectureTwoProof` now
prove this input for the actual model. -/

namespace Wormald.FiniteModel
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

def LegalPartialPermutationArcs {m : ℕ} (D : Finset (Fin m × Fin m)) : Prop :=
  (∀ e ∈ D, e.1 ≠ e.2) ∧
    Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D ∧
    Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D ∧
    (∀ a b, (a, b) ∈ D → (b, a) ∉ D)

theorem internalCycleArcSet_legal {d m : ℕ} (σ : Equiv.Perm (Fin d × Fin m))
    (hN : 3 ≤ d * m) (hσ : SingleOrbit σ) (i : Fin d) :
    LegalPartialPermutationArcs (internalCycleArcSet σ i) := by
  refine ⟨?_, internalCycleArcSet_source_injOn σ i,
    internalCycleArcSet_target_injOn σ i, internalCycleArcSet_no_opposite σ hN hσ i⟩
  rintro ⟨a, b⟩ hab heq
  change a = b at heq
  subst b
  exact internalCycleArcSet_no_loops σ hN hσ i a hab

/-- The precise uniform relative estimate supplied by the regular tournament
Fourier analysis in `ConjectureTwoProof`. Odd orders are indexed by m=2*k+1. -/
def UniformRegularContainmentAsymptotic : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ k, 0 ≤ ε k) ∧
    ∀ᶠ k : ℕ in atTop, ∀ D : Finset (Fin (2 * k + 1) × Fin (2 * k + 1)),
      LegalPartialPermutationArcs D →
        |(2 : ℝ) ^ D.card * (regularContainmentProbability D ⟨k, rfl⟩ : ℝ) *
          Real.exp (-(internalInOutCount D : ℝ) / (2 * k + 1 : ℕ)) - 1| ≤ ε k

theorem regularContainmentProbability_nonneg {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hm : Odd m) :
    (0 : ℝ) ≤ (regularContainmentProbability D hm : ℝ) := by
  unfold regularContainmentProbability uniformMean
  positivity

theorem regularContainmentProbability_bounds {m : ℕ} (D : Finset (Fin m × Fin m))
    (hm : Odd m) (ε : ℝ)
    (h : |(2 : ℝ) ^ D.card * (regularContainmentProbability D hm : ℝ) *
      Real.exp (-(internalInOutCount D : ℝ) / (m : ℝ)) - 1| ≤ ε) :
    (1 - ε) * independentTiltedBlockWeight D ≤ (regularContainmentProbability D hm : ℝ) ∧
      (regularContainmentProbability D hm : ℝ) ≤ (1 + ε) * independentTiltedBlockWeight D := by
  let t : ℝ := (internalInOutCount D : ℝ) / (m : ℝ)
  let z : ℝ := (2 : ℝ) ^ D.card * Real.exp (-t)
  have hz : z * independentTiltedBlockWeight D = 1 := by
    unfold z independentTiltedBlockWeight
    change (2 ^ D.card * Real.exp (-t)) * ((1 / 2) ^ D.card * Real.exp t) = 1
    rw [mul_mul_mul_comm, ← mul_pow, ← Real.exp_add]
    norm_num
  have heq : ((2 : ℝ) ^ D.card * (regularContainmentProbability D hm : ℝ) *
      Real.exp (-(internalInOutCount D : ℝ) / (m : ℝ))) * independentTiltedBlockWeight D =
        (regularContainmentProbability D hm : ℝ) := by
    have ht : -(internalInOutCount D : ℝ) / (m : ℝ) = -t := by dsimp [t]; ring
    rw [ht]
    calc
      _ = (regularContainmentProbability D hm : ℝ) * (z * independentTiltedBlockWeight D) := by
        dsimp [z]; ring
      _ = _ := by rw [hz, mul_one]
  have hh := abs_sub_le_iff.mp h
  have hw := (independentTiltedBlockWeight_pos D).le
  constructor
  · have hlow : 1 - ε ≤ (2 : ℝ) ^ D.card * (regularContainmentProbability D hm : ℝ) *
        Real.exp (-(internalInOutCount D : ℝ) / (m : ℝ)) := by linarith
    simpa only [heq] using mul_le_mul_of_nonneg_right hlow hw
  · have hup : (2 : ℝ) ^ D.card * (regularContainmentProbability D hm : ℝ) *
        Real.exp (-(internalInOutCount D : ℝ) / (m : ℝ)) ≤ 1 + ε := by linarith
    simpa only [heq] using mul_le_mul_of_nonneg_right hup hw

def normalizedExpectedRegularCycles {d : ℕ} (base : Orientation d) (k : ℕ) : ℝ :=
  (expectedRegularCycles base (2 * k + 1)
    ((legalRegularOrder_iff d (2 * k + 1)).mpr ⟨k, rfl⟩) : ℝ) /
      cycleNormalizer (d * (2 * k + 1))

theorem expectedRegularCycles_tilted_bounds {d m : ℕ} (base : Orientation d)
    (hm : Odd m) (hN : 3 ≤ d * m) (ε : ℝ) (_hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprob : ∀ D : Finset (Fin m × Fin m), LegalPartialPermutationArcs D →
      |(2 : ℝ) ^ D.card * (regularContainmentProbability D hm : ℝ) *
        Real.exp (-(internalInOutCount D : ℝ) / (m : ℝ)) - 1| ≤ ε) :
    (1 - ε) ^ d * tiltedIndependentCycleSum base m ≤
      (expectedRegularCycles base m ((legalRegularOrder_iff d m).mpr hm) : ℝ) ∧
    (expectedRegularCycles base m ((legalRegularOrder_iff d m).mpr hm) : ℝ) ≤
      (1 + ε) ^ d * tiltedIndependentCycleSum base m := by
  rw [expectedRegularCycles_eq_weightedArcSets, tiltedIndependentCycleSum_eq_internalWeights]
  simp only [regularWeightedHamiltonianCycleSum, Rat.cast_sum, apply_ite,
    Rat.cast_prod, Rat.cast_zero, Finset.mul_sum]
  constructor <;> apply Finset.sum_le_sum <;> intro σ _
  · by_cases hσ : SingleOrbit σ ∧ CrossBlockCycleCompatible base σ
    · simp only [ite_eq_left hσ]
      have hp := fun i => regularContainmentProbability_bounds (internalCycleArcSet σ i) hm ε
        (hprob _ (internalCycleArcSet_legal σ hN hσ.1 i))
      have hh := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => (1 - ε) * independentTiltedBlockWeight (internalCycleArcSet σ i))
        (g := fun i => (regularContainmentProbability (internalCycleArcSet σ i) hm : ℝ))
        (fun i _ => mul_nonneg (by linarith) (independentTiltedBlockWeight_pos _).le)
        (fun i _ => (hp i).1)
      simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] using hh
    · simp [hσ]
  · by_cases hσ : SingleOrbit σ ∧ CrossBlockCycleCompatible base σ
    · simp only [ite_eq_left hσ]
      have hp := fun i => regularContainmentProbability_bounds (internalCycleArcSet σ i) hm ε
        (hprob _ (internalCycleArcSet_legal σ hN hσ.1 i))
      have hh := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => (regularContainmentProbability (internalCycleArcSet σ i) hm : ℝ))
        (g := fun i => (1 + ε) * independentTiltedBlockWeight (internalCycleArcSet σ i))
        (fun i _ => regularContainmentProbability_nonneg _ hm) (fun i _ => (hp i).2)
      simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] using hh
    · simp [hσ]

theorem tendsto_normalizedExpectedRegularCycles_of_containment {d : ℕ} (hd : 3 ≤ d)
    (base : Orientation d) (hT : (toTournament base).Regular)
    (hcontain : UniformRegularContainmentAsymptotic) :
    Tendsto (normalizedExpectedRegularCycles base) atTop
      (𝓝 ((toTournament base).spectralRatio.re * Real.exp (1 / (d : ℝ)))) := by
  obtain ⟨ε, hε, hε0, hest⟩ := hcontain
  have hodd : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => show k ≤ 2 * k + 1 by omega) tendsto_id
  have htilt := (tendsto_normalizedTiltedIndependentCycles hd base hT).comp hodd
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlo := ((hone.sub hε).pow d).mul htilt
  have hup := ((hone.add hε).pow d).mul htilt
  simp only [sub_zero, add_zero, one_pow, one_mul, Function.comp_def] at hlo hup
  have hbounds : ∀ᶠ k : ℕ in atTop,
      (1 - ε k) ^ d * normalizedTiltedIndependentCycles base (2 * k + 1) ≤
          normalizedExpectedRegularCycles base k ∧
      normalizedExpectedRegularCycles base k ≤
          (1 + ε k) ^ d * normalizedTiltedIndependentCycles base (2 * k + 1) := by
    filter_upwards [hest, hε.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with k hk hk1
    have hN : 3 ≤ d * (2 * k + 1) := le_trans hd (by
      simpa using Nat.mul_le_mul_left d (show 1 ≤ 2 * k + 1 by omega))
    have hb := expectedRegularCycles_tilted_bounds base ⟨k, rfl⟩ hN (ε k) (hε0 k) hk1.le hk
    constructor
    · simpa only [normalizedTiltedIndependentCycles, normalizedExpectedRegularCycles,
        mul_div_assoc] using
        div_le_div_of_nonneg_right hb.1 (cycleNormalizer_pos (d * (2 * k + 1))).le
    · simpa only [normalizedTiltedIndependentCycles, normalizedExpectedRegularCycles,
        mul_div_assoc] using
        div_le_div_of_nonneg_right hb.2 (cycleNormalizer_pos (d * (2 * k + 1))).le
  exact hlo.squeeze' hup (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

theorem carouselClosedConstant_re_eq_independent_correction (d : ℕ) (hd : Odd d) :
    (Wormald.carouselClosedConstant d).re =
      (toTournament (carousel d)).spectralRatio.re * Real.exp (1 / (d : ℝ)) := by
  have harg : (1 / (d : ℂ)) = ((1 / (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  have hcomplex := Wormald.carouselClosedConstant_eq_determinant d hd
  rw [harg, ← Complex.ofReal_exp] at hcomplex
  have hratio : Wormald.carouselSpectralRatio d = (toTournament (carousel d)).spectralRatio := rfl
  rw [hratio] at hcomplex
  have hreal := congrArg Complex.re hcomplex
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    mul_comm] using hreal

theorem tendsto_regularCarouselNormalized_of_containment (hcontain : UniformRegularContainmentAsymptotic)
    (j : ℕ) :
    Tendsto (regularCarouselNormalized (2 * j + 3)) atTop
      (𝓝 (Wormald.carouselClosedConstant (2 * j + 3)).re) := by
  rw [carouselClosedConstant_re_eq_independent_correction (2 * j + 3) ⟨j + 1, by omega⟩]
  exact tendsto_normalizedExpectedRegularCycles_of_containment (by omega)
    (carousel (2 * j + 3)) (carousel_regular ⟨j + 1, by omega⟩) hcontain

/-- Internal conditional reduction only: proving the explicitly defined
uniform finite arc-set estimate is enough for the original two-stage target. -/
theorem conjectureTwoWithModelLimits_of_uniform_containment
    (hcontain : UniformRegularContainmentAsymptotic) : conjectureTwoWithModelLimits :=
  conjectureTwoWithModelLimits_of_closed_model_limits
    (tendsto_regularCarouselNormalized_of_containment hcontain)

theorem conjectureTwo_exact_of_uniform_containment
    (hcontain : UniformRegularContainmentAsymptotic) :
    ∃ r : ℕ → ℝ,
      (∀ j, Tendsto (regularCarouselNormalized (2 * j + 3)) atTop (𝓝 (r j))) ∧
      Tendsto r atTop (𝓝 (Real.cosh 1 / Real.cos 1)) :=
  conjectureTwo_exact_of_closed_model_limits
    (tendsto_regularCarouselNormalized_of_containment hcontain)

end
end Wormald.FiniteModel

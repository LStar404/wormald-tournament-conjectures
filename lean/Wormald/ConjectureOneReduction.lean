import Wormald.CountIsomorphism
import Wormald.Eventual

/-!
# Conditional reduction for the actual Wormald model

The expectations in this module are the finite sums over all independent
internal tournament assignments, rather than arbitrary test functions. They are divided by Wormald’s
normalizer ν_(d*m); raw counts are not assumed to converge to finite constants.
The unresolved convergence and limiting comparison obligations remain explicit
hypotheses. Ordinary-isomorphism invariance is proved in `CountIsomorphism.lean`. This module does not prove Conjecture 1.
-/

open Filter Topology

namespace Wormald.FiniteModel

/-- Wormald's normalizer ν_N=(N−1)!/2^N. For N≥3 this is the mean
Hamilton-cycle count in the uniform random N-tournament. The algebraic expression
is defined and strictly positive for every N. -/
noncomputable def cycleNormalizer (N : ℕ) : ℝ :=
  (Nat.factorial (N - 1) : ℝ) / (2 : ℝ) ^ N

theorem cycleNormalizer_pos (N : ℕ) : 0 < cycleNormalizer N := by
  unfold cycleNormalizer
  positivity

/-- The paper's normalized expectation, with total order N=d*m. -/
noncomputable def normalizedExpectedCycles {d : ℕ} (base : Orientation d) (m : ℕ) : ℝ :=
  (expectedCycles base m : ℝ) / cycleNormalizer (d * m)

/-- The stronger unique-isomorphism-class target implies the original Conjecture 1. -/
theorem conjectureOne_of_uniqueClass (h : uniqueClassConjectureOne) : conjectureOne := by
  intro d hd ho
  obtain ⟨M, hM⟩ := h d hd ho
  exact ⟨M, fun m hm base => (hM m hm base).1⟩

/-- Appendix A.6 specialized to the actual expected Hamilton-cycle counts.
All assumptions concern this exact finite random model and are displayed here.
In particular, the required convergence and limiting gap are not inferred from
finite computations or from the abstract reduction theorem. -/
theorem uniqueClassConjectureOne_of_actual_limits
    (L : (d : ℕ) → Orientation d → ℝ)
    (hconv : ∀ d, 3 ≤ d → Odd d → ∀ base : Orientation d,
      Tendsto (normalizedExpectedCycles base) atTop (𝓝 (L d base)))
    (hequal : ∀ d, 3 ≤ d → Odd d → ∀ base : Orientation d,
      Isomorphic base (carousel d) → ∀ m,
        expectedCycles base m = expectedCycles (carousel d) m)
    (hgap : ∀ d, 3 ≤ d → Odd d → ∀ base : Orientation d,
      ¬ Isomorphic base (carousel d) → L d base < L d (carousel d)) :
    uniqueClassConjectureOne := by
  intro d hd ho
  have hevent := Wormald.eventually_unique_class_of_limiting_gap atTop
    (fun base m => normalizedExpectedCycles base m) (L d) (carousel d)
    (fun base => Isomorphic base (carousel d))
    (hconv d hd ho)
    (fun base hiso m => by
      unfold normalizedExpectedCycles
      rw [hequal d hd ho base hiso m])
    (hgap d hd ho)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨M, ?_⟩
  intro m hm base
  have hb := hM m hm base
  refine ⟨?_, ?_⟩
  · have hraw : (expectedCycles base m : ℝ) ≤ (expectedCycles (carousel d) m : ℝ) :=
      (div_le_div_iff_of_pos_right (cycleNormalizer_pos (d * m))).mp hb.1
    exact_mod_cast hraw
  · constructor
    · intro h
      apply hb.2.mp
      unfold normalizedExpectedCycles
      rw [h]
    · intro h
      have hreal := hb.2.mpr h
      have hraw : (expectedCycles base m : ℝ) = (expectedCycles (carousel d) m : ℝ) :=
        (div_left_inj' (ne_of_gt (cycleNormalizer_pos (d * m)))).mp hreal
      exact_mod_cast hraw

/-- The same explicit assumptions imply the original, non-uniqueness statement. -/
theorem conjectureOne_of_actual_limits
    (L : (d : ℕ) → Orientation d → ℝ)
    (hconv : ∀ d, 3 ≤ d → Odd d → ∀ base : Orientation d,
      Tendsto (normalizedExpectedCycles base) atTop (𝓝 (L d base)))
    (hequal : ∀ d, 3 ≤ d → Odd d → ∀ base : Orientation d,
      Isomorphic base (carousel d) → ∀ m,
        expectedCycles base m = expectedCycles (carousel d) m)
    (hgap : ∀ d, 3 ≤ d → Odd d → ∀ base : Orientation d,
      ¬ Isomorphic base (carousel d) → L d base < L d (carousel d)) :
    conjectureOne :=
  conjectureOne_of_uniqueClass
    (uniqueClassConjectureOne_of_actual_limits L hconv hequal hgap)

/-- With ordinary-isomorphism invariance already proved, only the genuine
normalized-model limits and their strict comparison remain as hypotheses. -/
theorem uniqueClassConjectureOne_of_normalized_limits
    (L : (d : ℕ) → Orientation d → ℝ)
    (hconv : ∀ d, 3 ≤ d → Odd d → ∀ base : Orientation d,
      Tendsto (normalizedExpectedCycles base) atTop (𝓝 (L d base)))
    (hgap : ∀ d, 3 ≤ d → Odd d → ∀ base : Orientation d,
      ¬ Isomorphic base (carousel d) → L d base < L d (carousel d)) :
    uniqueClassConjectureOne :=
  uniqueClassConjectureOne_of_actual_limits L hconv
    (fun d _ _ base hiso m => expectedCycles_isomorphic base (carousel d) hiso m) hgap

/-- Conditional reduction to the original Conjecture 1, with no separate
isomorphism-invariance hypothesis. The two remaining analytic/spectral obligations
are explicit and have not yet been proved for arbitrary base order. -/
theorem conjectureOne_of_normalized_limits
    (L : (d : ℕ) → Orientation d → ℝ)
    (hconv : ∀ d, 3 ≤ d → Odd d → ∀ base : Orientation d,
      Tendsto (normalizedExpectedCycles base) atTop (𝓝 (L d base)))
    (hgap : ∀ d, 3 ≤ d → Odd d → ∀ base : Orientation d,
      ¬ Isomorphic base (carousel d) → L d base < L d (carousel d)) :
    conjectureOne :=
  conjectureOne_of_uniqueClass
    (uniqueClassConjectureOne_of_normalized_limits L hconv hgap)

end Wormald.FiniteModel

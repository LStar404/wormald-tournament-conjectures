import Wormald.CarouselRegular
import Wormald.ConjectureOneReduction
import Wormald.CarouselLimit

/-!
# The original two-stage random-model limit behind Conjecture 2

The block index k means the legal regular block order m=2*k+1. The outer
index j means the legal base order d=2*j+3. Both limits therefore use
exactly the odd orders prescribed in the original problem.

The target below includes existence of all inner random-model limits; it is
thus a strengthened formulation of Conjecture 2. No default value of a
nonexistent limit is used. The reduction keeps the connection from actual model
expectations to the closed expression explicit; `ConjectureTwoProof` now proves it.
-/

open Filter Topology

namespace Wormald.FiniteModel

private theorem odd_blockOrder (k : ℕ) : Odd (2 * k + 1) := ⟨k, by omega⟩

/-- The actual regular-block carousel expectation divided by ν_(d*m).
The block order is m=2*k+1, and its finite uniform sample space is proved nonempty. -/
noncomputable def regularCarouselNormalized (d k : ℕ) : ℝ :=
  (expectedRegularCycles (carousel d) (2 * k + 1)
    ((legalRegularOrder_iff d (2 * k + 1)).mpr (odd_blockOrder k)) : ℝ) /
      cycleNormalizer (d * (2 * k + 1))

/-- Strengthened original target: each fixed odd base has an inner model limit,
and these constants have an outer limit along increasing odd base orders.
Its proof is `ConjectureTwoProof.conjectureTwoWithModelLimits_proof`. -/
def conjectureTwoWithModelLimits : Prop :=
  ∃ r : ℕ → ℝ,
    (∀ j, Tendsto (regularCarouselNormalized (2 * j + 3)) atTop (𝓝 (r j))) ∧
    ∃ L : ℝ, Tendsto r atTop (𝓝 L)

/-- The real parts of the closed constants have the stated exact outer limit. -/
theorem tendsto_carouselClosedConstant_re_odd :
    Tendsto (fun j : ℕ => (Wormald.carouselClosedConstant (2 * j + 3)).re) atTop
      (𝓝 (Real.cosh 1 / Real.cos 1)) := by
  have h := (Complex.continuous_re.tendsto
      ((Real.cosh 1 / Real.cos 1 : ℝ) : ℂ)).comp
    Wormald.tendsto_carouselClosedConstant_odd
  simpa only [Function.comp_def, Complex.ofReal_re] using h

/-- Conditional exact-value version of Conjecture 2. The premise identifies the
actual normalized regular random-model limits with the closed formula and is
proved without extra hypotheses in `ConjectureTwoProof`.
The outer closed-form limit is proved independently in `CarouselLimit.lean`. -/
theorem conjectureTwo_exact_of_closed_model_limits
    (hmodel : ∀ j, Tendsto (regularCarouselNormalized (2 * j + 3)) atTop
      (𝓝 (Wormald.carouselClosedConstant (2 * j + 3)).re)) :
    ∃ r : ℕ → ℝ,
      (∀ j, Tendsto (regularCarouselNormalized (2 * j + 3)) atTop (𝓝 (r j))) ∧
      Tendsto r atTop (𝓝 (Real.cosh 1 / Real.cos 1)) := by
  exact ⟨fun j => (Wormald.carouselClosedConstant (2 * j + 3)).re,
    hmodel, tendsto_carouselClosedConstant_re_odd⟩

/-- The same explicit random-model identification implies the strengthened target. -/
theorem conjectureTwoWithModelLimits_of_closed_model_limits
    (hmodel : ∀ j, Tendsto (regularCarouselNormalized (2 * j + 3)) atTop
      (𝓝 (Wormald.carouselClosedConstant (2 * j + 3)).re)) :
    conjectureTwoWithModelLimits := by
  obtain ⟨r, hinner, houter⟩ := conjectureTwo_exact_of_closed_model_limits hmodel
  exact ⟨r, hinner, Real.cosh 1 / Real.cos 1, houter⟩

end Wormald.FiniteModel

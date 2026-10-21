import Wormald.UniformRegularTorusProof

/-! The original regular-block random model has its actual inner limits,
and their outer limit is exactly cosh(1)/cos(1). -/

namespace Wormald.FiniteModel
noncomputable section
open Filter
open scoped Topology

/-- Exact-value formulation of the original two-stage conjecture. Both
limits concern the actual finite regular-block probability model, along
the prescribed odd block and base orders. -/
def conjectureTwo : Prop :=
  ∃ r : ℕ → ℝ,
    (∀ j, Tendsto (regularCarouselNormalized (2 * j + 3)) atTop (𝓝 (r j))) ∧
      Tendsto r atTop (𝓝 (Real.cosh 1 / Real.cos 1))

theorem uniformRegularContainmentAsymptotic : UniformRegularContainmentAsymptotic :=
  uniformRegularContainmentAsymptotic_of_torusMainTerm uniformRegularTorusMainTerm

theorem tendsto_normalizedExpectedRegularCycles {d : ℕ} (hd : 3 ≤ d)
    (base : Orientation d) (hT : (toTournament base).Regular) :
    Tendsto (normalizedExpectedRegularCycles base) atTop
      (𝓝 ((toTournament base).spectralRatio.re * Real.exp (1 / (d : ℝ)))) :=
  tendsto_normalizedExpectedRegularCycles_of_containment hd base hT
    uniformRegularContainmentAsymptotic

theorem tendsto_regularCarouselNormalized (j : ℕ) :
    Tendsto (regularCarouselNormalized (2 * j + 3)) atTop
      (𝓝 (Wormald.carouselClosedConstant (2 * j + 3)).re) :=
  tendsto_regularCarouselNormalized_of_containment uniformRegularContainmentAsymptotic j

theorem conjectureTwo_proof : conjectureTwo :=
  conjectureTwo_exact_of_uniform_torus_mainTerm uniformRegularTorusMainTerm

theorem conjectureTwoWithModelLimits_proof : conjectureTwoWithModelLimits :=
  conjectureTwoWithModelLimits_of_uniform_torus_mainTerm uniformRegularTorusMainTerm

end
end Wormald.FiniteModel

import Wormald.ActualRegularCyclesLimit
import Wormald.ConjectureOneSpectralReduction

/-! The original eventual Hamilton-cycle extremum conjecture. Every counting,
analytic, spectral, and equality-classification input is proved in the import
chain; the final statements have no additional mathematical hypotheses. -/

namespace Wormald.FiniteModel
noncomputable section

theorem regularCycleAsymptotics : RegularCycleAsymptotics := by
  intro d hd _ base hT
  exact tendsto_normalizedExpectedCycles_regular hd base hT

/-- For each odd order at least three, the carousel is eventually the unique
maximizer up to tournament isomorphism, for the original independent model. -/
theorem uniqueClassConjectureOne_proof : uniqueClassConjectureOne :=
  uniqueClassConjectureOne_of_regularCycleAsymptotics regularCycleAsymptotics

/-- The literal original Conjecture 1. -/
theorem conjectureOne_proof : conjectureOne :=
  conjectureOne_of_regularCycleAsymptotics regularCycleAsymptotics

end
end Wormald.FiniteModel

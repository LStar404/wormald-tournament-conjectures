import Wormald.AnchoredCycleFourier
import Wormald.CriticalPoint

namespace Wormald.FiniteModel

noncomputable section
open Matrix MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The transfer matrix obtained from the actual finite counting model is
exactly the paper's critical transition J/d+C, over the complex numbers. -/
theorem markovBase_map_eq_criticalTransition {d : ℕ} (base : Orientation d) :
    (markovBase base).map Complex.ofRealHom = (toTournament base).criticalTransition := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [markovBase, weightedBase, Tournament.criticalTransition, Tournament.constantProjection,
      Tournament.complexNormalizedSign, Tournament.normalizedSign, Tournament.sign,
      toTournament]
    ring
  · cases harc : arc base i j <;>
      simp [markovBase, weightedBase, Tournament.criticalTransition, Tournament.constantProjection,
        Tournament.complexNormalizedSign, Tournament.normalizedSign, Tournament.sign,
        toTournament, hij, harc] <;> ring

/-- The anchored integral already uses the exact transition to which the finite
contraction and local analytic branch results apply. -/
theorem normalizedExpectedCycles_eq_criticalAnchoredFourierIntegral {d : ℕ}
    (base : Orientation (d + 1)) (m : ℕ) (hN : 3 ≤ (d + 1) * m) :
    (normalizedExpectedCycles base m : ℂ) = (factorialPrefactor (d + 1) m : ℂ) *
      ∫ x : UnitAddTorus (Fin d), UnitAddTorus.mFourier (fun _ => -(m : ℤ)) x *
        (((toTournament base).criticalTransition *
          Matrix.diagonal (anchoredFourierPhase x)) ^ ((d + 1) * m)).trace := by
  rw [normalizedExpectedCycles_eq_anchoredFourierIntegral base m hN,
    markovBase_map_eq_criticalTransition]

end
end Wormald.FiniteModel

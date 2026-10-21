import Wormald.StrictSpectralGap
import Wormald.NonregularCycles
import Wormald.CarouselRegular

/-!
# Reduction to the regular-base counting asymptotic for Conjecture 1

The former spectral-comparison and nonregular-decay inputs have both been
proved for the actual finite model. The one remaining premise here states
the precise original regular-model expectation limit, not an arbitrary test
function. `ActualRegularCyclesLimit` now proves this limit and
`ConjectureOneProof` discharges the premise of this retained reduction.
-/

namespace Wormald.FiniteModel
noncomputable section
open Filter Topology

/-- The independent-block counting theorem for regular bases, stated as a
Prop and proved by `regularCycleAsymptotics` in `ConjectureOneProof`. -/
def RegularCycleAsymptotics : Prop :=
  ∀ d : ℕ, 3 ≤ d → Odd d → ∀ base : Orientation d, (toTournament base).Regular →
    Tendsto (normalizedExpectedCycles base) atTop (𝓝 (toTournament base).spectralRatio.re)

/-- Every finite comparison, nonregular base and common-threshold step is now
proved. The displayed input is proved separately in `ActualRegularCyclesLimit`. -/
theorem uniqueClassConjectureOne_of_regularCycleAsymptotics
    (hregular : RegularCycleAsymptotics) : uniqueClassConjectureOne := by
  classical
  let L : (d : ℕ) → Orientation d → ℝ := fun _ base =>
    if (toTournament base).Regular then (toTournament base).spectralRatio.re else 0
  apply uniqueClassConjectureOne_of_normalized_limits L
  · intro d hd hodd base
    by_cases hb : (toTournament base).Regular
    · simpa only [L, ite_eq_left hb] using hregular d hd hodd base hb
    · simpa only [L, ite_eq_right hb] using
        tendsto_normalizedExpectedCycles_nonregular base (by omega) hb
  · intro d hd hodd base hnot
    have hCar := carousel_regular hodd
    by_cases hb : (toTournament base).Regular
    · simpa only [L, ite_eq_left hb, ite_eq_left hCar] using
        spectralRatio_re_lt_carousel_of_not_isomorphic (by omega) hodd base hb hnot
    · simpa only [L, ite_eq_right hb, ite_eq_left hCar] using
        (toTournament (carousel d)).spectralRatio_re_pos (by omega)

/-- The literal original Conjecture 1 follows from that counting theorem;
the final proof in `ConjectureOneProof` supplies it without extra hypotheses. -/
theorem conjectureOne_of_regularCycleAsymptotics
    (hregular : RegularCycleAsymptotics) : conjectureOne :=
  conjectureOne_of_uniqueClass
    (uniqueClassConjectureOne_of_regularCycleAsymptotics hregular)

end
end Wormald.FiniteModel

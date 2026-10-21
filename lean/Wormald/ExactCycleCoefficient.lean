import Wormald.MarkovCycleTransfer
import Wormald.TraceWordExpansion

/-! The original independent Hamilton-cycle expectation expressed as an
actual coefficient of a finite matrix trace polynomial. -/

namespace Wormald.FiniteModel
noncomputable section

/-- Exact counting identity, including the factorial labeling and cyclic
rotation factors, for the original independent sample space. -/
theorem expectedCycles_eq_traceCoefficient {d : ℕ} (base : Orientation d)
    (m : ℕ) (hN : 3 ≤ d * m) :
    (expectedCycles base m : ℝ) = (Nat.factorial m : ℝ) ^ d / (d * m : ℕ) *
      ((variableMatrix (weightedBase base) ^ (d * m)).trace).coeff (uniformExponent d m) := by
  rw [coeff_trace_variableMatrix_pow _ _ (by omega)]
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    expectedCycles_eq_balancedCycleWordSum base m hN

/-- The precise coefficient identity used by the occupation local limit
theorem proved in `ActualRegularCyclesLimit`. For regular bases `markovBase`
is doubly stochastic. -/
theorem normalizedExpectedCycles_eq_markovTraceCoefficient {d : ℕ} (base : Orientation d)
    (m : ℕ) (hN : 3 ≤ d * m) :
    normalizedExpectedCycles base m = factorialPrefactor d m *
      ((variableMatrix (markovBase base) ^ (d * m)).trace).coeff (uniformExponent d m) := by
  rw [coeff_trace_variableMatrix_pow _ _ (by omega)]
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    normalizedExpectedCycles_eq_markovWordSum base m hN

end
end Wormald.FiniteModel

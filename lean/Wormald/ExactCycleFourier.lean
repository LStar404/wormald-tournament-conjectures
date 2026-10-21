import Wormald.ExactCycleCoefficient
import Wormald.PolynomialFourierCoefficient

/-! Exact normalized Fourier integral for the original independent-block
Hamilton-cycle expectation. This remains an identity, not a limit theorem. -/

namespace Wormald
noncomputable section
open MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem real_polynomial_coeff_eq_torus_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (s : ι →₀ ℕ) :
    (p.coeff s : ℂ) = ∫ x : UnitAddTorus ι,
      UnitAddTorus.mFourier (fun i => -(s i : ℤ)) x *
        MvPolynomial.eval₂ Complex.ofRealHom (fun i => fourier 1 (x i)) p := by
  change Complex.ofRealHom (p.coeff s) = _
  simpa only [MvPolynomial.coeff_map, polynomialTorusEval, MvPolynomial.eval_map] using
    polynomial_coeff_eq_torus_integral (MvPolynomial.map Complex.ofRealHom p) s

namespace FiniteModel

theorem eval₂_trace_variableMatrix_pow {d N : ℕ}
    (B : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℂ) :
    MvPolynomial.eval₂ Complex.ofRealHom u ((variableMatrix B ^ N).trace) =
      ((B.map Complex.ofRealHom * Matrix.diagonal u) ^ N).trace := by
  let e := MvPolynomial.eval₂Hom Complex.ofRealHom u
  change e _ = _
  rw [AddMonoidHom.map_trace, Matrix.map_pow]
  congr 2
  ext i j
  simp [variableMatrix_entry, e, MvPolynomial.eval₂_monomial, Matrix.mul_diagonal]

/-- Every value in this integral is an evaluation of the actual transfer
matrix. There is no counting-asymptotic hypothesis in the identity. -/
theorem normalizedExpectedCycles_eq_markovFourierIntegral {d : ℕ} (base : Orientation d)
    (m : ℕ) (hN : 3 ≤ d * m) :
    (normalizedExpectedCycles base m : ℂ) = (factorialPrefactor d m : ℂ) *
      ∫ x : UnitAddTorus (Fin d), UnitAddTorus.mFourier (fun _ => -(m : ℤ)) x *
        (((markovBase base).map Complex.ofRealHom *
          Matrix.diagonal (fun i => fourier 1 (x i))) ^ (d * m)).trace := by
  rw [normalizedExpectedCycles_eq_markovTraceCoefficient base m hN,
    Complex.ofReal_mul, real_polynomial_coeff_eq_torus_integral]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [eval₂_trace_variableMatrix_pow]
    rfl

end FiniteModel
end
end Wormald

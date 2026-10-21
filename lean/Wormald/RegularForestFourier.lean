import Wormald.RegularDegreePolynomial
import Wormald.PolynomialFourierCoefficient

/-! Exact Fourier ratios for the genuine uniform regular tournament law.
The finite degree coefficients are proved in `RegularDegreePolynomial`;
this file changes those coefficients into integrals, without asymptotics. -/

namespace Wormald
noncomputable section
open MeasureTheory
open scoped BigOperators

local instance regularForestCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance regularForestCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem rational_polynomial_coeff_eq_torus_integral {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p : MvPolynomial ι ℚ) (s : ι →₀ ℕ) :
    (p.coeff s : ℂ) = ∫ x : UnitAddTorus ι,
      UnitAddTorus.mFourier (fun i => -(s i : ℤ)) x *
        MvPolynomial.eval₂ (Rat.castHom ℂ) (fun i => fourier 1 (x i)) p := by
  change (Rat.castHom ℂ) (p.coeff s) = _
  simpa only [MvPolynomial.coeff_map, polynomialTorusEval, MvPolynomial.eval_map] using
    polynomial_coeff_eq_torus_integral (MvPolynomial.map (Rat.castHom ℂ) p) s

theorem rational_polynomial_coeff_eq_cube_integral {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p : MvPolynomial ι ℚ) (s : ι →₀ ℕ) (a : ι → ℝ) :
    (p.coeff s : ℂ) = ∫ x : ι → ℝ in {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)},
      UnitAddTorus.mFourier (fun i => -(s i : ℤ)) (fun i => (x i : UnitAddCircle)) *
        MvPolynomial.eval₂ (Rat.castHom ℂ)
          (fun i => fourier 1 (x i : UnitAddCircle)) p := by
  change (Rat.castHom ℂ) (p.coeff s) = _
  simpa only [MvPolynomial.coeff_map, polynomialTorusEval, MvPolynomial.eval_map] using
    polynomial_coeff_eq_cube_integral (MvPolynomial.map (Rat.castHom ℂ) p) s a

namespace FiniteModel

def degreeFourierIntegrand {m : ℕ} (w : Edge m → Bool → ℚ)
    (x : UnitAddTorus (Fin m)) : ℂ :=
  UnitAddTorus.mFourier (fun _ => -((m / 2 : ℕ) : ℤ)) x *
    ∏ e : Edge m,
      ((w e true : ℂ) * fourier 1 (x e.1.1) + (w e false : ℂ) * fourier 1 (x e.1.2))

theorem eval₂_degreeGeneratingPolynomial {m : ℕ} (w : Edge m → Bool → ℚ)
    (u : Fin m → ℂ) :
    MvPolynomial.eval₂ (Rat.castHom ℂ) u (degreeGeneratingPolynomial w) =
      ∏ e : Edge m, ((w e true : ℂ) * u e.1.1 + (w e false : ℂ) * u e.1.2) := by
  simp only [degreeGeneratingPolynomial, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
    Rat.coe_castHom]

theorem degreeCoeff_eq_torusIntegral {m : ℕ} (w : Edge m → Bool → ℚ) :
    ((degreeGeneratingPolynomial w).coeff (regularDegreeExponent m) : ℂ) =
      ∫ x : UnitAddTorus (Fin m), degreeFourierIntegrand w x := by
  rw [rational_polynomial_coeff_eq_torus_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [eval₂_degreeGeneratingPolynomial]
    rfl

theorem degreeCoeff_eq_cubeIntegral {m : ℕ} (w : Edge m → Bool → ℚ) (a : Fin m → ℝ) :
    ((degreeGeneratingPolynomial w).coeff (regularDegreeExponent m) : ℂ) =
      ∫ x : Fin m → ℝ in {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)},
        degreeFourierIntegrand w (fun i => (x i : UnitAddCircle)) := by
  rw [rational_polynomial_coeff_eq_cube_integral _ _ a]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [eval₂_degreeGeneratingPolynomial]
    rfl

/-- An exact finite Fourier ratio for the original regular containment
probability. The normalizing integral is the actual regular count. -/
theorem regularContainmentProbability_eq_torus_ratio {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hm : Odd m) (hloop : ∀ i, (i, i) ∉ D) :
    (regularContainmentProbability D hm : ℂ) =
      (∫ x : UnitAddTorus (Fin m), degreeFourierIntegrand (arcSetWeight D) x) /
        (∫ x : UnitAddTorus (Fin m), degreeFourierIntegrand (fun _ _ => 1) x) := by
  rw [regularContainmentProbability_eq_coeff_ratio D hm hloop, Rat.cast_div]
  exact congrArg₂ (fun a b : ℂ => a / b)
    (degreeCoeff_eq_torusIntegral (arcSetWeight D))
    (degreeCoeff_eq_torusIntegral (fun (_ : Edge m) (_ : Bool) => 1))

theorem regularContainmentProbability_eq_cube_ratio {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hm : Odd m) (hloop : ∀ i, (i, i) ∉ D)
    (a : Fin m → ℝ) :
    (regularContainmentProbability D hm : ℂ) =
      (∫ x : Fin m → ℝ in {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)},
        degreeFourierIntegrand (arcSetWeight D) (fun i => (x i : UnitAddCircle))) /
      (∫ x : Fin m → ℝ in {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)},
        degreeFourierIntegrand (fun _ _ => 1) (fun i => (x i : UnitAddCircle))) := by
  rw [regularContainmentProbability_eq_coeff_ratio D hm hloop, Rat.cast_div]
  exact congrArg₂ (fun a b : ℂ => a / b)
    (degreeCoeff_eq_cubeIntegral (arcSetWeight D) a)
    (degreeCoeff_eq_cubeIntegral (fun (_ : Edge m) (_ : Bool) => 1) a)

theorem regularDegree_torusIntegral_ne_zero {m : ℕ} (hm : Odd m) :
    (∫ x : UnitAddTorus (Fin m), degreeFourierIntegrand (fun _ _ => 1) x) ≠ 0 := by
  rw [← degreeCoeff_eq_torusIntegral]
  exact_mod_cast (ne_of_gt (regularDegreeCoeff_pos m hm))

theorem regularDegree_cubeIntegral_ne_zero {m : ℕ} (hm : Odd m) (a : Fin m → ℝ) :
    (∫ x : Fin m → ℝ in {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)},
      degreeFourierIntegrand (fun _ _ => 1) (fun i => (x i : UnitAddCircle))) ≠ 0 := by
  rw [← degreeCoeff_eq_cubeIntegral]
  exact_mod_cast (ne_of_gt (regularDegreeCoeff_pos m hm))

end FiniteModel
end
end Wormald

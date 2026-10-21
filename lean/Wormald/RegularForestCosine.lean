import Wormald.RegularForestFourier

/-! Centering the exact regular-degree Fourier integral cancels its common
phase. Each free edge becomes twice a real cosine; each forced edge becomes
its oriented unit complex exponential. No asymptotic estimate is used. -/

namespace Wormald.FiniteModel
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem sum_edge_endpoints {m : ℕ} (x : Fin m → ℝ) :
    (∑ e : Edge m, (x e.1.1 + x e.1.2)) = ((m : ℝ) - 1) * ∑ i, x i := by
  have hlo : (∑ p : Fin m × Fin m, if p.1 < p.2 then x p.1 + x p.2 else 0) =
      ∑ e : Edge m, (x e.1.1 + x e.1.2) := by
    simpa only [Finset.sum_filter] using
      (Finset.sum_subtype (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2))
        (by simp) (fun p => x p.1 + x p.2))
  have hhi : (∑ p : Fin m × Fin m, if p.2 < p.1 then x p.2 + x p.1 else 0) =
      ∑ e : Edge m, (x e.1.1 + x e.1.2) := by
    exact (Fintype.sum_equiv (Equiv.prodComm (Fin m) (Fin m))
      (fun p => if p.2 < p.1 then x p.2 + x p.1 else 0)
      (fun p => if p.1 < p.2 then x p.1 + x p.2 else 0) (fun _ => rfl)).trans hlo
  have hsplit :
      (∑ e : Edge m, (x e.1.1 + x e.1.2)) + (∑ e : Edge m, (x e.1.1 + x e.1.2)) =
      ∑ p : Fin m × Fin m, if p.1 ≠ p.2 then x p.1 + x p.2 else 0 := by
    calc
      _ = (∑ p : Fin m × Fin m, if p.1 < p.2 then x p.1 + x p.2 else 0) +
          ∑ p : Fin m × Fin m, if p.2 < p.1 then x p.2 + x p.1 else 0 :=
        congrArg₂ (· + ·) hlo.symm hhi.symm
      _ = _ := ?_
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    rintro ⟨i, j⟩ _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_gt h]
    · simp [h]
    · simp [h, ne_of_gt h, not_lt_of_gt h, add_comm]
  have hoff : (∑ p : Fin m × Fin m, if p.1 ≠ p.2 then x p.1 + x p.2 else 0) =
      2 * ((m : ℝ) - 1) * ∑ i, x i := by
    calc
      _ = ∑ p : Fin m × Fin m,
          ((x p.1 + x p.2) - if p.1 = p.2 then x p.1 + x p.2 else 0) := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases h : p.1 = p.2 <;> simp [h]
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp [Fintype.sum_prod_type, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
  linarith

def centeredDegreeIntegrand {m : ℕ} (w : Edge m → Bool → ℚ) (x : Fin m → ℝ) : ℂ :=
  ∏ e : Edge m,
    ((w e true : ℂ) * Complex.exp ((Real.pi * (x e.1.1 - x e.1.2) : ℝ) * Complex.I) +
      (w e false : ℂ) * Complex.exp (-((Real.pi * (x e.1.1 - x e.1.2) : ℝ) : ℂ) * Complex.I))

private theorem edge_fourier_centering (a b : ℚ) (x y : ℝ) :
    (a : ℂ) * fourier 1 (x : UnitAddCircle) + (b : ℂ) * fourier 1 (y : UnitAddCircle) =
      Complex.exp ((Real.pi * (x + y) : ℝ) * Complex.I) *
        ((a : ℂ) * Complex.exp ((Real.pi * (x - y) : ℝ) * Complex.I) +
          (b : ℂ) * Complex.exp (-((Real.pi * (x - y) : ℝ) : ℂ) * Complex.I)) := by
  simp only [fourier_coe_apply, Int.cast_one, mul_one, Complex.ofReal_one, div_one]
  rw [mul_add]
  simp only [mul_left_comm _ (a : ℂ), mul_left_comm _ (b : ℂ), ← Complex.exp_add]
  congr 1 <;> congr 1 <;> push_cast <;> ring_nf

private theorem regular_character_cancels {m : ℕ} (hm : Odd m) (x : Fin m → ℝ) :
    UnitAddTorus.mFourier (fun _ => -((m / 2 : ℕ) : ℤ))
        (fun i => (x i : UnitAddCircle)) *
      (∏ e : Edge m, Complex.exp ((Real.pi * (x e.1.1 + x e.1.2) : ℝ) * Complex.I)) = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one, ← Complex.exp_sum, ← Complex.exp_add]
  have hhalf : (2 : ℝ) * (m / 2 : ℕ) = (m : ℝ) - 1 := by
    rcases hm with ⟨k, hk⟩
    have hh : m / 2 = k := by omega
    rw [hh, hk]
    push_cast
    ring
  have hs := sum_edge_endpoints x
  have hsc : (∑ e : Edge m, ((x e.1.1 : ℂ) + (x e.1.2 : ℂ))) =
      ((m : ℂ) - 1) * ∑ i, (x i : ℂ) := by exact_mod_cast hs
  have hhalfC : (2 : ℂ) * (m / 2 : ℕ) = (m : ℂ) - 1 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast,
      Complex.ofReal_sub, Complex.ofReal_one] using congrArg Complex.ofReal hhalf
  simp only [Int.cast_neg, Int.cast_natCast, Complex.ofReal_mul, Complex.ofReal_add]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hsc]
  convert Complex.exp_zero using 1
  congr 1
  linear_combination -(Real.pi : ℂ) * Complex.I * (∑ i, (x i : ℂ)) * hhalfC

theorem degreeFourierIntegrand_eq_centered {m : ℕ} (w : Edge m → Bool → ℚ)
    (hm : Odd m) (x : Fin m → ℝ) :
    degreeFourierIntegrand w (fun i => (x i : UnitAddCircle)) = centeredDegreeIntegrand w x := by
  unfold degreeFourierIntegrand centeredDegreeIntegrand
  simp_rw [edge_fourier_centering]
  rw [Finset.prod_mul_distrib, ← mul_assoc, regular_character_cancels hm, one_mul]

theorem centeredDegreeIntegrand_unrestricted {m : ℕ} (x : Fin m → ℝ) :
    centeredDegreeIntegrand (fun (_ : Edge m) (_ : Bool) => 1) x =
      (2 : ℂ) ^ Fintype.card (Edge m) *
        ∏ e : Edge m, (Real.cos (Real.pi * (x e.1.1 - x e.1.2)) : ℂ) := by
  unfold centeredDegreeIntegrand
  rw [← Finset.card_univ (α := Edge m)]
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  simp only [Rat.cast_one, one_mul, Complex.ofReal_cos, Complex.cos]
  ring

def forestCosineEdgeFactor {m : ℕ} (D : Finset (Fin m × Fin m)) (x : Fin m → ℝ)
    (e : Edge m) : ℂ :=
  if (e.1.1, e.1.2) ∈ D then
    if (e.1.2, e.1.1) ∈ D then 0
    else Complex.exp ((Real.pi * (x e.1.1 - x e.1.2) : ℝ) * Complex.I)
  else if (e.1.2, e.1.1) ∈ D then
    Complex.exp (-((Real.pi * (x e.1.1 - x e.1.2) : ℝ) : ℂ) * Complex.I)
  else 2 * (Real.cos (Real.pi * (x e.1.1 - x e.1.2)) : ℂ)

theorem centeredDegreeIntegrand_forced {m : ℕ} (D : Finset (Fin m × Fin m))
    (x : Fin m → ℝ) :
    centeredDegreeIntegrand (arcSetWeight D) x = ∏ e : Edge m, forestCosineEdgeFactor D x e := by
  unfold centeredDegreeIntegrand
  apply Finset.prod_congr rfl
  intro e _
  by_cases hf : (e.1.1, e.1.2) ∈ D <;> by_cases hr : (e.1.2, e.1.1) ∈ D <;>
    simp [forestCosineEdgeFactor, arcSetWeight, hf, hr, Complex.ofReal_cos, Complex.cos]
  ring

/-- An exact cosine-product ratio for the actual uniform regular law. Forced
edges retain their directed complex phase, and free edges contribute cosines. -/
theorem regularContainmentProbability_eq_centered_cube_ratio {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hm : Odd m) (hloop : ∀ i, (i, i) ∉ D)
    (a : Fin m → ℝ) :
    (regularContainmentProbability D hm : ℂ) =
      (∫ x : Fin m → ℝ in {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)},
        ∏ e : Edge m, forestCosineEdgeFactor D x e) /
      ((2 : ℂ) ^ Fintype.card (Edge m) *
        ∫ x : Fin m → ℝ in {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)},
          ∏ e : Edge m, (Real.cos (Real.pi * (x e.1.1 - x e.1.2)) : ℂ)) := by
  rw [regularContainmentProbability_eq_cube_ratio D hm hloop a]
  simp_rw [degreeFourierIntegrand_eq_centered _ hm, centeredDegreeIntegrand_forced,
    centeredDegreeIntegrand_unrestricted]
  rw [integral_const_mul]

end
end Wormald.FiniteModel

import Wormald.RegularCycleLimitReduction
import Wormald.RegularFourierAnchoring
import Wormald.GaussianQuotientVolume

/-! The uniform regular-containment estimate is reduced to the
actual normalized torus integral, including its empty-arc denominator.
This file retains a conditional analysis reduction; `UniformRegularTorusProof`
proves its integral input without further analytic or counting assumptions. -/

namespace Wormald.FiniteModel
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

local instance reductionCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance reductionCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def normalizedRegularTorusIntegral {m : ℕ} (D : Finset (Fin m × Fin m)) : ℂ :=
  ∫ x : UnitAddTorus (Fin m), normalizedRegularTorusIntegrand D x

def regularGaussianTorusVolume (m : ℕ) : ℝ :=
  Wormald.quotientGaussianVolume m / Real.pi ^ (m - 1)

theorem regularGaussianTorusVolume_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < regularGaussianTorusVolume m :=
  div_pos (Wormald.quotientGaussianVolume_pos hm) (pow_pos Real.pi_pos _)

theorem normalizedRegularTorusIntegral_eq_cube {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hm : Odd m) (a : Fin m → ℝ) :
    normalizedRegularTorusIntegral D =
      ∫ x : Fin m → ℝ in {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)},
        normalizedRegularIntegrand D x := by
  unfold normalizedRegularTorusIntegral
  rw [UnitAddTorus.integral_preimage _ a]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => normalizedRegularTorusIntegrand_coe D hm x

/-- The normalized torus estimate is exactly the anchored physical-angle
estimate divided by V_m; the π Jacobian cancels, with no extra factor. -/
theorem normalizedRegularTorusIntegral_div_volume_eq_physical {n : ℕ}
    (D : Finset (Fin (n + 1) × Fin (n + 1))) (hm : Odd (n + 1)) :
    normalizedRegularTorusIntegral D / (regularGaussianTorusVolume (n + 1) : ℂ) =
      (∫ θ in Wormald.centeredPiCube n,
        normalizedRegularPhysicalIntegrand D (Fin.snoc θ 0)) /
          (Wormald.quotientGaussianVolume (n + 1) : ℂ) := by
  have hpi : (Real.pi : ℂ) ^ n ≠ 0 := by
    exact_mod_cast pow_ne_zero n Real.pi_ne_zero
  unfold normalizedRegularTorusIntegral
  rw [integral_normalizedRegularTorus_eq_physical_anchored D hm]
  simp only [regularGaussianTorusVolume, Nat.add_sub_cancel,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.real_smul, Complex.ofReal_inv]
  field_simp

@[simp] theorem normalizedRegularIntegrand_empty {m : ℕ} (x : Fin m → ℝ) :
    normalizedRegularIntegrand (∅ : Finset (Fin m × Fin m)) x =
      ∏ e : Edge m, (Real.cos (Real.pi * (x e.1.1 - x e.1.2)) : ℂ) := by
  simp [normalizedRegularIntegrand, normalizedForestCosineFactor, freeCosineEdges]

/-- All factors two in the original finite conditional probability are
accounted for: only 2^{-card D} remains outside the normalized ratio. -/
theorem regularContainmentProbability_eq_normalizedTorus_ratio {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hm : Odd m)
    (hD : ∀ a b, (a, b) ∈ D → (b, a) ∉ D) :
    (regularContainmentProbability D hm : ℂ) = ((2 : ℂ) ^ D.card)⁻¹ *
      (normalizedRegularTorusIntegral D /
        normalizedRegularTorusIntegral (∅ : Finset (Fin m × Fin m))) := by
  rw [regularContainmentProbability_eq_normalized_cube_ratio D hm hD (fun _ => 0),
    normalizedRegularTorusIntegral_eq_cube D hm (fun _ => 0),
    normalizedRegularTorusIntegral_eq_cube ∅ hm (fun _ => 0)]
  simp only [normalizedRegularIntegrand_empty]

theorem legalPartialPermutationArcs_empty (m : ℕ) :
    LegalPartialPermutationArcs (∅ : Finset (Fin m × Fin m)) := by
  constructor
  · simp
  constructor
  · simpa only [Finset.coe_empty] using Set.injOn_empty (Prod.fst : Fin m × Fin m → Fin m)
  constructor
  · simpa only [Finset.coe_empty] using Set.injOn_empty (Prod.snd : Fin m × Fin m → Fin m)
  · simp

@[simp] theorem internalInOutCount_empty (m : ℕ) :
    internalInOutCount (∅ : Finset (Fin m × Fin m)) = 0 := by
  simp [internalInOutCount]

/-- The exact integral main term that remains to be proved uniformly.
The volume includes the physical-angle Jacobian π^{-(m-1)}. -/
def UniformRegularTorusMainTerm : Prop :=
  ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧ (∀ k, 0 ≤ η k) ∧
    ∀ᶠ k : ℕ in atTop, ∀ D : Finset (Fin (2 * k + 1) × Fin (2 * k + 1)),
      LegalPartialPermutationArcs D →
        ‖normalizedRegularTorusIntegral D / (regularGaussianTorusVolume (2 * k + 1) : ℂ) -
          ((Real.exp (-(1 / 2 : ℝ)) *
            Real.exp ((internalInOutCount D : ℝ) / (2 * k + 1 : ℕ)) : ℝ) : ℂ)‖ ≤ η k

theorem complex_ratio_exp_error_le (A B : ℂ) (c t η : ℝ)
    (hc : 0 < c) (ht : 0 ≤ t) (hη0 : 0 ≤ η) (hηc : η ≤ c / 2)
    (hA : ‖A - ((c * Real.exp t : ℝ) : ℂ)‖ ≤ η)
    (hB : ‖B - (c : ℂ)‖ ≤ η) :
    ‖A / B * (Real.exp (-t) : ℂ) - 1‖ ≤ 4 * η / c := by
  have he0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hBn : c / 2 ≤ ‖B‖ := by
    have hh := norm_sub_norm_le (c : ℂ) B
    rw [norm_sub_rev] at hh
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at hh
    linarith
  have hBp : 0 < ‖B‖ := lt_of_lt_of_le (by linarith : 0 < c / 2) hBn
  have hBne : B ≠ 0 := norm_pos_iff.mp hBp
  have hexp : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have hdiff : A * (Real.exp (-t) : ℂ) - B =
      (A - ((c * Real.exp t : ℝ) : ℂ)) * (Real.exp (-t) : ℂ) - (B - (c : ℂ)) := by
    push_cast
    have he := congrArg (fun r : ℝ => (r : ℂ)) hexp
    push_cast at he
    linear_combination c * he
  have hnum : ‖A * (Real.exp (-t) : ℂ) - B‖ ≤ 2 * η := by
    rw [hdiff]
    calc
      _ ≤ ‖(A - ((c * Real.exp t : ℝ) : ℂ)) * (Real.exp (-t) : ℂ)‖ + ‖B - (c : ℂ)‖ := norm_sub_le _ _
      _ = ‖A - ((c * Real.exp t : ℝ) : ℂ)‖ * Real.exp (-t) + ‖B - (c : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he0]
      _ ≤ η * Real.exp (-t) + η := add_le_add (mul_le_mul_of_nonneg_right hA he0) hB
      _ ≤ 2 * η := by nlinarith
  have hquot : A / B * (Real.exp (-t) : ℂ) - 1 = (A * (Real.exp (-t) : ℂ) - B) / B := by
    field_simp
  rw [hquot, norm_div]
  calc
    _ ≤ (2 * η) / ‖B‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (2 * η) / (c / 2) := div_le_div_of_nonneg_left (by positivity) (by linarith) hBn
    _ = 4 * η / c := by ring

theorem uniformRegularContainmentAsymptotic_of_torusMainTerm
    (hmain : UniformRegularTorusMainTerm) : UniformRegularContainmentAsymptotic := by
  obtain ⟨η, hη, hη0, hest⟩ := hmain
  let c : ℝ := Real.exp (-(1 / 2 : ℝ))
  have hc : 0 < c := Real.exp_pos _
  refine ⟨fun k => 4 * η k / c, ?_,
    fun k => div_nonneg (mul_nonneg (by norm_num) (hη0 k)) hc.le, ?_⟩
  · simpa only [mul_zero, zero_div] using (hη.const_mul 4).div_const c
  filter_upwards [hest, hη.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < c / 2)),
    eventually_ge_atTop 1] with k hk hkη hk1 D hD
  have hm : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hvolume : regularGaussianTorusVolume (2 * k + 1) ≠ 0 :=
    (regularGaussianTorusVolume_pos (by omega)).ne'
  have hvC : (regularGaussianTorusVolume (2 * k + 1) : ℂ) ≠ 0 := by exact_mod_cast hvolume
  have hzero := hk ∅ (legalPartialPermutationArcs_empty _)
  simp only [internalInOutCount_empty, Nat.cast_zero, zero_div, Real.exp_zero, mul_one] at hzero
  have hDmain := hk D hD
  have ht : 0 ≤ (internalInOutCount D : ℝ) / (2 * k + 1 : ℕ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbound := complex_ratio_exp_error_le
    (normalizedRegularTorusIntegral D / (regularGaussianTorusVolume (2 * k + 1) : ℂ))
    (normalizedRegularTorusIntegral (∅ : Finset (Fin (2 * k + 1) × Fin (2 * k + 1))) /
      (regularGaussianTorusVolume (2 * k + 1) : ℂ))
    c ((internalInOutCount D : ℝ) / (2 * k + 1 : ℕ)) (η k)
    hc ht (hη0 k) hkη.le hDmain hzero
  rw [div_div_div_cancel_right₀ hvC] at hbound
  have hratio := regularContainmentProbability_eq_normalizedTorus_ratio D hm hD.2.2.2
  have htwo : (2 : ℂ) ^ D.card ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcancel : (2 : ℂ) ^ D.card * (regularContainmentProbability D hm : ℂ) =
      normalizedRegularTorusIntegral D /
        normalizedRegularTorusIntegral (∅ : Finset (Fin (2 * k + 1) × Fin (2 * k + 1))) := by
    rw [hratio, ← mul_assoc, mul_inv_cancel₀ htwo, one_mul]
  rw [← hcancel] at hbound
  have hexp : -((internalInOutCount D : ℝ) / (2 * k + 1 : ℕ)) =
      -(internalInOutCount D : ℝ) / (2 * k + 1 : ℕ) := by ring
  rw [hexp] at hbound
  have hreal : (((2 : ℝ) ^ D.card * (regularContainmentProbability D hm : ℝ) *
      Real.exp (-(internalInOutCount D : ℝ) / (2 * k + 1 : ℕ)) - 1 : ℝ) : ℂ) =
      (2 : ℂ) ^ D.card * (regularContainmentProbability D hm : ℂ) *
        (Real.exp (-(internalInOutCount D : ℝ) / (2 * k + 1 : ℕ)) : ℂ) - 1 := by
    push_cast
    rfl
  rw [← hreal, Complex.norm_real, Real.norm_eq_abs] at hbound
  exact hbound

/-- Only the actual uniform integral estimate remains as an input to C2. -/
theorem conjectureTwoWithModelLimits_of_uniform_torus_mainTerm
    (hmain : UniformRegularTorusMainTerm) : conjectureTwoWithModelLimits :=
  conjectureTwoWithModelLimits_of_uniform_containment
    (uniformRegularContainmentAsymptotic_of_torusMainTerm hmain)

theorem conjectureTwo_exact_of_uniform_torus_mainTerm
    (hmain : UniformRegularTorusMainTerm) :
    ∃ r : ℕ → ℝ,
      (∀ j, Tendsto (regularCarouselNormalized (2 * j + 3)) atTop (𝓝 (r j))) ∧
      Tendsto r atTop (𝓝 (Real.cosh 1 / Real.cos 1)) :=
  conjectureTwo_exact_of_uniform_containment
    (uniformRegularContainmentAsymptotic_of_torusMainTerm hmain)

end
end Wormald.FiniteModel

import Wormald.LocalGaussianIntegralError
import Wormald.GaussianGraphMainTerm

namespace Wormald
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

def centralMainError (m : ℕ) : ℝ :=
  Real.sqrt (Real.exp 4) *
    (2 * centralGaussianError m + Real.sqrt (quarticFactorSquareError m) +
      Real.sqrt (centralGaussianTail m)) +
        Real.exp (-(1 / 2 : ℝ)) * Real.exp 1 * (32 / (m : ℝ))

theorem centralMainError_nonneg (m : ℕ) : 0 ≤ centralMainError m := by
  unfold centralMainError centralGaussianError
  positivity

theorem tendsto_centralMainError : Tendsto centralMainError atTop (𝓝 0) := by
  unfold centralMainError
  have hq := Real.continuous_sqrt.tendsto 0 |>.comp tendsto_quarticFactorSquareError
  have ht := Real.continuous_sqrt.tendsto 0 |>.comp tendsto_centralGaussianTail
  have hi : Tendsto (fun m : ℕ => 32 / (m : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (32 : ℝ))
  have h := (((tendsto_centralGaussianError.const_mul 2).add hq).add ht).const_mul
    (Real.sqrt (Real.exp 4))
  simpa only [Function.comp_apply, Real.sqrt_zero, mul_zero,
    add_zero, zero_add] using h.add (hi.const_mul (Real.exp (-(1 / 2 : ℝ)) * Real.exp 1))

namespace FiniteModel
open Matrix

theorem integrableOn_scaledRegularFactor_central {m : ℕ} (hm : 16 ≤ m)
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hloop : ∀ e ∈ D, e.1 ≠ e.2)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D)
    (herror : centralGaussianError m ≤ 1) (j : Fin m) :
    IntegrableOn (scaledRegularFactor D) (gaussianCentralWindow j (centralGaussianRadius m))
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  let G := partialPermutationGaussianGraphData D hloop hs ht
  have hw := memLp_graphGaussianWeight_centralScale hm G
  have hdom := ((hw.norm.integrable (by norm_num)).const_mul (2 * centralGaussianError m + 1)).restrict
    (s := gaussianCentralWindow j (centralGaussianRadius m))
  apply hdom.mono' (continuous_scaledRegularFactor D hD).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem (measurableSet_gaussianCentralWindow j (centralGaussianRadius m))]
    with x hx
  have he := norm_scaledRegularFactor_central_error (by omega) D hD hloop hs ht herror j x hx
  have hq := norm_graphQuarticWeight_le G x
  calc
    ‖scaledRegularFactor D x‖ = ‖(scaledRegularFactor D x - graphQuarticWeight G x) +
        graphQuarticWeight G x‖ := by rw [sub_add_cancel]
    _ ≤ ‖scaledRegularFactor D x - graphQuarticWeight G x‖ + ‖graphQuarticWeight G x‖ :=
      norm_add_le _ _
    _ ≤ (2 * centralGaussianError m + 1) * ‖graphGaussianWeight G (1 / (m : ℝ)) x‖ := by
      linarith

/-- A uniform main-term estimate for the actual local integrand under its
growing-dimensional Gaussian law. Every error on the right tends to zero. -/
theorem norm_gaussianCentralMainTerm_error_le {m : ℕ} (hm : 16 ≤ m)
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hloop : ∀ e ∈ D, e.1 ≠ e.2)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D)
    (herror : centralGaussianError m ≤ 1) (j : Fin m) :
    ‖(∫ x in gaussianCentralWindow j (centralGaussianRadius m), scaledRegularFactor D x
      ∂Measure.pi (fun _ => gaussianReal 0 1)) -
        (Real.exp (-(1 / 2 : ℝ)) * Real.exp (internalInOutCount D / (m : ℝ)) : ℂ)‖ ≤
      centralMainError m := by
  let G := partialPermutationGaussianGraphData D hloop hs ht
  let μ := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let A := gaussianCentralWindow j (centralGaussianRadius m)
  let IF := ∫ x in A, scaledRegularFactor D x ∂μ
  let IQA := ∫ x in A, graphQuarticWeight G x ∂μ
  let IQ := ∫ x, graphQuarticWeight G x ∂μ
  let c : ℂ := Real.exp (-(1 / 2 : ℝ))
  let L : ℂ := Real.exp (graphGaussianLogFactor G (1 / (m : ℝ)))
  let J : ℂ := Real.exp (G.joinCount / (m : ℝ))
  have hA := measurableSet_gaussianCentralWindow j (centralGaussianRadius m)
  have hqi := (memLp_graphQuarticWeight hm G).integrable (by norm_num)
  have hfi := integrableOn_scaledRegularFactor_central hm D hD hloop hs ht herror j
  have ha : ‖IF - IQA‖ ≤ (2 * centralGaussianError m) * Real.sqrt (Real.exp 4) := by
    rw [show IF - IQA = ∫ x in A, (scaledRegularFactor D x - graphQuarticWeight G x) ∂μ
      from (integral_sub hfi hqi.restrict).symm]
    exact norm_integral_scaledRegularFactor_central_error hm D hD hloop hs ht herror j
  have hb : ‖IQA - IQ‖ ≤ Real.sqrt (Real.exp 4) * Real.sqrt (centralGaussianTail m) := by
    have heq : IQA - IQ = -(∫ x in Aᶜ, graphQuarticWeight G x ∂μ) := by
      dsimp [IQA, IQ]
      rw [← integral_add_compl hA hqi]
      ring
    rw [heq, norm_neg]
    exact norm_integral_graphQuarticWeight_outside_le hm G j
  have hc : ‖IQ - c * L‖ ≤ Real.sqrt (Real.exp 4) * Real.sqrt (quarticFactorSquareError m) := by
    simpa only [Complex.ofReal_mul] using norm_integral_graphQuarticWeight_mean_error hm G
  have hd : ‖c * (L - J)‖ ≤
      Real.exp (-(1 / 2 : ℝ)) * Real.exp 1 * (32 / (m : ℝ)) := by
    have hm16 : 16 ≤ (m : ℝ) := by exact_mod_cast hm
    have hm0 : 0 < (m : ℝ) := by linarith
    have h := norm_integral_graphGaussianWeight_main_error_le hm G
    rw [integral_graphGaussianWeight G _ (by positivity)
      (by rw [mul_one_div, div_lt_one hm0]; linarith)] at h
    rw [norm_mul, show ‖c‖ = Real.exp (-(1 / 2 : ℝ)) by
      dsimp [c]; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]]
    exact (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq (by ring)
  change ‖IF - c * J‖ ≤ _
  rw [show IF - c * J = ((IF - IQA) + (IQA - IQ)) + (IQ - c * L) + c * (L - J) by ring]
  calc
    _ ≤ ‖((IF - IQA) + (IQA - IQ)) + (IQ - c * L)‖ + ‖c * (L - J)‖ := norm_add_le _ _
    _ ≤ (‖(IF - IQA) + (IQA - IQ)‖ + ‖IQ - c * L‖) + ‖c * (L - J)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((‖IF - IQA‖ + ‖IQA - IQ‖) + ‖IQ - c * L‖) + ‖c * (L - J)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (((2 * centralGaussianError m) * Real.sqrt (Real.exp 4) +
        Real.sqrt (Real.exp 4) * Real.sqrt (centralGaussianTail m)) +
        Real.sqrt (Real.exp 4) * Real.sqrt (quarticFactorSquareError m)) +
          Real.exp (-(1 / 2 : ℝ)) * Real.exp 1 * (32 / (m : ℝ)) :=
      add_le_add (add_le_add (add_le_add ha hb) hc) hd
    _ = _ := by unfold centralMainError; ring

end FiniteModel
end
end Wormald

import Wormald.GaussianCentralWindow
import Wormald.RegularCentralWindow

namespace Wormald.FiniteModel
noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem continuous_normalizedRegularIntegrand_of_no_opposite {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) :
    Continuous (normalizedRegularIntegrand D) := by
  have hfun := funext (normalizedRegularIntegrand_eq_phase_product D hD)
  rw [hfun]
  unfold dotProduct
  fun_prop

theorem continuous_scaledRegularFactor {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) :
    Continuous (scaledRegularFactor D) := by
  have hc := continuous_normalizedRegularIntegrand_of_no_opposite D hD
  unfold scaledRegularFactor completeSquareEnergy
  fun_prop

theorem norm_scaledRegularFactor_central_error {m : ℕ} (hm : 1 ≤ m)
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hloop : ∀ e ∈ D, e.1 ≠ e.2)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D)
    (herror : centralGaussianError m ≤ 1) (j : Fin m) (x : Fin m → ℝ)
    (hx : x ∈ gaussianCentralWindow j (centralGaussianRadius m)) :
    ‖scaledRegularFactor D x - graphQuarticWeight
      (partialPermutationGaussianGraphData D hloop hs ht) x‖ ≤
        (2 * centralGaussianError m) *
          ‖graphGaussianWeight (partialPermutationGaussianGraphData D hloop hs ht)
            (1 / (m : ℝ)) x‖ := by
  let G := partialPermutationGaussianGraphData D hloop hs ht
  obtain ⟨e, he, hfact⟩ := exists_scaledRegularFactor_central_error hm D hD hloop hs ht x
    (gaussianCentralWindow_pair_bound j (centralGaussianRadius m) x hx)
  have he1 : |e| ≤ 1 := he.trans herror
  have hexp : ‖(Real.exp e : ℂ) - 1‖ ≤ 2 * centralGaussianError m := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (Real.abs_exp_sub_one_le he1).trans
      (mul_le_mul_of_nonneg_left he (by norm_num))
  have hdiff : scaledRegularFactor D x - graphQuarticWeight G x =
      graphQuarticWeight G x * ((Real.exp e : ℂ) - 1) := by
    rw [hfact]
    dsimp [graphQuarticWeight, G]
    ring
  rw [hdiff, norm_mul]
  calc
    _ ≤ ‖graphGaussianWeight G (1 / (m : ℝ)) x‖ * (2 * centralGaussianError m) :=
      mul_le_mul (norm_graphQuarticWeight_le G x) hexp (norm_nonneg _)
        (norm_nonneg _)
    _ = _ := by ring

theorem norm_integral_scaledRegularFactor_central_error {m : ℕ} (hm : 16 ≤ m)
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hloop : ∀ e ∈ D, e.1 ≠ e.2)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D)
    (herror : centralGaussianError m ≤ 1) (j : Fin m) :
    ‖∫ x in gaussianCentralWindow j (centralGaussianRadius m),
      (scaledRegularFactor D x - graphQuarticWeight
        (partialPermutationGaussianGraphData D hloop hs ht) x)
          ∂Measure.pi (fun _ => gaussianReal 0 1)‖ ≤
      (2 * centralGaussianError m) * Real.sqrt (Real.exp 4) := by
  let G := partialPermutationGaussianGraphData D hloop hs ht
  have hm16 : 16 ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have hw := memLp_graphGaussianWeight G (1 / (m : ℝ)) (by positivity)
    (by rw [mul_one_div, div_lt_one hm0]; linarith)
  have hnonneg : 0 ≤ 2 * centralGaussianError m := by
    unfold centralGaussianError
    positivity
  have h := norm_setIntegral_le_mul_sqrt_L2 hw
    (((continuous_scaledRegularFactor D hD).sub (continuous_graphQuarticWeight G)).aestronglyMeasurable)
    (measurableSet_gaussianCentralWindow j (centralGaussianRadius m))
    (2 * centralGaussianError m) hnonneg
    (fun x hx => norm_scaledRegularFactor_central_error (by omega) D hD hloop hs ht herror j x hx)
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (graphGaussianWeight_L2_le hm G)) hnonneg)

end
end Wormald.FiniteModel

import Wormald.AnchoredPhaseGeometry
import Mathlib.Analysis.SpecificLimits.Normed

namespace Wormald

noncomputable section
open Matrix MeasureTheory Filter
open scoped Topology BigOperators

def anchoredRealCycleIntegrand {d : ℕ} (T : Tournament (d + 1)) (m : ℕ)
    (t : Fin d → ℝ) : ℂ :=
  UnitAddTorus.mFourier (fun _ => -(m : ℤ)) (fun i => (t i : UnitAddCircle)) *
    ((T.criticalTransition * Matrix.diagonal (anchoredRealPhase t)) ^ ((d + 1) * m)).trace

theorem norm_mFourier_apply {ι : Type*} [Fintype ι] (k : ι → ℤ) (x : UnitAddTorus ι) :
    ‖UnitAddTorus.mFourier k x‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, Finset.prod_const_one]

theorem norm_anchoredRealCycleIntegrand {d : ℕ} (T : Tournament (d + 1)) (m : ℕ) (t : Fin d → ℝ) :
    ‖anchoredRealCycleIntegrand T m t‖ =
      ‖((T.criticalTransition * Matrix.diagonal (anchoredRealPhase t)) ^ ((d + 1) * m)).trace‖ := by
  rw [anchoredRealCycleIntegrand, norm_mul, norm_mFourier_apply, one_mul]

/-- The finite Fourier integral over any far-region subset is exponentially
small, uniformly in the original block size. -/
theorem Tournament.anchored_far_integral_bound {d : ℕ} (T : Tournament (d + 1))
    (hT : T.Regular) (a : ℝ) (ha : 0 < a)
    (S : Set (Fin d → ℝ)) (hS : S ⊆ phaseFarRegion d a) :
    ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ m : ℕ,
      ‖∫ t in S, anchoredRealCycleIntegrand T m t‖ ≤
        (((d + 1 : ℕ) : ℝ) * volume.real S) * s ^ (((d + 1) * m) / 2) := by
  rcases T.criticalTransition_real_phase_far_trace_decay hT a ha with ⟨s, hs0, hs1, htrace⟩
  have hfinite : volume S < ⊤ :=
    (measure_mono hS).trans_lt (isCompact_phaseFarRegion d a).measure_lt_top
  refine ⟨s, hs0, hs1, ?_⟩
  intro m
  have hnorm : ‖∫ t in S, anchoredRealCycleIntegrand T m t‖ ≤
      (((d + 1 : ℕ) : ℝ) * s ^ (((d + 1) * m) / 2)) * volume.real S := by
    apply norm_setIntegral_le_of_norm_le_const_ae' hfinite
    exact Filter.Eventually.of_forall (fun t ht => by
      rw [norm_anchoredRealCycleIntegrand]
      exact htrace t (hS ht) ((d + 1) * m))
  convert hnorm using 1
  ring

/-- The Gaussian normalization `(sqrt m)^k` cannot offset the proved far-region
exponential decay. The dimension condition covers all original d≥3 bases. -/
theorem Tournament.anchored_far_integral_sqrt_normalized_tendsto_zero {d : ℕ}
    (T : Tournament (d + 1)) (hd : 1 ≤ d) (hT : T.Regular)
    (a : ℝ) (ha : 0 < a) (S : Set (Fin d → ℝ)) (hS : S ⊆ phaseFarRegion d a) (k : ℕ) :
    Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ) : ℂ) ^ k *
      ∫ t in S, anchoredRealCycleIntegrand T m t) atTop (𝓝 0) := by
  rcases T.anchored_far_integral_bound hT a ha S hS with ⟨s, hs0, hs1, hbound⟩
  let C : ℝ := ((d + 1 : ℕ) : ℝ) * volume.real S
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  have hpower (m : ℕ) : s ^ (((d + 1) * m) / 2) ≤ s ^ m := by
    have hmul : 2 * m ≤ (d + 1) * m := Nat.mul_le_mul_right m (by omega)
    exact pow_le_pow_of_le_one hs0 hs1.le (by omega)
  have hnorm (m : ℕ) : ‖∫ t in S, anchoredRealCycleIntegrand T m t‖ ≤ C * s ^ m :=
    (hbound m).trans (mul_le_mul_of_nonneg_left (hpower m) hC)
  have hlim : Tendsto (fun m : ℕ => C * ((m : ℝ) ^ k * s ^ m)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_const_mul_const_pow_of_lt_one k hs0 hs1)
  have hweighted : Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ)) ^ k *
      ‖∫ t in S, anchoredRealCycleIntegrand T m t‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun m =>
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _))) _ hlim
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hsqrt : Real.sqrt (m : ℝ) ≤ m := Real.sqrt_le_self_iff.mpr (Or.inr hmR)
    have hsqrtpow := pow_le_pow_left₀ (Real.sqrt_nonneg (m : ℝ)) hsqrt k
    calc
      _ ≤ (Real.sqrt (m : ℝ)) ^ k * (C * s ^ m) :=
        mul_le_mul_of_nonneg_left (hnorm m) (pow_nonneg (Real.sqrt_nonneg _) _)
      _ ≤ (m : ℝ) ^ k * (C * s ^ m) :=
        mul_le_mul_of_nonneg_right hsqrtpow (mul_nonneg hC (pow_nonneg hs0 _))
      _ = _ := by ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using hweighted

end
end Wormald

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Pointwise Gaussian scaling from a local quadratic remainder. -/

namespace Wormald
noncomputable section
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendsto_invSqrt_smul (x : E) :
    Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ))⁻¹ • x) atTop (𝓝 0) := by
  have hinv : Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  simpa using hinv.smul_const x

theorem nat_mul_norm_invSqrt_smul_sq (m : ℕ) (hm : 0 < m) (x : E) :
    (m : ℝ) * ‖(Real.sqrt (m : ℝ))⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  field_simp

theorem nat_mul_quadratic_invSqrt_smul (Q : E → ℝ)
    (hQ : ∀ (a : ℝ) x, Q (a • x) = a ^ 2 * Q x) (m : ℕ) (hm : 0 < m) (x : E) :
    (m : ℝ) * Q ((Real.sqrt (m : ℝ))⁻¹ • x) = Q x := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  rw [hQ, inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  field_simp

theorem tendsto_nat_mul_phase_invSqrt (phase : E → ℂ) (Q : E → ℝ) (err : E → ℂ)
    (hQ : ∀ (a : ℝ) x, Q (a • x) = a ^ 2 * Q x)
    (herr : Tendsto err (𝓝 0) (𝓝 0))
    (hphase : ∀ᶠ y in 𝓝 (0 : E),
      phase y = -(Q y : ℂ) + ((‖y‖ ^ 2 : ℝ) : ℂ) * err y) (x : E) :
    Tendsto (fun m : ℕ => (m : ℂ) * phase ((Real.sqrt (m : ℝ))⁻¹ • x))
      atTop (𝓝 (-(Q x : ℂ))) := by
  have hy := tendsto_invSqrt_smul x
  have hlim' : Tendsto (fun m : ℕ => -(Q x : ℂ) +
      ((‖x‖ ^ 2 : ℝ) : ℂ) * err ((Real.sqrt (m : ℝ))⁻¹ • x))
      atTop (𝓝 (-(Q x : ℂ))) := by
    simpa only [mul_zero, add_zero, Function.comp_def] using
      ((herr.comp hy).const_mul ((‖x‖ ^ 2 : ℝ) : ℂ)).const_add (-(Q x : ℂ))
  apply hlim'.congr'
  filter_upwards [hy.eventually hphase, eventually_ge_atTop 1] with m hform hm
  have hq : (m : ℂ) * (Q ((Real.sqrt (m : ℝ))⁻¹ • x) : ℂ) = (Q x : ℂ) := by
    exact_mod_cast nat_mul_quadratic_invSqrt_smul Q hQ m (by omega) x
  have hn : (m : ℂ) * ((‖(Real.sqrt (m : ℝ))⁻¹ • x‖ ^ 2 : ℝ) : ℂ) =
      ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast nat_mul_norm_invSqrt_smul_sq m (by omega) x
  symm
  rw [hform]
  calc
    _ = -((m : ℂ) * (Q ((Real.sqrt (m : ℝ))⁻¹ • x) : ℂ)) +
      ((m : ℂ) * ((‖(Real.sqrt (m : ℝ))⁻¹ • x‖ ^ 2 : ℝ) : ℂ)) *
        err ((Real.sqrt (m : ℝ))⁻¹ • x) := by ring
    _ = _ := by rw [hq, hn]

theorem tendsto_exp_nat_mul_phase_invSqrt (phase : E → ℂ) (Q : E → ℝ) (err : E → ℂ)
    (hQ : ∀ (a : ℝ) x, Q (a • x) = a ^ 2 * Q x)
    (herr : Tendsto err (𝓝 0) (𝓝 0))
    (hphase : ∀ᶠ y in 𝓝 (0 : E),
      phase y = -(Q y : ℂ) + ((‖y‖ ^ 2 : ℝ) : ℂ) * err y) (x : E) :
    Tendsto (fun m : ℕ => Complex.exp ((m : ℂ) * phase ((Real.sqrt (m : ℝ))⁻¹ • x)))
      atTop (𝓝 (Complex.exp (-(Q x : ℂ)))) :=
  Complex.continuous_exp.continuousAt.tendsto.comp
    (tendsto_nat_mul_phase_invSqrt phase Q err hQ herr hphase x)

omit [NormedSpace ℝ E] in
theorem exists_quadratic_phase_error (phase : E → ℂ) (Q : E → ℝ)
    (hsmall : (fun y => phase y + (Q y : ℂ)) =o[𝓝 (0 : E)]
      (fun y => ((‖y‖ ^ 2 : ℝ) : ℂ))) :
    ∃ err : E → ℂ, Tendsto err (𝓝 0) (𝓝 0) ∧
      ∀ᶠ y in 𝓝 (0 : E), phase y = -(Q y : ℂ) + ((‖y‖ ^ 2 : ℝ) : ℂ) * err y := by
  obtain ⟨err, herr, heq⟩ := hsmall.exists_eq_mul
  refine ⟨err, herr, heq.mono ?_⟩
  intro y hy
  change phase y + (Q y : ℂ) = err y * ((‖y‖ ^ 2 : ℝ) : ℂ) at hy
  calc
    phase y = (phase y + (Q y : ℂ)) - (Q y : ℂ) := by ring
    _ = err y * ((‖y‖ ^ 2 : ℝ) : ℂ) - (Q y : ℂ) := by rw [hy]
    _ = _ := by ring

theorem tendsto_nat_mul_phase_invSqrt_of_isLittleO (phase : E → ℂ) (Q : E → ℝ)
    (hQ : ∀ (a : ℝ) x, Q (a • x) = a ^ 2 * Q x)
    (hsmall : (fun y => phase y + (Q y : ℂ)) =o[𝓝 (0 : E)]
      (fun y => ((‖y‖ ^ 2 : ℝ) : ℂ))) (x : E) :
    Tendsto (fun m : ℕ => (m : ℂ) * phase ((Real.sqrt (m : ℝ))⁻¹ • x))
      atTop (𝓝 (-(Q x : ℂ))) := by
  obtain ⟨err, herr, heq⟩ := exists_quadratic_phase_error phase Q hsmall
  exact tendsto_nat_mul_phase_invSqrt phase Q err hQ herr heq x

end
end Wormald

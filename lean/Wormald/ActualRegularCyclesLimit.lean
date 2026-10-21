import Wormald.LocalFourierIntegral
import Wormald.GaussianSpectralConstant

/-! The exact finite Hamilton-cycle expectation converges to the literal
spectral determinant ratio. The proof combines its exact Fourier integral,
the actual local spectral branch, Gaussian scaling, and decay away from zero. -/

namespace Wormald
noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators Topology

theorem Tournament.tendsto_sqrt_mul_anchored_integral {n : ℕ} (hn : 0 < n)
    (T : Tournament (n + 1)) (hT : T.Regular) :
    Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ) : ℂ) ^ n *
      ∫ t in unitPhaseCubeIoc n, anchoredRealCycleIntegrand T m t) atTop
        (𝓝 ((Real.sqrt (2 * Real.pi) ^ n / Real.sqrt T.periodicCovariance.det : ℝ) : ℂ)) := by
  obtain ⟨rL, hrL, hL⟩ := T.exists_periodicSpectralLaplace_radius hn hT
  obtain ⟨rR, hrR, hR⟩ := T.exists_anchoredResidual_local_integral_decay hT
  obtain ⟨rD, hrD, hD⟩ := T.exists_anchored_local_integral_decomposition hT
  let a : ℝ := min (1 / 2) (min rL (min rR rD))
  have ha : 0 < a := lt_min (by norm_num) (lt_min hrL (lt_min hrR hrD))
  have haH : a ≤ 1 / 2 := min_le_left _ _
  have haL : a ≤ rL := (min_le_right _ _).trans (min_le_left _ _)
  have haR : a ≤ rR := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have haD : a ≤ rD := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hlocal : Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ) : ℂ) ^ n *
      ∫ t : Fin n → ℝ, localComplexPeak (T.periodicSpectralPhase hT) a m t) atTop
        (𝓝 ((Real.sqrt (2 * Real.pi) ^ n / Real.sqrt T.periodicCovariance.det : ℝ) : ℂ)) := by
    simpa only [Complex.real_smul, Complex.ofReal_pow] using hL a ha haL
  have hres := hR a ha haR n
  have hfar := T.anchored_realCube_far_sqrt_normalized_tendsto_zero (by omega) hT a ha n
  have hsum := (hlocal.add hres).add hfar
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  rw [anchored_realCubeIntegral_eq_local_add_far T m a haH, hD a ha haD m hm]
  ring

namespace FiniteModel

/-- The original independent internal-block law, with no analytic assumption
on the expectation and no substitute counting statistic. -/
theorem tendsto_normalizedExpectedCycles_regular_succ {n : ℕ} (hn : 0 < n)
    (base : Orientation (n + 1)) (hT : (toTournament base).Regular) :
    Tendsto (normalizedExpectedCycles base) atTop (𝓝 (toTournament base).spectralRatio.re) := by
  let T := toTournament base
  have hfac : Tendsto
      (fun m : ℕ => ((factorialPrefactor (n + 1) m / Real.sqrt (m : ℝ) ^ n : ℝ) : ℂ))
      atTop (𝓝 ((Real.sqrt (2 * Real.pi) ^ n / Real.sqrt ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)) :=
    tendsto_ofReal_iff.mpr (tendsto_factorialPrefactor_div_sqrt n)
  have hprod := hfac.mul (T.tendsto_sqrt_mul_anchored_integral hn hT)
  have hconst :
      ((Real.sqrt (2 * Real.pi) ^ n / Real.sqrt ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      ((Real.sqrt (2 * Real.pi) ^ n / Real.sqrt T.periodicCovariance.det : ℝ) : ℂ) =
        (T.spectralRatio.re : ℂ) := by
    rw [← Complex.ofReal_mul]
    have heq := T.gaussianStirlingProduct_eq_spectralRatio hT
    simpa only [Tournament.gaussianStirlingProduct, Nat.cast_add, Nat.cast_one] using
      congrArg Complex.ofReal heq
  rw [hconst] at hprod
  apply tendsto_ofReal_iff.mp
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 3] with m hm
  have hm0 : 0 < m := by omega
  have hN : 3 ≤ (n + 1) * m := (show 3 ≤ m from hm).trans
    (Nat.le_mul_of_pos_left m (Nat.succ_pos n))
  rw [normalizedExpectedCycles_eq_criticalRealCubeIntegral base m hN]
  have hs : (Real.sqrt (m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < m by exact_mod_cast hm0)).ne'
  push_cast
  field_simp
  rfl

theorem tendsto_normalizedExpectedCycles_regular {d : ℕ} (hd : 3 ≤ d)
    (base : Orientation d) (hT : (toTournament base).Regular) :
    Tendsto (normalizedExpectedCycles base) atTop (𝓝 (toTournament base).spectralRatio.re) := by
  cases d with
  | zero => omega
  | succ n => exact tendsto_normalizedExpectedCycles_regular_succ (by omega) base hT

end FiniteModel
end
end Wormald

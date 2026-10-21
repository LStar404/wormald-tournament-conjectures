import Wormald.LocalFourierDecomposition

namespace Wormald

noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem integral_localComplexPeak_eq_ball {d : ℕ} (phase : (Fin d → ℝ) → ℂ)
    (a : ℝ) (m : ℕ) :
    (∫ t : Fin d → ℝ, localComplexPeak phase a m t) =
      ∫ t in Metric.ball 0 a, Complex.exp ((m : ℂ) * phase t) := by
  have hfun : localComplexPeak phase a m =
      (Metric.ball 0 a).indicator (fun t => Complex.exp ((m : ℂ) * phase t)) := by
    ext t
    simp [localComplexPeak, Set.indicator, Metric.mem_ball, dist_zero_right]
  rw [hfun, integral_indicator Metric.isOpen_ball.measurableSet]

/-- The same sufficiently small ball works for every positive block size.
All three integrands are integrable there; the remainder is identified with
the difference of the continuous original integrand and the local peak. -/
theorem Tournament.exists_anchored_local_integral_decomposition {d : ℕ}
    (T : Tournament (d + 1)) (hT : T.Regular) :
    ∃ r : ℝ, 0 < r ∧ ∀ a : ℝ, 0 < a → a ≤ r → ∀ m : ℕ, 0 < m →
      (∫ t in Metric.ball 0 a, anchoredRealCycleIntegrand T m t) =
        (∫ t : Fin d → ℝ, localComplexPeak (T.periodicSpectralPhase hT) a m t) +
          ∫ t in Metric.ball 0 a, anchoredResidualCycleIntegrand T hT m t := by
  have hc : ∀ᶠ t in 𝓝 (0 : Fin d → ℝ), ContinuousAt (T.periodicSpectralPhase hT) t :=
    ((T.contDiffAt_periodicSpectralPhase hT).eventually (by norm_num)).mono
      (fun _ ht => ht.continuousAt)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hc.and (T.eventually_anchored_integrand_eq_peak_add_residual hT))
  refine ⟨r / 2, by linarith, ?_⟩
  intro a ha har m hm
  have hmem (t : Fin d → ℝ) (ht : t ∈ Metric.closedBall 0 a) :
      t ∈ Metric.ball 0 r := by
    simp only [Metric.mem_ball, Metric.mem_closedBall, dist_zero_right] at ht ⊢
    linarith
  have hphase : ContinuousOn (T.periodicSpectralPhase hT) (Metric.closedBall 0 a) :=
    fun t ht => (hball (hmem t ht)).1.continuousWithinAt
  have hpeak : IntegrableOn
      (fun t => Complex.exp ((m : ℂ) * T.periodicSpectralPhase hT t)) (Metric.ball 0 a) :=
    ((Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hphase)).integrableOn_compact
      (isCompact_closedBall (0 : Fin d → ℝ) a)).mono_set Metric.ball_subset_closedBall
  have hg : IntegrableOn (anchoredRealCycleIntegrand T m) (Metric.ball 0 a) :=
    ((continuous_anchoredRealCycleIntegrand T m).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Fin d → ℝ) a)).mono_set Metric.ball_subset_closedBall
  have hpoint (t : Fin d → ℝ) (ht : t ∈ Metric.ball 0 a) :
      anchoredRealCycleIntegrand T m t =
        Complex.exp ((m : ℂ) * T.periodicSpectralPhase hT t) +
          anchoredResidualCycleIntegrand T hT m t :=
    (hball (hmem t (Metric.ball_subset_closedBall ht))).2 m hm
  have hres : IntegrableOn (anchoredResidualCycleIntegrand T hT m) (Metric.ball 0 a) :=
    (hg.sub hpeak).congr_fun (fun t ht => by
      change anchoredRealCycleIntegrand T m t -
        Complex.exp ((m : ℂ) * T.periodicSpectralPhase hT t) = _
      rw [hpoint t ht]
      abel) Metric.isOpen_ball.measurableSet
  rw [integral_localComplexPeak_eq_ball, ← integral_add hpeak hres]
  exact setIntegral_congr_fun Metric.isOpen_ball.measurableSet hpoint

end
end Wormald

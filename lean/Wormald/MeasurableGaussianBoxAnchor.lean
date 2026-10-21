import Wormald.GaussianBoxAnchor

/-! The common-translation box bound also holds for measurable cutoffs.
Its pullback integrability is explicit, so no continuity of an indicator or
additivity of a nonintegrable totalized integral is used. -/

namespace Wormald
noncomputable section
open MeasureTheory

theorem integral_closedBall_anchorDifference_le_of_integrableOn {n : ℕ}
    (a : ℝ) (ha : 0 ≤ a) (F : (Fin n → ℝ) → ℝ)
    (hF0 : ∀ y, 0 ≤ F y) (hFi : Integrable F)
    (hFbox : IntegrableOn (fun x : Fin (n + 1) → ℝ => F (anchorDifference x))
      (Metric.closedBall 0 a)) :
    (∫ x : Fin (n + 1) → ℝ in Metric.closedBall 0 a, F (anchorDifference x)) ≤
      2 * a * ∫ y, F y := by
  let H : (Fin (n + 1) → ℝ) → ℝ :=
    (Metric.closedBall 0 a).indicator (fun x => F (anchorDifference x))
  have hH : Integrable H := hFbox.integrable_indicator Metric.isClosed_closedBall.measurableSet
  have hH0 (x) : 0 ≤ H x := Set.indicator_nonneg (fun _ _ => hF0 _) x
  have hslice (y : Fin n → ℝ) :
      (∫ t : ℝ, H (Fin.snoc (fun j => y j + t) t)) ≤ 2 * a * F y := by
    let J : ℝ → ℝ := (Set.Icc (-a) a).indicator (fun _ => F y)
    have hJ : Integrable J :=
      (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
        measurableSet_Icc
    have hpoint (t : ℝ) : H (Fin.snoc (fun j => y j + t) t) ≤ J t := by
      by_cases hx : Fin.snoc (fun j => y j + t) t ∈ Metric.closedBall (0 : Fin (n + 1) → ℝ) a
      · have hn : ‖Fin.snoc (α := fun _ => ℝ) (fun j => y j + t) t‖ ≤ a := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hx
        have ht : |t| ≤ a := by
          simpa only [Fin.snoc_last, Real.norm_eq_abs] using
            (norm_le_pi_norm (Fin.snoc (α := fun _ => ℝ) (fun j => y j + t) t) (Fin.last n)).trans hn
        have hd : anchorDifference (Fin.snoc (fun j => y j + t) t) = y := by
          ext j
          simp [anchorDifference]
        have htI : t ∈ Set.Icc (-a) a := abs_le.mp ht
        simp [H, J, hx, htI, hd]
      · by_cases ht : t ∈ Set.Icc (-a) a <;> simp [H, J, hx, ht, hF0]
    have hint := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => hH0 (Fin.snoc (fun j => y j + t) t)) hJ
      (Filter.Eventually.of_forall hpoint)
    have hJval : (∫ t, J t) = 2 * a * F y := by
      rw [show J = (Set.Icc (-a) a).indicator (fun _ : ℝ => F y) from rfl,
        integral_indicator measurableSet_Icc, setIntegral_const]
      simp only [Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (show 0 ≤ a - -a by linarith), smul_eq_mul]
      ring
    exact hint.trans_eq hJval
  rw [← integral_indicator Metric.isClosed_closedBall.measurableSet]
  change (∫ x, H x) ≤ _
  rw [integral_anchorShear_split H hH]
  calc
    _ ≤ ∫ y : Fin n → ℝ, 2 * a * F y := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun y => integral_nonneg fun t => hH0 _)
      (hFi.const_mul _) (Filter.Eventually.of_forall hslice)
    _ = _ := integral_const_mul _ _

theorem integral_closedBall_scaled_anchorDifference_le_of_integrableOn {n : ℕ}
    (a : ℝ) (ha : 0 ≤ a) (c : ℝ) (hc : 0 < c)
    (F : (Fin n → ℝ) → ℝ) (hF0 : ∀ y, 0 ≤ F y) (hFi : Integrable F)
    (hFbox : IntegrableOn (fun x : Fin (n + 1) → ℝ => F (c • anchorDifference x))
      (Metric.closedBall 0 a)) :
    (∫ x : Fin (n + 1) → ℝ in Metric.closedBall 0 a, F (c • anchorDifference x)) ≤
      (2 * a / c ^ n) * ∫ y, F y := by
  have h := integral_closedBall_anchorDifference_le_of_integrableOn a ha
    (fun y => F (c • y)) (fun y => hF0 _) (hFi.comp_smul hc.ne') hFbox
  rw [Measure.integral_comp_smul_of_nonneg volume F c (hR := hc.le)] at h
  simp only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul] at h
  convert h using 1
  ring

end
end Wormald

import Wormald.CriticalTransitionTwoStep
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Wormald

noncomputable section
open Matrix Finset

theorem continuous_complexEnergy (n : ℕ) : Continuous (@complexEnergy n) := by
  unfold complexEnergy
  fun_prop

theorem isCompact_complexEnergy_unit (n : ℕ) :
    IsCompact {x : Fin n → ℂ | complexEnergy x = 1} := by
  apply (isCompact_closedBall (0 : Fin n → ℂ) 1).of_isClosed_subset
    (isClosed_eq (continuous_complexEnergy n) continuous_const)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  have hi : Complex.normSq (x i) ≤ complexEnergy x :=
    Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i)
  rw [hx, Complex.normSq_eq_norm_sq] at hi
  nlinarith [norm_nonneg (x i)]

theorem continuous_phase_two_step_energy {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun z : (Fin n → ℂ) × (Fin n → ℂ) =>
      complexEnergy ((P * Matrix.diagonal z.1) ^ 2 *ᵥ z.2)) := by
  unfold complexEnergy
  simp only [pow_two, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  fun_prop

private theorem complexEnergy_unit_normalize {n : ℕ} (x : Fin n → ℂ) (hx : x ≠ 0) :
    complexEnergy (((Real.sqrt (complexEnergy x) : ℂ)⁻¹) • x) = 1 := by
  have he := complexEnergy_pos x hx
  rw [complexEnergy_smul, Complex.normSq_inv, Complex.normSq_ofReal,
    ← pow_two, Real.sq_sqrt (complexEnergy_nonneg x)]
  exact inv_mul_cancel₀ (ne_of_gt he)

/-- A homogeneous quadratic bound on the unit-energy sphere extends to every
vector by explicit positive normalization. -/
theorem energy_bound_of_unit_energy {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (r : ℝ)
    (hunit : ∀ x : Fin n → ℂ, complexEnergy x = 1 → complexEnergy (M *ᵥ x) ≤ r)
    (x : Fin n → ℂ) : complexEnergy (M *ᵥ x) ≤ r * complexEnergy x := by
  by_cases hx : x = 0
  · simp [hx, complexEnergy]
  · have he := complexEnergy_pos x hx
    let c : ℂ := (Real.sqrt (complexEnergy x) : ℂ)⁻¹
    have hc : Complex.normSq c = 1 / complexEnergy x := by
      dsimp [c]
      rw [Complex.normSq_inv, Complex.normSq_ofReal, ← pow_two,
        Real.sq_sqrt (complexEnergy_nonneg x)]
      simp only [one_div]
    have h := hunit (c • x) (complexEnergy_unit_normalize x hx)
    rw [Matrix.mulVec_smul, complexEnergy_smul, hc, one_div_mul_eq_div] at h
    exact (div_le_iff₀ he).mp h

/-- Uniform two-step contraction on any compact set of anchored phases avoiding
the all-one phase. All strictness comes from the actual tournament's proved
energy gap; compactness is used only to choose a common real rate. -/
theorem Tournament.criticalTransition_compact_phase_gap {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) (hT : T.Regular)
    (anchor : Fin n) (K : Set (Fin n → ℂ)) (hK : IsCompact K)
    (hunit : ∀ u ∈ K, ∀ i, ‖u i‖ = 1)
    (hanchor : ∀ u ∈ K, u anchor = 1)
    (hoff : ∀ u ∈ K, ¬∀ i, u i = 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ u ∈ K, ∀ x : Fin n → ℂ,
      complexEnergy ((T.criticalTransition * Matrix.diagonal u) ^ 2 *ᵥ x) ≤ r * complexEnergy x := by
  by_cases hne : K.Nonempty
  · let U : Set (Fin n → ℂ) := {x | complexEnergy x = 1}
    have hU : IsCompact U := isCompact_complexEnergy_unit n
    have hUne : U.Nonempty := by
      refine ⟨Pi.single anchor 1, ?_⟩
      simp [U, complexEnergy, Pi.single_apply]
    have hprod : IsCompact (K ×ˢ U) := hK.prod hU
    have hprodne : (K ×ˢ U).Nonempty := hne.prod hUne
    let f : (Fin n → ℂ) × (Fin n → ℂ) → ℝ := fun z =>
      complexEnergy ((T.criticalTransition * Matrix.diagonal z.1) ^ 2 *ᵥ z.2)
    rcases hprod.exists_isMaxOn hprodne (continuous_phase_two_step_energy T.criticalTransition).continuousOn with
      ⟨z, hz, hmax⟩
    have hzE : complexEnergy z.2 = 1 := hz.2
    have hzneq : z.2 ≠ 0 := by
      intro h
      simp [h, complexEnergy] at hzE
    have hlt : f z < 1 := by
      have h := T.criticalTransition_phase_two_step_energy_lt hn hT z.1
        (hunit _ hz.1) anchor (hanchor _ hz.1) (hoff _ hz.1) z.2 hzneq
      simpa only [hzE] using h
    refine ⟨f z, complexEnergy_nonneg _, hlt, ?_⟩
    intro u hu x
    apply energy_bound_of_unit_energy ((T.criticalTransition * Matrix.diagonal u) ^ 2) (f z) _ x
    intro y hy
    exact (isMaxOn_iff.mp hmax) (u, y) ⟨hu, hy⟩
  · refine ⟨0, le_rfl, by norm_num, ?_⟩
    intro u hu
    exact (hne ⟨u, hu⟩).elim

end
end Wormald

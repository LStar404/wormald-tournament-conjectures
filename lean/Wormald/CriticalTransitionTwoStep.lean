import Wormald.CriticalTransitionSpectralGap

namespace Wormald

noncomputable section
open Matrix Finset

theorem Tournament.criticalTransition_phase_energy_le {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) (hT : T.Regular)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1) (x : Fin n → ℂ) :
    complexEnergy ((T.criticalTransition * Matrix.diagonal u) *ᵥ x) ≤ complexEnergy x := by
  have huSq : ∀ i, Complex.normSq (u i) = 1 := by
    intro i
    simp [Complex.normSq_eq_norm_sq, hu i]
  rw [← Matrix.mulVec_mulVec, diagonal_mulVec_eq_pointwise]
  exact (T.criticalTransition_energy_le hn hT _).trans_eq (complexEnergy_pointwise_phase u huSq x)

theorem Tournament.criticalTransition_phase_energy_eq_iff {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) (hT : T.Regular)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1) (x : Fin n → ℂ) :
    complexEnergy ((T.criticalTransition * Matrix.diagonal u) *ᵥ x) = complexEnergy x ↔
      ∃ a : ℂ, (fun i => u i * x i) = fun _ => a := by
  have huSq : ∀ i, Complex.normSq (u i) = 1 := by
    intro i
    simp [Complex.normSq_eq_norm_sq, hu i]
  rw [← Matrix.mulVec_mulVec, diagonal_mulVec_eq_pointwise,
    ← complexEnergy_pointwise_phase u huSq x]
  exact T.criticalTransition_energy_eq_iff_constant hn hT _

/-- Equality after two phase-transition steps would force every anchored phase
to equal one. This strengthens eigenvalue rigidity to a direct norm statement. -/
theorem Tournament.criticalTransition_phase_two_step_eq_implies_all_one {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) (hT : T.Regular)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (anchor : Fin n) (hanchor : u anchor = 1) (x : Fin n → ℂ) (hx : x ≠ 0)
    (heq : complexEnergy ((T.criticalTransition * Matrix.diagonal u) ^ 2 *ᵥ x) = complexEnergy x) :
    ∀ i, u i = 1 := by
  let A := T.criticalTransition * Matrix.diagonal u
  have hfirst := T.criticalTransition_phase_energy_le hn hT u hu x
  have hsecond := T.criticalTransition_phase_energy_le hn hT u hu (A *ᵥ x)
  have heq' : complexEnergy (A *ᵥ (A *ᵥ x)) = complexEnergy x := by
    simpa only [A, pow_two, Matrix.mulVec_mulVec] using heq
  have hfirsteq : complexEnergy (A *ᵥ x) = complexEnergy x := by
    dsimp [A] at hsecond ⊢
    linarith
  have hsecondeq : complexEnergy (A *ᵥ (A *ᵥ x)) = complexEnergy (A *ᵥ x) := by linarith
  rcases (T.criticalTransition_phase_energy_eq_iff hn hT u hu x).mp hfirsteq with ⟨a, ha⟩
  have hAx : A *ᵥ x = (fun _ => a) := by
    dsimp [A]
    rw [← Matrix.mulVec_mulVec, diagonal_mulVec_eq_pointwise, ha,
      T.criticalTransition_mulVec_const hn hT]
  rcases (T.criticalTransition_phase_energy_eq_iff hn hT u hu (A *ᵥ x)).mp hsecondeq with ⟨b, hb⟩
  have hunitSq : ∀ i, Complex.normSq (u i) = 1 := by
    intro i
    simp [Complex.normSq_eq_norm_sq, hu i]
  have ha_ne : a ≠ 0 := by
    intro hzero
    apply hx
    apply (complexEnergy_eq_zero_iff x).mp
    calc
      _ = complexEnergy (fun i => u i * x i) := (complexEnergy_pointwise_phase u hunitSq x).symm
      _ = complexEnergy (fun _ : Fin n => a) := congrArg complexEnergy ha
      _ = 0 := by simp [hzero, complexEnergy]
  have hb_each : ∀ i, u i * a = b := by
    intro i
    have h := congrFun hb i
    simpa only [hAx] using h
  have hab : a = b := by simpa only [hanchor, one_mul] using hb_each anchor
  intro i
  apply mul_right_cancel₀ ha_ne
  calc
    u i * a = b := hb_each i
    _ = 1 * a := by rw [← hab, one_mul]

/-- Every nonzero vector strictly loses energy after two steps off the anchored
all-one phase. No eigenvalue or connectedness assumption is required. -/
theorem Tournament.criticalTransition_phase_two_step_energy_lt {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) (hT : T.Regular)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (anchor : Fin n) (hanchor : u anchor = 1) (hoff : ¬∀ i, u i = 1)
    (x : Fin n → ℂ) (hx : x ≠ 0) :
    complexEnergy ((T.criticalTransition * Matrix.diagonal u) ^ 2 *ᵥ x) < complexEnergy x := by
  have hfirst := T.criticalTransition_phase_energy_le hn hT u hu x
  have hsecond := T.criticalTransition_phase_energy_le hn hT u hu
    ((T.criticalTransition * Matrix.diagonal u) *ᵥ x)
  have hle : complexEnergy ((T.criticalTransition * Matrix.diagonal u) ^ 2 *ᵥ x) ≤ complexEnergy x := by
    rw [pow_two, ← Matrix.mulVec_mulVec]
    exact hsecond.trans hfirst
  by_contra hnot
  have heq := le_antisymm hle (le_of_not_gt hnot)
  exact hoff (T.criticalTransition_phase_two_step_eq_implies_all_one hn hT u hu anchor hanchor x hx heq)

end
end Wormald

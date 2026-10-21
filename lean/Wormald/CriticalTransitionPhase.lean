import Wormald.CriticalTransitionEquality

namespace Wormald

noncomputable section
open Matrix Finset

theorem complexEnergy_pointwise_phase {n : ℕ} (u : Fin n → ℂ)
    (hu : ∀ i, Complex.normSq (u i) = 1) (x : Fin n → ℂ) :
    complexEnergy (fun i => u i * x i) = complexEnergy x := by
  unfold complexEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.normSq_mul, hu, one_mul]

/-- Finite rigidity of a unit-modulus eigenvalue on the phase torus.
The only input is the proved energy equality criterion of the actual transition. -/
theorem Tournament.criticalTransition_phase_eigenvalue_rigidity_normSq {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) (hT : T.Regular)
    (u : Fin n → ℂ) (hu : ∀ i, Complex.normSq (u i) = 1)
    (anchor : Fin n) (hanchor : u anchor = 1)
    (lam : ℂ) (hlam : Complex.normSq lam = 1) (x : Fin n → ℂ) (hx : x ≠ 0)
    (heig : T.criticalTransition *ᵥ (fun i => u i * x i) = lam • x) :
    (∀ i, u i = 1) ∧ lam = 1 := by
  have hlamne : lam ≠ 0 := by
    intro h
    simp [h] at hlam
  have henergy : complexEnergy (T.criticalTransition *ᵥ (fun i => u i * x i)) =
      complexEnergy (fun i => u i * x i) := by
    calc
      _ = complexEnergy (lam • x) := congrArg complexEnergy heig
      _ = complexEnergy x := complexEnergy_pointwise_phase (fun _ => lam) (fun _ => hlam) x
      _ = _ := (complexEnergy_pointwise_phase u hu x).symm
  rcases (T.criticalTransition_energy_eq_iff_constant hn hT _).mp henergy with ⟨a, hconst⟩
  have hP : T.criticalTransition *ᵥ (fun i => u i * x i) = (fun _ => a) := by
    rw [hconst, T.criticalTransition_mulVec_const hn hT]
  have heach : ∀ i, lam * x i = a := by
    intro i
    have h := congrFun (heig.symm.trans hP) i
    simpa only [Pi.smul_apply, smul_eq_mul] using h
  have hphase : ∀ i, u i * x i = a := fun i => congrFun hconst i
  have ha : a ≠ 0 := by
    intro hzero
    apply hx
    funext i
    have hi : lam * x i = 0 := by rw [heach, hzero]
    exact (mul_eq_zero.mp hi).resolve_left hlamne
  have hanchor_ne : x anchor ≠ 0 := by
    intro hzero
    apply ha
    have h := heach anchor
    rw [hzero, mul_zero] at h
    exact h.symm
  have hlamone : lam = 1 := by
    apply mul_right_cancel₀ hanchor_ne
    calc
      lam * x anchor = a := heach anchor
      _ = u anchor * x anchor := (hphase anchor).symm
      _ = 1 * x anchor := by rw [hanchor]
  have hxconst : ∀ i, x i = a := by
    intro i
    simpa only [hlamone, one_mul] using heach i
  constructor
  · intro i
    apply mul_right_cancel₀ ha
    simpa only [hxconst, one_mul] using hphase i
  · exact hlamone

/-- The unit-modulus formulation for the actual matrix P diag(u). An arbitrary
anchored coordinate is allowed; in the application it is the last coordinate. -/
theorem Tournament.criticalTransition_phase_eigenvalue_rigidity {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) (hT : T.Regular)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (anchor : Fin n) (hanchor : u anchor = 1)
    (lam : ℂ) (hlam : ‖lam‖ = 1) (x : Fin n → ℂ) (hx : x ≠ 0)
    (heig : (T.criticalTransition * Matrix.diagonal u) *ᵥ x = lam • x) :
    (∀ i, u i = 1) ∧ lam = 1 := by
  have huSq : ∀ i, Complex.normSq (u i) = 1 := by
    intro i
    simp [Complex.normSq_eq_norm_sq, hu i]
  have hlamSq : Complex.normSq lam = 1 := by simp [Complex.normSq_eq_norm_sq, hlam]
  have heig' : T.criticalTransition *ᵥ (fun i => u i * x i) = lam • x := by
    have hd : Matrix.diagonal u *ᵥ x = (fun i => u i * x i) := by
      funext i
      exact Matrix.mulVec_diagonal u x i
    rw [← Matrix.mulVec_mulVec, hd] at heig
    exact heig
  exact T.criticalTransition_phase_eigenvalue_rigidity_normSq hn hT u huSq
    anchor hanchor lam hlamSq x hx heig'

end
end Wormald


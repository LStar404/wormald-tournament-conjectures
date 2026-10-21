import Wormald.CriticalTransitionPhase
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace Wormald

noncomputable section
open Matrix Finset

theorem complexEnergy_smul {n : ℕ} (c : ℂ) (x : Fin n → ℂ) :
    complexEnergy (c • x) = Complex.normSq c * complexEnergy x := by
  simp only [complexEnergy, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, ← Finset.mul_sum]

theorem diagonal_mulVec_eq_pointwise {n : ℕ} (u x : Fin n → ℂ) :
    Matrix.diagonal u *ᵥ x = (fun i => u i * x i) := by
  funext i
  exact Matrix.mulVec_diagonal u x i

/-- Every eigenvalue of the actual phase transition lies in the closed unit disk. -/
theorem Tournament.criticalTransition_phase_eigenvalue_norm_le_one {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) (hT : T.Regular)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (lam : ℂ) (x : Fin n → ℂ) (hx : x ≠ 0)
    (heig : (T.criticalTransition * Matrix.diagonal u) *ᵥ x = lam • x) :
    ‖lam‖ ≤ 1 := by
  have huSq : ∀ i, Complex.normSq (u i) = 1 := by
    intro i
    simp [Complex.normSq_eq_norm_sq, hu i]
  rw [← Matrix.mulVec_mulVec, diagonal_mulVec_eq_pointwise] at heig
  have hE := T.criticalTransition_energy_le hn hT (fun i => u i * x i)
  rw [heig, complexEnergy_smul, complexEnergy_pointwise_phase u huSq x] at hE
  have hxpos := complexEnergy_pos x hx
  have hsq : Complex.normSq lam ≤ 1 := by nlinarith
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg lam]

/-- Off the anchored all-one phase, every actual eigenvalue is strictly inside
the unit disk. This is a proved finite spectral gap, not an irreducibility premise. -/
theorem Tournament.criticalTransition_phase_eigenvalue_norm_lt_one {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) (hT : T.Regular)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (anchor : Fin n) (hanchor : u anchor = 1) (hoff : ¬∀ i, u i = 1)
    (lam : ℂ) (x : Fin n → ℂ) (hx : x ≠ 0)
    (heig : (T.criticalTransition * Matrix.diagonal u) *ᵥ x = lam • x) :
    ‖lam‖ < 1 := by
  have hle := T.criticalTransition_phase_eigenvalue_norm_le_one hn hT u hu lam x hx heig
  by_contra hnot
  have hlam : ‖lam‖ = 1 := le_antisymm hle (le_of_not_gt hnot)
  exact hoff (T.criticalTransition_phase_eigenvalue_rigidity hn hT u hu anchor hanchor
    lam hlam x hx heig).1

/-- The actual critical determinant has exactly one zero on the anchored phase
torus. The anchor may be chosen to be the last coordinate. -/
theorem Tournament.criticalTransition_phase_det_eq_zero_iff {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) (hT : T.Regular)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (anchor : Fin n) (hanchor : u anchor = 1) :
    (1 - T.criticalTransition * Matrix.diagonal u).det = 0 ↔ ∀ i, u i = 1 := by
  constructor
  · intro hdet
    rcases (Matrix.exists_mulVec_eq_zero_iff).mpr hdet with ⟨x, hx, hker⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hker
    have heig : (T.criticalTransition * Matrix.diagonal u) *ᵥ x = (1 : ℂ) • x := by
      simpa only [one_smul] using (sub_eq_zero.mp hker).symm
    exact (T.criticalTransition_phase_eigenvalue_rigidity hn hT u hu anchor hanchor
      1 (by norm_num) x hx heig).1
  · intro hall
    have huone : u = (fun _ => (1 : ℂ)) := funext hall
    rw [huone, Matrix.diagonal_one, mul_one]
    apply (Matrix.exists_mulVec_eq_zero_iff).mp
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      have hi := congrFun h anchor
      simp at hi
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec, T.criticalTransition_mulVec_const hn hT 1, sub_self]

end
end Wormald

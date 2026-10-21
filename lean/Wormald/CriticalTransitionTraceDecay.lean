import Wormald.CriticalTransitionCompactGap

namespace Wormald

noncomputable section
open Matrix Finset

/-- Two-step Euclidean contraction gives geometric energy decay at every power. -/
theorem matrix_power_energy_le_of_two_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (hr : 0 ≤ r)
    (hone : ∀ x, complexEnergy (A *ᵥ x) ≤ complexEnergy x)
    (htwo : ∀ x, complexEnergy (A ^ 2 *ᵥ x) ≤ r * complexEnergy x)
    (m : ℕ) (x : Fin n → ℂ) :
    complexEnergy (A ^ m *ᵥ x) ≤ r ^ (m / 2) * complexEnergy x := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using hone x
  | more m hm _ =>
    have hpow : A ^ (m + 2) *ᵥ x = A ^ 2 *ᵥ (A ^ m *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← pow_add, Nat.add_comm 2 m]
    calc
      _ = complexEnergy (A ^ 2 *ᵥ (A ^ m *ᵥ x)) := congrArg complexEnergy hpow
      _ ≤ r * complexEnergy (A ^ m *ᵥ x) := htwo _
      _ ≤ r * (r ^ (m / 2) * complexEnergy x) := mul_le_mul_of_nonneg_left hm hr
      _ = _ := by
        rw [show (m + 2) / 2 = m / 2 + 1 by omega, pow_succ]
        ring

/-- The geometric energy estimate controls the actual trace, with no chosen
matrix norm or spectral-radius continuity theorem. -/
theorem matrix_power_trace_norm_le_of_two_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (hr : 0 ≤ r)
    (hone : ∀ x, complexEnergy (A *ᵥ x) ≤ complexEnergy x)
    (htwo : ∀ x, complexEnergy (A ^ 2 *ᵥ x) ≤ r * complexEnergy x)
    (m : ℕ) :
    ‖(A ^ m).trace‖ ≤ (n : ℝ) * (Real.sqrt r) ^ (m / 2) := by
  have hdiagonal : ∀ j : Fin n, ‖(A ^ m) j j‖ ≤ (Real.sqrt r) ^ (m / 2) := by
    intro j
    have hcol := matrix_power_energy_le_of_two_step A r hr hone htwo m (Pi.single j 1)
    have hbasis : complexEnergy (Pi.single j (1 : ℂ)) = 1 := by
      simp [complexEnergy, Pi.single_apply]
    rw [Matrix.mulVec_single_one, hbasis, mul_one] at hcol
    have hj : Complex.normSq ((A ^ m) j j) ≤ complexEnergy ((A ^ m).col j) :=
      Finset.single_le_sum (fun i _ => Complex.normSq_nonneg ((A ^ m) i j)) (Finset.mem_univ j)
    have hsq := hj.trans hcol
    rw [Complex.normSq_eq_norm_sq] at hsq
    have hsqrt : ((Real.sqrt r) ^ (m / 2)) ^ 2 = r ^ (m / 2) := by
      rw [pow_right_comm, Real.sq_sqrt hr]
    nlinarith [norm_nonneg ((A ^ m) j j), pow_nonneg (Real.sqrt_nonneg r) (m / 2)]
  calc
    _ = ‖∑ j, (A ^ m) j j‖ := rfl
    _ ≤ ∑ j, ‖(A ^ m) j j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, (Real.sqrt r) ^ (m / 2) :=
      Finset.sum_le_sum (fun j _ => hdiagonal j)
    _ = _ := by simp [nsmul_eq_mul]

/-- A compact region of the anchored phase torus away from the unique critical
point has a common exponential trace-decay rate, for every matrix power. -/
theorem Tournament.criticalTransition_compact_phase_trace_decay {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) (hT : T.Regular)
    (anchor : Fin n) (K : Set (Fin n → ℂ)) (hK : IsCompact K)
    (hunit : ∀ u ∈ K, ∀ i, ‖u i‖ = 1)
    (hanchor : ∀ u ∈ K, u anchor = 1)
    (hoff : ∀ u ∈ K, ¬∀ i, u i = 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ u ∈ K, ∀ m : ℕ,
      ‖((T.criticalTransition * Matrix.diagonal u) ^ m).trace‖ ≤ (n : ℝ) * s ^ (m / 2) := by
  rcases T.criticalTransition_compact_phase_gap hn hT anchor K hK hunit hanchor hoff with
    ⟨r, hr0, hr1, hgap⟩
  have hs : Real.sqrt r < 1 := by
    have hsq := Real.sq_sqrt hr0
    have hnonneg := Real.sqrt_nonneg r
    nlinarith
  refine ⟨Real.sqrt r, Real.sqrt_nonneg r, hs, ?_⟩
  intro u hu m
  exact matrix_power_trace_norm_le_of_two_step _ r hr0
    (T.criticalTransition_phase_energy_le hn hT u (hunit u hu)) (hgap u hu) m

end
end Wormald

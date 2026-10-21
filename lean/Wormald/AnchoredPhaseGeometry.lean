import Wormald.MarkovCriticalBridge
import Wormald.CriticalTransitionTraceDecay

namespace Wormald

noncomputable section
open Matrix MeasureTheory

def anchoredRealPhase {d : ℕ} (t : Fin d → ℝ) : Fin (d + 1) → ℂ :=
  anchoredFourierPhase (fun i => (t i : UnitAddCircle))

def unitPhaseCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.Icc (fun _ => -(1 / 2 : ℝ)) (fun _ => 1 / 2)

def phaseFarRegion (d : ℕ) (a : ℝ) : Set (Fin d → ℝ) :=
  unitPhaseCube d \ Metric.ball 0 a

theorem continuous_anchoredFourierPhase (d : ℕ) :
    Continuous (@anchoredFourierPhase d) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using (continuous_const : Continuous (fun _ : UnitAddTorus (Fin d) => (1 : ℂ)))
  · simpa [Function.comp_def] using (fourier (T := (1 : ℝ)) 1).continuous.comp
      (continuous_apply j : Continuous (fun x : UnitAddTorus (Fin d) => x j))

theorem continuous_anchoredRealPhase (d : ℕ) : Continuous (@anchoredRealPhase d) :=
  (continuous_anchoredFourierPhase d).comp
    (continuous_pi (fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
      (continuous_apply i : Continuous (fun x : Fin d → ℝ => x i))))

theorem anchoredFourierPhase_norm {d : ℕ} (x : UnitAddTorus (Fin d)) (i : Fin (d + 1)) :
    ‖anchoredFourierPhase x i‖ = 1 := by
  rw [anchoredFourierPhase, fourier_apply]
  exact Circle.norm_coe _

theorem fourier_one_eq_one_iff (x : UnitAddCircle) : fourier 1 x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
    apply Subtype.ext
    simpa only [fourier_one, AddCircle.toCircle_zero, Circle.coe_one] using h
  · rintro rfl
    simp

theorem anchoredRealPhase_all_one_iff {d : ℕ} (t : Fin d → ℝ) (ht : t ∈ unitPhaseCube d) :
    (∀ i, anchoredRealPhase t i = 1) ↔ t = 0 := by
  constructor
  · intro h
    funext i
    have hFourier : fourier 1 (t i : UnitAddCircle) = 1 := by
      simpa [anchoredRealPhase] using h i.castSucc
    have hzero := (fourier_one_eq_one_iff _).mp hFourier
    rcases (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero with ⟨k, hk⟩
    have hkR : (k : ℝ) = t i := by simpa using hk
    have hlo : -(1 / 2 : ℝ) ≤ t i := ht.1 i
    have hhi : t i ≤ (1 / 2 : ℝ) := ht.2 i
    have hklo : (-1 : ℤ) < k := by exact_mod_cast (show (-1 : ℝ) < (k : ℝ) by linarith)
    have hkhi : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < (1 : ℝ) by linarith)
    have hk0 : k = 0 := by omega
    simpa [hk0] using hkR.symm
  · rintro rfl
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact anchoredFourierPhase_last _
    · simp [anchoredRealPhase]

theorem isCompact_unitPhaseCube (d : ℕ) : IsCompact (unitPhaseCube d) := isCompact_Icc

theorem isCompact_phaseFarRegion (d : ℕ) (a : ℝ) : IsCompact (phaseFarRegion d a) :=
  (isCompact_unitPhaseCube d).diff Metric.isOpen_ball

/-- The real Fourier cube away from any positive-radius neighborhood has a
common trace-decay rate for the exact critical transition. -/
theorem Tournament.criticalTransition_real_phase_far_trace_decay {d : ℕ}
    (T : Tournament (d + 1)) (hT : T.Regular) (a : ℝ) (ha : 0 < a) :
    ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ t ∈ phaseFarRegion d a, ∀ m : ℕ,
      ‖((T.criticalTransition * Matrix.diagonal (anchoredRealPhase t)) ^ m).trace‖ ≤
        ((d + 1 : ℕ) : ℝ) * s ^ (m / 2) := by
  let K := anchoredRealPhase '' phaseFarRegion d a
  have hK : IsCompact K := (isCompact_phaseFarRegion d a).image (continuous_anchoredRealPhase d)
  have hunit : ∀ u ∈ K, ∀ i, ‖u i‖ = 1 := by
    rintro u ⟨t, ht, rfl⟩ i
    exact anchoredFourierPhase_norm _ _
  have hanchor : ∀ u ∈ K, u (Fin.last d) = 1 := by
    rintro u ⟨t, ht, rfl⟩
    exact anchoredFourierPhase_last _
  have hoff : ∀ u ∈ K, ¬∀ i, u i = 1 := by
    rintro u ⟨t, ht, rfl⟩ hall
    have htzero := (anchoredRealPhase_all_one_iff t ht.1).mp hall
    exact ht.2 (by simpa [htzero] using ha)
  rcases T.criticalTransition_compact_phase_trace_decay (Nat.succ_ne_zero d) hT
    (Fin.last d) K hK hunit hanchor hoff with ⟨s, hs0, hs1, htrace⟩
  exact ⟨s, hs0, hs1, fun t ht m => htrace _ ⟨t, ht, rfl⟩ m⟩

end
end Wormald

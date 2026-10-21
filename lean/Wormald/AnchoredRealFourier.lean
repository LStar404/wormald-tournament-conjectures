import Wormald.AnchoredFarField
import Mathlib.Topology.Instances.Matrix

namespace Wormald

noncomputable section
open Matrix MeasureTheory Filter
open scoped Topology BigOperators

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def unitPhaseCubeIoc (d : ℕ) : Set (Fin d → ℝ) :=
  {t | ∀ i, t i ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)}

theorem unitPhaseCubeIoc_subset (d : ℕ) : unitPhaseCubeIoc d ⊆ unitPhaseCube d := by
  intro t ht
  exact ⟨fun i => (ht i).1.le, fun i => (ht i).2⟩

theorem anchored_torus_integral_eq_realCubeIntegral {d : ℕ}
    (T : Tournament (d + 1)) (m : ℕ) :
    (∫ x : UnitAddTorus (Fin d), UnitAddTorus.mFourier (fun _ => -(m : ℤ)) x *
      ((T.criticalTransition * Matrix.diagonal (anchoredFourierPhase x)) ^ ((d + 1) * m)).trace) =
      ∫ t in unitPhaseCubeIoc d, anchoredRealCycleIntegrand T m t := by
  rw [UnitAddTorus.integral_preimage _ (fun _ => -(1 / 2 : ℝ))]
  have hset : {t : Fin d → ℝ | ∀ i, t i ∈ Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)} =
      unitPhaseCubeIoc d := by norm_num [unitPhaseCubeIoc]
  rw [hset]
  rfl

/-- Exact real-cube integral for the original normalized independent expectation,
with the precise critical transition and final phase anchored at zero. -/
theorem FiniteModel.normalizedExpectedCycles_eq_criticalRealCubeIntegral {d : ℕ}
    (base : FiniteModel.Orientation (d + 1)) (m : ℕ) (hN : 3 ≤ (d + 1) * m) :
    (FiniteModel.normalizedExpectedCycles base m : ℂ) =
      (factorialPrefactor (d + 1) m : ℂ) *
        ∫ t in unitPhaseCubeIoc d, anchoredRealCycleIntegrand (FiniteModel.toTournament base) m t := by
  rw [FiniteModel.normalizedExpectedCycles_eq_criticalAnchoredFourierIntegral base m hN,
    anchored_torus_integral_eq_realCubeIntegral]

theorem continuous_anchoredRealCycleIntegrand {d : ℕ} (T : Tournament (d + 1)) (m : ℕ) :
    Continuous (anchoredRealCycleIntegrand T m) := by
  unfold anchoredRealCycleIntegrand
  apply Continuous.mul
  · exact (UnitAddTorus.mFourier _).continuous.comp (continuous_pi (fun i =>
      (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)))
  · apply Continuous.matrix_trace
    have hA : Continuous (fun t : Fin d → ℝ =>
        T.criticalTransition * Matrix.diagonal (anchoredRealPhase t)) :=
      continuous_const.matrix_mul (continuous_anchoredRealPhase d).matrix_diagonal
    exact hA.pow _

theorem ball_subset_unitPhaseCubeIoc {d : ℕ} (a : ℝ) (ha : a ≤ 1 / 2) :
    Metric.ball (0 : Fin d → ℝ) a ⊆ unitPhaseCubeIoc d := by
  intro t ht i
  have htN : ‖t‖ < a := by simpa only [Metric.mem_ball, dist_zero_right] using ht
  have hi : |t i| < (1 / 2 : ℝ) :=
    (norm_le_pi_norm t i).trans_lt (htN.trans_le ha)
  exact ⟨(abs_lt.mp hi).1, (abs_lt.mp hi).2.le⟩

/-- The exact anchored integral splits into a local ball and its far region;
integrability follows from continuity on the containing compact cube. -/
theorem anchored_realCubeIntegral_eq_local_add_far {d : ℕ} (T : Tournament (d + 1))
    (m : ℕ) (a : ℝ) (ha : a ≤ 1 / 2) :
    (∫ t in unitPhaseCubeIoc d, anchoredRealCycleIntegrand T m t) =
      (∫ t in Metric.ball 0 a, anchoredRealCycleIntegrand T m t) +
        ∫ t in unitPhaseCubeIoc d \ Metric.ball 0 a, anchoredRealCycleIntegrand T m t := by
  have hint : IntegrableOn (anchoredRealCycleIntegrand T m) (unitPhaseCubeIoc d) :=
    ((continuous_anchoredRealCycleIntegrand T m).continuousOn.integrableOn_compact
      (isCompact_unitPhaseCube d)).mono_set (unitPhaseCubeIoc_subset d)
  have h := setIntegral_sdiff Metric.isOpen_ball.measurableSet hint (ball_subset_unitPhaseCubeIoc a ha)
  rw [h]
  abel

theorem Tournament.anchored_realCube_far_sqrt_normalized_tendsto_zero {d : ℕ}
    (T : Tournament (d + 1)) (hd : 1 ≤ d) (hT : T.Regular)
    (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ) : ℂ) ^ k *
      ∫ t in unitPhaseCubeIoc d \ Metric.ball 0 a, anchoredRealCycleIntegrand T m t)
      atTop (𝓝 0) := by
  apply T.anchored_far_integral_sqrt_normalized_tendsto_zero hd hT a ha _ _ k
  intro t ht
  exact ⟨unitPhaseCubeIoc_subset d ht.1, ht.2⟩

end
end Wormald

import Wormald.GoodClusterRestriction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! Exact coordinate transport for a cluster. The torus projection discards
the outlier coordinates under probability Haar measure, and the remaining
coordinates are relabelled in increasing order without a volume factor. -/

namespace Wormald.FiniteModel
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

local instance goodCoordinateCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance goodCoordinateCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_goodCoordinates {m : ℕ} (G : Finset (Fin m))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin G.card → ℝ) → E) :
    (∫ x : G → ℝ, f (fun i => x (G.orderIsoOfFin rfl i))) =
      ∫ y : Fin G.card → ℝ, f y := by
  exact (volume_measurePreserving_piCongrLeft (fun _ : G => ℝ)
    (G.orderIsoOfFin rfl).toEquiv).symm.integral_comp' f

theorem integral_goodCoordinates_closedBall {m : ℕ} (G : Finset (Fin m))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin G.card → ℝ) → E) (r : ℝ) (hr : 0 ≤ r) :
    (∫ x : G → ℝ in Metric.closedBall 0 r, f (fun i => x (G.orderIsoOfFin rfl i))) =
      ∫ y : Fin G.card → ℝ in Metric.closedBall 0 r, f y := by
  let e := (MeasurableEquiv.piCongrLeft (fun _ : G => ℝ) (G.orderIsoOfFin rfl).toEquiv).symm
  have he := (volume_measurePreserving_piCongrLeft (fun _ : G => ℝ)
    (G.orderIsoOfFin rfl).toEquiv).symm
  have hpre : e ⁻¹' Metric.closedBall 0 r = Metric.closedBall 0 r := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg hr]
    change (∀ i : Fin G.card, ‖x (G.orderIsoOfFin rfl i)‖ ≤ r) ↔ ∀ i : G, ‖x i‖ ≤ r
    constructor
    · intro h i
      obtain ⟨k, rfl⟩ := (G.orderIsoOfFin rfl).surjective i
      exact h k
    · intro h i
      exact h _
  have hh := he.setIntegral_preimage_emb e.measurableEmbedding f (Metric.closedBall 0 r)
  change (∫ x in e ⁻¹' Metric.closedBall 0 r, f (e x)) = _ at hh
  rw [hpre] at hh
  exact hh

def goodCircleCoordinates {m : ℕ} (G : Finset (Fin m))
    (x : UnitAddTorus (Fin m)) : UnitAddTorus (Fin G.card) :=
  fun i => x (goodVertex G i)

theorem measurePreserving_goodCircleCoordinates {m : ℕ} (G : Finset (Fin m)) :
    MeasurePreserving (goodCircleCoordinates G) := by
  have hsplit := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin m => UnitAddCircle)
    (fun i => i ∈ G)
  have hFI : (Subtype.fintype fun i : Fin m => i ∈ G) = Finset.Subtype.fintype G :=
    Subsingleton.elim _ _
  rw [hFI] at hsplit
  have hfst : MeasurePreserving
      (Prod.fst : (G → UnitAddCircle) × ({i // i ∉ G} → UnitAddCircle) → (G → UnitAddCircle)) :=
    measurePreserving_fst
  have hlabel := (volume_measurePreserving_piCongrLeft (fun _ : G => UnitAddCircle)
    (G.orderIsoOfFin rfl).toEquiv).symm
  exact hlabel.comp (hfst.comp hsplit)

theorem integral_goodCircleCoordinates {m : ℕ} (G : Finset (Fin m))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddTorus (Fin G.card) → E) (hf : StronglyMeasurable f) :
    (∫ x : UnitAddTorus (Fin m), f (goodCircleCoordinates G x)) =
      ∫ y : UnitAddTorus (Fin G.card), f y := by
  have h := measurePreserving_goodCircleCoordinates G
  rw [← h.map_eq]
  exact (integral_map_of_stronglyMeasurable h.measurable hf).symm

end
end Wormald.FiniteModel

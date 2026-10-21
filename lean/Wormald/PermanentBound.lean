import Wormald.FiniteModel
import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# The permanent genuinely bounds the original Hamilton-cycle count

The bound applies to every individual sample, including regular-block samples.
The much stronger Brégman estimate for the permanent is a separate obligation.
-/

namespace Wormald.FiniteModel
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def arcMatrix {V : Type*} (a : V → V → Bool) : Matrix V V ℕ :=
  fun v w => if a v w = true then 1 else 0

theorem hamiltonCycleCount_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → V → Bool) :
    hamiltonCycleCount a = ∑ σ : Equiv.Perm V, if IsHamiltonCycle a σ then 1 else 0 := by
  classical
  unfold hamiltonCycleCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

/-- Counting only single-orbit successor permutations is bounded by counting
all supported permutations, which is exactly the permanent. -/
theorem hamiltonCycleCount_le_permanent {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → V → Bool) : hamiltonCycleCount a ≤ (arcMatrix a).permanent := by
  classical
  rw [hamiltonCycleCount_eq_sum, ← Matrix.permanent_transpose]
  unfold Matrix.permanent
  apply Finset.sum_le_sum
  intro σ _
  by_cases hσ : IsHamiltonCycle a σ
  · simp only [hσ, ite_true]
    have hprod : (∏ i, (arcMatrix a).transpose (σ i) i) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp [arcMatrix, hσ.2 i]
    rw [hprod]
  · simp [hσ]

/-- The permanent estimate applies before any averaging over internal blocks. -/
theorem blowup_hamiltonCycleCount_le_permanent {d m : ℕ} (base : Orientation d)
    (blocks : IndependentSample d m) :
    hamiltonCycleCount (blowupArc base blocks) ≤
      (arcMatrix (blowupArc base blocks)).permanent :=
  hamiltonCycleCount_le_permanent _

theorem uniformMean_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f g : Ω → ℕ) (hfg : ∀ ω, f ω ≤ g ω) : uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  apply div_le_div_of_nonneg_right
  · apply Finset.sum_le_sum
    intro ω _
    exact_mod_cast hfg ω
  · positivity

def expectedPermanent {d : ℕ} (base : Orientation d) (m : ℕ) : ℚ :=
  uniformMean (fun blocks : IndependentSample d m =>
    (arcMatrix (blowupArc base blocks)).permanent)

/-- The correct actual independent-model mean is bounded before any analytic
or degree estimate is invoked. -/
theorem expectedCycles_le_expectedPermanent {d : ℕ} (base : Orientation d) (m : ℕ) :
    expectedCycles base m ≤ expectedPermanent base m := by
  apply uniformMean_mono
  intro blocks
  exact blowup_hamiltonCycleCount_le_permanent base blocks

def expectedRegularPermanent {d : ℕ} (base : Orientation d) (m : ℕ)
    (hlegal : LegalRegularOrder d m) : ℚ := by
  classical
  letI : Fintype (RegularSample d m) := Fintype.ofFinite _
  letI : Nonempty (RegularSample d m) := hlegal.2
  exact uniformMean (fun blocks : RegularSample d m =>
    (arcMatrix (blowupArc base (fun i => (blocks i).1))).permanent)

/-- The regular-block bound is samplewise as required by the original model;
it does not replace regular edges by independent fair edges. -/
theorem expectedRegularCycles_le_expectedRegularPermanent {d : ℕ}
    (base : Orientation d) (m : ℕ) (hlegal : LegalRegularOrder d m) :
    expectedRegularCycles base m hlegal ≤ expectedRegularPermanent base m hlegal := by
  classical
  let _ : Fintype (RegularSample d m) := Fintype.ofFinite _
  let _ : Nonempty (RegularSample d m) := hlegal.2
  apply uniformMean_mono
  intro blocks
  exact hamiltonCycleCount_le_permanent _

end
end Wormald.FiniteModel

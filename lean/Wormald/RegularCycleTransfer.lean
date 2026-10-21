import Wormald.RegularConditioning
import Wormald.ExactCycleTransfer

/-! Exact cycle transfer for the genuine uniform regular-block model.
For each successor permutation its internal directed arc sets are tested in
the true regular law; the block probabilities multiply by block independence.
No replacement of dependent internal arcs by independent fair edges is made. -/

namespace Wormald.FiniteModel
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem uniformMean_fintype_independent {Ω : Type*} [Nonempty Ω]
    (F G : Fintype Ω) (f : Ω → ℕ) :
    @uniformMean Ω F ‹Nonempty Ω› f = @uniformMean Ω G ‹Nonempty Ω› f := by
  cases Subsingleton.elim F G
  rfl

theorem uniformMean_sum {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (f : I → Ω → ℕ) :
    uniformMean (fun ω => ∑ i, f i ω) = ∑ i, uniformMean (f i) := by
  unfold uniformMean
  simp only [Nat.cast_sum, Finset.sum_div]
  exact Finset.sum_comm

/-- The internal directed arc set used by a successor permutation in block i. -/
def internalCycleArcSet {d m : ℕ} (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d) :
    Finset (Fin m × Fin m) := Finset.univ.filter (fun p => σ (i, p.1) = (i, p.2))

@[simp] theorem mem_internalCycleArcSet {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d) (a b : Fin m) :
    (a, b) ∈ internalCycleArcSet σ i ↔ σ (i, a) = (i, b) := by
  simp only [internalCycleArcSet, Finset.mem_filter, Finset.mem_univ, true_and]

def CrossBlockCycleCompatible {d m : ℕ} (base : Orientation d)
    (σ : Equiv.Perm (Fin d × Fin m)) : Prop :=
  ∀ v, v.1 ≠ (σ v).1 → arc base v.1 (σ v).1 = true

theorem contains_internalCycleArcSet_iff {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (blocks : IndependentSample d m) :
    (∀ i, ContainsArcSet (internalCycleArcSet σ i) (blocks i)) ↔
      ∀ v, v.1 = (σ v).1 → arc (blocks v.1) v.2 (σ v).2 = true := by
  constructor
  · intro h v hv
    exact h v.1 (v.2, (σ v).2)
      ((mem_internalCycleArcSet σ v.1 v.2 (σ v).2).mpr (Prod.ext hv.symm rfl))
  · intro h i p hp
    have heq := (mem_internalCycleArcSet σ i p.1 p.2).mp hp
    have hi : i = (σ (i, p.1)).1 := (congrArg Prod.fst heq).symm
    simpa only [heq] using h (i, p.1) hi

theorem isHamiltonCycle_blowup_iff_internalArcSets {d m : ℕ} (base : Orientation d)
    (blocks : IndependentSample d m) (σ : Equiv.Perm (Fin d × Fin m)) :
    IsHamiltonCycle (blowupArc base blocks) σ ↔
      SingleOrbit σ ∧ CrossBlockCycleCompatible base σ ∧
        ∀ i, ContainsArcSet (internalCycleArcSet σ i) (blocks i) := by
  rw [contains_internalCycleArcSet_iff]
  constructor
  · intro h
    refine ⟨h.1, ?_, ?_⟩
    · intro v hv
      simpa only [blowupArc, ite_eq_right hv] using h.2 v
    · intro v hv
      simpa only [blowupArc, ite_eq_left hv] using h.2 v
  · rintro ⟨ho, hc, hi⟩
    refine ⟨ho, fun v => ?_⟩
    by_cases h : v.1 = (σ v).1
    · simpa only [blowupArc, ite_eq_left h] using hi v h
    · simpa only [blowupArc, ite_eq_right h] using hc v h

def regularArcSetIndicator {m : ℕ} (D : Finset (Fin m × Fin m))
    (T : {T : Orientation m // RegularBlock T}) : ℕ :=
  if ContainsArcSet D T.1 then 1 else 0

theorem regularBlockEvents_mean_eq_product {d m : ℕ}
    (D : Fin d → Finset (Fin m × Fin m)) (hm : Odd m) :
    let _ : Nonempty {T : Orientation m // RegularBlock T} :=
      ⟨⟨carousel m, carousel_regular hm⟩⟩
    uniformMean (fun blocks : RegularSample d m =>
      if ∀ i, ContainsArcSet (D i) (blocks i).1 then 1 else 0) =
        ∏ i, regularContainmentProbability (D i) hm := by
  have : Nonempty {T : Orientation m // RegularBlock T} :=
    ⟨⟨carousel m, carousel_regular hm⟩⟩
  dsimp only
  have hfun : (fun blocks : RegularSample d m =>
      if ∀ i, ContainsArcSet (D i) (blocks i).1 then 1 else 0) =
      (fun blocks => ∏ i, regularArcSetIndicator (D i) (blocks i) : RegularSample d m → ℕ) := by
    funext blocks
    unfold regularArcSetIndicator
    rw [Fintype.prod_boole]
    split <;> rfl
  rw [hfun]
  exact uniformMean_product (fun i => regularArcSetIndicator (D i))

def regularWeightedHamiltonianCycleSum {d m : ℕ} (base : Orientation d) (hm : Odd m) : ℚ :=
  ∑ σ : Equiv.Perm (Fin d × Fin m),
    if SingleOrbit σ ∧ CrossBlockCycleCompatible base σ then
      ∏ i, regularContainmentProbability (internalCycleArcSet σ i) hm else 0

/-- Exact transfer for the actual original regular-block expectation. The
successor-permutation convention already identifies cyclic starting points. -/
theorem expectedRegularCycles_eq_weightedArcSets {d m : ℕ} (base : Orientation d)
    (hlegal : LegalRegularOrder d m) :
    expectedRegularCycles base m hlegal = regularWeightedHamiltonianCycleSum base hlegal.1 := by
  have : Nonempty {T : Orientation m // RegularBlock T} :=
    ⟨⟨carousel m, carousel_regular hlegal.1⟩⟩
  have hmean : expectedRegularCycles base m hlegal =
      uniformMean (fun blocks : RegularSample d m =>
        hamiltonCycleCount (blowupArc base (fun i => (blocks i).1))) := by
    unfold expectedRegularCycles
    exact uniformMean_fintype_independent _ _ _
  rw [hmean]
  have hfun : (fun blocks : RegularSample d m =>
      hamiltonCycleCount (blowupArc base (fun i => (blocks i).1))) =
      (fun blocks => ∑ σ : Equiv.Perm (Fin d × Fin m),
        if IsHamiltonCycle (blowupArc base (fun i => (blocks i).1)) σ then 1 else 0) := by
    funext blocks
    exact hamiltonCycleCount_eq_sum _
  rw [hfun, uniformMean_sum]
  unfold regularWeightedHamiltonianCycleSum
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hglobal : SingleOrbit σ ∧ CrossBlockCycleCompatible base σ
  · rw [ite_eq_left hglobal]
    have hevent : (fun blocks : RegularSample d m =>
        if IsHamiltonCycle (blowupArc base (fun i => (blocks i).1)) σ then 1 else 0) =
        (fun blocks => if ∀ i, ContainsArcSet (internalCycleArcSet σ i) (blocks i).1 then 1 else 0) := by
      funext blocks
      have hiff := isHamiltonCycle_blowup_iff_internalArcSets base
        (fun i => (blocks i).1) σ
      by_cases hi : ∀ i, ContainsArcSet (internalCycleArcSet σ i) (blocks i).1
      · have hh := hiff.mpr ⟨hglobal.1, hglobal.2, hi⟩
        simp only [ite_eq_left hh, ite_eq_left hi]
      · have hh : ¬ IsHamiltonCycle (blowupArc base (fun i => (blocks i).1)) σ :=
          fun h => hi (hiff.mp h).2.2
        simp only [ite_eq_right hh, ite_eq_right hi]
    rw [hevent]
    exact regularBlockEvents_mean_eq_product (internalCycleArcSet σ) hlegal.1
  · rw [ite_eq_right hglobal]
    have hfalse (blocks : RegularSample d m) :
        ¬ IsHamiltonCycle (blowupArc base (fun i => (blocks i).1)) σ := by
      intro h
      have hh := (isHamiltonCycle_blowup_iff_internalArcSets base
        (fun i => (blocks i).1) σ).mp h
      exact hglobal ⟨hh.1, hh.2.1⟩
    simp only [hfalse, ite_false, uniformMean, Nat.cast_zero, Finset.sum_const_zero, zero_div]

theorem internalCycleArcSet_no_loops {d m : ℕ} (σ : Equiv.Perm (Fin d × Fin m))
    (hN : 3 ≤ d * m) (hσ : SingleOrbit σ) (i : Fin d) (v : Fin m) :
    (v, v) ∉ internalCycleArcSet σ i := by
  rw [mem_internalCycleArcSet]
  exact singleOrbit_no_fixedPoint (by simpa using hN) σ hσ (i, v)

theorem internalCycleArcSet_no_opposite {d m : ℕ} (σ : Equiv.Perm (Fin d × Fin m))
    (hN : 3 ≤ d * m) (hσ : SingleOrbit σ) (i : Fin d) (u v : Fin m) :
    (u, v) ∈ internalCycleArcSet σ i → (v, u) ∉ internalCycleArcSet σ i := by
  simp only [mem_internalCycleArcSet]
  intro huv hvu
  exact singleOrbit_no_twoCycle (by simpa using hN) σ hσ (i, u) (i, v) ⟨huv, hvu⟩

end
end Wormald.FiniteModel

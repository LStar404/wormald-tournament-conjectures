import Wormald.CyclicTripleBasics
import Wormald.RegularCycleTransfer

namespace Wormald.FiniteModel

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Vertices of an internal arc set having both an incoming and an outgoing
prescribed arc. This is the `b` statistic in the regular-block correction. -/
def internalInOutCount {m : ℕ} (D : Finset (Fin m × Fin m)) : ℕ :=
  (Finset.univ.filter (fun a => (∃ b, (b, a) ∈ D) ∧ ∃ c, (a, c) ∈ D)).card

theorem internalCycleArcSet_incoming_iff {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d) (a : Fin m) :
    (∃ b, (b, a) ∈ internalCycleArcSet σ i) ↔ (σ.symm (i, a)).1 = i := by
  constructor
  · rintro ⟨b, hb⟩
    have he := congrArg σ.symm ((mem_internalCycleArcSet σ i b a).mp hb)
    simp only [Equiv.symm_apply_apply] at he
    exact (congrArg Prod.fst he).symm
  · intro h
    refine ⟨(σ.symm (i, a)).2, (mem_internalCycleArcSet σ i _ a).mpr ?_⟩
    have he : (i, (σ.symm (i, a)).2) = σ.symm (i, a) := Prod.ext h.symm rfl
    rw [he, Equiv.apply_symm_apply]

theorem internalCycleArcSet_outgoing_iff {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d) (a : Fin m) :
    (∃ b, (a, b) ∈ internalCycleArcSet σ i) ↔ (σ (i, a)).1 = i := by
  constructor
  · rintro ⟨b, hb⟩
    exact congrArg Prod.fst ((mem_internalCycleArcSet σ i a b).mp hb)
  · intro h
    exact ⟨(σ (i, a)).2, (mem_internalCycleArcSet σ i a _).mpr (Prod.ext h rfl)⟩

theorem internalCycleArcSet_outgoing_unique {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d) (a b c : Fin m)
    (hb : (a, b) ∈ internalCycleArcSet σ i) (hc : (a, c) ∈ internalCycleArcSet σ i) : b = c := by
  exact congrArg Prod.snd (((mem_internalCycleArcSet σ i a b).mp hb).symm.trans
    ((mem_internalCycleArcSet σ i a c).mp hc))

theorem internalCycleArcSet_incoming_unique {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d) (a b c : Fin m)
    (hb : (b, a) ∈ internalCycleArcSet σ i) (hc : (c, a) ∈ internalCycleArcSet σ i) : b = c := by
  exact congrArg Prod.snd (σ.injective
    (((mem_internalCycleArcSet σ i b a).mp hb).trans ((mem_internalCycleArcSet σ i c a).mp hc).symm))

theorem internalInOutCount_internalCycleArcSet {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d) :
    internalInOutCount (internalCycleArcSet σ i) =
      ∑ a, if (σ.symm (i, a)).1 = i ∧ (σ (i, a)).1 = i then 1 else 0 := by
  simp only [internalInOutCount, Finset.card_filter, internalCycleArcSet_incoming_iff,
    internalCycleArcSet_outgoing_iff]

def successorTripleCount {d m : ℕ} (σ : Equiv.Perm (Fin d × Fin m)) : ℕ :=
  ∑ v, if v.1 = (σ v).1 ∧ (σ v).1 = (σ (σ v)).1 then 1 else 0

/-- Reindexing the central vertex by its predecessor converts simultaneous
internal in/out incidence into a three-label event along the successor. -/
theorem sum_internalInOutCount_eq_successorTripleCount {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) :
    (∑ i, internalInOutCount (internalCycleArcSet σ i)) = successorTripleCount σ := by
  simp_rw [internalInOutCount_internalCycleArcSet]
  let F : (Fin d × Fin m) → ℕ := fun v =>
    if (σ.symm v).1 = v.1 ∧ (σ v).1 = v.1 then 1 else 0
  change (∑ i, ∑ a, F (i, a)) = successorTripleCount σ
  rw [← Fintype.sum_prod_type F]
  symm
  apply Fintype.sum_equiv σ
  intro v
  dsimp [F]
  simp only [Equiv.symm_apply_apply]
  simp [eq_comm]

theorem successorTripleCount_orderSuccessor {d m : ℕ}
    (e : Fin (Fintype.card (Fin d × Fin m)) ≃ (Fin d × Fin m)) :
    successorTripleCount (orderSuccessor e) = cyclicTripleCount (fun t => (e t).1) := by
  unfold successorTripleCount cyclicTripleCount cyclicTripleIndicator
  symm
  apply Fintype.sum_equiv e
  intro t
  simp only [orderSuccessor_order_apply]

/-- The correction statistic of the actual internal prescribed arc sets is
exactly the cyclic triple statistic whose concentration has been proved. -/
theorem sum_internalInOutCount_orderSuccessor_eq_cyclicTripleCount {d m : ℕ}
    (e : Fin (Fintype.card (Fin d × Fin m)) ≃ (Fin d × Fin m)) :
    (∑ i, internalInOutCount (internalCycleArcSet (orderSuccessor e) i)) =
      cyclicTripleCount (fun t => (e t).1) := by
  rw [sum_internalInOutCount_eq_successorTripleCount, successorTripleCount_orderSuccessor]

end
end Wormald.FiniteModel

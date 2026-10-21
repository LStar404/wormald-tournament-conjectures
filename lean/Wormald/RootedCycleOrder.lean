import Wormald.ExactCycleTransfer
import Mathlib.Logic.Equiv.Fin.Rotate

/-! A single-orbit successor together with its chosen starting vertex is
exactly a bijective cyclic vertex order. This supplies the precise rotation
factor used in the trace coefficient formula. -/

namespace Wormald.FiniteModel
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [Nonempty V]

private instance cardNeZero : NeZero (Fintype.card V) := ⟨ne_of_gt Fintype.card_pos⟩

def orbitOrder (σ : Equiv.Perm V) (hσ : SingleOrbit σ) (v : V) : Fin (Fintype.card V) ≃ V :=
  Equiv.ofBijective (fun i => (σ^[i.val]) v)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨fun w => hσ v w, Fintype.card_fin _⟩)

omit [Nonempty V] in
@[simp] theorem orbitOrder_apply (σ : Equiv.Perm V) (hσ : SingleOrbit σ) (v : V)
    (i : Fin (Fintype.card V)) : orbitOrder σ hσ v i = (σ^[i.val]) v := rfl

@[simp] theorem orbitOrder_zero (σ : Equiv.Perm V) (hσ : SingleOrbit σ) (v : V) :
    orbitOrder σ hσ v 0 = v := rfl

theorem singleOrbit_iterate_card (σ : Equiv.Perm V) (hσ : SingleOrbit σ) (v : V) :
    (σ^[Fintype.card V]) v = v := by
  obtain ⟨k, hk⟩ := hσ v (σ.symm v)
  have hperiod : (σ^[k.val + 1]) v = v := by
    rw [Function.iterate_succ_apply', hk, Equiv.apply_symm_apply]
  have hlast : k.val + 1 = Fintype.card V := by
    by_contra h
    have hlt : k.val + 1 < Fintype.card V := by omega
    have heq : orbitOrder σ hσ v ⟨k.val + 1, hlt⟩ = orbitOrder σ hσ v 0 := hperiod
    have hval := congrArg Fin.val ((orbitOrder σ hσ v).injective heq)
    simp only [Fin.val_zero] at hval
    omega
  rwa [hlast] at hperiod

private theorem finRotate_val (n : ℕ) (i : Fin n) :
    (finRotate n i).val = if i.val + 1 < n then i.val + 1 else 0 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
      rw [coe_finRotate]
      by_cases h : i = Fin.last n
      · subst i
        simp
      · have hi := Fin.val_lt_last h
        simp [h, show i.val + 1 < n + 1 by omega]

theorem orbitOrder_rotate (σ : Equiv.Perm V) (hσ : SingleOrbit σ) (v : V)
    (i : Fin (Fintype.card V)) :
    orbitOrder σ hσ v (finRotate (Fintype.card V) i) = σ (orbitOrder σ hσ v i) := by
  simp only [orbitOrder_apply, finRotate_val]
  by_cases hi : i.val + 1 < Fintype.card V
  · rw [ite_eq_left hi, Function.iterate_succ_apply']
  · have hlast : i.val + 1 = Fintype.card V := by omega
    rw [ite_eq_right hi]
    change v = σ ((σ^[i.val]) v)
    rw [← Function.iterate_succ_apply' σ i.val v]
    change v = (σ^[i.val + 1]) v
    rw [hlast, singleOrbit_iterate_card σ hσ v]

def orderSuccessor (e : Fin (Fintype.card V) ≃ V) : Equiv.Perm V :=
  e.symm.trans ((finRotate (Fintype.card V)).trans e)

omit [Nonempty V] in
@[simp] theorem orderSuccessor_order_apply (e : Fin (Fintype.card V) ≃ V)
    (i : Fin (Fintype.card V)) :
    orderSuccessor e (e i) = e (finRotate (Fintype.card V) i) := by
  simp [orderSuccessor]

theorem orderSuccessor_singleOrbit (e : Fin (Fintype.card V) ≃ V) :
    SingleOrbit (orderSuccessor e) := by
  intro v w
  let k : Fin (Fintype.card V) := e.symm w - e.symm v
  have hrot : ((finRotate (Fintype.card V))^[k.val]) (e.symm v) = e.symm w := by
    rw [← finCycle_eq_finRotate_iterate]
    simp [finCycle, k]
  have hsem : Function.Semiconj e (finRotate (Fintype.card V)) (orderSuccessor e) := by
    intro i
    simp
  refine ⟨k, ?_⟩
  have h := hsem.iterate_right k.val (e.symm v)
  rw [hrot] at h
  simpa using h.symm

theorem orderSuccessor_orbitOrder (σ : Equiv.Perm V) (hσ : SingleOrbit σ) (v : V) :
    orderSuccessor (orbitOrder σ hσ v) = σ := by
  ext w
  obtain ⟨i, rfl⟩ := (orbitOrder σ hσ v).surjective w
  rw [orderSuccessor_order_apply, orbitOrder_rotate]

theorem orbitOrder_orderSuccessor (e : Fin (Fintype.card V) ≃ V) :
    orbitOrder (orderSuccessor e) (orderSuccessor_singleOrbit e) (e 0) = e := by
  ext i
  have hrot : ((finRotate (Fintype.card V))^[i.val]) 0 = i := by
    rw [← finCycle_eq_finRotate_iterate]
    simp [finCycle]
  have hsem : Function.Semiconj e (finRotate (Fintype.card V)) (orderSuccessor e) := by
    intro i
    simp
  have h := hsem.iterate_right i.val 0
  rw [hrot] at h
  exact h.symm

/-- Choosing a starting vertex removes exactly the cyclic rotation ambiguity. -/
def rootedCycleEquivOrder : ({σ : Equiv.Perm V // SingleOrbit σ} × V) ≃
    (Fin (Fintype.card V) ≃ V) where
  toFun p := orbitOrder p.1.1 p.1.2 p.2
  invFun e := (⟨orderSuccessor e, orderSuccessor_singleOrbit e⟩, e 0)
  left_inv p := by
    apply Prod.ext
    · exact Subtype.ext (orderSuccessor_orbitOrder p.1.1 p.1.2 p.2)
    · exact orbitOrder_zero p.1.1 p.1.2 p.2
  right_inv := orbitOrder_orderSuccessor

def rootedOrderWeight (A : Matrix V V ℝ) (e : Fin (Fintype.card V) ≃ V) : ℝ :=
  ∏ i, A (e i) (e (finRotate (Fintype.card V) i))

theorem rootedOrderWeight_orbitOrder (A : Matrix V V ℝ)
    (σ : Equiv.Perm V) (hσ : SingleOrbit σ) (v : V) :
    rootedOrderWeight A (orbitOrder σ hσ v) = ∏ w, A w (σ w) := by
  unfold rootedOrderWeight
  simp only [orbitOrder_rotate]
  exact Equiv.prod_comp (orbitOrder σ hσ v) (fun w => A w (σ w))

variable [DecidableEq V]

omit [Nonempty V] in
theorem weightedHamiltonianCycleSum_eq_subtype (A : Matrix V V ℝ) :
    weightedHamiltonianCycleSum A =
      ∑ σ : {σ : Equiv.Perm V // SingleOrbit σ}, ∏ v, A v (σ.1 v) := by
  unfold weightedHamiltonianCycleSum
  simpa only [Finset.sum_filter] using
    (Finset.sum_subtype (Finset.univ.filter (fun σ : Equiv.Perm V => SingleOrbit σ))
      (by simp) (fun σ => ∏ v, A v (σ v)))

/-- Summing over all vertex orders counts each successor cycle exactly once
for each possible starting vertex. -/
theorem rootedOrder_sum_eq_card_mul_weightedSum (A : Matrix V V ℝ) :
    (∑ e : Fin (Fintype.card V) ≃ V, rootedOrderWeight A e) =
      (Fintype.card V : ℝ) * weightedHamiltonianCycleSum A := by
  have hsum := Fintype.sum_equiv (rootedCycleEquivOrder (V := V))
    (fun p : {σ : Equiv.Perm V // SingleOrbit σ} × V => ∏ v, A v (p.1.1 v))
    (rootedOrderWeight A)
    (fun p => (rootedOrderWeight_orbitOrder A p.1.1 p.1.2 p.2).symm)
  rw [← hsum, weightedHamiltonianCycleSum_eq_subtype]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum]

theorem expectedCycles_eq_rootedOrderSum {d : ℕ} (base : Orientation d)
    (m : ℕ) (hN : 3 ≤ d * m) :
    (expectedCycles base m : ℝ) =
      (∑ e : Fin (Fintype.card (Fin d × Fin m)) ≃ (Fin d × Fin m),
        rootedOrderWeight (blockConstantMatrix (weightedBase base) m) e) / (d * m : ℕ) := by
  have : Nonempty (Fin d × Fin m) :=
    Fintype.card_pos_iff.mp (by simpa using (show 0 < d * m by omega))
  rw [rootedOrder_sum_eq_card_mul_weightedSum
      (V := Fin d × Fin m) (blockConstantMatrix (weightedBase base) m),
    ← expectedCycles_eq_weightedHamiltonianCycleSum base m hN]
  have hNr : ((d * m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show d * m ≠ 0 by omega)
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact (mul_div_cancel_left₀ _ hNr).symm

end
end Wormald.FiniteModel


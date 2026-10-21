import Wormald.RootedCycleOrder
import Mathlib.Logic.Equiv.Basic

/-! A balanced cyclic base word has exactly `(m!)^d` bijective vertex
labelings. The proof constructs a labeling and identifies its full fiber
with the group of permutations internal to the blocks. -/

namespace Wormald.FiniteModel
noncomputable section
attribute [local instance] Classical.propDecidable

def firstProjectionFiberEquiv {d m : ℕ} (i : Fin d) :
    {v : Fin d × Fin m // v.1 = i} ≃ Fin m where
  toFun v := v.1.2
  invFun k := ⟨(i, k), rfl⟩
  left_inv v := Subtype.ext (Prod.ext v.2.symm rfl)
  right_inv _ := rfl

theorem firstProjectionFiber_card_eq {d m : ℕ} (i : Fin d) :
    Fintype.card {v : Fin d × Fin m // v.1 = i} = m :=
  (Fintype.card_congr (firstProjectionFiberEquiv i)).trans (Fintype.card_fin m)

theorem blockPreservingPerm_card (d m : ℕ) :
    Fintype.card {σ : Equiv.Perm (Fin d × Fin m) // Prod.fst ∘ σ = Prod.fst} =
      Nat.factorial m ^ d := by
  rw [DomMulAct.stabilizer_card]
  simp only [firstProjectionFiber_card_eq, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

abbrev labelingFiber {U : Type*} {d m : ℕ} (f : U → Fin d) :=
  {e : U ≃ (Fin d × Fin m) // (fun u => (e u).1) = f}

def balancedLabeling {U : Type*} [Fintype U] [DecidableEq U] {d m : ℕ}
    (f : U → Fin d) (hf : ∀ i, Fintype.card {u // f u = i} = m) : labelingFiber (m := m) f :=
  let efiber : ∀ i, {u // f u = i} ≃ {v : Fin d × Fin m // v.1 = i} :=
    fun i => Fintype.equivOfCardEq ((hf i).trans (firstProjectionFiber_card_eq i).symm)
  ⟨Equiv.ofFiberEquiv efiber, funext (Equiv.ofFiberEquiv_map efiber)⟩

/-- Once one labeling is fixed, all others differ by exactly one permutation
internal to the target blocks. -/
def labelingFiberEquivBlockPerm {U : Type*} {d m : ℕ} (f : U → Fin d)
    (e₀ : labelingFiber (m := m) f) : labelingFiber (m := m) f ≃
      {σ : Equiv.Perm (Fin d × Fin m) // Prod.fst ∘ σ = Prod.fst} where
  toFun e := ⟨e₀.1.symm.trans e.1, by
    funext v
    change (e.1 (e₀.1.symm v)).1 = v.1
    rw [congrFun e.2 (e₀.1.symm v), ← congrFun e₀.2 (e₀.1.symm v)]
    rw [Equiv.apply_symm_apply]⟩
  invFun σ := ⟨e₀.1.trans σ.1, by
    funext u
    change (σ.1 (e₀.1 u)).1 = f u
    change (Prod.fst ∘ σ.1) (e₀.1 u) = f u
    rw [σ.2]
    exact congrFun e₀.2 u⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro u
    change e.1 (e₀.1.symm (e₀.1 u)) = e.1 u
    rw [Equiv.symm_apply_apply]
  right_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro v
    change σ.1 (e₀.1 (e₀.1.symm v)) = σ.1 v
    rw [Equiv.apply_symm_apply]

/-- The exact factorial labeling multiplicity of a balanced base word. -/
theorem labelingFiber_card {U : Type*} [Fintype U] [DecidableEq U] {d m : ℕ}
    (f : U → Fin d) (hf : ∀ i, Fintype.card {u // f u = i} = m) :
    Fintype.card (labelingFiber (m := m) f) = Nat.factorial m ^ d :=
  (Fintype.card_congr (labelingFiberEquivBlockPerm f (balancedLabeling f hf))).trans
    (blockPreservingPerm_card d m)

theorem labelingFiber_balanced {U : Type*} [Fintype U] [DecidableEq U] {d m : ℕ}
    (f : U → Fin d) (e : labelingFiber (m := m) f) :
    ∀ i, Fintype.card {u // f u = i} = m := by
  intro i
  let efiber : {u // f u = i} ≃ {v : Fin d × Fin m // v.1 = i} :=
    e.1.subtypeEquiv (by intro u; rw [congrFun e.2 u])
  exact (Fintype.card_congr efiber).trans (firstProjectionFiber_card_eq i)

theorem labelingFiber_nonempty_iff {U : Type*} [Fintype U] [DecidableEq U] {d m : ℕ}
    (f : U → Fin d) : Nonempty (labelingFiber (m := m) f) ↔
      ∀ i, Fintype.card {u // f u = i} = m := by
  constructor
  · rintro ⟨e⟩
    exact labelingFiber_balanced f e
  · intro hf
    exact ⟨balancedLabeling f hf⟩

theorem labelingFiber_card_eq_ite {U : Type*} [Fintype U] [DecidableEq U] {d m : ℕ}
    (f : U → Fin d) : Fintype.card (labelingFiber (m := m) f) =
      if ∀ i, Fintype.card {u // f u = i} = m then Nat.factorial m ^ d else 0 := by
  split_ifs with hf
  · exact labelingFiber_card f hf
  · have hempty : IsEmpty (labelingFiber (m := m) f) :=
      not_nonempty_iff.mp (fun h => hf ((labelingFiber_nonempty_iff f).mp h))
    exact Fintype.card_eq_zero

end
end Wormald.FiniteModel

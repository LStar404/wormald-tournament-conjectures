import Wormald.FiniteModel

/-!
# Relabelling preserves exact Hamilton counts and independent-model expectations

The equivalences here preserve edge directions. No switching operation is used.
-/

namespace Wormald.FiniteModel

private theorem permCongr_iterate {V : Type*} (e σ : Equiv.Perm V)
    (k : ℕ) (v : V) :
    ((e.permCongr σ)^[k]) (e v) = e ((σ^[k]) v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ih, Equiv.permCongr_apply,
      Equiv.symm_apply_apply]

private theorem hamiltonCycle_transport {V : Type*} [Fintype V]
    (a b : V → V → Bool) (e : Equiv.Perm V)
    (he : ∀ v w, a v w = b (e v) (e w))
    (σ : Equiv.Perm V) (hσ : IsHamiltonCycle a σ) :
    IsHamiltonCycle b (e.permCongr σ) := by
  constructor
  · intro v w
    obtain ⟨k, hk⟩ := hσ.1 (e.symm v) (e.symm w)
    refine ⟨k, ?_⟩
    calc
      ((e.permCongr σ)^[k.val]) v = e ((σ^[k.val]) (e.symm v)) := by
        simpa only [Equiv.apply_symm_apply] using permCongr_iterate e σ k.val (e.symm v)
      _ = w := by rw [hk, Equiv.apply_symm_apply]
  · intro v
    have ha := hσ.2 (e.symm v)
    rw [he] at ha
    simpa only [Equiv.permCongr_apply, Equiv.apply_symm_apply] using ha

/-- A direction-preserving relabelling preserves each cycle count exactly. -/
theorem hamiltonCycleCount_relabel {V : Type*} [Fintype V]
    (a b : V → V → Bool) (e : Equiv.Perm V)
    (he : ∀ v w, a v w = b (e v) (e w)) :
    hamiltonCycleCount a = hamiltonCycleCount b := by
  apply Nat.card_congr
  apply e.permCongr.subtypeEquiv
  intro σ
  constructor
  · exact hamiltonCycle_transport a b e he σ
  · intro hσ
    have hrev : ∀ v w, b v w = a (e.symm v) (e.symm w) := by
      intro v w
      simpa only [Equiv.apply_symm_apply] using (he (e.symm v) (e.symm w)).symm
    have ht := hamiltonCycle_transport b a e.symm hrev (e.permCongr σ) hσ
    simpa only [← Equiv.permCongr_symm, Equiv.symm_apply_apply] using ht

/-- A direction-preserving relabelling preserves each ordered Hamilton path count. -/
theorem hamiltonPathCount_relabel {V : Type*} [Fintype V]
    (a b : V → V → Bool) (e : Equiv.Perm V)
    (he : ∀ v w, a v w = b (e v) (e w)) :
    hamiltonPathCount a = hamiltonPathCount b := by
  apply Nat.card_congr
  apply ((Equiv.refl (Fin (Fintype.card V))).equivCongr e).subtypeEquiv
  intro π
  simp only [IsHamiltonPath, Equiv.equivCongr_apply_apply,
    Equiv.refl_symm, Equiv.refl_apply, he]

private def relabelBlocks {d m : ℕ} (e : Equiv.Perm (Fin d)) :
    IndependentSample d m ≃ IndependentSample d m where
  toFun blocks j := blocks (e.symm j)
  invFun blocks j := blocks (e j)
  left_inv blocks := by funext j; simp
  right_inv blocks := by funext j; simp

private def relabelRegularBlocks {d m : ℕ} (e : Equiv.Perm (Fin d)) :
    RegularSample d m ≃ RegularSample d m where
  toFun blocks j := blocks (e.symm j)
  invFun blocks j := blocks (e j)
  left_inv blocks := by funext j; simp
  right_inv blocks := by funext j; simp

private def relabelVertices {d m : ℕ} (e : Equiv.Perm (Fin d)) :
    Equiv.Perm (Fin d × Fin m) where
  toFun v := (e v.1, v.2)
  invFun v := (e.symm v.1, v.2)
  left_inv v := by simp
  right_inv v := by simp

private theorem blowupArc_relabel {d m : ℕ} (T U : Orientation d)
    (e : Equiv.Perm (Fin d)) (he : ∀ i j, arc T i j = arc U (e i) (e j))
    (blocks : IndependentSample d m) (v w : Fin d × Fin m) :
    blowupArc T blocks v w =
      blowupArc U (relabelBlocks e blocks) (relabelVertices e v) (relabelVertices e w) := by
  change (if v.1 = w.1 then arc (blocks v.1) v.2 w.2 else arc T v.1 w.1) =
    (if e v.1 = e w.1 then arc (blocks (e.symm (e v.1))) v.2 w.2
      else arc U (e v.1) (e w.1))
  simp only [Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq, he]

/-- Exact independent-block cycle expectation is invariant under ordinary isomorphism. -/
theorem expectedCycles_isomorphic {d : ℕ} (T U : Orientation d)
    (hiso : Isomorphic T U) (m : ℕ) : expectedCycles T m = expectedCycles U m := by
  obtain ⟨e, he⟩ := hiso
  unfold expectedCycles uniformMean
  congr 1
  apply Fintype.sum_equiv (relabelBlocks e)
  intro blocks
  exact_mod_cast hamiltonCycleCount_relabel
    (blowupArc T blocks) (blowupArc U (relabelBlocks e blocks))
    (relabelVertices e) (blowupArc_relabel T U e he blocks)

/-- Exact independent-block path expectation is invariant under ordinary isomorphism. -/
theorem expectedPaths_isomorphic {d : ℕ} (T U : Orientation d)
    (hiso : Isomorphic T U) (m : ℕ) : expectedPaths T m = expectedPaths U m := by
  obtain ⟨e, he⟩ := hiso
  unfold expectedPaths uniformMean
  congr 1
  apply Fintype.sum_equiv (relabelBlocks e)
  intro blocks
  exact_mod_cast hamiltonPathCount_relabel
    (blowupArc T blocks) (blowupArc U (relabelBlocks e blocks))
    (relabelVertices e) (blowupArc_relabel T U e he blocks)

/-- The uniform regular-block cycle expectation is also invariant under
ordinary isomorphism; regular block edges are not treated as independent. -/
theorem expectedRegularCycles_isomorphic {d : ℕ} (T U : Orientation d)
    (hiso : Isomorphic T U) (m : ℕ) (hlegal : LegalRegularOrder d m) :
    expectedRegularCycles T m hlegal = expectedRegularCycles U m hlegal := by
  classical
  let : Fintype (RegularSample d m) := Fintype.ofFinite _
  let : Nonempty (RegularSample d m) := hlegal.2
  obtain ⟨e, he⟩ := hiso
  unfold expectedRegularCycles uniformMean
  congr 1
  apply Fintype.sum_equiv (relabelRegularBlocks e)
  intro blocks
  exact_mod_cast hamiltonCycleCount_relabel
    (blowupArc T (fun i => (blocks i).1))
    (blowupArc U (fun i => (relabelRegularBlocks e blocks i).1))
    (relabelVertices e) (blowupArc_relabel T U e he (fun i => (blocks i).1))

/-- The uniform regular-block path expectation is invariant under ordinary isomorphism. -/
theorem expectedRegularPaths_isomorphic {d : ℕ} (T U : Orientation d)
    (hiso : Isomorphic T U) (m : ℕ) (hlegal : LegalRegularOrder d m) :
    expectedRegularPaths T m hlegal = expectedRegularPaths U m hlegal := by
  classical
  let : Fintype (RegularSample d m) := Fintype.ofFinite _
  let : Nonempty (RegularSample d m) := hlegal.2
  obtain ⟨e, he⟩ := hiso
  unfold expectedRegularPaths uniformMean
  congr 1
  apply Fintype.sum_equiv (relabelRegularBlocks e)
  intro blocks
  exact_mod_cast hamiltonPathCount_relabel
    (blowupArc T (fun i => (blocks i).1))
    (blowupArc U (fun i => (relabelRegularBlocks e blocks i).1))
    (relabelVertices e) (blowupArc_relabel T U e he (fun i => (blocks i).1))

end Wormald.FiniteModel

import Wormald.FiniteModel

/-!
# Regular carousel bases and nonempty regular-block sample spaces
-/

namespace Wormald.FiniteModel

private def clockwiseNeighbor {n : ℕ} (i : Fin n) (k : Fin (n / 2)) : Fin n :=
  ⟨if i.val + k.val + 1 < n then i.val + k.val + 1
    else i.val + k.val + 1 - n, by
    have hi := i.isLt
    have hk := k.isLt
    split_ifs <;> omega⟩

private theorem clockwiseNeighbor_arc {n : ℕ} (hn : Odd n)
    (i : Fin n) (k : Fin (n / 2)) :
    arc (carousel n) i (clockwiseNeighbor i k) = true := by
  apply (carousel_arc_iff hn i (clockwiseNeighbor i k)).2
  have hi := i.isLt
  have hk := k.isLt
  unfold clockwiseDistance clockwiseNeighbor
  simp only [Fin.le_def]
  split_ifs <;> omega

private theorem clockwiseNeighbor_injective {n : ℕ} (i : Fin n) :
    Function.Injective (clockwiseNeighbor i) := by
  intro k l h
  apply Fin.ext
  have heq := congrArg Fin.val h
  have hi := i.isLt
  have hk := k.isLt
  have hl := l.isLt
  dsimp [clockwiseNeighbor] at heq
  split_ifs at heq <;> omega

private theorem clockwiseNeighbor_surjective {n : ℕ} (hn : Odd n) (i : Fin n) :
    ∀ j, arc (carousel n) i j = true → ∃ k : Fin (n / 2), clockwiseNeighbor i k = j := by
  intro j hj
  have hd := (carousel_arc_iff hn i j).1 hj
  have hk : clockwiseDistance i j - 1 < n / 2 := by omega
  refine ⟨⟨clockwiseDistance i j - 1, hk⟩, ?_⟩
  apply Fin.ext
  have hi := i.isLt
  have hjlt := j.isLt
  dsimp [clockwiseNeighbor]
  unfold clockwiseDistance at *
  split_ifs at * <;> omega

private noncomputable def carouselNeighborEquiv {n : ℕ} (hn : Odd n) (i : Fin n) :
    Fin (n / 2) ≃ {j : Fin n // arc (carousel n) i j = true} :=
  Equiv.ofBijective
    (fun k => ⟨clockwiseNeighbor i k, clockwiseNeighbor_arc hn i k⟩)
    ⟨by
      intro k l h
      apply clockwiseNeighbor_injective i
      exact congrArg Subtype.val h,
     by
      intro j
      obtain ⟨k, hk⟩ := clockwiseNeighbor_surjective hn i j.val j.property
      exact ⟨k, Subtype.ext hk⟩⟩

/-- Every vertex of the odd-order carousel has exactly n/2 outgoing neighbours. -/
theorem carousel_outdegree {n : ℕ} (hn : Odd n) (i : Fin n) :
    Fintype.card {j : Fin n // arc (carousel n) i j = true} = n / 2 := by
  simpa using (Fintype.card_congr (carouselNeighborEquiv hn i)).symm

/-- The carousel satisfies the exact regularity definition used in the Hessian model. -/
theorem carousel_regular {n : ℕ} (hn : Odd n) : (toTournament (carousel n)).Regular := by
  intro i
  change (∑ j, if arc (carousel n) i j then (1 : ℚ) else 0) = ((n : ℚ) - 1) / 2
  have hcard := carousel_outdegree hn i
  rw [Fintype.card_subtype] at hcard
  have hcount : (∑ j : Fin n, if arc (carousel n) i j then (1 : ℕ) else 0) = n / 2 := by
    rw [Finset.card_filter] at hcard
    exact hcard
  have hsum : (∑ j : Fin n, if arc (carousel n) i j then (1 : ℚ) else 0) = (n / 2 : ℕ) := by
    exact_mod_cast hcount
  rw [hsum]
  rcases hn with ⟨k, hk⟩
  have hq : n / 2 = k := by omega
  rw [hq, hk]
  push_cast
  ring

/-- A regular internal tournament exists at every odd order, including order one. -/
theorem regularSample_nonempty (d m : ℕ) (hm : Odd m) : Nonempty (RegularSample d m) :=
  ⟨fun _ => ⟨carousel m, carousel_regular hm⟩⟩

/-- The support condition in the regular model follows from the original parity condition. -/
theorem legalRegularOrder_iff (d m : ℕ) : LegalRegularOrder d m ↔ Odd m :=
  ⟨fun h => h.1, fun h => ⟨h, regularSample_nonempty d m h⟩⟩

end Wormald.FiniteModel

import Wormald.CircleClusterCover
import Wormald.RegularCycleTransfer

/-! The core–outlier pairs used for a tail bound are different unordered
edges. Removing at most two neighbors at each outlier therefore leaves
at least r(c−2) separate cosine factors. -/

namespace Wormald.FiniteModel
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def canonicalEdge {m : ℕ} (u v : Fin m) (hne : u ≠ v) : Edge m :=
  if h : u < v then ⟨(u, v), h⟩ else
    ⟨(v, u), lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)⟩

theorem canonicalEdge_pair {m : ℕ} (u v : Fin m) (hne : u ≠ v) :
    (canonicalEdge u v hne).1 = (u, v) ∨ (canonicalEdge u v hne).1 = (v, u) := by
  unfold canonicalEdge
  split <;> simp

private theorem canonicalEdge_eq_or_flip {m : ℕ} {u v a b : Fin m}
    (huv : u ≠ v) (hab : a ≠ b) (h : canonicalEdge u v huv = canonicalEdge a b hab) :
    (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  have hv := congrArg Subtype.val h
  unfold canonicalEdge at hv
  split_ifs at hv <;> simp only [Prod.mk.injEq] at hv
  · exact Or.inl hv
  · exact Or.inr hv
  · exact Or.inr ⟨hv.2, hv.1⟩
  · exact Or.inl ⟨hv.2, hv.1⟩

private theorem crossPair_ne {m : ℕ} (O C : Finset (Fin m)) (hd : Disjoint O C)
    (p : {p : Fin m × Fin m // p ∈ O ×ˢ C}) : p.1.1 ≠ p.1.2 := by
  intro h
  have hp := Finset.mem_product.mp p.2
  exact Finset.disjoint_left.mp hd (h ▸ hp.1) hp.2

def crossPairEdge {m : ℕ} (O C : Finset (Fin m)) (hd : Disjoint O C)
    (p : {p : Fin m × Fin m // p ∈ O ×ˢ C}) : Edge m :=
  canonicalEdge p.1.1 p.1.2 (crossPair_ne O C hd p)

theorem crossPairEdge_injective {m : ℕ} (O C : Finset (Fin m)) (hd : Disjoint O C) :
    Function.Injective (crossPairEdge O C hd) := by
  intro p q h
  rcases canonicalEdge_eq_or_flip (crossPair_ne O C hd p) (crossPair_ne O C hd q) h with h | h
  · exact Subtype.ext (Prod.ext h.1 h.2)
  · have hp := Finset.mem_product.mp p.2
    have hq := Finset.mem_product.mp q.2
    exact False.elim (Finset.disjoint_left.mp hd hp.1 (h.1.symm ▸ hq.2))

def selectedCrossEdges {m : ℕ} (O C : Finset (Fin m)) (hd : Disjoint O C)
    (p : Fin m → Fin m → Prop) : Finset (Edge m) :=
  ((O ×ˢ C).filter (fun uv => p uv.1 uv.2)).attach.image
    (fun uv => crossPairEdge O C hd ⟨uv.1, (Finset.mem_filter.mp uv.2).1⟩)

theorem selectedCrossEdges_card {m : ℕ} (O C : Finset (Fin m)) (hd : Disjoint O C)
    (p : Fin m → Fin m → Prop) :
    (selectedCrossEdges O C hd p).card = ((O ×ˢ C).filter (fun uv => p uv.1 uv.2)).card := by
  unfold selectedCrossEdges
  rw [Finset.card_image_of_injective, Finset.card_attach]
  intro a b h
  exact Subtype.ext (congrArg (fun z : {uv : Fin m × Fin m // uv ∈ O ×ˢ C} => z.1)
    ((crossPairEdge_injective O C hd) h))

theorem selectedCrossEdges_card_lower {m : ℕ} (O C : Finset (Fin m)) (hd : Disjoint O C)
    (p : Fin m → Fin m → Prop) (Δ : ℕ)
    (hdeleted : ∀ u ∈ O, (C.filter (fun v => ¬ p u v)).card ≤ Δ) :
    O.card * (C.card - Δ) ≤ (selectedCrossEdges O C hd p).card := by
  rw [selectedCrossEdges_card]
  exact available_core_pairs_card_lower O C p Δ hdeleted

theorem selectedCrossEdges_witness {m : ℕ} (O C : Finset (Fin m)) (hd : Disjoint O C)
    (p : Fin m → Fin m → Prop) {e : Edge m} (he : e ∈ selectedCrossEdges O C hd p) :
    ∃ u ∈ O, ∃ v ∈ C, p u v ∧ (e.1 = (u, v) ∨ e.1 = (v, u)) := by
  obtain ⟨uv, _, rfl⟩ := Finset.mem_image.mp he
  have hmem := Finset.mem_filter.mp uv.2
  have hcross := Finset.mem_product.mp hmem.1
  refine ⟨uv.1.1, hcross.1, uv.1.2, hcross.2, hmem.2, ?_⟩
  exact canonicalEdge_pair _ _ _

theorem circleOutliers_disjoint_core {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16) :
    Disjoint (circleOutliers x j) (circleCore x j) := by
  apply Finset.disjoint_left.mpr
  intro i ho hc
  have hout := (mem_circleOutliers x j i).mp ho
  have hcore := (mem_circleCore x j i).mp hc
  linarith

theorem selectedCrossEdges_circle_separation {m : ℕ} (x : Fin m → UnitAddCircle) (j : Fin 16)
    (p : Fin m → Fin m → Prop) {e : Edge m}
    (he : e ∈ selectedCrossEdges (circleOutliers x j) (circleCore x j)
      (circleOutliers_disjoint_core x j) p) :
    (1 / 8 : ℝ) < dist (x e.1.1) (x e.1.2) := by
  obtain ⟨u, hu, v, hv, _, heq⟩ := selectedCrossEdges_witness _ _ _ p he
  rcases heq with heq | heq
  · rw [heq]
    exact circleCore_outlier_separation x j hu hv
  · rw [heq, dist_comm]
    exact circleCore_outlier_separation x j hu hv

/-- The genuine internal arc set of any successor permutation has at most
two incident prescribed neighbors, without a forest representation. -/
theorem internalCycleArcSet_neighbor_card_le_two {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d) (u : Fin m) (C : Finset (Fin m)) :
    (C.filter (fun v => (u, v) ∈ internalCycleArcSet σ i ∨
      (v, u) ∈ internalCycleArcSet σ i)).card ≤ 2 := by
  have hsub : C.filter (fun v => (u, v) ∈ internalCycleArcSet σ i ∨
      (v, u) ∈ internalCycleArcSet σ i) ⊆ {(σ (i, u)).2, (σ.symm (i, u)).2} := by
    intro v hv
    rcases (Finset.mem_filter.mp hv).2 with hout | hin
    · have heq := (mem_internalCycleArcSet σ i u v).mp hout
      have hval := congrArg Prod.snd heq
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl hval.symm
    · have heq := (mem_internalCycleArcSet σ i v u).mp hin
      have hpre : (i, v) = σ.symm (i, u) := (Equiv.eq_symm_apply σ).mpr heq
      have hval := congrArg Prod.snd hpre
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr hval
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem internalCycleCore_far_edges_card {d m : ℕ} (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d)
    (x : Fin m → UnitAddCircle) (j : Fin 16) :
    (circleOutliers x j).card * ((circleCore x j).card - 2) ≤
      (selectedCrossEdges (circleOutliers x j) (circleCore x j) (circleOutliers_disjoint_core x j)
        (fun u v => (u, v) ∉ internalCycleArcSet σ i ∧ (v, u) ∉ internalCycleArcSet σ i)).card := by
  apply selectedCrossEdges_card_lower _ _ _ _ 2
  intro u _
  simpa only [not_and_or, not_not] using
    internalCycleArcSet_neighbor_card_le_two σ i u (circleCore x j)

end
end Wormald.FiniteModel

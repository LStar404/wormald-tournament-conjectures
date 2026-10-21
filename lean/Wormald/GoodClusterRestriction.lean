import Wormald.RegularLocalPhase
import Wormald.PartialPermutationShift
import Mathlib.Data.Finset.Sort

/-! Restricting the genuine prescribed arc set to a good cluster, with an
order-preserving relabelling. No graph approximation is introduced. -/

namespace Wormald.FiniteModel
noncomputable section
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def goodVertex {m : ℕ} (G : Finset (Fin m)) (i : Fin G.card) : Fin m :=
  (G.orderIsoOfFin rfl i).1

theorem goodVertex_injective {m : ℕ} (G : Finset (Fin m)) :
    Function.Injective (goodVertex G) :=
  Subtype.val_injective.comp (G.orderIsoOfFin rfl).injective

@[simp] theorem goodVertex_mem {m : ℕ} (G : Finset (Fin m)) (i : Fin G.card) :
    goodVertex G i ∈ G := (G.orderIsoOfFin rfl i).2

theorem goodVertex_strictMono {m : ℕ} (G : Finset (Fin m)) :
    StrictMono (goodVertex G) := by
  intro i j hij
  exact (G.orderIsoOfFin rfl).strictMono hij

theorem goodVertex_surjective {m : ℕ} (G : Finset (Fin m)) (v : Fin m) (hv : v ∈ G) :
    ∃ i, goodVertex G i = v := by
  refine ⟨(G.orderIsoOfFin rfl).symm ⟨v, hv⟩, ?_⟩
  exact congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨v, hv⟩)

def restrictedArcSet {m : ℕ} (D : Finset (Fin m × Fin m)) (G : Finset (Fin m)) :
    Finset (Fin G.card × Fin G.card) :=
  Finset.univ.filter (fun p => (goodVertex G p.1, goodVertex G p.2) ∈ D)

@[simp] theorem mem_restrictedArcSet {m : ℕ} (D : Finset (Fin m × Fin m))
    (G : Finset (Fin m)) (p : Fin G.card × Fin G.card) :
    p ∈ restrictedArcSet D G ↔ (goodVertex G p.1, goodVertex G p.2) ∈ D := by
  simp [restrictedArcSet]

theorem restrictedArcSet_source_injOn {m : ℕ} (D : Finset (Fin m × Fin m))
    (G : Finset (Fin m)) (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D) :
    Set.InjOn (Prod.fst : Fin G.card × Fin G.card → Fin G.card) (restrictedArcSet D G) := by
  intro p hp q hq hpq
  apply Prod.ext hpq
  apply goodVertex_injective G
  exact congrArg Prod.snd (hs (mem_restrictedArcSet D G p |>.mp hp)
    (mem_restrictedArcSet D G q |>.mp hq) (congrArg (goodVertex G) hpq))

theorem restrictedArcSet_target_injOn {m : ℕ} (D : Finset (Fin m × Fin m))
    (G : Finset (Fin m)) (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D) :
    Set.InjOn (Prod.snd : Fin G.card × Fin G.card → Fin G.card) (restrictedArcSet D G) := by
  intro p hp q hq hpq
  apply Prod.ext _ hpq
  apply goodVertex_injective G
  exact congrArg Prod.fst (ht (mem_restrictedArcSet D G p |>.mp hp)
    (mem_restrictedArcSet D G q |>.mp hq) (congrArg (goodVertex G) hpq))

theorem restrictedArcSet_no_loops {m : ℕ} (D : Finset (Fin m × Fin m))
    (G : Finset (Fin m)) (hl : ∀ e ∈ D, e.1 ≠ e.2) :
    ∀ e ∈ restrictedArcSet D G, e.1 ≠ e.2 := by
  intro e he heq
  exact hl _ ((mem_restrictedArcSet D G e).mp he) (congrArg (goodVertex G) heq)

theorem restrictedArcSet_no_opposite {m : ℕ} (D : Finset (Fin m × Fin m))
    (G : Finset (Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) :
    ∀ u v, (u, v) ∈ restrictedArcSet D G → (v, u) ∉ restrictedArcSet D G := by
  intro u v huv hvu
  exact hD _ _ ((mem_restrictedArcSet D G _).mp huv) ((mem_restrictedArcSet D G _).mp hvu)

def restrictedGaussianGraphData {m : ℕ} (D : Finset (Fin m × Fin m))
    (G : Finset (Fin m)) (hl : ∀ e ∈ D, e.1 ≠ e.2)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D) : GaussianGraphData G.card :=
  partialPermutationGaussianGraphData (restrictedArcSet D G)
    (restrictedArcSet_no_loops D G hl) (restrictedArcSet_source_injOn D G hs)
    (restrictedArcSet_target_injOn D G ht)

theorem restrictedGaussianGraphData_mulVec_one {m : ℕ} (D : Finset (Fin m × Fin m))
    (G : Finset (Fin m)) (hl : ∀ e ∈ D, e.1 ≠ e.2)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D) :
    (restrictedGaussianGraphData D G hl hs ht).laplacian *ᵥ (fun _ => 1) = 0 :=
  partialLaplacian_mulVec_one _

def goodEdgeEmbedding {m : ℕ} (G : Finset (Fin m)) : Edge G.card ↪ Edge m where
  toFun e := ⟨(goodVertex G e.1.1, goodVertex G e.1.2), goodVertex_strictMono G e.2⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact Prod.ext (goodVertex_injective G (congrArg (fun e : Edge m => e.1.1) h))
      (goodVertex_injective G (congrArg (fun e : Edge m => e.1.2) h))

theorem goodEdgeEmbedding_free_image {m : ℕ} (D : Finset (Fin m × Fin m))
    (G : Finset (Fin m)) :
    (freeCosineEdges (restrictedArcSet D G)).image (goodEdgeEmbedding G) =
      goodFreeCosineEdges D G := by
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := (Finset.mem_filter.mp ha).2
    simp only [goodFreeCosineEdges, freeCosineEdges, Finset.mem_filter, Finset.mem_univ,
      true_and, goodEdgeEmbedding]
    exact ⟨⟨fun h => ha'.1 ((mem_restrictedArcSet D G _).mpr h),
      fun h => ha'.2 ((mem_restrictedArcSet D G _).mpr h)⟩, goodVertex_mem G _, goodVertex_mem G _⟩
  · intro he
    obtain ⟨hefree, heG⟩ := Finset.mem_filter.mp he
    obtain ⟨a, ha⟩ := goodVertex_surjective G e.1.1 heG.1
    obtain ⟨b, hb⟩ := goodVertex_surjective G e.1.2 heG.2
    have hab : a < b := (goodVertex_strictMono G).lt_iff_lt.mp (by simpa only [ha, hb] using e.2)
    let p : Edge G.card := ⟨(a, b), hab⟩
    have hp : goodEdgeEmbedding G p = e := Subtype.ext (Prod.ext ha hb)
    refine Finset.mem_image.mpr ⟨p, ?_, hp⟩
    have hf := (Finset.mem_filter.mp hefree).2
    simp only [freeCosineEdges, Finset.mem_filter, Finset.mem_univ, true_and, mem_restrictedArcSet]
    exact ⟨by simpa only [p, ha, hb] using hf.1, by simpa only [p, ha, hb] using hf.2⟩

theorem sum_goodFreeCosineEdges_reindex {m : ℕ} (D : Finset (Fin m × Fin m))
    (G : Finset (Fin m)) (x : Fin m → ℝ) :
    (∑ e ∈ goodFreeCosineEdges D G, (x e.1.1 - x e.1.2) ^ 2) =
      ∑ e ∈ freeCosineEdges (restrictedArcSet D G),
        (x (goodVertex G e.1.1) - x (goodVertex G e.1.2)) ^ 2 := by
  rw [← goodEdgeEmbedding_free_image D G, Finset.sum_image (goodEdgeEmbedding G).injective.injOn]
  rfl

theorem goodFreeCosineEdges_energy {m : ℕ} (D : Finset (Fin m × Fin m))
    (G : Finset (Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) (x : Fin m → ℝ) :
    (∑ e ∈ goodFreeCosineEdges D G, (x e.1.1 - x e.1.2) ^ 2) =
      completeSquareEnergy (fun i => x (goodVertex G i)) -
        (fun i => x (goodVertex G i)) ⬝ᵥ (partialLaplacian (restrictedArcSet D G) *ᵥ
          (fun i => x (goodVertex G i))) := by
  rw [sum_goodFreeCosineEdges_reindex D G x, ← freeCosineEdges_eq_sdiff]
  have hsplit := Finset.sum_sdiff (f := fun e : Edge G.card =>
    (x (goodVertex G e.1.1) - x (goodVertex G e.1.2)) ^ 2)
      (Finset.subset_univ (forcedUnorderedEdges (restrictedArcSet D G)))
  rw [sum_edges_square_eq_completeSquareEnergy (fun i => x (goodVertex G i)),
    sum_forced_square_eq_partialLaplacian _ (restrictedArcSet_no_opposite D G hD)
      (fun i => x (goodVertex G i))] at hsplit
  linarith

end
end Wormald.FiniteModel

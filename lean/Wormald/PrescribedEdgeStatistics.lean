import Wormald.RegularKernelNormalization
import Wormald.PartialPermutationLaplacian
import Wormald.GaussianQuarticIdentity

/-! Exact sums over directed prescribed edges and their unordered images.
These identities connect the actual cosine product to its Laplacian energy. -/

namespace Wormald.FiniteModel
noncomputable section
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem prescribedArc_ne {m : ℕ} (D : Finset (Fin m × Fin m))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) (p : {p // p ∈ D}) : p.1.1 ≠ p.1.2 := by
  intro h
  have hp : (p.1.1, p.1.2) ∈ D := p.2
  exact hD _ _ hp (by simpa only [h] using hp)

def prescribedArcToEdge {m : ℕ} (D : Finset (Fin m × Fin m))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) (p : {p // p ∈ D}) : Edge m :=
  canonicalEdge p.1.1 p.1.2 (prescribedArc_ne D hD p)

theorem prescribedArcToEdge_injective {m : ℕ} (D : Finset (Fin m × Fin m))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) : Function.Injective (prescribedArcToEdge D hD) := by
  intro p q h
  have hv := congrArg Subtype.val h
  unfold prescribedArcToEdge canonicalEdge at hv
  split_ifs at hv <;> simp only [Prod.mk.injEq] at hv
  · exact Subtype.ext (Prod.ext hv.1 hv.2)
  · exact False.elim (hD _ _ p.2 (by simpa only [hv.1, hv.2] using q.2))
  · exact False.elim (hD _ _ p.2 (by simpa only [hv.1, hv.2] using q.2))
  · exact Subtype.ext (Prod.ext hv.2 hv.1)

theorem prescribedArcToEdge_image {m : ℕ} (D : Finset (Fin m × Fin m))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) :
    D.attach.image (prescribedArcToEdge D hD) = forcedUnorderedEdges D := by
  ext e
  constructor
  · intro he
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp he
    have hpair := canonicalEdge_pair p.1.1 p.1.2 (prescribedArc_ne D hD p)
    change (prescribedArcToEdge D hD p).1 = p.1 ∨
      (prescribedArcToEdge D hD p).1 = (p.1.2, p.1.1) at hpair
    rw [hp] at hpair
    simp only [forcedUnorderedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hpair with h | h
    · exact Or.inl (by change e.1 ∈ D; rw [h]; exact p.2)
    · exact Or.inr (by rw [h]; exact p.2)
  · intro he
    rcases (Finset.mem_filter.mp he).2 with hf | hr
    · let p : {p // p ∈ D} := ⟨(e.1.1, e.1.2), hf⟩
      refine Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, ?_⟩
      simp only [prescribedArcToEdge, p, canonicalEdge, dite_eq_left e.2]
    · let p : {p // p ∈ D} := ⟨(e.1.2, e.1.1), hr⟩
      refine Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, ?_⟩
      simp only [prescribedArcToEdge, p, canonicalEdge, dite_eq_right (not_lt_of_gt e.2)]

theorem sum_forcedUnorderedEdges {m : ℕ} {A : Type*} [AddCommMonoid A]
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (f : Fin m → Fin m → A) (hf : ∀ i j, f i j = f j i) :
    (∑ e ∈ forcedUnorderedEdges D, f e.1.1 e.1.2) = ∑ p ∈ D, f p.1 p.2 := by
  rw [← prescribedArcToEdge_image D hD,
    Finset.sum_image (prescribedArcToEdge_injective D hD).injOn]
  calc
    _ = ∑ p ∈ D.attach, f p.1.1 p.1.2 := Finset.sum_congr rfl fun p _ => by
      rcases canonicalEdge_pair p.1.1 p.1.2 (prescribedArc_ne D hD p) with h | h
      · change (prescribedArcToEdge D hD p).1 = p.1 at h
        rw [h]
      · change (prescribedArcToEdge D hD p).1 = (p.1.2, p.1.1) at h
        rw [h]
        exact hf _ _
    _ = _ := Finset.sum_attach D (fun p => f p.1 p.2)

theorem sum_forced_square_eq_partialLaplacian {m : ℕ} (D : Finset (Fin m × Fin m))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) (x : Fin m → ℝ) :
    (∑ e ∈ forcedUnorderedEdges D, (x e.1.1 - x e.1.2) ^ 2) =
      x ⬝ᵥ (partialLaplacian D *ᵥ x) := by
  rw [partialLaplacian_quadratic]
  exact sum_forcedUnorderedEdges D hD (fun i j => (x i - x j) ^ 2) (by intros; ring)

theorem sum_edges_eq_sum_lt {m : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin m → Fin m → A) :
    (∑ e : Edge m, f e.1.1 e.1.2) = ∑ i, ∑ j, if i < j then f i j else 0 := by
  have h : (∑ p : Fin m × Fin m, if p.1 < p.2 then f p.1 p.2 else 0) =
      ∑ e : Edge m, f e.1.1 e.1.2 := by
    simpa only [Finset.sum_filter] using
      (Finset.sum_subtype (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2))
        (by simp) (fun p => f p.1 p.2))
  simpa only [Fintype.sum_prod_type] using h.symm

theorem sum_edges_square_eq_completeSquareEnergy {m : ℕ} (x : Fin m → ℝ) :
    (∑ e : Edge m, (x e.1.1 - x e.1.2) ^ 2) = completeSquareEnergy x := by
  rw [sum_edges_eq_sum_lt (fun i j => (x i - x j) ^ 2), completeSquareEnergy_eq_sum_lt]

theorem sum_edges_quartic_eq_completeQuarticEnergy {m : ℕ} (x : Fin m → ℝ) :
    (∑ e : Edge m, (x e.1.1 - x e.1.2) ^ 4) = completeQuarticEnergy x := by
  rw [sum_edges_eq_sum_lt (fun i j => (x i - x j) ^ 4), completeQuarticEnergy_eq_sum_lt]

theorem partialImbalance_dot_eq_sum {m : ℕ} (D : Finset (Fin m × Fin m)) (x : Fin m → ℝ) :
    partialImbalance D ⬝ᵥ x = ∑ p ∈ D, (x p.1 - x p.2) := by
  simp only [partialImbalance, sum_dotProduct, arcIncidence_dotProduct]

end
end Wormald.FiniteModel

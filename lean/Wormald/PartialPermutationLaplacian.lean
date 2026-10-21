import Wormald.GaussianGraphCorrection
import Wormald.InternalTripleStatistic

namespace Wormald

noncomputable section
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def arcIncidence {m : ℕ} (e : Fin m × Fin m) : Fin m → ℝ :=
  Pi.single e.1 1 - Pi.single e.2 1

def partialLaplacian {m : ℕ} (D : Finset (Fin m × Fin m)) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ e ∈ D, Matrix.vecMulVec (arcIncidence e) (arcIncidence e)

def partialImbalance {m : ℕ} (D : Finset (Fin m × Fin m)) : Fin m → ℝ :=
  ∑ e ∈ D, arcIncidence e

def partialOutgoing {m : ℕ} (D : Finset (Fin m × Fin m)) (i : Fin m) : ℝ :=
  if i ∈ D.image Prod.fst then 1 else 0

def partialIncoming {m : ℕ} (D : Finset (Fin m × Fin m)) (i : Fin m) : ℝ :=
  if i ∈ D.image Prod.snd then 1 else 0

@[simp] theorem arcIncidence_dotProduct {m : ℕ} (e : Fin m × Fin m) (x : Fin m → ℝ) :
    arcIncidence e ⬝ᵥ x = x e.1 - x e.2 := by simp [arcIncidence, sub_dotProduct]

@[simp] theorem dotProduct_arcIncidence {m : ℕ} (e : Fin m × Fin m) (x : Fin m → ℝ) :
    x ⬝ᵥ arcIncidence e = x e.1 - x e.2 := by rw [dotProduct_comm, arcIncidence_dotProduct]

theorem arcIncidence_square {m : ℕ} (e : Fin m × Fin m) (he : e.1 ≠ e.2) :
    arcIncidence e ⬝ᵥ arcIncidence e = 2 := by
  rw [arcIncidence_dotProduct]
  norm_num [arcIncidence, he, he.symm]

@[simp] theorem sum_arcIncidence {m : ℕ} (e : Fin m × Fin m) :
    ∑ i, arcIncidence e i = 0 := by simp [arcIncidence, Finset.sum_sub_distrib]

theorem partialLaplacian_positive {m : ℕ} (D : Finset (Fin m × Fin m)) :
    (partialLaplacian D).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro e _
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (arcIncidence e)

theorem partialLaplacian_quadratic {m : ℕ} (D : Finset (Fin m × Fin m)) (x : Fin m → ℝ) :
    x ⬝ᵥ (partialLaplacian D *ᵥ x) = ∑ e ∈ D, (x e.1 - x e.2) ^ 2 := by
  simp only [partialLaplacian, Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [dotProduct_mulVec, Matrix.vecMul_vecMulVec, smul_dotProduct, smul_eq_mul,
    dotProduct_arcIncidence, arcIncidence_dotProduct, pow_two]

theorem partialLaplacian_quadratic_le_four {m : ℕ} (D : Finset (Fin m × Fin m))
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D) (x : Fin m → ℝ) :
    x ⬝ᵥ (partialLaplacian D *ᵥ x) ≤ 4 * (x ⬝ᵥ x) := by
  rw [partialLaplacian_quadratic]
  have hsource : (∑ e ∈ D, x e.1 ^ 2) ≤ ∑ i, x i ^ 2 := by
    calc
      _ = ∑ i ∈ D.image Prod.fst, x i ^ 2 := (Finset.sum_image hs).symm
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  have htarget : (∑ e ∈ D, x e.2 ^ 2) ≤ ∑ i, x i ^ 2 := by
    calc
      _ = ∑ i ∈ D.image Prod.snd, x i ^ 2 := (Finset.sum_image ht).symm
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  calc
    _ ≤ ∑ e ∈ D, (2 * x e.1 ^ 2 + 2 * x e.2 ^ 2) :=
      Finset.sum_le_sum (fun e _ => by nlinarith [sq_nonneg (x e.1 + x e.2)])
    _ = 2 * (∑ e ∈ D, x e.1 ^ 2) + 2 * (∑ e ∈ D, x e.2 ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by simp only [dotProduct, ← pow_two]; linarith

theorem partialLaplacian_trace {m : ℕ} (D : Finset (Fin m × Fin m))
    (hloop : ∀ e ∈ D, e.1 ≠ e.2) : (partialLaplacian D).trace = 2 * D.card := by
  simp only [partialLaplacian, Matrix.trace_sum, Matrix.trace_vecMulVec]
  calc
    _ = ∑ _e ∈ D, (2 : ℝ) := Finset.sum_congr rfl (fun e he => arcIncidence_square e (hloop e he))
    _ = _ := by simp [nsmul_eq_mul]; ring

theorem sum_single_eq_image_indicator {m : ℕ} (D : Finset (Fin m × Fin m))
    (f : (Fin m × Fin m) → Fin m) (hf : Set.InjOn f D) :
    (∑ e ∈ D, (Pi.single (f e) (1 : ℝ) : Fin m → ℝ)) =
      fun i => if i ∈ D.image f then 1 else 0 := by
  have he : (∑ i ∈ D.image f, (Pi.single i (1 : ℝ) : Fin m → ℝ)) =
      ∑ e ∈ D, (Pi.single (f e) (1 : ℝ) : Fin m → ℝ) := Finset.sum_image hf
  rw [← he]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem partialImbalance_eq_out_sub_in {m : ℕ} (D : Finset (Fin m × Fin m))
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D) :
    partialImbalance D = partialOutgoing D - partialIncoming D := by
  unfold partialImbalance arcIncidence
  rw [Finset.sum_sub_distrib, sum_single_eq_image_indicator D Prod.fst hs,
    sum_single_eq_image_indicator D Prod.snd ht]
  rfl

theorem partialOutgoing_dot_self {m : ℕ} (D : Finset (Fin m × Fin m))
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D) :
    partialOutgoing D ⬝ᵥ partialOutgoing D = D.card := by
  have hpoint (i : Fin m) : partialOutgoing D i * partialOutgoing D i = partialOutgoing D i := by
    unfold partialOutgoing
    split_ifs <;> norm_num
  simp only [dotProduct]
  simp_rw [hpoint]
  unfold partialOutgoing
  have hfilter : Finset.univ.filter (fun i : Fin m => i ∈ D.image Prod.fst) = D.image Prod.fst := by
    ext i
    simp
  rw [Finset.sum_boole, hfilter, Finset.card_image_of_injOn hs]

theorem partialIncoming_dot_self {m : ℕ} (D : Finset (Fin m × Fin m))
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D) :
    partialIncoming D ⬝ᵥ partialIncoming D = D.card := by
  have hpoint (i : Fin m) : partialIncoming D i * partialIncoming D i = partialIncoming D i := by
    unfold partialIncoming
    split_ifs <;> norm_num
  simp only [dotProduct]
  simp_rw [hpoint]
  unfold partialIncoming
  have hfilter : Finset.univ.filter (fun i : Fin m => i ∈ D.image Prod.snd) = D.image Prod.snd := by
    ext i
    simp
  rw [Finset.sum_boole, hfilter, Finset.card_image_of_injOn ht]

theorem mem_source_image_iff {m : ℕ} (D : Finset (Fin m × Fin m)) (i : Fin m) :
    i ∈ D.image Prod.fst ↔ ∃ b, (i, b) ∈ D := by
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨⟨a, b⟩, hab, ha⟩
    change a = i at ha
    subst a
    exact ⟨b, hab⟩
  · rintro ⟨b, hb⟩
    exact Finset.mem_image.mpr ⟨(i, b), hb, rfl⟩

theorem mem_target_image_iff {m : ℕ} (D : Finset (Fin m × Fin m)) (i : Fin m) :
    i ∈ D.image Prod.snd ↔ ∃ a, (a, i) ∈ D := by
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨⟨a, b⟩, hab, hb⟩
    change b = i at hb
    subst b
    exact ⟨a, hab⟩
  · rintro ⟨a, ha⟩
    exact Finset.mem_image.mpr ⟨(a, i), ha, rfl⟩

theorem partialOutgoing_dot_incoming {m : ℕ} (D : Finset (Fin m × Fin m)) :
    partialOutgoing D ⬝ᵥ partialIncoming D = FiniteModel.internalInOutCount D := by
  have hterm (i : Fin m) : partialOutgoing D i * partialIncoming D i =
      if (∃ a, (a, i) ∈ D) ∧ ∃ b, (i, b) ∈ D then (1 : ℝ) else 0 := by
    by_cases hs : i ∈ D.image Prod.fst <;> by_cases ht : i ∈ D.image Prod.snd <;>
      simp [partialOutgoing, partialIncoming, ← mem_source_image_iff, ← mem_target_image_iff, hs, ht]
  simp only [dotProduct, hterm, FiniteModel.internalInOutCount]
  simp

theorem partialImbalance_square {m : ℕ} (D : Finset (Fin m × Fin m))
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D) :
    partialImbalance D ⬝ᵥ partialImbalance D =
      2 * (D.card : ℝ) - 2 * FiniteModel.internalInOutCount D := by
  rw [partialImbalance_eq_out_sub_in D hs ht, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    partialOutgoing_dot_self D hs, partialIncoming_dot_self D ht, partialOutgoing_dot_incoming,
    dotProduct_comm (partialIncoming D) (partialOutgoing D), partialOutgoing_dot_incoming]
  ring

@[simp] theorem sum_partialImbalance {m : ℕ} (D : Finset (Fin m × Fin m)) :
    ∑ i, partialImbalance D i = 0 := by
  simp only [partialImbalance, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp

theorem partialPermutation_edges_le {m : ℕ} (D : Finset (Fin m × Fin m))
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D) : D.card ≤ m := by
  calc
    _ = (D.image Prod.fst).card := (Finset.card_image_of_injOn hs).symm
    _ ≤ Fintype.card (Fin m) := Finset.card_le_univ _
    _ = _ := Fintype.card_fin _

/-- Concrete incidence data for every loop-free directed partial permutation.
All fields required by the Gaussian correction are proved from its arc set. -/
def partialPermutationGaussianGraphData {m : ℕ} (D : Finset (Fin m × Fin m))
    (hloop : ∀ e ∈ D, e.1 ≠ e.2)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D) :
    GaussianGraphData m where
  laplacian := partialLaplacian D
  imbalance := partialImbalance D
  edgeCount := D.card
  joinCount := FiniteModel.internalInOutCount D
  positive := partialLaplacian_positive D
  quadratic_le := partialLaplacian_quadratic_le_four D hs ht
  trace_eq := partialLaplacian_trace D hloop
  imbalance_square := partialImbalance_square D hs ht
  imbalance_sum := sum_partialImbalance D
  edges_le := partialPermutation_edges_le D hs

theorem FiniteModel.internalCycleArcSet_source_injOn {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d) :
    Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) (internalCycleArcSet σ i) := by
  rintro ⟨a, b⟩ hab ⟨c, e⟩ hce hac
  change a = c at hac
  subst c
  exact Prod.ext rfl (internalCycleArcSet_outgoing_unique σ i a b e hab hce)

theorem FiniteModel.internalCycleArcSet_target_injOn {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (i : Fin d) :
    Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) (internalCycleArcSet σ i) := by
  rintro ⟨a, b⟩ hab ⟨c, e⟩ hce hbe
  change b = e at hbe
  subst e
  exact Prod.ext (internalCycleArcSet_incoming_unique σ i b a c hab hce) rfl

def FiniteModel.internalCycleGaussianGraphData {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (hN : 3 ≤ d * m) (hσ : SingleOrbit σ) (i : Fin d) :
    GaussianGraphData m :=
  partialPermutationGaussianGraphData (internalCycleArcSet σ i)
    (by rintro ⟨a, b⟩ hab he; change a = b at he; subst b
        exact internalCycleArcSet_no_loops σ hN hσ i a hab)
    (internalCycleArcSet_source_injOn σ i) (internalCycleArcSet_target_injOn σ i)

@[simp] theorem FiniteModel.internalCycleGaussianGraphData_joinCount {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (hN : 3 ≤ d * m) (hσ : SingleOrbit σ) (i : Fin d) :
    (internalCycleGaussianGraphData σ hN hσ i).joinCount = internalInOutCount (internalCycleArcSet σ i) := rfl

end
end Wormald

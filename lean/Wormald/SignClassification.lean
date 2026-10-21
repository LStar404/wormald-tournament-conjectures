import Wormald.FourthMomentIdentity
import Wormald.MomentComparison
import Mathlib.Data.Finset.Sort

/-!
# Local Pfaffian bounds force a switched transitive tournament

Switching makes one vertex a source. A directed triangle among the remaining
vertices would have four-vertex Pfaffian square nine, whereas the hypothesis
bounds every such square by one. The resulting strict total order supplies
the actual permutation.
-/

namespace Wormald
noncomputable section
open Matrix FiniteModel

private theorem source_sign_transitive {ι : Type*} (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0) (hskew : ∀ i j, B j i = -B i j)
    (hentry : ∀ i j, i ≠ j → B i j = 1 ∨ B i j = -1)
    (root : ι) (hsource : ∀ j, root ≠ j → B root j = 1)
    (hpf : ∀ a b c d, pfaffianFour B a b c d ^ 2 ≤ 1) :
    ∀ ⦃i j k⦄, B i j = 1 → B j k = 1 → B i k = 1 := by
  intro i j k hij hjk
  have hijn : i ≠ j := by intro h; subst j; rw [hdiag] at hij; norm_num at hij
  have hjkn : j ≠ k := by intro h; subst k; rw [hdiag] at hjk; norm_num at hjk
  have hikn : i ≠ k := by
    intro h
    subst k
    rw [hskew i j, hij] at hjk
    norm_num at hjk
  rcases hentry i k hikn with hik | hik
  · exact hik
  · have hri : root ≠ i := by
      intro h
      subst i
      have h := hsource k hikn
      linarith
    have hrj : root ≠ j := by
      intro h
      subst j
      have h := hsource i hijn.symm
      rw [hskew i root, hij] at h
      norm_num at h
    have hrk : root ≠ k := by
      intro h
      subst k
      have h := hsource j hjkn.symm
      rw [hskew j root, hjk] at h
      norm_num at h
    have hp := hpf root i j k
    simp only [pfaffianFour, hsource i hri, hsource j hrj, hsource k hrk,
      hij, hjk, hik] at hp
    norm_num at hp

private structure OrderVertex (n : ℕ) where
  vertex : Fin n
  deriving Fintype, DecidableEq

private def orderVertexEquiv (n : ℕ) : OrderVertex n ≃ Fin n :=
  ⟨fun i => i.vertex, fun i => ⟨i⟩, fun ⟨_i⟩ => rfl, fun _ => rfl⟩

private theorem ordered_sign_permutation {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, B i i = 0) (hskew : ∀ i j, B j i = -B i j)
    (hentry : ∀ i j, i ≠ j → B i j = 1 ∨ B i j = -1)
    (htrans : ∀ ⦃i j k⦄, B i j = 1 → B j k = 1 → B i k = 1) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i j, B (σ i) (σ j) = transitiveSign n ℝ i j := by
  classical
  let r : OrderVertex n → OrderVertex n → Prop := fun i j => B i.vertex j.vertex = 1
  let : IsStrictTotalOrder (OrderVertex n) r := {
    irrefl := by intro i; dsimp [r]; rw [hdiag]; norm_num
    trans := by intro i j k hij hjk; exact htrans hij hjk
    trichotomous := by
      intro i j hij hji
      apply (orderVertexEquiv n).injective
      by_contra hne
      rcases hentry i.vertex j.vertex hne with h | h
      · exact hij h
      · apply hji
        dsimp [r]
        rw [hskew i.vertex j.vertex, h]
        norm_num }
  let : LinearOrder (OrderVertex n) := linearOrderOfSTO r
  let e : Fin n ≃o OrderVertex n := Fintype.orderIsoFinOfCardEq _ (by exact (Fintype.card_congr (orderVertexEquiv n)).trans (Fintype.card_fin n))
  let σ : Equiv.Perm (Fin n) := e.toEquiv.trans (orderVertexEquiv n)
  have hu : ∀ i j : Fin n, i < j → B (σ i) (σ j) = 1 := by
    intro i j hij
    change r (e i) (e j)
    exact e.lt_iff_lt.mpr hij
  refine ⟨σ, ?_⟩
  intro i j
  rcases lt_trichotomy i j with hij | heq | hji
  · simp [transitiveSign, hij, hu i j hij]
  · subst j; simp [hdiag, transitiveSign]
  · rw [hskew, hu j i hji]
    simp [transitiveSign, hji, not_lt_of_gt hji]

/-- A local four-vertex certificate produces an actual signed permutation of
the transitive tournament, in every finite dimension. -/
theorem signed_permutation_of_pfaffian_bound {n : ℕ} (T : Orientation n)
    (hpf : ∀ a b c d, pfaffianFour (orientationSign T ℝ) a b c d ^ 2 ≤ 1) :
    ∃ (σ : Equiv.Perm (Fin n)) (ε : Fin n → ℝ),
      (∀ i, ε i ^ 2 = 1) ∧ ∀ i j,
        orientationSign T ℝ (σ i) (σ j) = ε i * transitiveSign n ℝ i j * ε j := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨Equiv.refl _, fun _ => 1, fun _ => by norm_num, fun i => Fin.elim0 i⟩
  let root : Fin n := ⟨0, by omega⟩
  let A := orientationSign T ℝ
  let ε : Fin n → ℝ := fun i => if i = root then 1 else A root i
  have hAsq : ∀ i j, i ≠ j → A i j ^ 2 = 1 := by
    intro i j hij
    dsimp [A, orientationSign]
    rw [ite_eq_right hij]
    split_ifs <;> norm_num
  have hε : ∀ i, ε i ^ 2 = 1 := by
    intro i
    dsimp [ε]
    split_ifs with hi
    · norm_num
    · exact hAsq root i (Ne.symm hi)
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j => ε i * A i j * ε j
  have hdiag : ∀ i, B i i = 0 := by intro i; simp [B, A]
  have hskew : ∀ i j, B j i = -B i j := by
    intro i j
    dsimp [B]
    rw [show A j i = -A i j from orientationSign_skew T i j]
    ring
  have hentry : ∀ i j, i ≠ j → B i j = 1 ∨ B i j = -1 := by
    intro i j hij
    apply sq_eq_one_iff.mp
    dsimp [B]
    rw [mul_pow, mul_pow, hε i, hε j, hAsq i j hij]
    norm_num
  have hsource : ∀ j, root ≠ j → B root j = 1 := by
    intro j hj
    change ε root * A root j * ε j = 1
    simp only [ε, ite_eq_left rfl, ite_eq_right hj.symm, one_mul]
    simpa only [pow_two] using hAsq root j hj
  have hpfB : ∀ a b c d, pfaffianFour B a b c d ^ 2 ≤ 1 := by
    intro a b c d
    have hmap : pfaffianFour B a b c d =
        (ε a * ε b * ε c * ε d) * pfaffianFour A a b c d := by
      dsimp [pfaffianFour, B]
      ring
    rw [hmap]
    simpa only [mul_pow, hε, one_mul] using hpf a b c d
  obtain ⟨σ, hσ⟩ := ordered_sign_permutation B hdiag hskew hentry
    (source_sign_transitive B hdiag hskew hentry root hsource hpfB)
  refine ⟨σ, fun i => ε (σ i), fun i => hε (σ i), ?_⟩
  intro i j
  calc
    A (σ i) (σ j) = (ε (σ i) ^ 2) * (ε (σ j) ^ 2) * A (σ i) (σ j) := by
      rw [hε, hε]; ring
    _ = ε (σ i) * B (σ i) (σ j) * ε (σ j) := by dsimp [B]; ring
    _ = _ := by rw [hσ]

end
end Wormald

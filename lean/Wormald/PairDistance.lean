import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Tactic

namespace Wormald

open Finset

noncomputable section

private theorem sum_ite_lt_const {n : ℕ} (i : Fin n) (a : ℝ) :
    (∑ j : Fin n, if i < j then a else 0) = ((n - 1 - i.val : ℕ) : ℝ) * a := by
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun j : Fin n => i < j) = Finset.Ioi i := by
    ext j
    simp
  rw [hf]
  simp [nsmul_eq_mul]

private theorem sum_ite_gt_const {n : ℕ} (j : Fin n) (a : ℝ) :
    (∑ i : Fin n, if i < j then a else 0) = (j.val : ℝ) * a := by
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun i : Fin n => i < j) = Finset.Iio j := by
    ext i
    simp
  rw [hf]
  simp [nsmul_eq_mul]

/-- The exact internal-pair sum after sorting signed coordinates in decreasing order. -/
theorem half_sum_abs_sub_of_antitone {r : ℕ} (z : Fin r → ℝ) (hz : Antitone z) :
    (∑ i, ∑ j, |z i - z j|) / 2 =
      ∑ i : Fin r, ((r : ℝ) - 1 - 2 * i.val) * z i := by
  let H : ℝ := ∑ i : Fin r, ∑ j : Fin r, if i < j then z i - z j else 0
  have habs : ∀ i j, |z i - z j| =
      (if i < j then z i - z j else 0) + (if j < i then z j - z i else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | heq | hji
    · simp [hij, not_lt_of_gt hij, abs_of_nonneg (sub_nonneg.mpr (hz hij.le))]
    · subst j
      simp
    · simp [hji, not_lt_of_gt hji, abs_of_nonpos (sub_nonpos.mpr (hz hji.le))]

  have hdouble : (∑ i, ∑ j, |z i - z j|) = 2 * H := by
    simp only [habs, Finset.sum_add_distrib]
    have hswap : (∑ i : Fin r, ∑ j : Fin r, if j < i then z j - z i else 0) = H :=
      Finset.sum_comm
    rw [hswap]
    change H + H = 2 * H
    ring
  have htriangle : H = ∑ i : Fin r, ((r : ℝ) - 1 - 2 * i.val) * z i := by
    have hsplit : H = (∑ i : Fin r, ∑ j : Fin r, if i < j then z i else 0) -
        (∑ i : Fin r, ∑ j : Fin r, if i < j then z j else 0) := by
      dsimp [H]
      simp only [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring
    rw [hsplit]
    have hfirst : (∑ i : Fin r, ∑ j : Fin r, if i < j then z i else 0) =
        ∑ i : Fin r, ((r - 1 - i.val : ℕ) : ℝ) * z i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_ite_lt_const i (z i)
    have hsecond : (∑ i : Fin r, ∑ j : Fin r, if i < j then z j else 0) =
        ∑ j : Fin r, (j.val : ℝ) * z j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_ite_gt_const j (z j)
    rw [hfirst, hsecond, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi₁ : i.val ≤ r - 1 := by omega
    have hr₁ : 1 ≤ r := by have := i.isLt; omega
    rw [Nat.cast_sub hi₁, Nat.cast_sub hr₁]
    push_cast
    ring
  rw [hdouble, htriangle]
  ring

/-- A permutation that puts a finite real tuple in decreasing order. -/
def descendingPermutation {n : ℕ} (x : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => OrderDual.toDual (x i))

theorem antitone_descendingPermutation {n : ℕ} (x : Fin n → ℝ) :
    Antitone (fun i => x (descendingPermutation x i)) :=
  Tuple.monotone_sort (fun i => OrderDual.toDual (x i))

/-- Absolute values arranged in decreasing order, using an actual permutation. -/
def sortedAbs {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  |x (descendingPermutation (fun j => |x j|) i)|

theorem sortedAbs_antitone {n : ℕ} (x : Fin n → ℝ) : Antitone (sortedAbs x) :=
  antitone_descendingPermutation (fun j => |x j|)

/-- Rearrangement bounds any signed dot product by the decreasing absolute tuples. -/
theorem dot_le_sortedAbs_dot {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, a i * b i) ≤ ∑ i, sortedAbs a i * sortedAbs b i := by
  let p := descendingPermutation (fun i => |a i|)
  let q := descendingPermutation (fun i => |b i|)
  have hmono : Monovary (sortedAbs a) (sortedAbs b) :=
    (sortedAbs_antitone a).monovary (sortedAbs_antitone b)
  have hrearr := hmono.sum_smul_comp_perm_le_sum_smul (σ := p.trans q.symm)
  have hright : (∑ i, |a i| * |b i|) =
      ∑ i, sortedAbs a i * sortedAbs b ((p.trans q.symm) i) := by
    symm
    calc
      (∑ i, sortedAbs a i * sortedAbs b ((p.trans q.symm) i)) =
          ∑ i, |a (p i)| * |b (p i)| := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [sortedAbs, p, q]
      _ = _ := Equiv.sum_comp p (fun i => |a i| * |b i|)
  calc
    (∑ i, a i * b i) ≤ ∑ i, |a i| * |b i| := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [abs_mul] using (le_abs_self (a i * b i))
    _ ≤ _ := by rw [hright]; exact hrearr

/-- Sorting absolute values is invariant under any permutation of the original tuple. -/
theorem sortedAbs_comp_perm {n : ℕ} (x : Fin n → ℝ) (p : Equiv.Perm (Fin n)) :
    sortedAbs (fun i => x (p i)) = sortedAbs x := by
  have h := Tuple.comp_perm_comp_sort_eq_comp_sort
    (f := fun i => OrderDual.toDual (|x i|)) (σ := p)
  have hreal := congrArg (fun f : Fin n → ℝᵒᵈ => fun i => OrderDual.ofDual (f i)) h
  funext i
  have hi := congrFun hreal i
  simpa [sortedAbs, descendingPermutation, Function.comp_def] using hi

/-- A decreasing nonnegative tuple is already its absolute decreasing rearrangement. -/
theorem sortedAbs_eq_self_of_antitone_nonneg {n : ℕ} (x : Fin n → ℝ)
    (hx : Antitone x) (hnonneg : ∀ i, 0 ≤ x i) : sortedAbs x = x := by
  have habs : (fun i => |x i|) = x := funext (fun i => abs_of_nonneg (hnonneg i))
  have heq := Tuple.unique_antitone (f := x) (σ := descendingPermutation x)
    (τ := Equiv.refl _) (antitone_descendingPermutation x) hx
  funext i
  change (fun j => |x j|) (descendingPermutation (fun j => |x j|) i) = x i
  rw [habs]
  exact congrFun heq i

/-- The source's decreasing rearrangement of |r−1−2i|. -/
def pairCoefficients (r : ℕ) : Fin r → ℝ :=
  sortedAbs (fun i : Fin r => (r : ℝ) - 1 - 2 * i.val)

/-- The general sharp rearrangement bound for a finite pair-distance sum. -/
theorem half_sum_abs_sub_le_pairCoefficients {r : ℕ} (z : Fin r → ℝ) :
    (∑ i, ∑ j, |z i - z j|) / 2 ≤ ∑ i, pairCoefficients r i * sortedAbs z i := by
  let p := descendingPermutation z
  have hre : (∑ i : Fin r, ∑ j : Fin r, |z (p i) - z (p j)|) =
      ∑ i : Fin r, ∑ j : Fin r, |z i - z j| := by
    calc
      (∑ i : Fin r, ∑ j : Fin r, |z (p i) - z (p j)|) =
          ∑ i : Fin r, ∑ j : Fin r, |z (p i) - z j| := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Equiv.sum_comp p (fun j => |z (p i) - z j|)
      _ = _ := Equiv.sum_comp p (fun i => ∑ j : Fin r, |z i - z j|)
  have hsort := half_sum_abs_sub_of_antitone (fun i => z (p i))
    (antitone_descendingPermutation z)
  have hbound := dot_le_sortedAbs_dot
    (fun i : Fin r => (r : ℝ) - 1 - 2 * i.val) (fun i => z (p i))
  rw [sortedAbs_comp_perm z p] at hbound
  rw [hre] at hsort
  exact hsort.trans_le hbound

/-- Multiplying both coordinates by signs converts the source's cross difference
into an ordinary signed-coordinate distance without changing its absolute value. -/
theorem abs_signed_cross_eq (a b x y : ℝ)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    |a * y - b * x| = |a * x - b * y| := by
  have haa : |a| = 1 := by rcases ha with rfl | rfl <;> norm_num
  have hbb : |b| = 1 := by rcases hb with rfl | rfl <;> norm_num
  have heq : a * y - b * x = -(a * b) * (a * x - b * y) := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> ring
  rw [heq, abs_mul, abs_neg, abs_mul, haa, hbb]
  simp

/-- The sharp internal estimate from Fang–Huang Lemma 3.3, before the selected
coordinates are merged with the outside coordinates. No majorization is assumed. -/
theorem half_sum_abs_signed_cross_le {r : ℕ} (ε x : Fin r → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (∑ i, ∑ j, |ε i * x j - ε j * x i|) / 2 ≤
      ∑ i, pairCoefficients r i * sortedAbs x i := by
  have hbound := half_sum_abs_sub_le_pairCoefficients (fun i => ε i * x i)
  have habseq : (fun i => |ε i * x i|) = (fun i => |x i|) := by
    funext i
    rcases hε i with hi | hi <;> simp [hi]
  have hsort : sortedAbs (fun i => ε i * x i) = sortedAbs x := by
    change (fun i => (fun j => |ε j * x j|)
        (descendingPermutation (fun j => |ε j * x j|) i)) =
      (fun i => (fun j => |x j|) (descendingPermutation (fun j => |x j|) i))
    rw [habseq]
  rw [hsort] at hbound
  convert hbound using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact abs_signed_cross_eq (ε i) (ε j) (x i) (x j) (hε i) (hε j)

end
end Wormald

import Wormald.CycleWordTransfer
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace powers enumerate closed words

Matrix multiplication first enumerates open paths. Joining the endpoints and
using `finRotate` yields closed words. For a matrix whose arrival column carries
`X j`, each word contributes its weight times its exact letter-count monomial.
-/

namespace Wormald
noncomputable section
open scoped BigOperators
open Matrix MvPolynomial

private def pathWordWeight {V R : Type*} [CommMonoid R] {N : ℕ}
    (A : Matrix V V R) (s t : V) (f : Fin N → V) : R :=
  ∏ i : Fin (N + 1), A (Fin.cons (α := fun _ => V) s f i)
    (Fin.snoc (α := fun _ => V) f t i)

private theorem pathWordWeight_cons {V R : Type*} [CommMonoid R] {N : ℕ}
    (A : Matrix V V R) (s t k : V) (f : Fin N → V) :
    pathWordWeight A s t (Fin.cons k f) = A s k * pathWordWeight A k t f := by
  unfold pathWordWeight
  rw [← Fin.cons_snoc_eq_snoc_cons, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

private theorem matrix_pow_succ_path_sum {V R : Type*} [Fintype V] [DecidableEq V]
    [CommSemiring R] (A : Matrix V V R) (N : ℕ) (s t : V) :
    (A ^ (N + 1)) s t = ∑ f : Fin N → V, pathWordWeight A s t f := by
  induction N generalizing s t with
  | zero => simp [pathWordWeight, Fin.snoc]
  | succ N ih =>
    calc
      _ = ∑ k, A s k * (A ^ (N + 1)) k t := by
        rw [pow_succ', Matrix.mul_apply]
      _ = ∑ p : V × (Fin N → V), A s p.1 * pathWordWeight A p.1 t p.2 := by
        simp only [Fintype.sum_prod_type, ih, Finset.mul_sum]
      _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (N + 1) => V))
        (fun p => A s p.1 * pathWordWeight A p.1 t p.2)
        (pathWordWeight A s t) (fun p => (pathWordWeight_cons A s t p.1 p.2).symm)

/-- The finite closed-word expansion of a positive trace power, over any
commutative semiring. The positivity of the exponent is essential. -/
theorem trace_pow_eq_closedWord_sum {V R : Type*} [Fintype V] [DecidableEq V]
    [CommSemiring R] (A : Matrix V V R) (N : ℕ) (hN : 0 < N) :
    (A ^ N).trace = ∑ f : Fin N → V, ∏ i, A (f i) (f (finRotate N i)) := by
  cases N with
  | zero => omega
  | succ N =>
    calc
      _ = ∑ s, ∑ f : Fin N → V, pathWordWeight A s s f := by
        simp only [Matrix.trace, Matrix.diag_apply, matrix_pow_succ_path_sum]
      _ = ∑ p : V × (Fin N → V), pathWordWeight A p.1 p.1 p.2 := by
        rw [Fintype.sum_prod_type]
      _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (N + 1) => V))
        (fun p => pathWordWeight A p.1 p.1 p.2)
        (fun f => ∏ i, A (f i) (f (finRotate (N + 1) i))) (by
          intro p
          unfold pathWordWeight
          rw [Fin.snoc_eq_cons_rotate]
          rfl)

namespace FiniteModel

/-- Each arrival at base vertex `j` contributes one copy of `X j`. -/
def variableMatrix {d : ℕ} {R : Type*} [CommSemiring R]
    (B : Matrix (Fin d) (Fin d) R) : Matrix (Fin d) (Fin d) (MvPolynomial (Fin d) R) :=
  B.map C * Matrix.diagonal (fun j => X j)

@[simp] theorem variableMatrix_entry {d : ℕ} {R : Type*} [CommSemiring R]
    (B : Matrix (Fin d) (Fin d) R) (i j : Fin d) :
    variableMatrix B i j = monomial (Finsupp.single j 1) (B i j) := by
  simp [variableMatrix, Matrix.mul_diagonal, X, C_mul_monomial]

def wordMultiplicity {d N : ℕ} (f : Fin N → Fin d) : Fin d →₀ ℕ :=
  ∑ a, Finsupp.single (f a) 1

def uniformExponent (d m : ℕ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => m)

@[simp] theorem uniformExponent_apply (d m : ℕ) (i : Fin d) :
    uniformExponent d m i = m := rfl

theorem wordMultiplicity_apply {d N : ℕ} (f : Fin N → Fin d) (i : Fin d) :
    wordMultiplicity f i = Fintype.card {a // f a = i} := by
  simp only [wordMultiplicity, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Fintype.card_subtype, Finset.card_filter]

theorem wordMultiplicity_eq_uniform_iff {d N : ℕ} (f : Fin N → Fin d) (m : ℕ) :
    wordMultiplicity f = uniformExponent d m ↔ BalancedBaseWord m f := by
  constructor
  · intro h i
    have hi := congrArg (fun e : Fin d →₀ ℕ => e i) h
    simpa only [wordMultiplicity_apply, uniformExponent_apply] using hi
  · intro h
    ext i
    rw [wordMultiplicity_apply, uniformExponent_apply]
    exact h i

theorem cyclicWordWeight_variableMatrix {d N : ℕ} {R : Type*} [CommSemiring R]
    (B : Matrix (Fin d) (Fin d) R) (f : Fin N → Fin d) :
    cyclicWordWeight (variableMatrix B) f =
      monomial (wordMultiplicity f) (cyclicWordWeight B f) := by
  unfold cyclicWordWeight
  simp only [variableMatrix_entry]
  rw [← MvPolynomial.monomial_sum_prod]
  have he : (∑ i, Finsupp.single (f (finRotate N i)) 1) = wordMultiplicity f :=
    Equiv.sum_comp (finRotate N) (fun a => Finsupp.single (f a) 1)
  rw [he]

/-- The actual trace polynomial is the sum of the weight-monomial of every
closed base word, with no coefficient-extraction assumption. -/
theorem trace_variableMatrix_pow_eq {d N : ℕ} {R : Type*} [CommSemiring R]
    (B : Matrix (Fin d) (Fin d) R) (hN : 0 < N) :
    (variableMatrix B ^ N).trace =
      ∑ f : Fin N → Fin d, monomial (wordMultiplicity f) (cyclicWordWeight B f) := by
  rw [trace_pow_eq_closedWord_sum _ N hN]
  exact Finset.sum_congr rfl (fun f _ => cyclicWordWeight_variableMatrix B f)

/-- Extracting `∏ X_i^m` selects precisely the balanced cyclic words. -/
theorem coeff_trace_variableMatrix_pow {d N : ℕ} {R : Type*} [CommSemiring R]
    (B : Matrix (Fin d) (Fin d) R) (m : ℕ) (hN : 0 < N) :
    ((variableMatrix B ^ N).trace).coeff (uniformExponent d m) =
      balancedCycleWordSum (N := N) B m := by
  classical
  rw [trace_variableMatrix_pow_eq B hN, MvPolynomial.coeff_sum]
  unfold balancedCycleWordSum
  apply Finset.sum_congr rfl
  intro f _
  rw [MvPolynomial.coeff_monomial]
  by_cases hf : BalancedBaseWord m f
  · have hm := (wordMultiplicity_eq_uniform_iff f m).mpr hf
    simp [hf, hm]
  · have hm : wordMultiplicity f ≠ uniformExponent d m := by
      intro h
      exact hf ((wordMultiplicity_eq_uniform_iff f m).mp h)
    simp [hf, hm]

end FiniteModel
end
end Wormald

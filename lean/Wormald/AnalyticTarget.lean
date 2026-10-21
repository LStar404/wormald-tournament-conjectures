import Wormald.Definitions
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The original analytic target of Conjecture 6

These definitions deliberately retain Wormald's determinant, eliminated last
variable, logarithm, and real angular derivatives. `ConjectureSix` is a Prop,
not itself a theorem. The proof is `conjectureSix` in `ConjectureSixProof`.
In particular `angularHessianJet` is not substituted for the original analytic
Hessian by definition.

The explicit rational formula for h is total as a Lean function. A successful
proof must establish nonvanishing of its denominator and the analytic branch
near the critical point before using it as a solution of K=0.
-/

namespace Wormald

noncomputable section

open Matrix

def originalMatrix {d : ℕ} (T : Tournament d) (y : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => (if i = j then 1 else 0) -
    ((T.adjacency i j : ℂ) + if i = j then (1 / 2 : ℂ) else 0) * y j

def originalDeterminant {d : ℕ} (T : Tournament d) (y : Fin d → ℂ) : ℂ :=
  (originalMatrix T y).det

def appendLast {n : ℕ} (y : Fin n → ℂ) (a : ℂ) : Fin (n + 1) → ℂ :=
  Fin.lastCases a y

def eliminatedNumerator {n : ℕ} (T : Tournament (n + 1)) (y : Fin n → ℂ) : ℂ :=
  originalDeterminant T (appendLast y 0)

def eliminatedCoefficient {n : ℕ} (T : Tournament (n + 1)) (y : Fin n → ℂ) : ℂ :=
  originalDeterminant T (appendLast y 1) - eliminatedNumerator T y

def originalImplicitFunction {n : ℕ} (T : Tournament (n + 1))
    (y : Fin n → ℂ) : ℂ :=
  -eliminatedNumerator T y / eliminatedCoefficient T y

def originalAngularFunction {n : ℕ} (T : Tournament (n + 1))
    (θ : Fin n → ℝ) : ℂ :=
  Complex.log (originalImplicitFunction T
    (fun j => (2 / ((n + 1 : ℕ) : ℂ)) * Complex.exp (Complex.I * (θ j : ℂ))))

def originalAngularHessian {n : ℕ} (T : Tournament (n + 1)) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun j k =>
    fderiv ℝ (fun θ =>
      (fderiv ℝ (originalAngularFunction T) θ) (Pi.single j 1)) 0 (Pi.single k 1)

/-- Literal nonzero/rational-square target. This declaration proves nothing. -/
def ConjectureSix : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (T : Tournament (n + 1)), T.Regular →
    (originalAngularHessian T).det ≠ 0 ∧
      ∃ q : ℚ, ((n + 1 : ℕ) : ℂ) / (originalAngularHessian T).det = (q : ℂ) ^ 2

/-- The analytic bridge, defined as a proposition rather than an axiom and proved
from the original analytic function in `ConjectureSixProof`. -/
def AnalyticJetBridge {n : ℕ} (T : Tournament (n + 1)) : Prop :=
  ∀ j k : Fin n,
    originalAngularHessian T j k =
      (angularHessianJet (definingPolynomial T.adjacency)
        (2 / ((n + 1 : ℕ) : ℚ)) (Fin.last n) j.castSucc k.castSucc : ℂ)

end
end Wormald

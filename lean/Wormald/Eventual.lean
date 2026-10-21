import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Conditional finite-family reduction (paper, Appendix A.6)

These lemmas prove the last analytic step only. `F` denotes an arbitrary real-valued
family. Their hypotheses explicitly require convergence, strict separation of the
limiting values, and exact equality on the proposed equivalence class. They do not
assert that Hamilton-count expectations satisfy those hypotheses.
-/

open Filter Topology

namespace Wormald

/-- In a finite family, convergence and a strict limiting gap imply that every
competitor outside `E` is eventually strictly below the reference `r`. -/
theorem eventually_strict_of_limiting_gap
    {I X : Type*} [Finite I] (l : Filter X)
    (F : I → X → ℝ) (L : I → ℝ) (r : I) (E : I → Prop)
    (hconv : ∀ i, Tendsto (F i) l (𝓝 (L i)))
    (hgap : ∀ i, ¬ E i → L i < L r) :
    ∀ᶠ x in l, ∀ i, ¬ E i → F i x < F r x := by
  apply Filter.eventually_all.2
  intro i
  by_cases hi : E i
  · exact Filter.Eventually.of_forall (fun _ hnot => False.elim (hnot hi))
  · exact ((hconv i).eventually_lt (hconv r) (hgap i hi)).mono
      (fun _ hlt _ => hlt)

/-- Conditional unique-class maximization. The exact equality of isomorphic
models is an explicit premise, separate from strict separation of limits. -/
theorem eventually_unique_class_of_limiting_gap
    {I X : Type*} [Finite I] (l : Filter X)
    (F : I → X → ℝ) (L : I → ℝ) (r : I) (E : I → Prop)
    (hconv : ∀ i, Tendsto (F i) l (𝓝 (L i)))
    (hequal : ∀ i, E i → ∀ x, F i x = F r x)
    (hgap : ∀ i, ¬ E i → L i < L r) :
    ∀ᶠ x in l, ∀ i, F i x ≤ F r x ∧ (F i x = F r x ↔ E i) := by
  apply (eventually_strict_of_limiting_gap l F L r E hconv hgap).mono
  intro x hx i
  by_cases hi : E i
  · exact ⟨le_of_eq (hequal i hi x),
      ⟨fun _ => hi, fun _ => hequal i hi x⟩⟩
  · have hlt := hx i hi
    exact ⟨le_of_lt hlt,
      ⟨fun h => False.elim ((ne_of_lt hlt) h),
       fun h => False.elim (hi h)⟩⟩

/-- A numerical threshold version allowing restrictions such as odd block order.
The convergence filter is explicitly restricted to the legal indices. -/
theorem threshold_unique_class_of_limiting_gap
    {I : Type*} [Finite I]
    (F : I → ℕ → ℝ) (L : I → ℝ) (r : I) (E : I → Prop)
    (legal : ℕ → Prop)
    (hconv : ∀ i, Tendsto (F i)
      (atTop ⊓ 𝓟 {m | legal m}) (𝓝 (L i)))
    (hequal : ∀ i, E i → ∀ m, F i m = F r m)
    (hgap : ∀ i, ¬ E i → L i < L r) :
    ∃ M : ℕ, ∀ m, M ≤ m → legal m →
      ∀ i, F i m ≤ F r m ∧ (F i m = F r m ↔ E i) := by
  have h := eventually_unique_class_of_limiting_gap
    (atTop ⊓ 𝓟 {m | legal m}) F L r E hconv hequal hgap
  exact Filter.eventually_atTop.1 (Filter.eventually_inf_principal.1 h)

/-- One threshold works for finitely many models and count types. For the paper,
`Q` can index the two block models and the two Hamilton-count types. Each model
retains its own legality predicate, so odd-block restrictions are preserved. -/
theorem simultaneous_threshold_unique_class_of_limiting_gap
    {I Q : Type*} [Finite I] [Finite Q]
    (F : Q → I → ℕ → ℝ) (L : Q → I → ℝ) (r : I) (E : I → Prop)
    (legal : Q → ℕ → Prop)
    (hconv : ∀ q i, Tendsto (F q i)
      (atTop ⊓ 𝓟 {m | legal q m}) (𝓝 (L q i)))
    (hequal : ∀ q i, E i → ∀ m, F q i m = F q r m)
    (hgap : ∀ q i, ¬ E i → L q i < L q r) :
    ∃ M : ℕ, ∀ m, M ≤ m → ∀ q, legal q m →
      ∀ i, F q i m ≤ F q r m ∧ (F q i m = F q r m ↔ E i) := by
  apply Filter.eventually_atTop.1
  apply Filter.eventually_all.2
  intro q
  exact Filter.eventually_inf_principal.1
    (eventually_unique_class_of_limiting_gap
      (atTop ⊓ 𝓟 {m | legal q m}) (F q) (L q) r E
      (hconv q) (hequal q) (hgap q))

end Wormald

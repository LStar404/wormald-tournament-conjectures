import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# The positive odd-moment logarithmic series

This scalar spectral calculation will be applied to the eigenvalues of -C².
It supplies both termwise comparison and the exact equality implication, rather
than introducing comparison of determinant ratios as a premise.
-/

namespace Wormald
noncomputable section
open scoped BigOperators

def oddSpectralMoment {ι : Type*} [Fintype ι] (ev : ι → ℝ) (r : ℕ) : ℝ :=
  ∑ i, ev i ^ (2 * r + 1)

theorem hasSum_oddSpectralMoment {ι : Type*} [Fintype ι] (ev : ι → ℝ)
    (hev : ∀ i, |ev i| < 1) :
    HasSum (fun r => oddSpectralMoment ev r / ((2 * r + 1 : ℕ) : ℝ))
      (((∑ i, Real.log (1 + ev i)) - ∑ i, Real.log (1 - ev i)) / 2) := by
  classical
  have hsingle (i : ι) :
      HasSum (fun r : ℕ => ev i ^ (2 * r + 1) / ((2 * r + 1 : ℕ) : ℝ))
        ((Real.log (1 + ev i) - Real.log (1 - ev i)) / 2) := by
    convert (Real.hasSum_log_sub_log_of_abs_lt_one (hev i)).mul_left (1 / 2 : ℝ) using 1
    · funext r
      push_cast
      ring
    · ring
  have hfinite (s : Finset ι) :
      HasSum (fun r : ℕ => ∑ i ∈ s, ev i ^ (2 * r + 1) / ((2 * r + 1 : ℕ) : ℝ))
        ((∑ i ∈ s, (Real.log (1 + ev i) - Real.log (1 - ev i))) / 2) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      convert (hsingle a).add ih using 1
      ring
  simpa only [oddSpectralMoment, ← Finset.sum_div, Finset.sum_sub_distrib] using hfinite Finset.univ

theorem oddSpectralMoment_nonneg {ι : Type*} [Fintype ι] (ev : ι → ℝ)
    (hev : ∀ i, 0 ≤ ev i) (r : ℕ) : 0 ≤ oddSpectralMoment ev r :=
  Finset.sum_nonneg (fun i _ => pow_nonneg (hev i) _)

/-- Convergent termwise comparison preserves the sums. -/
theorem hasSum_mono {f g : ℕ → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) (hfg : ∀ r, f r ≤ g r) : a ≤ b := by
  have h := (hg.sub hf).nonneg (fun r => sub_nonneg.mpr (hfg r))
  linarith

/-- Under termwise comparison, equality of convergent sums forces every term
to agree. This is the needed strictly positive coefficient argument. -/
theorem eq_terms_of_hasSum_eq_of_le {f g : ℕ → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) (hfg : ∀ r, f r ≤ g r)
    (heq : a = b) (r : ℕ) : f r = g r := by
  by_contra hne
  have hstrict : f r < g r := lt_of_le_of_ne (hfg r) hne
  have h := Summable.tsum_lt_tsum hfg hstrict hf.summable hg.summable
  rw [hf.tsum_eq, hg.tsum_eq, heq] at h
  exact lt_irrefl b h

end
end Wormald

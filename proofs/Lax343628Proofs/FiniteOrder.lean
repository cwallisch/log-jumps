import Lax343628Proofs.FiniteComparison

namespace Lax343628Proofs.FiniteOrder

open Lax343628Proofs.FiniteDrift
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def lowerSum {N : ℕ} (a : Fin N → ℝ) (r : ℕ) : ℝ := ∑ i, if i.val < r then a i else 0

def upperSum {N : ℕ} (a : Fin N → ℝ) (r : ℕ) : ℝ := ∑ i, if r ≤ i.val then a i else 0

lemma split_sum {N : ℕ} (a : Fin N → ℝ) (r : ℕ) :
    lowerSum a r + upperSum a r = ∑ i, a i := by
  rw [lowerSum, upperSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < r
  · simp only [if_pos hi, if_neg (Nat.not_le.mpr hi), add_zero]
  · simp only [if_neg hi, if_pos (Nat.le_of_not_gt hi), zero_add]

lemma likelihood_cross {N : ℕ} (a b : Fin N → ℝ)
    (horder : ∀ i j, i < j → b i * a j ≤ a i * b j) (r : ℕ) :
    lowerSum b r * (∑ i, a i) ≤ lowerSum a r * (∑ i, b i) := by
  have hcross : lowerSum b r * upperSum a r ≤ lowerSum a r * upperSum b r := by
    unfold lowerSum upperSum
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hi : j.val < r <;> by_cases hj : r ≤ i.val
    · simp only [if_pos hi, if_pos hj]
      exact horder j i (by change j.val < i.val; omega)
    all_goals simp [hi, hj]
  have ha := split_sum a r
  have hb := split_sum b r
  rw [← ha, ← hb]
  nlinarith

lemma likelihood_cumulative {N : ℕ} (a b : Fin N → ℝ)
    (ha : 0 < ∑ i, a i) (hb : 0 < ∑ i, b i)
    (horder : ∀ i j, i < j → b i * a j ≤ a i * b j) (r : ℕ) :
    lowerSum b r / (∑ i, b i) ≤ lowerSum a r / (∑ i, a i) :=
  (div_le_div_iff₀ hb ha).mpr (likelihood_cross a b horder r)

def cumulative {N : ℕ} (p : PMF (Fin N)) (r : ℕ) : ℝ := lowerSum (fun i ↦ (p i).toReal) r

lemma cumulative_zero {N : ℕ} (p : PMF (Fin N)) : cumulative p 0 = 0 := by
  simp [cumulative, lowerSum]

lemma cumulative_full {N : ℕ} (p : PMF (Fin N)) (r : ℕ) (hr : N ≤ r) : cumulative p r = 1 := by
  have hi : ∀ i : Fin N, i.val < r := fun i ↦ lt_of_lt_of_le i.isLt hr
  simp only [cumulative, lowerSum, if_pos (hi _)]
  exact sum_mass p

lemma cumulative_step {N : ℕ} (p : PMF (Fin N)) (i : Fin N) :
    cumulative p (i.val + 1) - cumulative p i.val = (p i).toReal := by
  have heq : (fun j : Fin N ↦ if j.val < i.val + 1 then (p j).toReal else 0) =
      (fun j ↦ (if j.val < i.val then (p j).toReal else 0) +
        (if j = i then (p i).toReal else 0)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · have hv : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
      have hlt : j.val < i.val + 1 ↔ j.val < i.val := by omega
      simp [hji, hlt]
  unfold cumulative lowerSum
  rw [heq, Finset.sum_add_distrib]
  simp

end
end Lax343628Proofs.FiniteOrder

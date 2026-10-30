import Lax343628Proofs.CoreSpecies
import Lax343628Proofs.Flatness

namespace Lax343628Proofs.ColumnMarks

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.ClassChannels
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

lemma zero_fraction (P : Population n mu) (i : Fin n) :
    fraction i 0 P = (Flatness.columnCount P i : ℝ) / (mu : ℕ) := by
  unfold fraction Flatness.columnCount
  rw [Deletion.uniform_mean, Fintype.card_fin, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma sum_fractions (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = k) :
    ∑ i : Fin n, fraction i 0 P = k := by
  simp_rw [zero_fraction]
  rw [← Finset.sum_div]
  have hh := congrArg (fun m : ℕ ↦ (m : ℝ)) (Flatness.sum_columnCount P hP)
  rw [Nat.cast_sum, Nat.cast_mul] at hh
  rw [hh]
  have hm : ((mu : ℕ) : ℝ) ≠ 0 := by exact_mod_cast mu.ne_zero
  field_simp

def refresh (U : Finset (Fin n)) (astar : ℝ) (P : Population n mu) : Finset (Fin n) :=
  U.filter (fun i ↦ astar < fraction i 0 P)

lemma refresh_subset (U : Finset (Fin n)) (astar : ℝ) (P : Population n mu) : refresh U astar P ⊆ U :=
  Finset.filter_subset _ _

lemma refresh_removed (U : Finset (Fin n)) (astar : ℝ) (P : Population n mu) (i : Fin n)
    (hi : i ∈ U) (hprocess : fraction i 0 P ≤ astar) : (refresh U astar P).card < U.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨refresh_subset U astar P, ?_⟩
  intro heq
  have hh : i ∈ refresh U astar P := heq.symm ▸ hi
  exact (not_lt_of_ge hprocess) (Finset.mem_filter.mp hh).2

lemma size_bound (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = k)
    (U : Finset (Fin n)) (astar : ℝ) (ha : 0 < astar)
    (hU : ∀ i ∈ U, astar < fraction i 0 P) :
    (U.card : ℝ) ≤ (k : ℝ) / astar := by
  have h1 := Finset.sum_le_sum (s := U) (fun i hi ↦ (hU i hi).le)
  have h2 : ∑ i ∈ U, fraction i 0 P ≤ ∑ i : Fin n, fraction i 0 P :=
    Finset.sum_le_univ_sum_of_nonneg (fun i ↦ (fraction_bounds i 0 P).1)
  rw [sum_fractions P hP] at h2
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  apply (le_div_iff₀ ha).mpr
  exact h1.trans h2

lemma refresh_size (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = k)
    (U : Finset (Fin n)) (astar : ℝ) (ha : 0 < astar) :
    (refresh U astar P).card ≤ Nat.ceil ((k : ℝ) / astar) := by
  have hh := size_bound P hP (refresh U astar P) astar ha
    (fun i hi ↦ (Finset.mem_filter.mp hi).2)
  have hc := hh.trans (Nat.le_ceil ((k : ℝ) / astar))
  exact_mod_cast hc

end
end Lax343628Proofs.ColumnMarks

import Lax343628Proofs.FiniteDrift

namespace Lax343628Proofs.RankPotential

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

def tail (M : ℕ) (w : ℕ → ℝ) (a : ℕ) : ℝ := ∑ j ∈ Finset.range M, if a ≤ j then w j else 0

lemma tail_nonneg (M : ℕ) (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (a : ℕ) : 0 ≤ tail M w a := by
  apply Finset.sum_nonneg
  intro j _
  by_cases h : a ≤ j
  · rw [if_pos h]
    exact hw j
  · rw [if_neg h]

lemma tail_antitone (M : ℕ) (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) {a b : ℕ} (hab : a ≤ b) :
    tail M w b ≤ tail M w a := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hb : b ≤ j
  · simp only [if_pos hb, if_pos (hab.trans hb), le_refl]
  · rw [if_neg hb]
    by_cases h : a ≤ j
    · rw [if_pos h]
      exact hw j
    · rw [if_neg h]

lemma tail_drop (M : ℕ) (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) {a b : ℕ} (ha : a < M) (hab : a < b) :
    w a ≤ tail M w a - tail M w b := by
  have hnonneg (j : ℕ) : 0 ≤ (if a ≤ j then w j else 0) - (if b ≤ j then w j else 0) := by
    by_cases hb : b ≤ j
    · simp only [if_pos hb, if_pos (by omega : a ≤ j), sub_self, le_refl]
    · rw [if_neg hb, sub_zero]
      split_ifs <;> first | exact hw j | exact le_rfl
  have hh := Finset.single_le_sum (s := Finset.range M) (fun j _ ↦ hnonneg j) (Finset.mem_range.mpr ha)
  simp only [le_refl, if_true, if_neg (by omega : ¬b ≤ a), sub_zero, Finset.sum_sub_distrib] at hh
  exact hh

variable {α ι : Type*} [Fintype α] [Fintype ι]

def value (M : ℕ) (w : ι → ℕ → ℝ) (count : ι → α → ℕ) (x : α) : ℝ := ∑ i, tail M (w i) (count i x)

omit [Fintype α] in
lemma drop (M : ℕ) (w : ι → ℕ → ℝ) (count : ι → α → ℕ) (hw : ∀ i j, 0 ≤ w i j)
    (x y : α) (hmon : ∀ i, count i x ≤ count i y) (i : ι) (hi : count i x < M) :
    w i (count i x) * (if count i x < count i y then 1 else 0) ≤ value M w count x - value M w count y := by
  have hnonneg (j : ι) : 0 ≤ tail M (w j) (count j x) - tail M (w j) (count j y) :=
    sub_nonneg.mpr (tail_antitone M (w j) (hw j) (hmon j))
  have hh := Finset.single_le_sum (s := Finset.univ) (fun j _ ↦ hnonneg j) (Finset.mem_univ i)
  rw [Finset.sum_sub_distrib] at hh
  by_cases hinc : count i x < count i y
  · rw [if_pos hinc, mul_one]
    exact (tail_drop M (w i) (hw i) hi hinc).trans hh
  · rw [if_neg hinc, mul_zero]
    exact (hnonneg i).trans hh

lemma runtime (K : α → PMF α) (A : Set α) (M : ℕ) (w : ι → ℕ → ℝ) (count : ι → α → ℕ)
    (hw : ∀ i j, 0 ≤ w i j)
    (hmon : ∀ x ∈ A, ∀ y ∈ (K x).support, ∀ i, count i x ≤ count i y)
    (hselected : ∀ x ∈ A, ∃ i, count i x < M ∧
      1 ≤ w i (count i x) * mean (K x) (fun y ↦ if count i x < count i y then 1 else 0))
    (p : PMF α) :
    (∑' t, (law (stopped K A) p t).toOuterMeasure A) ≤ ENNReal.ofReal (∑ i, ∑ j ∈ Finset.range M, w i j) := by
  have hV : ∀ x, 0 ≤ value M w count x := by
    intro x
    exact Finset.sum_nonneg (fun i _ ↦ tail_nonneg M (w i) (hw i) (count i x))
  have hd : ∀ x ∈ A, mean (K x) (value M w count) ≤ value M w count x - 1 := by
    intro x hx
    obtain ⟨i, hi, hs⟩ := hselected x hx
    have hh := mean_mono_on_support (K x) (fun y hy ↦ drop M w count hw x y (hmon x hx y hy) i hi)
    rw [mean_mul, mean_sub, mean_const] at hh
    linarith
  have hh := stopped_runtime_le K A (value M w count) 1 (by norm_num) hV hd p
  simp only [div_one] at hh
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  apply (mean_mono p (fun x ↦ ?_)).trans_eq (mean_const p _)
  apply Finset.sum_le_sum
  intro i _
  have ht := tail_antitone M (w i) (hw i) (Nat.zero_le (count i x))
  simpa only [tail, Nat.zero_le, if_true] using ht

end
end Lax343628Proofs.RankPotential

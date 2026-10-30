import Lax343628Proofs.Weights
import Lax343628Proofs.Profiles

namespace Lax343628Proofs.WeightSums

open Lax343628Proofs.Weights Lax343628Proofs.Profiles
open scoped BigOperators

noncomputable section

lemma sum_initial (f : ℕ → ℝ) {s r : ℕ} (hs : s ≤ r) :
    (∑ i ∈ Finset.range (r + 1), if i ≤ s then f i else 0) =
      ∑ i ∈ Finset.range (s + 1), f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma sum_triangle (f : ℕ → ℕ → ℝ) (r : ℕ) :
    (∑ l ∈ Finset.range (r + 1), ∑ w ∈ Finset.range (l + 1), f l w) =
      ∑ w ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r + 1),
        if w ≤ l then f l w else 0 := by
  calc
    _ = ∑ l ∈ Finset.range (r + 1), ∑ w ∈ Finset.range (r + 1),
        if w ≤ l then f l w else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      exact (sum_initial (f l) (Nat.le_of_lt_succ (Finset.mem_range.mp hl))).symm
    _ = _ := Finset.sum_comm

lemma shifted_vandermonde {r w : ℕ} (hw : w ≤ r) :
    (∑ l ∈ Finset.range (r + 1),
      if w ≤ l then (r.choose l : ℝ) * (r.choose (l - w) : ℝ) else 0) =
        ((2 * r).choose (r - w) : ℝ) := by
  rw [← Finset.sum_range_reflect (fun l ↦
    if w ≤ l then (r.choose l : ℝ) * (r.choose (l - w) : ℝ) else 0) (r + 1)]
  have heq : (∑ i ∈ Finset.range (r + 1),
      if w ≤ r + 1 - 1 - i then (r.choose (r + 1 - 1 - i) : ℝ) *
        (r.choose (r + 1 - 1 - i - w) : ℝ) else 0) =
      ∑ i ∈ Finset.range (r + 1),
        if i ≤ r - w then (r.choose i : ℝ) * (r.choose (r - w - i) : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hsub : r - i - w = r - w - i := by omega
    have hcond : w ≤ r - i ↔ i ≤ r - w := by omega
    simp only [Nat.add_sub_cancel, hsub, hcond, Nat.choose_symm hi']
  rw [heq, sum_initial _ (Nat.sub_le r w)]
  have h := Nat.add_choose_eq r r (r - w)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [Nat.succ_eq_add_one, ← two_mul] at h
  exact_mod_cast h.symm

lemma coefficient_sum (r : ℕ) :
    (∑ l ∈ Finset.range (r + 1), coefficient r l) = viability r := by
  unfold coefficient viability
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.mul_sum, ← mul_div_assoc]
  rw [sum_triangle]
  apply Finset.sum_congr rfl
  intro w hw
  have hw' : w ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hw)
  rw [← shifted_vandermonde hw']
  simp_rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

lemma weight_three : weight 3 = 531 / 425 := by
  rw [weight_rec (by norm_num : 2 ≤ 3)]
  norm_num [Fin.sum_univ_succ, denominator, coefficient, Finset.sum_range_succ,
    weight_zero, weight_one, weight_two, Nat.choose, Nat.factorial]

lemma weight_four : weight 4 = 1595328 / 1298375 := by
  rw [weight_rec (by norm_num : 2 ≤ 4)]
  norm_num [Fin.sum_univ_succ, denominator, coefficient, Finset.sum_range_succ,
    weight_zero, weight_one, weight_two, weight_three, Nat.choose, Nat.factorial]

lemma weight_five : weight 5 = 1955186784 / 1655012645 := by
  rw [weight_rec (by norm_num : 2 ≤ 5)]
  norm_num [Fin.sum_univ_succ, denominator, coefficient, Finset.sum_range_succ,
    weight_zero, weight_one, weight_two, weight_three, weight_four, Nat.choose, Nat.factorial]

lemma weight_upper (r : ℕ) : weight r ≤ 5 / 4 := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr6 : r < 6
    · interval_cases r <;>
        norm_num [weight_zero, weight_one, weight_two, weight_three, weight_four, weight_five]
    · have hr : 6 ≤ r := by omega
      have hr2 : 2 ≤ r := by omega
      have hsum : (∑ l : Fin r, coefficient r l) = viability r - coefficient r r := by
        have htotal := coefficient_sum r
        rw [Finset.sum_range_succ] at htotal
        rw [Fin.sum_univ_eq_sum_range]
        linarith
      have hweighted : (∑ l : Fin r, coefficient r l * weight l) ≤
          (5 / 4 : ℝ) * (viability r - coefficient r r) := by
        calc
          _ ≤ ∑ l : Fin r, coefficient r l * (5 / 4 : ℝ) :=
            Finset.sum_le_sum fun l _ ↦
              mul_le_mul_of_nonneg_left (ih l l.isLt) (coefficient_nonneg r l)
          _ = (5 / 4 : ℝ) * (viability r - coefficient r r) := by
            rw [← Finset.sum_mul, hsum, mul_comm]
      rw [weight_rec hr2]
      apply (div_le_iff₀ (denominator_pos hr2)).mpr
      have hq := viability_le_seventeen hr
      unfold denominator
      nlinarith

lemma anchor_crossing {r : ℕ} (hr : 2 ≤ r) :
    2 * (∑ l ∈ Finset.range (r + 1), coefficient r l * weight l) = (17 / 16 : ℝ) * weight r := by
  have h := weight_rec hr
  have hd := denominator_pos hr
  have heq := (eq_div_iff hd.ne').mp h
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range]
  unfold denominator at heq
  nlinarith

lemma anchor_crossing_one :
    2 * (∑ l ∈ Finset.range 2, coefficient 1 l * weight l) = 1 := by
  norm_num [Finset.sum_range_succ, coefficient, weight_zero, weight_one]

end
end Lax343628Proofs.WeightSums

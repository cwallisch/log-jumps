import Lax343628Proofs.MutationApproximation
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic

namespace Lax343628Proofs.BinomialApproximation

open Lax343628Proofs.MutationApproximation
open scoped BigOperators

noncomputable section

def fallingRatio (n N w : ℕ) : ℝ := ∏ i ∈ Finset.range w, ((N - i : ℕ) : ℝ) / n

lemma fallingRatio_eq (n N w : ℕ) :
    fallingRatio n N w = (w.factorial : ℝ) * (N.choose w : ℝ) / (n : ℝ) ^ w := by
  rw [fallingRatio, Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_range]
  rw [← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]

lemma fallingRatio_le_one {n N w : ℕ} (hn : 0 < n) (hN : N ≤ n) : fallingRatio n N w ≤ 1 := by
  unfold fallingRatio
  apply Finset.prod_le_one
  · intro i _
    positivity
  · intro i _
    apply (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
    exact_mod_cast (Nat.sub_le N i).trans hN

lemma fallingRatio_lower {n N w : ℕ} (hn : 0 < n) (hN : N ≤ n) (hw : w ≤ N) :
    1 - (w : ℝ) * ((n - N + w : ℕ) : ℝ) / n ≤ fallingRatio n N w := by
  let D : ℝ := ((n - N + w : ℕ) : ℝ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  have hD : D ≤ n := by
    change ((n - N + w : ℕ) : ℝ) ≤ n
    exact_mod_cast (show n - N + w ≤ n by omega)
  have hb0 : 0 ≤ 1 - D / n := by apply sub_nonneg.mpr; exact (div_le_one hnpos).mpr hD
  have hprod : (1 - D / n) ^ w ≤ fallingRatio n N w := by
    have heq : (1 - D / n) ^ w = ∏ _i ∈ Finset.range w, (1 - D / n) := by simp
    rw [fallingRatio, heq]
    apply Finset.prod_le_prod
    · intro i _
      exact hb0
    · intro i hi
      have hiw : i < w := Finset.mem_range.mp hi
      have hiN : i ≤ N := by omega
      apply (le_div_iff₀ hnpos).mpr
      have hDexp : D = (n : ℝ) - N + w := by simp [D, Nat.cast_sub hN]
      rw [Nat.cast_sub hiN]
      have hmul : (1 - D / (n : ℝ)) * n = (n : ℝ) - D := by field_simp
      rw [hmul, hDexp]
      have hiwR : (i : ℝ) ≤ w := by exact_mod_cast Nat.le_of_lt hiw
      linarith
  have hbern := one_add_mul_sub_le_pow (a := 1 - D / n) (by linarith : -1 ≤ 1 - D / n) w
  have hsmall : 1 - (w : ℝ) * D / n ≤ (1 - D / n) ^ w := by
    have heq : 1 - (w : ℝ) * D / n = 1 + (w : ℝ) * (1 - D / n - 1) := by ring
    rw [heq]
    exact hbern
  exact hsmall.trans hprod

lemma binomial_factor_error {n N w : ℕ} (hn : 0 < n) (hN : N ≤ n) (hw : w ≤ N) :
    |(N.choose w : ℝ) / (n : ℝ) ^ w - 1 / (w.factorial : ℝ)| ≤
      (w : ℝ) * ((n - N + w : ℕ) : ℝ) / ((n : ℝ) * (w.factorial : ℝ)) := by
  have hf : (0 : ℝ) < w.factorial := by exact_mod_cast Nat.factorial_pos w
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlow := fallingRatio_lower hn hN hw
  have hupp := fallingRatio_le_one (w := w) hn hN
  have heq : (N.choose w : ℝ) / (n : ℝ) ^ w - 1 / (w.factorial : ℝ) =
      (fallingRatio n N w - 1) / (w.factorial : ℝ) := by
    rw [fallingRatio_eq]
    field_simp
  rw [heq, abs_div, abs_of_pos hf]
  apply (div_le_iff₀ hf).mpr
  have hradius : ((w : ℝ) * ((n - N + w : ℕ) : ℝ) /
      ((n : ℝ) * (w.factorial : ℝ))) * (w.factorial : ℝ) =
      (w : ℝ) * ((n - N + w : ℕ) : ℝ) / n := by field_simp
  rw [hradius]
  rw [abs_of_nonpos (by linarith : fallingRatio n N w - 1 ≤ 0)]
  linarith

lemma product_error (A B C D a b : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hA : |A - C| ≤ a) (hD : |B - D| ≤ b) :
    |A * B - C * D| ≤ a + C * b := by
  have heq : A * B - C * D = (A - C) * B + C * (B - D) := by ring
  rw [heq]
  calc
    _ ≤ |(A - C) * B| + |C * (B - D)| := abs_add_le _ _
    _ = |A - C| * B + C * |B - D| := by rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hC]
    _ ≤ a * 1 + C * b := add_le_add (mul_le_mul hA hB1 hB0 ha)
      (mul_le_mul_of_nonneg_left hD hC)
    _ = _ := by rw [mul_one]

def binomialTerm (n N w : ℕ) : ℝ :=
  (N.choose w : ℝ) / (n : ℝ) ^ w * (1 - 1 / (n : ℝ)) ^ (N - w)

lemma binomial_poisson_error {n N w : ℕ} (hn : 2 ≤ n) (hN : N ≤ n) (hw : w ≤ N) :
    |binomialTerm n N w - Real.exp (-1) / (w.factorial : ℝ)| ≤
      ((w : ℝ) + 2) * (((n - N + w : ℕ) : ℝ) + 1) /
        ((n : ℝ) * (w.factorial : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hf : (0 : ℝ) < w.factorial := by exact_mod_cast Nat.factorial_pos w
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnR
  have hq0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hbase : 0 ≤ 1 - 1 / (n : ℝ) := by linarith
  have hbase1 : 1 - 1 / (n : ℝ) ≤ 1 := by linarith
  have hB0 : 0 ≤ (1 - 1 / (n : ℝ)) ^ (N - w) := pow_nonneg hbase _
  have hB1 : (1 - 1 / (n : ℝ)) ^ (N - w) ≤ 1 := pow_le_one₀ hbase hbase1
  have hdef : n - (N - w) = n - N + w := by omega
  have hb := shorter_mutation_approximation n (N - w) hn ((Nat.sub_le N w).trans hN)
  rw [hdef] at hb
  have ha := binomial_factor_error (show 0 < n by omega) hN hw
  have h := product_error ((N.choose w : ℝ) / (n : ℝ) ^ w)
    ((1 - 1 / (n : ℝ)) ^ (N - w)) (1 / (w.factorial : ℝ)) (Real.exp (-1))
    ((w : ℝ) * ((n - N + w : ℕ) : ℝ) / ((n : ℝ) * (w.factorial : ℝ)))
    (2 * (((n - N + w : ℕ) : ℝ) + 1) / (n : ℝ)) hB0 hB1 (by positivity) (by positivity) ha hb
  have heq : (w : ℝ) * ((n - N + w : ℕ) : ℝ) / ((n : ℝ) * (w.factorial : ℝ)) +
      (1 / (w.factorial : ℝ)) * (2 * (((n - N + w : ℕ) : ℝ) + 1) / (n : ℝ)) =
      ((w : ℝ) * ((n - N + w : ℕ) : ℝ) + 2 * (((n - N + w : ℕ) : ℝ) + 1)) /
        ((n : ℝ) * (w.factorial : ℝ)) := by field_simp
  rw [heq] at h
  have hupper : ((w : ℝ) * ((n - N + w : ℕ) : ℝ) + 2 * (((n - N + w : ℕ) : ℝ) + 1)) /
      ((n : ℝ) * (w.factorial : ℝ)) ≤
      ((w : ℝ) + 2) * (((n - N + w : ℕ) : ℝ) + 1) /
        ((n : ℝ) * (w.factorial : ℝ)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [(Nat.cast_nonneg w : (0 : ℝ) ≤ w)]
  have h' := h.trans hupper
  simpa only [binomialTerm, div_eq_mul_inv, one_mul, mul_one, mul_comm] using h'

end
end Lax343628Proofs.BinomialApproximation

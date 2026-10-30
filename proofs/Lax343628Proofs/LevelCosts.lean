import Lax343628Proofs.ArrivalRanks
import Lax343628Proofs.ReciprocalCosts
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Lax343628Proofs.LevelCosts

open Lax343628Proofs.ArrivalRanks
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def ordinary (n z : ℕ) (mu : ℕ+) : ℝ := (n : ℝ) / z + 2 * (mu : ℕ) * Real.sqrt n / Real.sqrt z

lemma integer_offset (n z : ℕ) (mu : ℕ+) (hn : 0 < n) (hz : 0 < z) :
    (∑ l ∈ Finset.range (mu : ℕ), 1 / ((z : ℝ) / n + (l : ℝ) / (mu : ℕ))) ≤ ordinary n z mu := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hh := ReciprocalCosts.offset (mu : ℕ) ((z : ℝ) / n) (by positivity)
  apply hh.trans_eq
  unfold ordinary
  rw [Real.sqrt_div hzR.le]
  field_simp

lemma crude (n z : ℕ) (mu : ℕ+) (hn : 0 < n) (hz : 0 < z) :
    ordinary n z mu ≤ (n : ℝ) + 2 * (mu : ℕ) * Real.sqrt n := by
  have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hs : 1 ≤ Real.sqrt z := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hz1
  unfold ordinary
  exact add_le_add ((div_le_self (by positivity) hz1)) (div_le_self (by positivity) hs)

lemma coefficient_positive (n k v : ℕ) (pc : ℝ) (hp : 0 < pc) : 0 < coefficient n k pc v := by
  unfold coefficient
  split_ifs <;> positivity

lemma ordinary_level (n k : ℕ) (mu : ℕ+) (pc : ℝ) (hp : 0 < pc) (v : Fin n) (hk : k ≤ v.val) :
    (∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) ≤
      (1 / coefficient n k pc v.val) * ordinary n (n - (v.val - k)) mu := by
  have hn : 0 < n := by have := v.isLt; omega
  have hz : 0 < n - (v.val - k) := by have := v.isLt; omega
  have heq : (∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) =
      (1 / coefficient n k pc v.val) *
        (∑ l ∈ Finset.range (mu : ℕ), 1 / (((n - (v.val - k) : ℕ) : ℝ) / n + (l : ℝ) / (mu : ℕ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    unfold cost rate
    rw [if_neg (by omega : ¬v.val < k)]
    rw [one_div_mul_one_div]
    congr 1
    ring
  rw [heq]
  have hc := coefficient_positive n k v.val pc hp
  exact mul_le_mul_of_nonneg_left (integer_offset n _ mu hn hz) (by positivity : 0 ≤ 1 / coefficient n k pc v.val)

lemma valley_level (n k : ℕ) (mu : ℕ+) (pc : ℝ) (v : Fin n) (hk : v.val < k) :
    (∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) = (mu : ℕ) * (32 / pc : ℝ) := by
  simp only [cost, rate, if_pos hk, one_div_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma sum_ordinary (n : ℕ) (mu : ℕ+) (hn : 1 ≤ n) :
    (∑ j ∈ Finset.range n, ordinary n (j + 1) mu) ≤
      (n : ℝ) * (1 + Real.log n) + 4 * (mu : ℕ) * n := by
  have hsum : (∑ j ∈ Finset.range n, 1 / ((j + 1 : ℕ) : ℝ)) ≤ 1 + Real.log n := by
    have hh := harmonic_le_one_add_log n
    simpa only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using hh
  have hsqrt := ReciprocalCosts.sum_inv_sqrt n
  have hsqrt' : (∑ j ∈ Finset.range n, 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) ≤ 2 * Real.sqrt n := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsqrt
  have heq : (∑ j ∈ Finset.range n, ordinary n (j + 1) mu) =
      (n : ℝ) * (∑ j ∈ Finset.range n, 1 / ((j + 1 : ℕ) : ℝ)) +
        (2 * (mu : ℕ) * Real.sqrt n) * (∑ j ∈ Finset.range n, 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) := by
    simp only [ordinary, Finset.sum_add_distrib, Finset.mul_sum]
    apply congrArg₂ (fun a b : ℝ ↦ a + b)
    all_goals apply Finset.sum_congr rfl
    all_goals intro j _
    all_goals ring
  rw [heq]
  have h1 := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ n by positivity)
  have h2 := mul_le_mul_of_nonneg_left hsqrt' (show (0 : ℝ) ≤ 2 * (mu : ℕ) * Real.sqrt n by positivity)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  nlinarith

end
end Lax343628Proofs.LevelCosts

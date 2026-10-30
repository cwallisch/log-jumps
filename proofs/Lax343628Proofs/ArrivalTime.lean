import Lax343628Proofs.FarLevelCosts

namespace Lax343628Proofs.ArrivalTime

open Lax343628Proofs.ArrivalRanks Lax343628Proofs.EntropyLedger
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma absorb_near (s n m : ℝ) (hs : 16777216 ≤ s) (hn : s ^ 300 ≤ n) (hm : s ^ 300 ≤ m) :
    s ^ 70 * (n + 2 * m * Real.sqrt n) ≤ 2 * m * n := by
  have hs1 : 1 ≤ s := by linarith
  have hp : 1 ≤ s ^ 300 := one_le_pow₀ hs1
  have hn0 : 0 ≤ n := by linarith
  have hm0 : 0 ≤ m := by linarith
  have h70 : s ^ 70 ≤ m := (pow_le_pow_right₀ hs1 (by norm_num : 70 ≤ 300)).trans hm
  have h140 : 4 * s ^ 140 ≤ n := (SpeciesScale.constant_power s 4 hs1 (by nlinarith) 140 300 (by norm_num)).trans hn
  have hroot : 2 * s ^ 70 ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    have heq : (2 * s ^ 70) ^ 2 = 4 * s ^ 140 := by rw [mul_pow, ← pow_mul]; norm_num
    rwa [heq]
  have h1 := mul_le_mul_of_nonneg_right h70 hn0
  have h2 := mul_le_mul_of_nonneg_right hroot (show 0 ≤ m * Real.sqrt n by positivity)
  have heq : Real.sqrt n * (m * Real.sqrt n) = m * n := by
    calc
      _ = m * (Real.sqrt n) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hn0]
  rw [heq] at h2
  nlinarith

lemma sum_costs (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n k : ℕ) (mu : ℕ+) (pc delta : ℝ)
    (hk : 1 ≤ k) (hks : k ≤ (S : ℕ)) (hD : (3 : ℝ) ^ k ≤ (S : ℕ))
    (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n) :
    (∑ v : Fin n, ∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) ≤
      (4096 / pc) * (mu : ℕ) * (n : ℝ) := by
  let s : ℝ := (S : ℕ)
  let W := logarithms n mu delta
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hs1 : 1 ≤ s := by linarith
  have hsp : 0 < s := by linarith
  have hpcp : 0 < pc := (div_pos (by norm_num) hsp).trans_le hpc.1
  have hW : 1 ≤ W := (logarithms_bounds n mu delta hd).1
  have hpow : 1 ≤ s ^ 300 := one_le_pow₀ hs1
  have hmu300 : s ^ 300 ≤ (mu : ℕ) := by
    have hh := mul_le_mul_of_nonneg_left hW (show 0 ≤ s ^ 300 by positivity)
    linarith
  have hn300 : s ^ 300 ≤ (n : ℝ) := PhaseScale.dimension S n mu delta hd hn
  have hn1 : 1 ≤ n := by
    have hh : (1 : ℝ) ≤ n := hpow.trans hn300
    exact_mod_cast hh
  have hmuW : W ≤ (mu : ℕ) := by nlinarith [mul_nonneg (show 0 ≤ s ^ 300 - 1 by linarith) (show 0 ≤ W by linarith)]
  have hlog : 1 + Real.log (n : ℝ) ≤ (mu : ℕ) := by
    have hm0 : (0 : ℝ) ≤ (mu : ℕ) := Nat.cast_nonneg _
    have hmLog := Real.log_nonneg (show (1 : ℝ) ≤ (mu : ℕ) + 1 by linarith)
    have hdLog := Real.log_nonneg ((one_le_div hd.1).mpr hd.2)
    have hnLog := Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
      (show (n : ℝ) ≤ n + 1 by linarith)
    dsimp only [W, logarithms] at hmuW
    linarith
  have hnear := (NearLevelCosts.bound S hS hk hks hD pc hpc.1).trans (absorb_near s n (mu : ℕ) hs hn300 hmu300)
  have hfar := FarLevelCosts.bound n k mu pc hpcp hn1
  have hfar' : (∑ v ∈ FarLevelCosts.levels n k, ∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) ≤
      (640 / pc) * (mu : ℕ) * (n : ℝ) := by
    apply hfar.trans
    have hh := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ n by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 128 / pc by positivity)
    linear_combination hh'
  have hvalley := FarLevelCosts.valley_bound n k mu pc hpcp
  have hnear' : (∑ v ∈ NearLevelCosts.levels n k, ∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) ≤
      (2 / pc) * (mu : ℕ) * (n : ℝ) := by
    apply hnear.trans
    have hh : 1 ≤ 1 / pc := (le_div_iff₀ hpcp).mpr (by simpa only [one_mul] using hpc.2)
    have hm := mul_le_mul_of_nonneg_right hh (show (0 : ℝ) ≤ 2 * (mu : ℕ) * n by positivity)
    linear_combination hm
  rw [FarLevelCosts.partition]
  apply (add_le_add (add_le_add hvalley hfar') hnear').trans
  have hh : 0 ≤ ((mu : ℕ) : ℝ) * n / pc := by positivity
  linear_combination 3422 * hh

end
end Lax343628Proofs.ArrivalTime

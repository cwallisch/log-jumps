import Lax343628Proofs.SpeciesScale
import Lax343628Proofs.FlatSampling

namespace Lax343628Proofs.SpeciesConditions

open Lax343628Proofs.SpeciesParameters Lax343628Proofs.EntropyLedger
open Lax343628Proofs.PlateauKernelApproximation
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma assemble (n k : ℕ) (pc p v : ℝ) (hk : 1 ≤ k) (hn : 2 ≤ n) (hkn : 4 * k ≤ n)
    (hv : 0 < v) (hp : 0 < p ∧ p ≤ 1) (hsmall : p ≤ 1 / (16 * Real.sqrt k))
    (hA : v / 800 ≤ Real.exp (-1) * (p * (4 : ℝ)⁻¹ ^ k / 100))
    (hB : v / 16 ≤ Real.exp (-1) * p * (1 / (2 * Real.sqrt k)))
    (hC : v / 16 ≤ pc * Real.exp (-1) * p * (1 / (2 * Real.sqrt k)))
    (hp2 : v ≤ p ^ 2) (hpk : v ≤ p * k)
    (hE : approximationError n k ≤ v / 1000000000)
    (hE2 : approximationError n k ^ 2 * n ≤ v / 1000000000)
    (hkN : (k : ℝ) / n ≤ v / 1000000000) (hN : 1 / (n : ℝ) ≤ v / 1000000000) :
    CloneProtection.Conditions n k pc p ∧
      (129 / 100 : ℝ) * approximationError n k ≤ SpeciesProtection.strictConstant * p ^ 2 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hgain : 2 * ((k : ℝ) / (16 * n)) ≤ Real.exp (-1) * (p * (4 : ℝ)⁻¹ ^ k / 100) := by
    have heq : 2 * ((k : ℝ) / (16 * n)) = ((k : ℝ) / n) / 8 := by ring
    rw [heq]
    linarith
  have hA0 : 0 ≤ Real.exp (-1) * (p * (4 : ℝ)⁻¹ ^ k / 100) := by
    have hpp := hp.1
    positivity
  have hAk := mul_le_mul_of_nonneg_left hkR hA0
  have hsquared : 8 * ((129 / 100 : ℝ) * approximationError n k) ^ 2 ≤
      (Real.exp (-1) * (p * (4 : ℝ)⁻¹ ^ k / 100)) * ((k : ℝ) / (16 * n)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (show (0 : ℝ) < 16 * n by positivity)).mpr
    nlinarith
  have hmutation : (1 / (n : ℝ)) ^ 2 ≤ p * (k : ℝ) / (32 * n) := by
    apply (le_div_iff₀ (show (0 : ℝ) < 32 * n by positivity)).mpr
    have heq : (1 / (n : ℝ)) ^ 2 * (32 * n) = 32 * (1 / (n : ℝ)) := by field_simp
    rw [heq]
    linarith
  have happrox : approximationError n k ≤ Real.exp (-1) * p * (1 / (2 * Real.sqrt k)) / 16 := by linarith
  have hN1 : 1 / (n : ℝ) ≤ 1 := (div_le_one hnp).mpr (by exact_mod_cast (show 1 ≤ n by omega))
  have hN0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hreturn : (1 / (n : ℝ)) ^ 2 ≤ pc * Real.exp (-1) * p * (1 / (2 * Real.sqrt k)) / 8 := by
    have hh : (1 / (n : ℝ)) ^ 2 ≤ 1 / (n : ℝ) := by nlinarith
    linarith
  refine ⟨⟨⟨hk, hn, hkn, hp.1, hp.2, hgain, hsquared, hmutation⟩, hsmall, happrox, hreturn⟩, ?_⟩
  unfold SpeciesProtection.strictConstant
  linarith

lemma of_size (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n k : ℕ) (mu : ℕ+) (delta pc : ℝ)
    (hk : 1 ≤ k) (hks : k ≤ (S : ℕ)) (hD : (3 : ℝ) ^ k ≤ (S : ℕ))
    (hpc : 1 / (S : ℕ) ≤ pc) (hd : 0 < delta ∧ delta ≤ 1)
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n) :
    CloneProtection.Conditions n k pc (threshold k) ∧
      (129 / 100 : ℝ) * approximationError n k ≤ SpeciesProtection.strictConstant * threshold k ^ 2 := by
  let s : ℝ := (S : ℕ)
  let v : ℝ := 1 / s ^ 4
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hs1 : 1 ≤ s := by linarith
  have hsp : 0 < s := by linarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hksR : (k : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hks
  have hroot : Real.sqrt k ≤ s := (Real.sqrt_le_self_iff.mpr (Or.inr hkR)).trans hksR
  have hrootp : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by linarith)
  have hp := threshold_bounds k hk
  have hpLower := SpeciesScale.threshold_lower s hs k hk hksR
  have hnlarge := SpeciesScale.large_dimension S hS n mu delta hd hn
  have hnR : (2 : ℝ) ≤ n := by
    have hh : 1 ≤ s ^ 10 := one_le_pow₀ hs1
    linarith
  have hdim : 4 * k ≤ n := by
    have hh : s ≤ s ^ 10 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (show 1 ≤ 10 by norm_num)
    have hh' : 4 * (k : ℝ) ≤ n := by linarith
    exact_mod_cast hh'
  have he := SpeciesScale.error_bounds s hs n k hk hksR hnlarge
  have hpow6 : s ≤ s ^ 6 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (show 1 ≤ 6 by norm_num)
  have hkN := SpeciesScale.quotient s n k hs1 hnlarge (hksR.trans hpow6) (by positivity)
  have hN := SpeciesScale.quotient s n 1 hs1 hnlarge (one_le_pow₀ hs1) (by norm_num)
  have hinv4 : 1 / s ^ 2 ≤ (4 : ℝ)⁻¹ ^ k := by
    have hfour : (4 : ℝ) ^ k ≤ s ^ 2 := by
      have hh : (4 : ℝ) ^ k ≤ ((3 : ℝ) ^ 2) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
      have heq : ((3 : ℝ) ^ 2) ^ k = ((3 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [heq] at hh
      exact hh.trans (pow_le_pow_left₀ (by positivity) hD 2)
    rw [inv_pow, ← one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hfour
  have hpprod : v ≤ threshold k * (4 : ℝ)⁻¹ ^ k := by
    have hh := mul_le_mul hpLower hinv4 (by positivity) hp.1.le
    have heq : (1 / s ^ 2) * (1 / s ^ 2) = v := by dsimp [v]; field_simp
    rw [heq] at hh
    exact hh
  have hpsq : v ≤ threshold k ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / s ^ 2) hpLower 2
    have heq : (1 / s ^ 2) ^ 2 = v := by dsimp [v]; field_simp
    rwa [heq] at hh
  have hpv : v ≤ threshold k := by
    apply le_trans _ hpLower
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ hs1 (by norm_num : 2 ≤ 4))
  have hexp : (1 / 8 : ℝ) ≤ Real.exp (-1) := by linarith [Real.exp_neg_one_gt_d9]
  have hA : v / 800 ≤ Real.exp (-1) * (threshold k * (4 : ℝ)⁻¹ ^ k / 100) := by
    have hh := mul_le_mul hexp (div_le_div_of_nonneg_right hpprod (show (0 : ℝ) ≤ 100 by norm_num))
      (by positivity : 0 ≤ v / 100) (Real.exp_nonneg (-1))
    nlinarith
  have hrootInv : 1 / (2 * s) ≤ 1 / (2 * Real.sqrt k) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hB0 : (1 / (2 * s ^ 3)) ≤ threshold k * (1 / (2 * Real.sqrt k)) := by
    have hh := mul_le_mul hpLower hrootInv (by positivity) hp.1.le
    have heq : 1 / s ^ 2 * (1 / (2 * s)) = 1 / (2 * s ^ 3) := by field_simp
    rwa [heq] at hh
  have hB : v / 16 ≤ Real.exp (-1) * threshold k * (1 / (2 * Real.sqrt k)) := by
    have hh := mul_le_mul hexp hB0 (by positivity : 0 ≤ 1 / (2 * s ^ 3)) (Real.exp_nonneg (-1))
    have h34 : v / 16 ≤ (1 / 8 : ℝ) * (1 / (2 * s ^ 3)) := by
      dsimp [v]
      have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num) (show 0 < s ^ 3 by positivity)
        (pow_le_pow_right₀ hs1 (by norm_num : 3 ≤ 4))
      linear_combination hh / 16
    exact h34.trans (by convert hh using 1; ring)
  have hpc0 : 0 ≤ pc := (by positivity : (0 : ℝ) ≤ 1 / s).trans hpc
  have hC : v / 16 ≤ pc * Real.exp (-1) * threshold k * (1 / (2 * Real.sqrt k)) := by
    have hh := mul_le_mul hpc hB0 (by positivity : 0 ≤ 1 / (2 * s ^ 3))
      hpc0
    have heq : 1 / s * (1 / (2 * s ^ 3)) = v / 2 := by dsimp [v]; field_simp
    rw [heq] at hh
    have hh' := mul_le_mul hexp hh (by positivity : 0 ≤ v / 2) (Real.exp_nonneg (-1))
    nlinarith
  apply assemble n k pc (threshold k) v hk (by exact_mod_cast hnR) hdim (by dsimp [v]; positivity)
    ⟨hp.1, by linarith [hp.2.1]⟩ hp.2.2 hA hB hC hpsq _ he.1 he.2 hkN hN
  exact hpv.trans (by nlinarith [mul_nonneg hp.1.le (show 0 ≤ (k : ℝ) - 1 by linarith)])

end
end Lax343628Proofs.SpeciesConditions

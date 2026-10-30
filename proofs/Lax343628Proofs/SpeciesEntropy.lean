import Lax343628Proofs.SpeciesExponents
import Lax343628Proofs.TimeAbsorption
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Fintype.Powerset

namespace Lax343628Proofs.SpeciesEntropy

open Lax343628Proofs.SpeciesParameters Lax343628Proofs.EntropyLedger Lax343628Proofs.Genotypes
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma genotypes (n k : ℕ) (s W : ℝ) (hn : 1 ≤ n) (hk : (k : ℝ) ≤ s)
    (hW : Real.log ((n : ℝ) + 1) ≤ W) (_hW0 : 0 ≤ W) :
    (Fintype.card (Genotype n k) : ℝ) ≤ Real.exp (s * W) := by
  have hcount : Fintype.card (Genotype n k) ≤ (n + 1) ^ k := by
    rw [Fintype.card_finset_len, Fintype.card_fin]
    exact (Nat.choose_le_pow n k).trans (Nat.pow_le_pow_left (by omega) k)
  have hcountR : (Fintype.card (Genotype n k) : ℝ) ≤ ((n : ℝ) + 1) ^ k := by exact_mod_cast hcount
  apply hcountR.trans
  have heq : ((n : ℝ) + 1) ^ k = Real.exp ((k : ℝ) * Real.log ((n : ℝ) + 1)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [heq]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul hk hW (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith)

lemma horizon_log (n J : ℕ) (mu : ℕ+) (s W : ℝ) (hs : 16777216 ≤ s) (hW : 1 ≤ W)
    (hlogn : Real.log ((n : ℝ) + 1) ≤ W) (hlogm : Real.log ((mu : ℕ) + 1 : ℝ) ≤ W)
    (hJ : (J : ℝ) ≤ 67108864 * (mu : ℕ) * (n : ℝ)) :
    Real.log ((J : ℝ) + 1) ≤ 4 * s * W := by
  have hsp : 0 < s := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hm1 : (1 : ℝ) ≤ (mu : ℕ) := by exact_mod_cast mu.pos
  have hs2 : (67108865 : ℝ) ≤ s ^ 2 := by nlinarith
  have hprod : ((mu : ℕ) : ℝ) * n ≤ ((mu : ℕ) + 1 : ℝ) * ((n : ℝ) + 1) := by nlinarith
  have hbase : (1 : ℝ) ≤ ((mu : ℕ) + 1 : ℝ) * ((n : ℝ) + 1) := by nlinarith
  have hupper : (J : ℝ) + 1 ≤ s ^ 2 * (((mu : ℕ) + 1 : ℝ) * ((n : ℝ) + 1)) := by
    have hh := mul_le_mul_of_nonneg_right hs2 (show 0 ≤ ((mu : ℕ) + 1 : ℝ) * ((n : ℝ) + 1) by positivity)
    nlinarith
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < (J : ℝ) + 1) hupper
  rw [Real.log_mul (by positivity : s ^ 2 ≠ 0) (by positivity : ((mu : ℕ) + 1 : ℝ) * ((n : ℝ) + 1) ≠ 0),
    Real.log_pow, Real.log_mul (by positivity : ((mu : ℕ) + 1 : ℝ) ≠ 0) (by positivity : (n : ℝ) + 1 ≠ 0)] at hh
  have hlogs := Real.log_le_self hsp.le
  have hsW := mul_le_mul_of_nonneg_left hW hsp.le
  have hWscale : W ≤ s * W := by nlinarith [mul_nonneg (show 0 ≤ s - 1 by linarith) (show 0 ≤ W by linarith)]
  norm_num only [Nat.cast_ofNat] at hh
  linarith

lemma divide_powers (s W : ℝ) (hs : 0 < s) (p q : ℕ) :
    (s ^ (p + q) * W) / s ^ p = s ^ q * W := by
  rw [pow_add]
  field_simp

lemma error (s W m C t : ℝ) (hs : 16777216 ≤ s) (hW : 1 ≤ W)
    (hm : s ^ 300 * W ≤ m) (_hC : 0 ≤ C) (ht : 0 < t)
    (hcount : C ≤ Real.exp (s * W)) (hlogt : Real.log t ≤ 4 * s * W) :
    C * t ^ 2 * (2 * Real.exp (-m / s ^ 12)) ≤ 1 / 128 := by
  have hsp : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hW0 : 0 ≤ W := by linarith
  have htupper : t ≤ Real.exp (4 * s * W) := by
    rw [← Real.exp_log ht]
    exact Real.exp_le_exp.mpr hlogt
  have hcoef : C * t ^ 2 ≤ Real.exp (9 * s * W) := by
    have hh := mul_le_mul hcount (pow_le_pow_left₀ ht.le htupper 2) (sq_nonneg t) (Real.exp_nonneg _)
    apply hh.trans_eq
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hmdiv : s ^ 288 * W ≤ m / s ^ 12 := by
    have hh := div_le_div_of_nonneg_right hm (show 0 ≤ s ^ 12 by positivity)
    rw [show (300 : ℕ) = 12 + 288 by rfl, divide_powers s W hsp] at hh
    exact hh
  have hp : s ^ 2 ≤ s ^ 288 := pow_le_pow_right₀ hs1 (by norm_num)
  have hbig : 9 * s + 256 ≤ s ^ 288 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hbig hW0
  have hsmall : 9 * s * W - m / s ^ 12 ≤ -256 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ 2 * Real.exp (-m / s ^ 12) by positivity)
  have heq : Real.exp (9 * s * W) * (2 * Real.exp (-m / s ^ 12)) =
      2 * Real.exp (9 * s * W - m / s ^ 12) := by rw [← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, ← Real.exp_add]; simp only [neg_div, sub_eq_add_neg]
  rw [heq] at hprod
  have hexp := Real.add_one_le_exp (256 : ℝ)
  have hfinal : 2 * Real.exp (-256) ≤ (1 / 128 : ℝ) := by
    rw [Real.exp_neg]
    have hh : (Real.exp (256 : ℝ))⁻¹ ≤ (1 / 256 : ℝ) :=
      by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 256) (show (256 : ℝ) ≤ Real.exp 256 by linarith)
    linarith
  exact hprod.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsmall) (by norm_num)).trans hfinal)

end
end Lax343628Proofs.SpeciesEntropy

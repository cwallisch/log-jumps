import Lax343628Proofs.MutationLower

namespace Lax343628Proofs.FarBirth

open Lax343628.Algorithm Lax343628Proofs.FiniteDrift Lax343628Proofs.CrossoverCount
open Lax343628Proofs.PhysicalOffspring
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k i : ℕ}

lemma crossover (hkn : k ≤ n) (hfar : 16 * (k + 1) ≤ n - k - i)
    (x y : BitString n) (hx : i ≤ ones x ∧ ones x ≤ n - k)
    (hy : i ≤ ones y ∧ ones y ≤ n - k) (hxy : x ≠ y) :
    1 / 8 ≤ mean (pairMutation x y 0) (fun z ↦ if i < ones z ∧ ones z ≤ n - k then 1 else 0) := by
  have hi : i ≤ n - k := by omega
  have hdim : differing x y ≤ 2 * (n - i) := by
    have hh := differing_le x y
    omega
  have hsum := parent_sum x y
  have hsumR : (ones x : ℝ) + (ones y : ℝ) = 2 * (common x y : ℝ) + differing x y := by exact_mod_cast hsum
  have hxR : (i : ℝ) ≤ ones x ∧ (ones x : ℝ) ≤ (n - k : ℕ) := by exact_mod_cast hx
  have hyR : (i : ℝ) ≤ ones y ∧ (ones y : ℝ) ≤ (n - k : ℕ) := by exact_mod_cast hy
  have hmean : (i : ℝ) ≤ (common x y : ℝ) + (differing x y : ℝ) / 2 ∧
      (common x y : ℝ) + (differing x y : ℝ) / 2 ≤ (n - k : ℕ) := by
    constructor <;> nlinarith
  have hwidth : (i : ℝ) < (n - k : ℕ) := by exact_mod_cast (show i < n - k by omega)
  have hvarNat : 8 * differing x y ≤ (n - k - i) ^ 2 := by
    have hr : 16 ≤ n - k - i := by omega
    have hri : n - i = k + (n - k - i) := by omega
    have hmul := Nat.mul_le_mul_right (n - k - i) hr
    nlinarith
  have hvar : 8 * (differing x y : ℝ) ≤ (((n - k : ℕ) : ℝ) - i) ^ 2 := by
    have hrR : ((n - k - i : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) - i := by
      have hh : ((n - k - i : ℕ) : ℝ) + i = (n - k : ℕ) := by exact_mod_cast (Nat.sub_add_cancel hi)
      linarith
    have hh : 8 * (differing x y : ℝ) ≤ ((n - k - i : ℕ) : ℝ) ^ 2 := by exact_mod_cast hvarNat
    rwa [hrR] at hh
  rw [count_mean x y (fun m ↦ if i < m ∧ m ≤ n - k then 1 else 0)]
  have hh := FairInterval.bound (differing x y) (differing_pos x y hxy) (common x y) i ((n - k : ℕ) : ℝ) hwidth hmean hvar
  convert hh using 1
  unfold FairMedian.probability
  congr 1
  funext w
  simp only [Set.mem_ofPred_eq, ← Nat.cast_add, Nat.cast_lt, Nat.cast_le]

lemma standard (hn : 2 ≤ n) (hkn : k ≤ n) (hfar : 16 * (k + 1) ≤ n - k - i)
    (x y : BitString n) (hx : i ≤ ones x ∧ ones x ≤ n - k)
    (hy : i ≤ ones y ∧ ones y ≤ n - k) (hxy : x ≠ y) :
    1 / 64 ≤ mean (pairMutation x y (1 / n)) (fun z ↦ if i < ones z ∧ ones z ≤ n - k then 1 else 0) := by
  have hc := crossover hkn hfar x y hx hy hxy
  have hm := MutationLower.standard hn x y (fun z ↦ if i < ones z ∧ ones z ≤ n - k then 1 else 0)
    (by intro z; split_ifs <;> norm_num)
  linarith

end
end Lax343628Proofs.FarBirth

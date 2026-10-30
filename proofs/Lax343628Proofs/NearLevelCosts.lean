import Lax343628Proofs.LevelCosts
import Lax343628Proofs.SpeciesScale

namespace Lax343628Proofs.NearLevelCosts

open Lax343628Proofs.ArrivalRanks Lax343628Proofs.LevelCosts
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

def levels (n k : ℕ) : Finset (Fin n) := Finset.univ.filter
  (fun v ↦ k ≤ v.val ∧ ¬16 * (k + 1) ≤ n - k - (v.val - k))

lemma cardinality (n k : ℕ) : (levels n k).card ≤ 16 * (k + 1) := by
  let f : Fin n → ℕ := fun v ↦ v.rev.val
  have hf : Function.Injective f := by
    intro v w hh
    have heq : v.rev = w.rev := Fin.ext hh
    exact Fin.rev_injective heq
  have hsub : (levels n k).image f ⊆ Finset.range (16 * (k + 1)) := by
    intro t ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    have hvc := (Finset.mem_filter.mp hv).2
    have hn := v.isLt
    apply Finset.mem_range.mpr
    dsimp only [f]
    simp only [Fin.val_rev]
    omega
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf, Finset.card_range] at hh
  exact hh

lemma inverse (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hk : 1 ≤ k) (_hks : k ≤ (S : ℕ))
    (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (pc : ℝ) (hpc : 1 / (S : ℕ) ≤ pc)
    (v : Fin n) (hv : v ∈ levels n k) : 1 / coefficient n k pc v.val ≤ ((S : ℕ) : ℝ) ^ 68 := by
  let s : ℝ := (S : ℕ)
  let z := n - (v.val - k)
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hsp : 0 < s := by linarith
  have hpcp : 0 < pc := (div_pos (by norm_num) hsp).trans_le hpc
  have hvc := (Finset.mem_filter.mp hv).2
  have hn := v.isLt
  have hz : z ≤ 33 * k := by dsimp [z]; omega
  have hfour : (4 : ℝ) ^ z ≤ s ^ 66 := by
    have h1 : (4 : ℝ) ^ z ≤ (4 : ℝ) ^ (33 * k) := pow_le_pow_right₀ (by norm_num) hz
    have h2 : (4 : ℝ) ^ (33 * k) ≤ ((3 : ℝ) ^ 2) ^ (33 * k) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have heq : ((3 : ℝ) ^ 2) ^ (33 * k) = ((3 : ℝ) ^ k) ^ 66 := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    exact h1.trans ((h2.trans_eq heq).trans (pow_le_pow_left₀ (by positivity) hD 66))
  have hinv : 1 / pc ≤ s := by
    have hh := (div_le_iff₀ hsp).mp hpc
    apply (div_le_iff₀ hpcp).mpr
    nlinarith
  have heq : 1 / coefficient n k pc v.val = 16 * (4 : ℝ) ^ z / pc := by
    unfold coefficient
    rw [if_neg hvc.2]
    change 1 / (pc * (1 / 4 : ℝ) ^ z / 16) = _
    rw [div_pow, one_pow]
    field_simp
  rw [heq]
  calc
    _ ≤ 16 * s ^ 66 / pc := div_le_div_of_nonneg_right (by nlinarith) hpcp.le
    _ = (16 * s ^ 66) * (1 / pc) := by ring
    _ ≤ (s * s ^ 66) * s := mul_le_mul
      (mul_le_mul_of_nonneg_right (by linarith : (16 : ℝ) ≤ s) (by positivity)) hinv (by positivity) (by positivity)
    _ = s ^ 68 := by ring

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hk : 1 ≤ k) (hks : k ≤ (S : ℕ))
    (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (pc : ℝ) (hpc : 1 / (S : ℕ) ≤ pc) :
    (∑ v ∈ levels n k, ∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) ≤
      ((S : ℕ) : ℝ) ^ 70 * ((n : ℝ) + 2 * (mu : ℕ) * Real.sqrt n) := by
  let s : ℝ := (S : ℕ)
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hpcp : 0 < pc := (by positivity : (0 : ℝ) < 1 / s).trans_le hpc
  have hpoint (v : Fin n) (hv : v ∈ levels n k) :
      (∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) ≤ s ^ 68 * ((n : ℝ) + 2 * (mu : ℕ) * Real.sqrt n) := by
    have hvc := (Finset.mem_filter.mp hv).2
    have hn : 0 < n := by have := v.isLt; omega
    have hz : 0 < n - (v.val - k) := by have := v.isLt; omega
    apply (ordinary_level n k mu pc hpcp v hvc.1).trans
    exact mul_le_mul (inverse S hS hk hks hD pc hpc v hv) (crude n _ mu hn hz)
      (by unfold ordinary; positivity) (by positivity)
  have hh := Finset.sum_le_sum hpoint
  rw [Finset.sum_const, nsmul_eq_mul] at hh
  have hc : ((levels n k).card : ℝ) ≤ s ^ 2 := by
    have hcard : ((levels n k).card : ℝ) ≤ 16 * ((k : ℝ) + 1) := by exact_mod_cast cardinality n k
    have hksR : (k : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hks
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hc (show 0 ≤ s ^ 68 * ((n : ℝ) + 2 * (mu : ℕ) * Real.sqrt n) by positivity)
  apply hh.trans (hmul.trans_eq ?_)
  ring

end
end Lax343628Proofs.NearLevelCosts

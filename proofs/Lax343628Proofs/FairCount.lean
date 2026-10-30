import Lax343628Proofs.EmpiricalSampling
import Lax343628Proofs.MaskCounts
import Mathlib.Data.Nat.Choose.Bounds

namespace Lax343628Proofs.FairCount

open Lax343628.Algorithm Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.EmpiricalSampling Lax343628Proofs.MaskCounts
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

def law (N : ℕ) := weightLaw N (1 / 2)

lemma mass (N : ℕ) (w : Fin (N + 1)) : (law N w).toReal = (N.choose w.val : ℝ) * (1 / 2 : ℝ) ^ N := by
  rw [law, weightLaw_apply, independentBits_count_real N w.val (1 / 2) (by norm_num)]
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ w.isLt)]

lemma atom (N : ℕ) (hN : 1 ≤ N) (w : Fin (N + 1)) : (law N w).toReal ≤ 1 / 2 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hc : ((M + 1).choose w.val : ℝ) ≤ (2 : ℝ) ^ M := by exact_mod_cast Nat.choose_succ_le_two_pow M w.val
  rw [mass]
  have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ (1 / 2 : ℝ) ^ (M + 1) by positivity)
  apply hh.trans_eq
  rw [pow_succ, ← mul_assoc, ← mul_pow]
  norm_num

lemma reflection (N : ℕ) : (law N).map (Fin.revPerm : Fin (N + 1) ≃ Fin (N + 1)) = law N := by
  apply PMF.ext
  intro w
  rw [FiniteProduct.map_equiv_apply]
  apply (ENNReal.toReal_eq_toReal_iff' ((law N).apply_ne_top _) ((law N).apply_ne_top _)).mp
  rw [mass, mass]
  simp only [Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_rev, Nat.add_sub_add_right]
  rw [Nat.choose_symm (Nat.le_of_lt_succ w.isLt)]

lemma second (N : ℕ) : mean (law N) (fun w ↦ ((w.val : ℝ) - (N : ℝ) / 2) ^ 2) = (N : ℝ) / 4 := by
  let f : Fin 2 → ℝ := fun b ↦ (b.val : ℝ) - 1 / 2
  have hf : mean (coin (1 / 2)) f = 0 := by rw [mean_coin _ (by norm_num)]; norm_num [f]
  have hf2 : mean (coin (1 / 2)) (fun b ↦ f b ^ 2) = 1 / 4 := by rw [mean_coin _ (by norm_num)]; norm_num [f]
  have hpoint (mask : BitString N) : sampleSum f mask = (ones mask : ℝ) - (N : ℝ) / 2 := by
    unfold sampleSum f ones
    rw [Nat.cast_sum, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [law, weightLaw, mean_map]
  simp_rw [← hpoint]
  change mean (samples (coin (1 / 2)) N) (fun mask ↦ sampleSum f mask ^ 2) = _
  rw [centered_sum_second _ f hf N, hf2]
  ring

end
end Lax343628Proofs.FairCount

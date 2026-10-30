import Lax343628Proofs.CountStatistics
import Lax343628Proofs.BaseSubsets

namespace Lax343628Proofs.UniformMutation

open Lax343628.Algorithm Lax343628Proofs.MaskCounts
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.CountStatistics Lax343628Proofs.FiniteProduct
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def weightAverage (N : ℕ) (f : BitString N → ℝ) (w : ℕ) : ℝ :=
  if hw : w ≤ N then mean (uniformWeight N ⟨w, by omega⟩) f else 0

lemma weightAverage_bound (N : ℕ) (f : BitString N → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ mask, |f mask| ≤ M) (w : ℕ) : |weightAverage N f w| ≤ M := by
  unfold weightAverage
  split_ifs
  · exact mean_abs_le _ f M hf
  · simpa using hM

lemma weightAverage_support {N k : ℕ} (f : BitString N → ℝ)
    (hf : ∀ mask, k < ones mask → f mask = 0) (w : ℕ) (hw : k < w) :
    weightAverage N f w = 0 := by
  unfold weightAverage
  split_ifs with hwN
  · unfold mean
    apply Finset.sum_eq_zero
    intro mask _
    rw [uniformWeight_apply]
    by_cases hmask : ones mask = w
    · rw [hf mask (by omega), mul_zero]
    · simp [hmask]
  · rfl

lemma independent_mean (N : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (f : BitString N → ℝ) :
    mean (independentBits N p) f = countMean N p (weightAverage N f) := by
  rw [← independentBits_mixture N p hp, mean_bind]
  unfold countMean
  apply congrArg (mean (weightLaw N p))
  funext w
  simp only [weightAverage, dif_pos (Nat.le_of_lt_succ w.isLt)]

def poissonPlacement (k N : ℕ) (f : BitString N → ℝ) : ℝ :=
  poissonMean k (weightAverage N f)

lemma mutation_poisson_placement {n N k : ℕ} (hn : 2 ≤ n) (hN : N ≤ n) (hk : k ≤ N)
    (f : BitString N → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ mask, |f mask| ≤ M)
    (hsupport : ∀ mask, k < ones mask → f mask = 0) :
    |mean (independentBits N (1 / n)) f - poissonPlacement k N f| ≤
      3 * M * ((k : ℝ) + 2) * (((n - N + k : ℕ) : ℝ) + 1) / n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (1 : ℝ) / n ∧ (1 : ℝ) / n ≤ 1 := ⟨by positivity, by
    exact (div_le_one (by linarith : (0 : ℝ) < n)).mpr (by linarith)⟩
  rw [independent_mean N (1 / n) hp]
  exact count_poisson_comparison hn hN hk (weightAverage N f) M hM
    (fun w _ ↦ weightAverage_bound N f M hM hf w) (weightAverage_support f hsupport)

def setEquiv (n : ℕ) : BitString n ≃ Finset (Fin n) where
  toFun := onesSet
  invFun := fromSet
  left_inv := fromSet_onesSet
  right_inv := onesSet_fromSet

lemma uniformWeight_sets (n : ℕ) (w : Fin (n + 1)) :
    (uniformWeight n w).map onesSet = BaseSubsets.subsetLaw (α := Fin n)
      ⟨w.val, by simpa using w.isLt⟩ := by
  ext S
  have hm : (uniformWeight n w).map onesSet S = uniformWeight n w (fromSet S) :=
    map_equiv_apply (uniformWeight n w) (setEquiv n) S
  rw [hm]
  have hr : (uniformWeight n w (fromSet S)).toReal =
      (BaseSubsets.subsetLaw (α := Fin n) (⟨w.val, by simpa using w.isLt⟩ : Fin (Fintype.card (Fin n) + 1)) S).toReal := by
    rw [uniformWeight_apply, ones_fromSet, BaseSubsets.subsetLaw_mass]
    split_ifs <;> simp
  rw [← ENNReal.ofReal_toReal ((uniformWeight n w).apply_ne_top _), hr,
    ENNReal.ofReal_toReal ((BaseSubsets.subsetLaw _).apply_ne_top _)]

end
end Lax343628Proofs.UniformMutation

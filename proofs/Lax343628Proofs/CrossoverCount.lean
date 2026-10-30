import Lax343628Proofs.CountStatistics
import Lax343628Proofs.FairInterval

namespace Lax343628Proofs.CrossoverCount

open Lax343628.Algorithm Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.Sampling Lax343628Proofs.PhysicalOffspring Lax343628Proofs.RegionGeometry
open Lax343628Proofs.OffspringRegions Lax343628Proofs.SuppressedRegions Lax343628Proofs.MaskCounts
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def common (x y : BitString n) := regionSize (fun _ ↦ 0) x y 1
def differing (x y : BitString n) := regionSize (fun _ ↦ 0) x y 2

lemma zero_mutation (n : ℕ) : independentBits n 0 = PMF.pure (fun _ ↦ 0) := by
  have hmass : independentBits n 0 (fun _ ↦ 0) = 1 := by
    rw [no_mutation_probability n 0 (by norm_num)]
    norm_num
  have hs := (PMF.apply_eq_one_iff _ _).mp hmass
  apply PMF.ext
  intro mask
  by_cases hm : mask = fun _ ↦ 0
  · subst mask
    rw [hmass, PMF.pure_apply_self]
  · have hz : independentBits n 0 mask = 0 := by
      by_contra hne
      have hh : mask ∈ (independentBits n 0).support := hne
      rw [hs, Set.mem_singleton_iff] at hh
      exact hm hh
    rw [hz, PMF.pure_apply_of_ne _ _ hm]

lemma no_mutation (x y : BitString n) :
    pairMutation x y 0 = (PMF.uniformOfFintype (BitString n)).map (crossover x y) := by
  simp only [pairMutation, zero_mutation, PMF.pure_bind, mutate_zero]
  rfl

lemma count_mean (x y : BitString n) (f : ℕ → ℝ) :
    mean (pairMutation x y 0) (fun z ↦ f (ones z)) =
      mean (FairCount.law (differing x y)) (fun w ↦ f (common x y + w.val)) := by
  unfold differing
  rw [regionSize_eq_fintype]
  let B : BitString n := fun _ ↦ 0
  let N : Fin 6 → ℕ := fun r ↦ Fintype.card {j // classify B x y j = r}
  have hones (z : BitString n) : ones z = (regionCounts B x y z 0).val +
      (regionCounts B x y z 1).val + (regionCounts B x y z 2).val := by
    have hh := inside_region_counts B x y z
    simpa only [insideCount, B, if_true, ones] using hh
  have hrate : rate 0 = suppressedRate 0 := by
    funext r
    fin_cases r <;> norm_num [rate, suppressedRate, Fin.ext_iff]
  have hh := congrArg (fun q ↦ mean q (fun c ↦ f ((c 0).val + (c 1).val + (c 2).val)))
    (region_count_law B x y 0 (by norm_num))
  rw [mean_map, hrate] at hh
  simp_rw [← hones] at hh
  apply hh.trans
  have hs := CountStatistics.six_count_mean N 0 (fun inside _ ↦ f inside)
  simp only [CountStatistics.countMean_const] at hs
  simpa only [CountStatistics.countMean, common, differing, regionSize_eq_fintype, N, B, FairCount.law] using hs

lemma parent_sum (x y : BitString n) : ones x + ones y = 2 * common x y + differing x y := by
  have hh := inside_parent_pair_sum (fun _ ↦ 0) x y
  simpa only [insideCount, if_true, common, differing, ones] using hh

lemma differing_set (x y : BitString n) :
    differing x y = (Finset.univ.filter (fun j ↦ x j ≠ y j)).card := by
  unfold differing regionSize regionSet
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, classify]
  have hpoint (a b : Fin 2) : region 0 a b = 2 ↔ a ≠ b := by
    fin_cases a <;> fin_cases b <;> norm_num [region, Fin.ext_iff]
  exact hpoint _ _

lemma differing_pos (x y : BitString n) (hxy : x ≠ y) : 1 ≤ differing x y := by
  rw [differing_set, Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
  have hn : ¬∀ j, x j = y j := fun hh ↦ hxy (funext hh)
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by simpa only [not_forall] using hn
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

lemma differing_le (x y : BitString n) : differing x y ≤ (n - ones x) + (n - ones y) := by
  rw [differing_set, ← card_zeros, ← card_zeros]
  apply le_trans _ (Finset.card_union_le (zeros x) (zeros y))
  apply Finset.card_le_card
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).2
  have hpoint (a b : Fin 2) : a ≠ b → a = 0 ∨ b = 0 := by
    fin_cases a <;> fin_cases b <;> norm_num
  exact Finset.mem_union.mpr (by simpa only [mem_zeros] using hpoint (x j) (y j) hj')

lemma strict (i : ℕ) (x y : BitString n) (hx : i ≤ ones x) (hy : i ≤ ones y) (hxy : x ≠ y) :
    1 / 4 ≤ mean (pairMutation x y 0) (fun z ↦ if i < ones z then 1 else 0) := by
  rw [count_mean x y (fun m ↦ if i < m then 1 else 0)]
  apply (FairMedian.strict_upper (differing x y) (differing_pos x y hxy)).trans
  unfold FairMedian.probability
  apply mean_mono
  intro w
  have hh := parent_sum x y
  simp only [Set.mem_ofPred_eq]
  split_ifs <;> norm_num; omega

end
end Lax343628Proofs.CrossoverCount

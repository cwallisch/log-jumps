import Lax343628Proofs.OffspringRegions
import Lax343628Proofs.PlateauDynamics

namespace Lax343628Proofs.RegionGeometry

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.Dynamics
open Lax343628Proofs.OffspringRegions Lax343628Proofs.PartitionCounts
open Lax343628Proofs.PlateauDynamics
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma region_inside (B x y : Fin 2) : (region B x y).val < 3 ↔ B = 0 := by
  fin_cases B <;> fin_cases x <;> fin_cases y <;> norm_num [region, Fin.ext_iff]

def insideCount {n : ℕ} (B child : BitString n) : ℕ :=
  ∑ j, if B j = 0 then (child j : ℕ) else 0

def outsideCount {n : ℕ} (B child : BitString n) : ℕ :=
  ∑ j, if B j = 1 then ((1 - child j : Fin 2) : ℕ) else 0

lemma inside_region_counts {n : ℕ} (B x y child : BitString n) :
    insideCount B child = (regionCounts B x y child 0).val +
      (regionCounts B x y child 1).val + (regionCounts B x y child 2).val := by
  have heq : insideCount B child = ∑ j : Fin n,
      (if (classify B x y j).val < 3 then 1 else 0) * (oriented B child j : ℕ) := by
    apply Finset.sum_congr rfl
    intro j _
    have hregion := region_inside (B j) (x j) (y j)
    by_cases hB : B j = 0
    · have hreg : (classify B x y j).val < 3 := hregion.mpr hB
      simp [hB, hreg, oriented, orientedBit]
    · have hreg : ¬(classify B x y j).val < 3 := fun h ↦ hB (hregion.mp h)
      simp [hB, hreg]
  rw [heq, sum_region_weights (classify B x y) (oriented B child)
    (fun r ↦ if r.val < 3 then 1 else 0)]
  simp only [regionCounts, counts_eq_rawCount]
  norm_num [Fin.sum_univ_succ, Fin.succ, Nat.add_assoc]
  rfl

lemma outside_region_counts {n : ℕ} (B x y child : BitString n) :
    outsideCount B child = (regionCounts B x y child 3).val +
      (regionCounts B x y child 4).val + (regionCounts B x y child 5).val := by
  have heq : outsideCount B child = ∑ j : Fin n,
      (if 3 ≤ (classify B x y j).val then 1 else 0) * (oriented B child j : ℕ) := by
    apply Finset.sum_congr rfl
    intro j _
    have hregion := region_inside (B j) (x j) (y j)
    by_cases hB : B j = 0
    · have hreg : ¬3 ≤ (classify B x y j).val := Nat.not_le.mpr (hregion.mpr hB)
      simp [hB, hreg]
    · have hB1 : B j = 1 := by have h := (B j).isLt; omega
      have hreg : 3 ≤ (classify B x y j).val := Nat.le_of_not_gt (fun h ↦ hB (hregion.mp h))
      simp [hB1, hreg, oriented, orientedBit]
  rw [heq, sum_region_weights (classify B x y) (oriented B child)
    (fun r ↦ if 3 ≤ r.val then 1 else 0)]
  simp only [regionCounts, counts_eq_rawCount]
  norm_num [Fin.sum_univ_succ, Fin.succ, Nat.add_assoc]
  rfl

lemma anchor_missing_eq {n : ℕ} (B child : BitString n) :
    (zeros B \ zeros child).card = insideCount B child := by
  have heq : zeros B \ zeros child = Finset.univ.filter (fun j ↦ B j = 0 ∧ child j = 1) := by
    ext j
    simp only [Finset.mem_sdiff, mem_zeros, Finset.mem_filter, Finset.mem_univ, true_and]
    have hc : child j = 0 ∨ child j = 1 := by have h := (child j).isLt; omega
    rcases hc with hc | hc <;> simp [hc]
  rw [heq, Finset.card_eq_sum_ones, Finset.sum_filter, insideCount]
  apply Finset.sum_congr rfl
  intro j _
  have hc : child j = 0 ∨ child j = 1 := by have h := (child j).isLt; omega
  rcases hc with hc | hc <;> by_cases hB : B j = 0 <;> simp [hc, hB]

lemma outside_zeros_eq {n : ℕ} (B child : BitString n) :
    (zeros child \ zeros B).card = outsideCount B child := by
  have heq : zeros child \ zeros B = Finset.univ.filter (fun j ↦ B j = 1 ∧ child j = 0) := by
    ext j
    simp only [Finset.mem_sdiff, mem_zeros, Finset.mem_filter, Finset.mem_univ, true_and]
    have hB : B j = 0 ∨ B j = 1 := by have h := (B j).isLt; omega
    rcases hB with hB | hB <;> simp [hB, and_comm]
  rw [heq, Finset.card_eq_sum_ones, Finset.sum_filter, outsideCount]
  apply Finset.sum_congr rfl
  intro j _
  have hc : child j = 0 ∨ child j = 1 := by have h := (child j).isLt; omega
  rcases hc with hc | hc <;> by_cases hB : B j = 1 <;> simp [hc, hB]

lemma zero_count_balance {n : ℕ} (B child : BitString n) :
    (zeros child).card + insideCount B child = (zeros B).card + outsideCount B child := by
  rw [← anchor_missing_eq, ← outside_zeros_eq]
  have h1 := Finset.card_sdiff_add_card (zeros B) (zeros child)
  have h2 := Finset.card_sdiff_add_card (zeros child) (zeros B)
  rw [Finset.union_comm (zeros child) (zeros B)] at h2
  omega

lemma plateau_iff_counts {n k : ℕ} (hk : k ≤ n) (B child : BitString n)
    (hB : onPlateau k B) : onPlateau k child ↔ insideCount B child = outsideCount B child := by
  have hBc : (zeros B).card = k := by
    rw [card_zeros]
    have hB' : ones B = n - k := hB
    rw [hB']
    omega
  have hbal := zero_count_balance B child
  rw [hBc, card_zeros] at hbal
  have hle := ones_le child
  unfold onPlateau
  omega

def regionSet {n : ℕ} (B x y : BitString n) (r : Fin 6) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ classify B x y j = r)

def regionSize {n : ℕ} (B x y : BitString n) (r : Fin 6) : ℕ := (regionSet B x y r).card

lemma regionSize_eq_fintype {n : ℕ} (B x y : BitString n) (r : Fin 6) :
    regionSize B x y r = Fintype.card {j // classify B x y j = r} := by
  rw [regionSize, regionSet, Fintype.card_subtype]

lemma regionSize_eq_sum {n : ℕ} (B x y : BitString n) (r : Fin 6) :
    regionSize B x y r = ∑ j : Fin n, if classify B x y j = r then 1 else 0 := by
  rw [regionSize, regionSet, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma inside_parent_pair_sum {n : ℕ} (B x y : BitString n) :
    insideCount B x + insideCount B y = 2 * regionSize B x y 1 + regionSize B x y 2 := by
  rw [insideCount, insideCount, regionSize_eq_sum, regionSize_eq_sum, ← Finset.sum_add_distrib,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hpoint (b a c : Fin 2) :
      (if b = 0 then (a : ℕ) else 0) + (if b = 0 then (c : ℕ) else 0) =
      2 * (if region b a c = 1 then 1 else 0) + (if region b a c = 2 then 1 else 0) := by
    fin_cases b <;> fin_cases a <;> fin_cases c <;> norm_num [region, Fin.ext_iff]
  exact hpoint (B j) (x j) (y j)

lemma outside_parent_pair_sum {n : ℕ} (B x y : BitString n) :
    outsideCount B x + outsideCount B y = 2 * regionSize B x y 3 + regionSize B x y 5 := by
  rw [outsideCount, outsideCount, regionSize_eq_sum, regionSize_eq_sum, ← Finset.sum_add_distrib,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hpoint (b a c : Fin 2) :
      (if b = 1 then ((1 - a : Fin 2) : ℕ) else 0) +
        (if b = 1 then ((1 - c : Fin 2) : ℕ) else 0) =
      2 * (if region b a c = 3 then 1 else 0) + (if region b a c = 5 then 1 else 0) := by
    fin_cases b <;> fin_cases a <;> fin_cases c <;> norm_num [region, Fin.ext_iff]
  exact hpoint (B j) (x j) (y j)

lemma region_one_set {n : ℕ} (B x y : BitString n) :
    regionSet B x y 1 = zeros B \ (zeros x ∪ zeros y) := by
  ext j
  simp only [regionSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    mem_zeros, Finset.mem_union]
  have hpoint (b a c : Fin 2) : region b a c = 1 ↔ b = 0 ∧ ¬(a = 0 ∨ c = 0) := by
    fin_cases b <;> fin_cases a <;> fin_cases c <;> norm_num [region, Fin.ext_iff]
  exact hpoint (B j) (x j) (y j)

lemma region_three_set {n : ℕ} (B x y : BitString n) :
    regionSet B x y 3 = (zeros x ∩ zeros y) \ zeros B := by
  ext j
  simp only [regionSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    mem_zeros, Finset.mem_inter]
  have hpoint (b a c : Fin 2) : region b a c = 3 ↔ (a = 0 ∧ c = 0) ∧ b ≠ 0 := by
    fin_cases b <;> fin_cases a <;> fin_cases c <;> norm_num [region, Fin.ext_iff]
  exact hpoint (B j) (x j) (y j)

lemma region_four_set {n : ℕ} (B x y : BitString n) :
    regionSet B x y 4 = (zeros B ∪ zeros x ∪ zeros y)ᶜ := by
  ext j
  simp only [regionSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
    mem_zeros, Finset.mem_union]
  have hpoint (b a c : Fin 2) : region b a c = 4 ↔ ¬(b = 0 ∨ a = 0 ∨ c = 0) := by
    fin_cases b <;> fin_cases a <;> fin_cases c <;> norm_num [region, Fin.ext_iff]
  simpa only [classify, or_assoc] using hpoint (B j) (x j) (y j)

lemma fresh_region_deficit {n k : ℕ} (B x y : BitString n)
    (hB : (zeros B).card = k) (hx : (zeros x).card = k) (hy : (zeros y).card = k) :
    n - regionSize B x y 4 ≤ 3 * k := by
  have hcard := Finset.card_compl (zeros B ∪ zeros x ∪ zeros y)
  rw [Fintype.card_fin] at hcard
  have hle : (zeros B ∪ zeros x ∪ zeros y).card ≤ n := by
    simpa using Finset.card_le_univ (zeros B ∪ zeros x ∪ zeros y)
  have hunion : (zeros B ∪ zeros x ∪ zeros y).card ≤ 3 * k := by
    have h1 := Finset.card_union_le (zeros B) (zeros x)
    have h2 := Finset.card_union_le (zeros B ∪ zeros x) (zeros y)
    rw [hB, hx] at h1
    rw [hy] at h2
    omega
  rw [regionSize, region_four_set, hcard]
  omega

lemma differing_inside_size {n : ℕ} (B x y : BitString n) :
    regionSize B x y 2 = insideCount B x + insideCount B y - 2 * regionSize B x y 1 := by
  have h := inside_parent_pair_sum B x y
  omega

lemma differing_outside_size {n : ℕ} (B x y : BitString n)
    (hx : (zeros x).card = (zeros B).card) (hy : (zeros y).card = (zeros B).card) :
    regionSize B x y 5 = insideCount B x + insideCount B y - 2 * regionSize B x y 3 := by
  have h1 := zero_count_balance B x
  have h2 := zero_count_balance B y
  rw [hx] at h1
  rw [hy] at h2
  have h := outside_parent_pair_sum B x y
  omega

lemma regionSet_disjoint {n : ℕ} (B x y : BitString n) {r s : Fin 6} (hrs : r ≠ s) :
    Disjoint (regionSet B x y r) (regionSet B x y s) := by
  apply Finset.disjoint_left.mpr
  intro j hjr hjs
  simp only [regionSet, Finset.mem_filter, Finset.mem_univ, true_and] at hjr hjs
  exact hrs (hjr.symm.trans hjs)

lemma common_zero_regions {n : ℕ} (B x y : BitString n) :
    regionSet B x y 0 ∪ regionSet B x y 3 = zeros x ∩ zeros y := by
  ext j
  simp only [Finset.mem_union, regionSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter, mem_zeros]
  have hpoint (b a c : Fin 2) : region b a c = 0 ∨ region b a c = 3 ↔ a = 0 ∧ c = 0 := by
    fin_cases b <;> fin_cases a <;> fin_cases c <;> norm_num [region, Fin.ext_iff]
  exact hpoint (B j) (x j) (y j)

lemma forbidden_region_size {n k : ℕ} (B x y : BitString n)
    (hB : (zeros B).card = k) (hx : (zeros x).card = k) :
    regionSize B x y 0 + regionSize B x y 1 + regionSize B x y 3 ≤ 2 * k := by
  have hcommon : regionSize B x y 0 + regionSize B x y 3 ≤ k := by
    rw [regionSize, regionSize, ← Finset.card_union_of_disjoint
      (regionSet_disjoint B x y (by norm_num [Fin.ext_iff] : (0 : Fin 6) ≠ 3)), common_zero_regions]
    have h := Finset.card_le_card (Finset.inter_subset_left : zeros x ∩ zeros y ⊆ zeros x)
    simpa only [hx] using h
  have hmissing : regionSize B x y 1 ≤ k := by
    rw [regionSize, region_one_set]
    have h := Finset.card_le_card (Finset.sdiff_subset : zeros B \ (zeros x ∪ zeros y) ⊆ zeros B)
    simpa only [hB] using h
  omega

lemma insideCount_le {n : ℕ} (B child : BitString n) : insideCount B child ≤ (zeros B).card := by
  rw [← anchor_missing_eq]
  exact Finset.card_le_card Finset.sdiff_subset

lemma variable_inside_size {n : ℕ} (B x y : BitString n) :
    regionSize B x y 1 + regionSize B x y 2 ≤ (zeros B).card := by
  have hdis : Disjoint (regionSet B x y 1) (regionSet B x y 2) :=
    regionSet_disjoint B x y (by norm_num [Fin.ext_iff])
  rw [regionSize, regionSize, ← Finset.card_union_of_disjoint hdis]
  apply Finset.card_le_card
  intro j hj
  have hj' : classify B x y j = 1 ∨ classify B x y j = 2 := by
    simpa only [Finset.mem_union, regionSet, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  rw [mem_zeros]
  apply (region_inside (B j) (x j) (y j)).mp
  rcases hj' with hj' | hj' <;> change (classify B x y j).val < 3 <;> rw [hj'] <;> decide

end
end Lax343628Proofs.RegionGeometry

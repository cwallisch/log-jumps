import Lax343628Proofs.ActualBirthKernels

namespace Lax343628Proofs.AnchorMutation

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.BitProduct
open Lax343628Proofs.PartitionCounts Lax343628Proofs.FiniteProduct
open Lax343628Proofs.RegionGeometry Lax343628Proofs.MaskCounts
open Lax343628Proofs.CountStatistics Lax343628Proofs.FiniteComparison
open Lax343628Proofs.FiniteDrift Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.PlateauApproximation Lax343628Proofs.Genotypes
open Lax343628Proofs.ActualBirthKernels Lax343628Proofs.Weights
open Lax343628Proofs.PlateauDynamics Lax343628Proofs.PlateauKernelApproximation
open Lax343628Proofs.ElementaryBounds
open Lax343628Proofs.IdealCountKernel
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def side {n : ℕ} (B : BitString n) (j : Fin n) : Fin 2 := if B j = 0 then 0 else 1

lemma side_size_zero {n : ℕ} (B : BitString n) :
    Fintype.card {j // side B j = 0} = (zeros B).card := by
  rw [Fintype.card_subtype]
  congr 1
  ext j
  simp [side, mem_zeros]

lemma side_size_one {n : ℕ} (B : BitString n) :
    Fintype.card {j // side B j = 1} = n - (zeros B).card := by
  rw [Fintype.card_subtype]
  have heq : Finset.univ.filter (fun j ↦ side B j = 1) = (zeros B)ᶜ := by
    ext j
    simp [side, mem_zeros]
  rw [heq, Finset.card_compl, Fintype.card_fin]

lemma mutation_inside_count {n : ℕ} (B mask : BitString n) :
    insideCount B (mutate B mask) = (counts (side B) mask 0).val := by
  rw [counts_eq_rawCount, rawCount, Finset.sum_filter]
  unfold insideCount
  apply Finset.sum_congr rfl
  intro j _
  have hpoint (b m : Fin 2) :
      (if b = 0 then ((if m = 1 then 1 - b else b : Fin 2) : ℕ) else 0) =
        if (if b = 0 then (0 : Fin 2) else 1) = 0 then (m : ℕ) else 0 := by
    fin_cases b <;> fin_cases m <;> norm_num
  exact hpoint (B j) (mask j)

lemma mutation_outside_count {n : ℕ} (B mask : BitString n) :
    outsideCount B (mutate B mask) = (counts (side B) mask 1).val := by
  rw [counts_eq_rawCount, rawCount, Finset.sum_filter]
  unfold outsideCount
  apply Finset.sum_congr rfl
  intro j _
  have hpoint (b m : Fin 2) :
      (if b = 1 then ((1 - (if m = 1 then 1 - b else b) : Fin 2) : ℕ) else 0) =
        if (if b = 0 then (0 : Fin 2) else 1) = 1 then (m : ℕ) else 0 := by
    fin_cases b <;> fin_cases m <;> norm_num
  exact hpoint (B j) (mask j)

lemma two_count_mean (N : Fin 2 → ℕ) (p : ℝ) (f : ℕ → ℕ → ℝ) :
    mean (distribution (fun r ↦ weightLaw (N r) p))
      (fun c ↦ f (c 0).val (c 1).val) =
      countMean (N 0) p (fun a ↦ countMean (N 1) p (fun b ↦ f a b)) := by
  unfold countMean
  simp_rw [mean_distribution_cons]
  simp only [mean_distribution_empty]
  rfl

lemma mutation_statistic_mean {n : ℕ} (B : BitString n) (p : ℝ) (f : ℕ → ℕ → ℝ) :
    mean (pairMutation B B p) (fun child ↦ f (insideCount B child) (outsideCount B child)) =
      countMean (zeros B).card p (fun a ↦ countMean (n - (zeros B).card) p (fun b ↦ f a b)) := by
  rw [pairMutation_self, mean_map]
  have h := partition_counts (side B) (fun _ ↦ p)
  have hbits : product (Fin n) (fun _ ↦ coin p) = independentBits n p := by
    rw [product_coin, bits_fin]
  rw [hbits] at h
  have hm := mean_map (independentBits n p) (counts (side B))
    (fun c ↦ f (c 0).val (c 1).val)
  rw [h] at hm
  simp_rw [← mutation_inside_count, ← mutation_outside_count] at hm
  rw [← hm, two_count_mean, side_size_zero, side_size_one]

lemma countMean_single_lower (N w : ℕ) (hw : w ≤ N) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) (f : ℕ → ℝ) (hf : ∀ a ≤ N, 0 ≤ f a) :
    (N.choose w : ℝ) * p ^ w * (1 - p) ^ (N - w) * f w ≤ countMean N p f := by
  rw [countMean_formula N p hp]
  apply Finset.single_le_sum (s := Finset.range (N + 1))
    (f := fun a ↦ (N.choose a : ℝ) * p ^ a * (1 - p) ^ (N - a) * f a)
    _ (Finset.mem_range.mpr (by omega : w < N + 1))
  intro a ha
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hp.1 _))
    (pow_nonneg (sub_nonneg.mpr hp.2) _)) (hf a (by have h := Finset.mem_range.mp ha; omega))

lemma anchor_acceptance_formula {n k : ℕ} (B : Genotype n k) (p : ℝ) (ψ : ℕ → ℝ) :
    mean (pairMutation (toString B) (toString B) p)
      (fun child ↦ if onPlateau k child then ψ (insideCount (toString B) child) else 0) =
      countMean k p (fun a ↦ countMean (n - k) p (fun b ↦ balanced ψ a b)) := by
  have hkn : k ≤ n := by
    simpa only [B.property, Fintype.card_fin] using Finset.card_le_univ B.val
  have hplateau := plateau_of_zero_card hkn (toString B) (by simpa using B.property)
  have h := mutation_statistic_mean (toString B) p (balanced ψ)
  rw [zeros_toString, B.property] at h
  rw [← h]
  congr 1
  funext child
  rw [plateau_iff_counts hkn (toString B) child hplateau]
  by_cases hc : insideCount (toString B) child = outsideCount (toString B) child <;>
    simp [balanced, hc]

lemma weightedBirth_self_lower {n k : ℕ} (hk : 1 ≤ k) (hlarge : 2 * k ≤ n)
    (hn : 2 ≤ n) (B : Genotype n k) :
    (k : ℝ) * (n - k : ℕ) * (1 / (n : ℝ)) ^ 2 *
      (1 - 1 / (n : ℝ)) ^ (n - 2) ≤ weightedBirth B B B := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (1 : ℝ) / n ∧ (1 : ℝ) / n ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by linarith : (0 : ℝ) < n)).mpr
      linarith
  have hnk : 1 ≤ n - k := by omega
  unfold weightedBirth acceptedWeight
  rw [anchor_acceptance_formula]
  let q : ℝ := 1 - 1 / (n : ℝ)
  have hq : 0 ≤ q := sub_nonneg.mpr hp.2
  have hnonneg (a b : ℕ) : 0 ≤ balanced weight a b := by
    unfold balanced
    split_ifs
    · exact weight_nonneg a
    · exact le_rfl
  have hinner := countMean_single_lower (n - k) 1 hnk (1 / n) hp
    (balanced weight 1) (fun b _ ↦ hnonneg 1 b)
  simp only [Nat.choose_one_right, pow_one, balanced, ite_true, weight_one, mul_one] at hinner
  have houter := countMean_single_lower k 1 hk (1 / n) hp
    (fun a ↦ countMean (n - k) (1 / n) (balanced weight a))
    (fun a _ ↦ countMean_nonneg _ _ _ (fun b _ ↦ hnonneg a b))
  simp only [Nat.choose_one_right, pow_one] at houter
  have hmul := mul_le_mul_of_nonneg_left hinner
    (show 0 ≤ (k : ℝ) * (1 / (n : ℝ)) * q ^ (k - 1) by positivity)
  have hexp : (k - 1) + (n - k - 1) = n - 2 := by omega
  have heq : ((k : ℝ) * (1 / (n : ℝ)) * q ^ (k - 1)) *
      ((n - k : ℕ) * (1 / (n : ℝ)) * q ^ (n - k - 1)) =
      (k : ℝ) * (n - k : ℕ) * (1 / (n : ℝ)) ^ 2 * q ^ (n - 2) := by
    calc
      _ = (k : ℝ) * (n - k : ℕ) * (1 / (n : ℝ)) ^ 2 *
          (q ^ (k - 1) * q ^ (n - k - 1)) := by ring
      _ = _ := by rw [← pow_add, hexp]
  rw [heq] at hmul
  exact hmul.trans houter

lemma weightedBirth_self_gain {n k : ℕ} (hk : 1 ≤ k) (hlarge : 2 * k ≤ n)
    (hn : 2 ≤ n) (B : Genotype n k) : (k : ℝ) / (16 * n) ≤ weightedBirth B B B := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkn : k ≤ n := by omega
  have hlargeR : 2 * (k : ℝ) ≤ n := by exact_mod_cast hlarge
  have hnpos : (0 : ℝ) < n := by linarith
  have hp : 0 ≤ 1 / (n : ℝ) := by positivity
  have hp1 : 1 / (n : ℝ) ≤ 1 := by
    apply (div_le_one hnpos).mpr
    linarith
  have hpow : (1 / 8 : ℝ) ≤ (1 - 1 / (n : ℝ)) ^ (n - 2) :=
    (no_mutation_lower n hn).trans (pow_le_pow_of_le_one (sub_nonneg.mpr hp1)
      (by linarith : 1 - 1 / (n : ℝ) ≤ 1) (Nat.sub_le n 2))
  have hnum : (k : ℝ) * n ≤ 2 * k * (n - k : ℕ) := by
    rw [Nat.cast_sub hkn]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by positivity) (sub_nonneg.mpr hlargeR)]
  have hfront : (k : ℝ) / (2 * n) ≤ (k : ℝ) * (n - k : ℕ) / (n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)
      (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hnum hnpos.le]
  have hmul := mul_le_mul hfront hpow (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by positivity : (0 : ℝ) ≤ (k : ℝ) * (n - k : ℕ) / (n : ℝ) ^ 2)
  have hlow : (k : ℝ) / (16 * n) ≤
      (k : ℝ) * (n - k : ℕ) * (1 / (n : ℝ)) ^ 2 *
        (1 - 1 / (n : ℝ)) ^ (n - 2) := by
    convert hmul using 1 <;> first | rfl | ring
  exact hlow.trans (weightedBirth_self_lower hk hlarge hn B)

lemma countMean_zero_pick (N : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (c : ℝ) :
    countMean N p (fun w ↦ if w = 0 then c else 0) = (1 - p) ^ N * c := by
  rw [countMean_formula N p hp, Finset.sum_eq_single 0]
  · simp
  · intro w _ hw
    simp [hw]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.succ_pos N)))

lemma cloneBirth_self {n k : ℕ} (hn : 2 ≤ n) (B : Genotype n k) :
    cloneBirth B B B = (1 - 1 / (n : ℝ)) ^ n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (1 : ℝ) / n ∧ (1 : ℝ) / n ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by linarith : (0 : ℝ) < n)).mpr
      linarith
  have hkn : k ≤ n := by
    simpa only [B.property, Fintype.card_fin] using Finset.card_le_univ B.val
  unfold cloneBirth acceptedClone
  rw [anchor_acceptance_formula]
  have hbalanced : ∀ a b, balanced cloneWeight a b = if a = 0 then (if b = 0 then 1 else 0) else 0 := by
    intro a b
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
      simp [balanced, cloneWeight, ha, hb, eq_comm]
  simp_rw [hbalanced]
  have hinner : ∀ a, countMean (n - k) (1 / (n : ℝ))
      (fun b ↦ if a = 0 then (if b = 0 then 1 else 0) else 0) =
      if a = 0 then (1 - 1 / (n : ℝ)) ^ (n - k) else 0 := by
    intro a
    by_cases ha : a = 0
    · simp only [if_pos ha, countMean_zero_pick _ _ hp, mul_one]
    · simp only [if_neg ha, countMean_const]
  simp_rw [hinner]
  rw [countMean_zero_pick _ _ hp, ← pow_add, Nat.add_sub_of_le hkn]

lemma acceptedClone_indicator {n k : ℕ} (B : Genotype n k) (child : BitString n) :
    acceptedClone B child = if child = toString B then 1 else 0 := by
  have hkn : k ≤ n := by
    simpa only [B.property, Fintype.card_fin] using Finset.card_le_univ B.val
  by_cases hchild : child = toString B
  · subst child
    have hp := plateau_of_zero_card hkn (toString B) (by simpa using B.property)
    simp [acceptedClone, hp, insideCount_self, cloneWeight]
  · rw [if_neg hchild]
    unfold acceptedClone
    by_cases hp : onPlateau k child
    · have hz : (zeros child).card = k := by
        rw [card_zeros]
        have hp' : ones child = n - k := hp
        rw [hp']
        omega
      let z : Genotype n k := ofString child hz
      have hzB : z ≠ B := by
        intro heq
        have h := congrArg toString heq
        have hzc : toString z = child := toString_ofString child hz
        rw [hzc] at h
        exact hchild h
      have hd : distance B z = insideCount (toString B) child := by
        change (B.val \ zeros child).card = _
        rw [← zeros_toString B, anchor_missing_eq]
      have hpos := distance_pos B z hzB
      rw [hd] at hpos
      simp [hp, cloneWeight, Nat.ne_of_gt hpos]
    · simp only [if_neg hp]

lemma cloneBirth_mass {n k : ℕ} (B x y : Genotype n k) :
    cloneBirth B x y = (pairMutation (toString x) (toString y) (1 / n) (toString B)).toReal := by
  unfold cloneBirth
  have hf : acceptedClone B = (fun child ↦ if child = toString B then 1 else 0) :=
    funext (acceptedClone_indicator B)
  rw [hf]
  have h := mean_indicator (pairMutation (toString x) (toString y) (1 / n)) {toString B}
  simpa only [Set.mem_singleton_iff, PMF.toOuterMeasure_apply_singleton] using h

lemma mutation_two_sites {n : ℕ} (x target : BitString n) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) (a b : Fin n) (hab : a ≠ b)
    (ha : x a ≠ target a) (hb : x b ≠ target b) :
    pairMutation x x p target ≤ ENNReal.ofReal p ^ 2 := by
  rw [pairMutation_apply x x target p hp]
  have hle : ∀ j, siteProbability (x j) (x j) (target j) p ≤
      if j ∈ ({a, b} : Finset (Fin n)) then ENNReal.ofReal p else 1 := by
    intro j
    by_cases hj : j ∈ ({a, b} : Finset (Fin n))
    · rw [if_pos hj]
      have hj' : j = a ∨ j = b := by simpa using hj
      rcases hj' with rfl | rfl <;>
        simp only [siteProbability, ite_true, if_neg (Ne.symm ha), if_neg (Ne.symm hb), le_refl]
    · rw [if_neg hj, ← siteLaw_apply (x j) (x j) (target j) p hp]
      exact (siteLaw (x j) (x j) p).coe_le_one _
  calc
    _ ≤ ∏ j : Fin n, if j ∈ ({a, b} : Finset (Fin n)) then ENNReal.ofReal p else 1 :=
      Finset.prod_le_prod' (fun j _ ↦ hle j)
    _ = _ := by
      rw [Finset.prod_ite]
      have heq : Finset.univ.filter (fun j : Fin n ↦ j ∈ ({a, b} : Finset (Fin n))) = {a, b} := by
        ext j
        simp
      simp only [heq, Finset.prod_const_one, mul_one, Finset.prod_const, Finset.card_pair hab]

lemma cloneBirth_changed_upper {n k : ℕ} (hn : 2 ≤ n) (B x : Genotype n k) (hx : x ≠ B) :
    cloneBirth B x x ≤ (1 / (n : ℝ)) ^ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (1 : ℝ) / n ∧ (1 : ℝ) / n ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by linarith : (0 : ℝ) < n)).mpr
      linarith
  have hXB : 0 < (x.val \ B.val).card := by
    exact distance_pos x B (Ne.symm hx)
  have hBX : 0 < (B.val \ x.val).card := by
    exact distance_pos B x hx
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hXB
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hBX
  have ha' := Finset.mem_sdiff.mp ha
  have hb' := Finset.mem_sdiff.mp hb
  have hab : a ≠ b := by intro h; subst b; exact hb'.2 ha'.1
  have hxa : toString x a ≠ toString B a := by simp [Genotypes.toString, ha'.1, ha'.2]
  have hxb : toString x b ≠ toString B b := by simp [Genotypes.toString, hb'.1, hb'.2]
  have h := mutation_two_sites (toString x) (toString B) (1 / n) hp a b hab hxa hxb
  rw [cloneBirth_mass]
  have hR := ENNReal.toReal_mono (by simp : ENNReal.ofReal (1 / (n : ℝ)) ^ 2 ≠ ∞) h
  simpa only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hp.1] using hR

lemma weightedBirth_unchanged_lower {n k : ℕ} (hn : 2 ≤ n) (B x : Genotype n k) :
    (1 - 1 / (n : ℝ)) ^ n * weight (distance B x) ≤ weightedBirth B x x := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (1 : ℝ) / n ∧ (1 : ℝ) / n ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by linarith : (0 : ℝ) < n)).mpr
      linarith
  unfold weightedBirth
  rw [pairMutation_self, mean_map]
  have h := mean_single_lower (independentBits n (1 / (n : ℝ)))
    (fun mask ↦ acceptedWeight B (mutate (toString x) mask))
    (fun mask ↦ acceptedWeight_nonneg B _) (fun _ ↦ 0)
  rw [no_mutation_probability _ _ hp, mutate_zero, acceptedWeight_toString,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)] at h
  exact h

lemma weightedBirth_self_with_seed {n k : ℕ} (hk : 1 ≤ k) (hlarge : 2 * k ≤ n)
    (hn : 2 ≤ n) (B x : Genotype n k) :
    (1 - 1 / (n : ℝ)) ^ n * weight (distance B x) +
      (if x = B then (k : ℝ) / (16 * n) else 0) ≤ weightedBirth B x x := by
  by_cases hx : x = B
  · subst x
    simpa only [distance_self, weight_zero, mul_zero, ite_true, zero_add] using
      weightedBirth_self_gain hk hlarge hn B
  · rw [if_neg hx, add_zero]
    exact weightedBirth_unchanged_lower hn B x

end
end Lax343628Proofs.AnchorMutation

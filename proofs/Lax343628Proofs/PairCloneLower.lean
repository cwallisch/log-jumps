import Lax343628Proofs.SeedPairs

namespace Lax343628Proofs.PairCloneLower

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.FiniteDrift
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

lemma site_lower (x y z : Fin 2) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (if x = y then (1 : ℝ) else 1 / 2) * (siteProbability x x z p).toReal ≤ (siteProbability x y z p).toReal := by
  by_cases hxy : x = y
  · subst y
    simp only [if_true, one_mul, le_refl]
  · have hu := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) ((siteLaw x x p).coe_le_one z)
    rw [siteLaw_apply x x z p hp] at hu
    norm_num only [ENNReal.toReal_one] at hu
    simp only [if_neg hxy]
    have heq : siteProbability x y z p = (2 : ℝ≥0∞)⁻¹ := by
      simp only [siteProbability, if_neg hxy]
    rw [heq]
    norm_num only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    linarith

lemma differing_card (x y : BitString n) (hx : (zeros x).card = k) (hy : (zeros y).card = k) :
    (Finset.univ.filter (fun j ↦ x j ≠ y j)).card ≤ 2 * k := by
  have hsub : Finset.univ.filter (fun j ↦ x j ≠ y j) ⊆ zeros x ∪ zeros y := by
    intro j hj
    have hne := (Finset.mem_filter.mp hj).2
    by_cases hxj : x j = 0
    · exact Finset.mem_union_left _ ((mem_zeros x j).mpr hxj)
    · have hyj : y j = 0 := by have hhx := (x j).isLt; have hhy := (y j).isLt; omega
      exact Finset.mem_union_right _ ((mem_zeros y j).mpr hyj)
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le (zeros x) (zeros y))
  rw [hx, hy] at hh
  omega

lemma point_lower_of_card (x y z : BitString n)
    (hcard : (Finset.univ.filter (fun j ↦ x j ≠ y j)).card ≤ 2 * k) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (1 / 4 : ℝ) ^ k * (pairMutation x x p z).toReal ≤ (pairMutation x y p z).toReal := by
  have hsite := Finset.prod_le_prod
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦ show 0 ≤
      (if x j = y j then (1 : ℝ) else 1 / 2) * (siteProbability (x j) (x j) (z j) p).toReal by
        apply mul_nonneg
        · split_ifs <;> norm_num
        · exact ENNReal.toReal_nonneg)
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦ site_lower (x j) (y j) (z j) p hp)
  rw [Finset.prod_mul_distrib] at hsite
  have hprod : (∏ j : Fin n, if x j = y j then (1 : ℝ) else 1 / 2) =
      (1 / 2 : ℝ) ^ (Finset.univ.filter (fun j ↦ x j ≠ y j)).card := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [hprod] at hsite
  have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    hcard
  have heq : (1 / 2 : ℝ) ^ (2 * k) = (1 / 4 : ℝ) ^ k := by rw [pow_mul]; norm_num
  rw [heq] at hpow
  have hm := mul_le_mul_of_nonneg_right hpow (show 0 ≤ ∏ j : Fin n, (siteProbability (x j) (x j) (z j) p).toReal by positivity)
  rw [pairMutation_apply x x z p hp, pairMutation_apply x y z p hp, ENNReal.toReal_prod, ENNReal.toReal_prod]
  exact hm.trans hsite

lemma point_lower (x y z : BitString n) (hx : (zeros x).card = k) (hy : (zeros y).card = k)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (1 / 4 : ℝ) ^ k * (pairMutation x x p z).toReal ≤ (pairMutation x y p z).toReal :=
  point_lower_of_card x y z (differing_card x y hx hy) p hp

lemma mean_lower_of_card (x y : BitString n)
    (hcard : (Finset.univ.filter (fun j ↦ x j ≠ y j)).card ≤ 2 * k)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (f : BitString n → ℝ) (hf : ∀ z, 0 ≤ f z) :
    (1 / 4 : ℝ) ^ k * mean (pairMutation x x p) f ≤ mean (pairMutation x y p) f := by
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have hh := mul_le_mul_of_nonneg_right (point_lower_of_card x y z hcard p hp) (hf z)
  convert hh using 1; first | rfl | ring

lemma mean_lower (x y : BitString n) (hx : (zeros x).card = k) (hy : (zeros y).card = k)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (f : BitString n → ℝ) (hf : ∀ z, 0 ≤ f z) :
    (1 / 4 : ℝ) ^ k * mean (pairMutation x x p) f ≤ mean (pairMutation x y p) f := by
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have hh := mul_le_mul_of_nonneg_right (point_lower x y z hx hy p hp) (hf z)
  convert hh using 1; first | rfl | ring

end
end Lax343628Proofs.PairCloneLower

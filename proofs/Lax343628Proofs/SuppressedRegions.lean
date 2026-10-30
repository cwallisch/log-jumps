import Lax343628Proofs.RegionGeometry
import Lax343628Proofs.MutationCoupling

namespace Lax343628Proofs.SuppressedRegions

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.BitProduct
open Lax343628Proofs.OffspringRegions Lax343628Proofs.RegionGeometry
open Lax343628Proofs.MutationCoupling Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.FiniteDrift Lax343628Proofs.PartitionCounts
open Lax343628Proofs.FiniteProduct Lax343628Proofs.MaskCounts
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def forbidden {n : ℕ} (B x y : BitString n) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ classify B x y j = 0 ∨
    classify B x y j = 1 ∨ classify B x y j = 3)

lemma forbidden_common {n : ℕ} (B x y : BitString n) :
    ∀ j ∈ forbidden B x y, x j = y j := by
  intro j hj
  have hj' : region (B j) (x j) (y j) = 0 ∨ region (B j) (x j) (y j) = 1 ∨
      region (B j) (x j) (y j) = 3 := (Finset.mem_filter.mp hj).2
  have hpoint (b a c : Fin 2) :
      region b a c = 0 ∨ region b a c = 1 ∨ region b a c = 3 → a = c := by
    fin_cases b <;> fin_cases a <;> fin_cases c <;> norm_num [region, Fin.ext_iff]
  exact hpoint _ _ _ hj'

lemma forbidden_card {n k : ℕ} (B x y : BitString n)
    (hB : (zeros B).card = k) (hx : (zeros x).card = k) :
    (forbidden B x y).card ≤ 2 * k := by
  have heq : forbidden B x y = regionSet B x y 0 ∪ regionSet B x y 1 ∪
      regionSet B x y 3 := by ext j; simp [forbidden, regionSet]
  rw [heq]
  have h1 := Finset.card_union_le (regionSet B x y 0) (regionSet B x y 1)
  have h2 := Finset.card_union_le (regionSet B x y 0 ∪ regionSet B x y 1)
    (regionSet B x y 3)
  have hb := forbidden_region_size B x y hB hx
  change (regionSet B x y 0).card + (regionSet B x y 1).card +
    (regionSet B x y 3).card ≤ 2 * k at hb
  omega

def suppressedRate (p : ℝ) (r : Fin 6) : ℝ :=
  if r = 0 then 0 else if r = 1 ∨ r = 3 then 1 else rate p r

lemma coin_zero_rate : coin 0 = PMF.pure 0 := by
  ext b
  fin_cases b <;> norm_num [coin, PMF.pure_apply]

lemma coin_one_rate : coin 1 = PMF.pure 1 := by
  ext b
  fin_cases b <;> norm_num [coin, PMF.pure_apply]

lemma suppressed_site_oriented (B x y : Fin 2) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (if region B x y = 0 ∨ region B x y = 1 ∨ region B x y = 3
      then PMF.pure x else siteLaw x y p).map (orientedBit B) =
        coin (suppressedRate p (region B x y)) := by
  have hs := siteLaw_oriented B x y p hp
  fin_cases B <;> fin_cases x <;> fin_cases y <;>
    norm_num [region, Fin.ext_iff, suppressedRate, rate] at hs ⊢ <;>
    first
    | exact hs
    | simp [PMF.pure_map, orientedBit, coin_zero_rate, coin_one_rate]

lemma suppressed_oriented_product {n : ℕ} (B x y : BitString n) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    (suppressedPair (forbidden B x y) x y p).map (oriented B) =
      product (Fin n) (fun j ↦ coin (suppressedRate p (classify B x y j))) := by
  rw [suppressed_product _ x y p hp (forbidden_common B x y)]
  have h := map_product (Fin n)
    (fun j ↦ if j ∈ forbidden B x y then PMF.pure (x j) else siteLaw (x j) (y j) p)
    (fun j ↦ orientedBit (B j))
  have hfamily : (fun j : Fin n ↦
      (if j ∈ forbidden B x y then PMF.pure (x j) else siteLaw (x j) (y j) p).map
        (orientedBit (B j))) =
      (fun j ↦ coin (suppressedRate p (classify B x y j))) := by
    funext j
    simpa only [forbidden, Finset.mem_filter, Finset.mem_univ, true_and, classify] using
      suppressed_site_oriented (B j) (x j) (y j) p hp
  rw [hfamily] at h
  exact h

lemma suppressed_count_law {n : ℕ} (B x y : BitString n) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    (suppressedPair (forbidden B x y) x y p).map (regionCounts B x y) =
      distribution (fun r : Fin 6 ↦ weightLaw
        (Fintype.card {j // classify B x y j = r}) (suppressedRate p r)) := by
  have h := partition_counts (classify B x y) (suppressedRate p)
  rw [← suppressed_oriented_product B x y p hp, PMF.map_comp] at h
  convert h using 1
  congr 1

lemma physical_suppressed_error {n k : ℕ} (hn : 2 ≤ n) (B x y : BitString n)
    (hB : (zeros B).card = k) (hx : (zeros x).card = k)
    (f : BitString n → ℝ) (M : ℝ) (hf : ∀ child, |f child| ≤ M) :
    |mean (pairMutation x y (1 / n)) f -
      mean (suppressedPair (forbidden B x y) x y (1 / n)) f| ≤ 4 * M * k / n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (1 : ℝ) / n ∧ (1 : ℝ) / n ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by linarith : (0 : ℝ) < n)).mpr
      linarith
  have hM : 0 ≤ M := (abs_nonneg (f x)).trans (hf x)
  have hc : ((forbidden B x y).card : ℝ) ≤ 2 * k := by
    exact_mod_cast forbidden_card B x y hB hx
  have h := pair_suppression_comparison (forbidden B x y) x y (1 / n) hp f M hf
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * M by positivity)) hp.1
  exact h.trans (hb.trans_eq (by ring))

end
end Lax343628Proofs.SuppressedRegions

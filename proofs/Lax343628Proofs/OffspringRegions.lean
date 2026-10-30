import Lax343628Proofs.PhysicalOffspring
import Lax343628Proofs.PartitionCounts

namespace Lax343628Proofs.OffspringRegions

open Lax343628.Algorithm Lax343628Proofs.BitProduct Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.PartitionCounts Lax343628Proofs.FiniteProduct
open Lax343628Proofs.MaskCounts
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def region (B x y : Fin 2) : Fin 6 :=
  if x = y then
    if B = 0 then (if x = 0 then 0 else 1) else (if x = 0 then 3 else 4)
  else if B = 0 then 2 else 5

def rate (p : ℝ) (r : Fin 6) : ℝ :=
  if r = 0 ∨ r = 4 then p else if r = 1 ∨ r = 3 then 1 - p else 1 / 2

def orientedBit (B child : Fin 2) : Fin 2 := if B = 0 then child else 1 - child

lemma siteLaw_oriented (B x y : Fin 2) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (siteLaw x y p).map (orientedBit B) = coin (rate p (region B x y)) := by
  have hp' : 0 ≤ 1 - p ∧ 1 - p ≤ 1 := by constructor <;> linarith [hp.1, hp.2]
  ext target
  rw [PMF.map_apply, tsum_fintype, Fin.sum_univ_two]
  have hs (a b t : Fin 2) := siteLaw_apply a b t p hp
  simp_rw [hs]
  fin_cases B <;> fin_cases x <;> fin_cases y <;> fin_cases target <;>
    simp only [orientedBit, region, rate, siteProbability] <;>
    norm_num [Fin.ext_iff] <;>
    norm_num [coin, hp, hp', ENNReal.ofReal_div_of_pos]

def classify {n : ℕ} (B x y : BitString n) (j : Fin n) : Fin 6 := region (B j) (x j) (y j)

def oriented {n : ℕ} (B child : BitString n) : BitString n := fun j ↦ orientedBit (B j) (child j)

lemma oriented_pair_product {n : ℕ} (B x y : BitString n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (pairMutation x y p).map (oriented B) =
      product (Fin n) (fun j ↦ coin (rate p (classify B x y j))) := by
  rw [pairMutation_eq_product x y p hp]
  have h := map_product (Fin n) (fun j ↦ siteLaw (x j) (y j) p) (fun j ↦ orientedBit (B j))
  have hfamily : (fun j : Fin n ↦ (siteLaw (x j) (y j) p).map (orientedBit (B j))) =
      (fun j ↦ coin (rate p (classify B x y j))) := by
    funext j
    exact siteLaw_oriented (B j) (x j) (y j) p hp
  rw [hfamily] at h
  convert h using 1
  congr 1

def regionCounts {n : ℕ} (B x y child : BitString n) :=
  counts (classify B x y) (oriented B child)

lemma region_count_law {n : ℕ} (B x y : BitString n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (pairMutation x y p).map (regionCounts B x y) =
      distribution (fun r : Fin 6 ↦ weightLaw
        (Fintype.card {j // classify B x y j = r}) (rate p r)) := by
  have h := partition_counts (classify B x y) (rate p)
  rw [← oriented_pair_product B x y p hp, PMF.map_comp] at h
  convert h using 1
  congr 1

end
end Lax343628Proofs.OffspringRegions

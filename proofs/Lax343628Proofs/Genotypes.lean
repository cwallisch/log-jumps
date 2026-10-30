import Lax343628Proofs.IdealKernel
import Lax343628Proofs.Sampling

namespace Lax343628Proofs.Genotypes

open Lax343628.Algorithm Lax343628Proofs.Weights Lax343628Proofs.Sampling
open Lax343628Proofs.IdealKernel
open scoped BigOperators Classical

noncomputable section

abbrev Genotype (n k : ℕ) := {Z : Finset (Fin n) // Z.card = k}

def ofString {n k : ℕ} (x : BitString n) (hx : (zeros x).card = k) : Genotype n k :=
  ⟨zeros x, hx⟩

def toString {n k : ℕ} (x : Genotype n k) : BitString n :=
  fun j ↦ if j ∈ x.val then 0 else 1

@[simp] lemma zeros_toString {n k : ℕ} (x : Genotype n k) : zeros (toString x) = x.val := by
  ext j
  simp [mem_zeros, toString]

@[simp] lemma toString_ofString {n k : ℕ} (x : BitString n) (hx : (zeros x).card = k) :
    toString (ofString x hx) = x := by
  funext j
  by_cases hj : x j = 0
  · simp [toString, ofString, mem_zeros, hj]
  · have hj1 : x j = 1 := by have h := (x j).isLt; omega
    simp [toString, ofString, mem_zeros, hj1]

@[simp] lemma ofString_toString {n k : ℕ} (x : Genotype n k) :
    ofString (toString x) (by rw [zeros_toString]; exact x.property) = x := by
  exact Subtype.ext (zeros_toString x)

lemma toString_injective {n k : ℕ} : Function.Injective (@toString n k) := by
  intro x y h
  apply Subtype.ext
  have hz := congrArg zeros h
  simpa only [zeros_toString] using hz

@[simp] lemma toString_eq_iff {n k : ℕ} (x y : Genotype n k) :
    toString x = toString y ↔ x = y := toString_injective.eq_iff

def distance {n k : ℕ} (B x : Genotype n k) : ℕ := (B.val \ x.val).card

lemma distance_eq {n k : ℕ} (B x : Genotype n k) :
    distance B x = k - (B.val ∩ x.val).card := by
  rw [distance, Finset.card_sdiff, B.property, Finset.inter_comm]

lemma distance_symm {n k : ℕ} (B x : Genotype n k) : distance B x = distance x B := by
  exact Finset.card_sdiff_comm (B.property.trans x.property.symm)

@[simp] lemma distance_self {n k : ℕ} (B : Genotype n k) : distance B B = 0 := by
  simp [distance]

lemma distance_le {n k : ℕ} (B x : Genotype n k) : distance B x ≤ k := by
  rw [distance_eq]
  exact Nat.sub_le _ _

lemma distance_pos {n k : ℕ} (B x : Genotype n k) (h : x ≠ B) : 0 < distance B x := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hsub : B.val ⊆ x.val := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hzero)
  have heq : B.val = x.val := Finset.eq_of_subset_of_card_le hsub (by rw [B.property, x.property])
  exact h (Subtype.ext heq.symm)

def missingBoth {n k : ℕ} (B x y : Genotype n k) : ℕ :=
  (B.val \ (x.val ∪ y.val)).card

def sharedOutside {n k : ℕ} (B x y : Genotype n k) : ℕ :=
  ((x.val ∩ y.val) \ B.val).card

lemma missingBoth_le {n k : ℕ} (B x y : Genotype n k) : missingBoth B x y ≤ distance B x := by
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hj ⊢
  exact ⟨hj.1, hj.2.1⟩

lemma sharedOutside_le {n k : ℕ} (B x y : Genotype n k) : sharedOutside B x y ≤ distance B x := by
  rw [distance_symm]
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_sdiff, Finset.mem_inter] at hj ⊢
  exact ⟨hj.1.1, hj.2⟩

def weightedKernel {n k : ℕ} (B x y : Genotype n k) : ℝ :=
  kernel (distance B x) (distance B y) (missingBoth B x y) (sharedOutside B x y)

def cloneKernel {n k : ℕ} (B x y : Genotype n k) : ℝ :=
  copyKernel (distance B x) (distance B y) (missingBoth B x y) (sharedOutside B x y)

lemma weightedKernel_nonneg {n k : ℕ} (B x y : Genotype n k) : 0 ≤ weightedKernel B x y :=
  kernel_nonneg _ _ _ _

lemma weightedKernel_symm {n k : ℕ} (B x y : Genotype n k) :
    weightedKernel B x y = weightedKernel B y x := by
  unfold weightedKernel kernel missingBoth sharedOutside
  rw [Finset.union_comm x.val y.val, Finset.inter_comm x.val y.val]
  simp only [Nat.add_comm (distance B x) (distance B y)]

lemma anchor_geometry {n k : ℕ} (B y : Genotype n k) :
    missingBoth B B y = 0 ∧ sharedOutside B B y = 0 := by
  constructor <;> apply Finset.card_eq_zero.mpr
  · exact Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_left
  · exact Finset.sdiff_eq_empty_iff_subset.mpr Finset.inter_subset_left

lemma weightedKernel_anchor {n k : ℕ} (B y : Genotype n k) :
    weightedKernel B B y = kernel 0 (distance B y) 0 0 := by
  unfold weightedKernel
  rw [distance_self, (anchor_geometry B y).1, (anchor_geometry B y).2]

@[simp] lemma weightedKernel_anchor_self {n k : ℕ} (B : Genotype n k) :
    weightedKernel B B B = 0 := by
  rw [weightedKernel_anchor, distance_self, kernel_anchor_zero]

lemma weightedKernel_anchor_one {n k : ℕ} (B y : Genotype n k) (hy : distance B y = 1) :
    2 * weightedKernel B B y = weight (distance B y) := by
  rw [weightedKernel_anchor, hy, weight_one]
  exact twice_anchor_one

lemma weightedKernel_anchor_far {n k : ℕ} (B y : Genotype n k) (hy : 2 ≤ distance B y) :
    2 * weightedKernel B B y = (17 / 16 : ℝ) * weight (distance B y) := by
  rw [weightedKernel_anchor]
  exact twice_anchor hy

lemma distance_one_kernel_lower {n k : ℕ} (B x y : Genotype n k)
    (hx : distance B x = 1) (hy : distance B y = 1) :
    (51 / 80 : ℝ) ≤ weightedKernel B x y := by
  have ht : missingBoth B x y ≤ 1 := by simpa only [hx] using missingBoth_le B x y
  have hu : sharedOutside B x y ≤ 1 := by simpa only [hx] using sharedOutside_le B x y
  unfold weightedKernel
  rw [hx, hy]
  exact (distance_one_bounds ht hu).1

lemma cloneKernel_anchor {n k : ℕ} (B y : Genotype n k) :
    cloneKernel B B y = (4 : ℝ)⁻¹ ^ distance B y := by
  unfold cloneKernel
  rw [distance_self, (anchor_geometry B y).1, (anchor_geometry B y).2]
  simp [copyKernel]

lemma cloneKernel_symm {n k : ℕ} (B x y : Genotype n k) : cloneKernel B x y = cloneKernel B y x := by
  unfold cloneKernel copyKernel missingBoth sharedOutside
  rw [Finset.union_comm x.val y.val, Finset.inter_comm x.val y.val, mul_comm]

lemma cloneKernel_le {n k : ℕ} (B x y : Genotype n k) :
    cloneKernel B x y ≤ (4 : ℝ)⁻¹ ^ distance B x * (4 : ℝ)⁻¹ ^ distance B y :=
  copy_le _ _ _ _

end
end Lax343628Proofs.Genotypes

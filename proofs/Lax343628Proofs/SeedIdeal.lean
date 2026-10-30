import Lax343628Proofs.SeedGeometry
import Lax343628Proofs.NormalizedPrivate
import Lax343628Proofs.BirthCouplings

namespace Lax343628Proofs.SeedIdeal

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.ColumnKernels
open Lax343628Proofs.PrivatePool Lax343628Proofs.BirthGeometry Lax343628Proofs.BirthCouplings
open Lax343628Proofs.GeneralBirthApproximation Lax343628Proofs.NormalizedPrivate
open Lax343628Proofs.FiniteDrift Lax343628Proofs.CurveBounds Lax343628Proofs.ClassTest
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {i : Fin n}

lemma mean_const_on_support {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ)
    (h : ∀ x ∈ p.support, f x = c) : mean p f = c := by
  apply le_antisymm
  · exact (mean_mono_on_support p (fun x hx ↦ (h x hx).le)).trans_eq (mean_const p c)
  · rw [← mean_const p c]
    exact mean_mono_on_support p (fun x hx ↦ (h x hx).ge)

def familyClass (C : Finset (Fin n)) (x : ColumnClass n (r + 1) i 1) : ℝ :=
  if C.erase i ⊆ zeros x.val then 1 else 0

lemma resident_value (C S : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r + 1)
    (hR : r + 1 ≤ (freshSet S).card) (hiS : i ∈ S)
    (x : ColumnClass n (r + 1) i 0) (y : BitString n)
    (hy : (zeros y).card = r + 1) (hyi : y i = 0)
    (hxS : zeros x.val ⊆ S) (hyS : zeros y ⊆ S) (hcommon : common i x.val y = C.erase i) :
    ColumnApproximation.idealAction S y (fun _ ↦ 1) x = Real.exp (-1) * q (r + 1 - C.card) := by
  let CC := common i x.val y
  let lab := label i x.val y
  let RR := freshSet S
  let hAd : Admissible CC lab RR := admissible _ i x.val y (freshSet_common_ones S x.val y hxS hyS)
  have hExtra : Extra CC lab RR i := column_extra RR i x.val y
    (by simpa only [RR, freshSet, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hiS)
  have hcle : CC.card ≤ r := (common_card_le i x.val y).trans_eq (resident_private_size x)
  have hpoint (Z : Finset (Pool i x.val y ⊕ Fin RR.card))
      (hZ : Z ∈ (PlacedBase.placedLaw (r - CC.card)).support) :
      test i 0 (liftClass (fun _ : ColumnClass n (r + 1) i 0 ↦ 1)) (NamedBirth.fromZeros (realize CC lab RR hAd.named_fresh Z)) = 1 := by
    have hzcard : (realize CC lab RR hAd.named_fresh Z).card = size (r + 1) 0 := by
      rw [realize_card CC lab RR hAd, SlotBirth.placedLaw_card (by simpa only [Fintype.card_fin] using (Nat.sub_le r CC.card).trans (Nat.le_succ r |>.trans hR)) Z hZ]
      simp only [size, if_true, Nat.add_sub_cancel]
      omega
    have hnot := extra_not_realize CC lab RR hAd.named_fresh hExtra Z
    change ClassTest.test (fun _ : ColumnClass n (r + 1) i 0 ↦ (1 : ℝ)) (realize CC lab RR hAd.named_fresh Z) = 1
    rw [test_encode (by omega) _ _ hzcard hnot]
  have hm := mean_const_on_support (PlacedBase.placedLaw (α := Pool i x.val y) (β := Fin RR.card) (r - CC.card)) _ 1 hpoint
  rw [resident_normalized S hR hiS x y hxS hyS]
  change mass r CC lab * _ = _
  rw [hm, mul_one, balanced_mass i x.val y (resident_private_size x)
    (resident_private_size (⟨y, hy, hyi⟩ : ColumnClass n (r + 1) i 0))]
  have hcpos := Finset.card_pos.mpr ⟨i, hi⟩
  have hccard : CC.card = C.card - 1 := by dsimp [CC]; rw [hcommon, Finset.card_erase_of_mem hi]
  rw [show r - CC.card = r + 1 - C.card by omega]

lemma mutant_value (C S : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r + 1)
    (hR : r + 1 ≤ (freshSet S).card) (hiS : i ∈ S)
    (x : ColumnClass n (r + 1) i 1) (y : BitString n)
    (hy : (zeros y).card = r + 1) (hyi : y i = 0)
    (hxS : zeros x.val ⊆ S) (hyS : zeros y ⊆ S) (hcommon : common i x.val y = C.erase i) :
    ColumnApproximation.idealAction S y (familyClass (r := r) (i := i) C) x = Real.exp (-1) * t (r + 1 - C.card) := by
  let CC := common i x.val y
  let lab := label i x.val y
  let RR := freshSet S
  let hAd : Admissible CC lab RR := admissible _ i x.val y (freshSet_common_ones S x.val y hxS hyS)
  have hExtra : Extra CC lab RR i := column_extra RR i x.val y
    (by simpa only [RR, freshSet, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hiS)
  have hcle : CC.card ≤ r + 1 := (common_card_le i x.val y).trans_eq (mutant_private_size x)
  have hpoint (Z : Finset (Pool i x.val y ⊕ Fin RR.card))
      (hZ : Z ∈ (PlacedBase.placedLaw (r + 1 - CC.card)).support) :
      test i 1 (liftClass (familyClass (r := r) (i := i) C)) (NamedBirth.fromZeros (realize CC lab RR hAd.named_fresh Z)) = 1 := by
    have hzcard : (realize CC lab RR hAd.named_fresh Z).card = size (r + 1) 1 := by
      rw [realize_card CC lab RR hAd, SlotBirth.placedLaw_card (by simpa only [Fintype.card_fin] using (Nat.sub_le (r + 1) CC.card).trans hR) Z hZ]
      simp only [size, if_neg (by decide : (1 : Fin 2) ≠ 0)]
      omega
    have hnot := extra_not_realize CC lab RR hAd.named_fresh hExtra Z
    change ClassTest.test (familyClass (r := r) (i := i) C) (realize CC lab RR hAd.named_fresh Z) = 1
    rw [test_encode (by omega) _ _ hzcard hnot]
    change (if C.erase i ⊆ zeros (NamedBirth.fromZeros (realize CC lab RR hAd.named_fresh Z)) then (1 : ℝ) else 0) = 1
    rw [NamedBirth.zeros_fromZeros]
    apply if_pos
    have hsub : CC ⊆ realize CC lab RR hAd.named_fresh Z := Finset.subset_union_left
    simpa only [CC, hcommon] using hsub
  have hm := mean_const_on_support (PlacedBase.placedLaw (α := Pool i x.val y) (β := Fin RR.card) (r + 1 - CC.card)) _ 1 hpoint
  rw [mutant_normalized S hR hiS x y hxS hyS]
  change mass (r + 1) CC lab * _ = _
  rw [hm, mul_one, upper_unbalanced_mass i x.val y (mutant_private_size x)
    (resident_private_size (⟨y, hy, hyi⟩ : ColumnClass n (r + 1) i 0))]
  have hcpos := Finset.card_pos.mpr ⟨i, hi⟩
  have hccard : CC.card = C.card - 1 := by dsimp [CC]; rw [hcommon, Finset.card_erase_of_mem hi]
  rw [show r - CC.card = r + 1 - C.card by omega]

end
end Lax343628Proofs.SeedIdeal

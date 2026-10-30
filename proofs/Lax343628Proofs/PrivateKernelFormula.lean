import Lax343628Proofs.PrivatePool
import Lax343628Proofs.ColumnApproximation

namespace Lax343628Proofs.PrivateKernelFormula

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.NamedBirth
open Lax343628Proofs.PrivatePool Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ColumnSlotSplit
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma common_eq_of_one {n : ℕ} (i : Fin n) (x y : BitString n) (hx : x i = 1) :
    zeros x ∩ zeros y = common i x y := by
  unfold common
  rw [Finset.erase_eq_of_notMem]
  intro hi
  have hx0 : x i = 0 := by simpa only [mem_zeros] using (Finset.mem_inter.mp hi).1
  rw [hx] at hx0
  exact (by decide : (1 : Fin 2) ≠ 0) hx0

lemma common_eq_of_different {n : ℕ} (i : Fin n) (x y : BitString n) (hxy : x i ≠ y i) :
    zeros x ∩ zeros y = common i x y := by
  unfold common
  rw [Finset.erase_eq_of_notMem]
  intro hi
  have hx0 : x i = 0 := by simpa only [mem_zeros] using (Finset.mem_inter.mp hi).1
  have hy0 : y i = 0 := by simpa only [mem_zeros] using (Finset.mem_inter.mp hi).2
  exact hxy (hx0.trans hy0.symm)

lemma common_eq_insert_of_zero {n : ℕ} (i : Fin n) (x y : BitString n)
    (hx : x i = 0) (hy : y i = 0) :
    zeros x ∩ zeros y = insert i (common i x y) :=
  (Finset.insert_erase (by simp only [Finset.mem_inter, mem_zeros]; exact ⟨hx, hy⟩)).symm

lemma ideal_private_formula {n k : ℕ} (R : Finset (Fin n)) (hk : k ≤ R.card)
    (i : Fin n) (x y : BitString n) (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1) (hiR : i ∉ R)
    (b : Fin 2) (hx : x i = b) (f : BitString n → ℝ)
    (hf : ∀ child, child i ≠ b → f child = 0) :
    classFactor i b y * GeneralBirthApproximation.idealBirthMean k R x y f =
      BirthOn.value k (common i x y) (label i x y) R (test i b f) := by
  rw [BirthOn.ideal_value R hk x y hR f]
  have hiExtra := column_extra R i x y hiR
  by_cases hsame : x i = y i
  · have hb : b = y i := hx.symm.trans hsame
    simp only [classFactor, if_pos hb, one_mul]
    have hre := (BirthOn.reindex k (zeros x ∩ zeros y) (differingEmbedding R x y)
      (label i x y) (sameEquiv R i x y hR hsame) (fun _ ↦ rfl) R f).symm
    refine hre.trans ?_
    fin_cases b
    · have hy : y i = 0 := hsame.symm.trans hx
      have hC := common_eq_insert_of_zero i x y hx hy
      calc
        BirthOn.value k (zeros x ∩ zeros y) (label i x y) R f =
            BirthOn.value k (insert i (common i x y)) (label i x y) R f :=
          congrArg (fun C ↦ BirthOn.value k C (label i x y) R f) hC
        _ = BirthOn.value k (common i x y) (label i x y) R
            (fun child ↦ f (Function.update child i 0)) := value_insert_common _ _ _ _ _ _
        _ = _ := (value_test k _ _ R i hiExtra 0 f).symm
    · have hC := common_eq_of_one i x y hx
      calc
        BirthOn.value k (zeros x ∩ zeros y) (label i x y) R f =
            BirthOn.value k (common i x y) (label i x y) R f :=
          congrArg (fun C ↦ BirthOn.value k C (label i x y) R f) hC
        _ = _ := (value_test_one k _ _ R i hiExtra f).symm
  · have hb : b ≠ y i := by rw [← hx]; exact hsame
    simp only [classFactor, if_neg hb]
    let a0 := distinguished R i x y hR hsame
    let smaller := (Function.Embedding.subtype (fun a : Differing R x y ↦ a ≠ a0)).trans
      (differingEmbedding R x y)
    have hC := common_eq_of_different i x y hsame
    have ha0 : differingEmbedding R x y a0 = i := rfl
    have hre (g : BitString n → ℝ) : BirthOn.value k (zeros x ∩ zeros y) smaller R g =
        BirthOn.value k (common i x y) (label i x y) R g := by
      have hr := (BirthOn.reindex k (zeros x ∩ zeros y) smaller (label i x y)
        (mixedEquiv R i x y hR hsame) (fun _ ↦ rfl) R g).symm
      exact hr.trans (congrArg (fun C ↦ BirthOn.value k C (label i x y) R g) hC)
    fin_cases b
    · have hnot : i ∉ zeros x ∩ zeros y := by
        intro hboth
        have hy0 : y i = 0 := by simpa only [mem_zeros] using (Finset.mem_inter.mp hboth).2
        exact hsame (hx.trans hy0.symm)
      have hc := mixed_resident_cancellation k (zeros x ∩ zeros y) (differingEmbedding R x y)
        a0 R (by rwa [ha0]) (by rwa [ha0]) f (fun child hc ↦ hf child (by rw [ha0] at hc; rw [hc]; decide))
      calc
        _ = BirthOn.value k (zeros x ∩ zeros y) smaller R
            (fun child ↦ f (Function.update child i 0)) := by simpa only [ha0] using hc
        _ = BirthOn.value k (common i x y) (label i x y) R
            (fun child ↦ f (Function.update child i 0)) := hre _
        _ = _ := (value_test k _ _ R i hiExtra 0 f).symm
    · have hc := mixed_mutant_cancellation k (zeros x ∩ zeros y) (differingEmbedding R x y)
        a0 R f (fun child hc ↦ hf child (by rw [ha0] at hc; rw [hc]; decide))
      exact hc.trans ((hre f).trans (value_test_one k _ _ R i hiExtra f).symm)

lemma column_ideal_private {n k : ℕ} {i : Fin n} {b : Fin 2} (S : Finset (Fin n))
    (hk : k ≤ (GeneralBirthApproximation.freshSet S).card) (hi : i ∈ S)
    (source : ColumnClass n k i b) (partner : BitString n)
    (hx : zeros source.val ⊆ S) (hy : zeros partner ⊆ S) (h : ColumnClass n k i b → ℝ) :
    ColumnApproximation.idealAction S partner h source =
      BirthOn.value k (common i source.val partner) (label i source.val partner)
        (GeneralBirthApproximation.freshSet S) (test i b (liftClass h)) := by
  apply ideal_private_formula _ hk i source.val partner
    (GeneralBirthApproximation.freshSet_common_ones S source.val partner hx hy)
    (by simpa only [GeneralBirthApproximation.freshSet, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hi)
    b source.property.2 (liftClass h)
  intro child hbit
  unfold liftClass
  rw [dif_neg (by tauto)]

end
end Lax343628Proofs.PrivateKernelFormula

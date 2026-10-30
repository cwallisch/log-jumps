import Lax343628Proofs.BitProduct

namespace Lax343628Proofs.FiniteProduct

open Lax343628Proofs.BitProduct
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def distribution {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Fintype (β i)]
    (p : ∀ i, PMF (β i)) : PMF (∀ i, β i) :=
  PMF.ofFintype (fun x ↦ ∏ i, p i (x i)) (by
    have h : ∀ i, (∑ b, p i b) = 1 := fun i ↦ by
      simpa only [tsum_fintype] using (p i).tsum_coe
    rw [← Fintype.prod_sum]
    simp only [h, Finset.prod_const_one])

lemma distribution_apply {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Fintype (β i)]
    (p : ∀ i, PMF (β i)) (x : ∀ i, β i) : distribution p x = ∏ i, p i (x i) := rfl

lemma indicator_product {ι : Type*} [Fintype ι] {β γ : ι → Type*}
    (p : ∀ i, β i → ℝ≥0∞) (f : ∀ i, β i → γ i) (x : ∀ i, β i) (target : ∀ i, γ i) :
    (∏ i, p i (x i)) * (if target = (fun i ↦ f i (x i)) then 1 else 0) =
      ∏ i, p i (x i) * (if target i = f i (x i) then 1 else 0) := by
  by_cases h : target = (fun i ↦ f i (x i))
  · have hi : ∀ i, target i = f i (x i) := congrFun h
    simp only [if_pos h, if_pos (hi _), mul_one]
  · obtain ⟨i, hi⟩ : ∃ i, target i ≠ f i (x i) := by
      simpa only [funext_iff, not_forall] using h
    rw [if_neg h, mul_zero]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi, mul_zero])

lemma map_distribution {ι : Type*} [Fintype ι] {β γ : ι → Type*}
    [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)] (p : ∀ i, PMF (β i)) (f : ∀ i, β i → γ i) :
    (distribution p).map (fun x i ↦ f i (x i)) = distribution (fun i ↦ (p i).map (f i)) := by
  classical
  ext target
  rw [PMF.map_apply, tsum_fintype, distribution_apply]
  simp_rw [PMF.map_apply, tsum_fintype]
  calc
    _ =
        ∑ x : (∀ i, β i), ∏ i, p i (x i) * (if target i = f i (x i) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← indicator_product (fun i ↦ p i) f x target, distribution_apply]
      split_ifs <;> simp
    _ = _ := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.prod_congr rfl
      intro i _
      split_ifs <;> simp

lemma map_equiv_apply {α β : Type*} (p : PMF α) (e : α ≃ β) (b : β) :
    p.map e b = p (e.symm b) := by
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp only [e.apply_symm_apply, ite_true]
  · intro a ha
    apply if_neg
    intro h
    apply ha
    simpa only [e.symm_apply_apply] using (congrArg e.symm h).symm

def partitionEquiv {ι κ : Type*} (c : ι → κ) :
    (ι → Fin 2) ≃ ((r : κ) → ({i // c i = r} → Fin 2)) where
  toFun x r i := x i
  invFun x i := x (c i) ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv x := by
    funext r ⟨i, hi⟩
    cases hi
    rfl

lemma partition_product {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (p : ι → PMF (Fin 2)) :
    (product ι p).map (partitionEquiv c) =
      distribution (fun r : κ ↦ product {i // c i = r} (fun i ↦ p i)) := by
  ext x
  rw [map_equiv_apply, product_apply, distribution_apply]
  simp only [product_apply]
  rw [← Fintype.prod_fiberwise c (fun i ↦ p i ((partitionEquiv c).symm x i))]
  apply Finset.prod_congr rfl
  intro r _
  apply Finset.prod_congr rfl
  intro i _
  rcases i with ⟨i, hi⟩
  cases hi
  rfl

lemma partition_constant_rates {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (rate : κ → ℝ) :
    (product ι (fun i ↦ Lax343628.Algorithm.coin (rate (c i)))).map (partitionEquiv c) =
      distribution (fun r : κ ↦ bits {i // c i = r} (rate r)) := by
  rw [partition_product]
  congr 1
  funext r
  have heq : (fun i : {i // c i = r} ↦ Lax343628.Algorithm.coin (rate (c i))) =
      (fun _ : {i // c i = r} ↦ Lax343628.Algorithm.coin (rate r)) := by
    funext i
    rw [i.property]
  rw [heq, product_coin]

end
end Lax343628Proofs.FiniteProduct

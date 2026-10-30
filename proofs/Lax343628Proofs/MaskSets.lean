import Lax343628Proofs.UniformMutation

namespace Lax343628Proofs.MaskSets

open Lax343628.Algorithm Lax343628Proofs.BitProduct
open Lax343628Proofs.FiniteProduct Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α]

def selected (mask : α → Fin 2) : Finset α := Finset.univ.filter (fun j ↦ mask j = 1)

def fromSet (S : Finset α) : α → Fin 2 := fun j ↦ if j ∈ S then 1 else 0

@[simp] lemma selected_fromSet (S : Finset α) : selected (fromSet S) = S := by
  ext j
  simp [selected, fromSet]

@[simp] lemma fromSet_selected (mask : α → Fin 2) : fromSet (selected mask) = mask := by
  funext j
  by_cases hj : mask j = 1
  · simp [fromSet, selected, hj]
  · have hj0 : mask j = 0 := by have h := (mask j).isLt; omega
    simp [fromSet, selected, hj0]

def setEquiv (α : Type*) [Fintype α] [DecidableEq α] : (α → Fin 2) ≃ Finset α where
  toFun := selected
  invFun := fromSet
  left_inv := fromSet_selected
  right_inv := selected_fromSet

omit [DecidableEq α] in
lemma fair_bits_mass (mask : α → Fin 2) :
    (bits α (1 / 2) mask).toReal = (1 / 2 : ℝ) ^ Fintype.card α := by
  rw [bits_apply, ENNReal.toReal_prod]
  have hc (b : Fin 2) : (coin (1 / 2) b).toReal = (1 / 2 : ℝ) := by
    fin_cases b <;> norm_num [coin]
  simp only [hc, Finset.prod_const, Finset.card_univ]

lemma fair_sets_mass (S : Finset α) :
    ((bits α (1 / 2)).map selected S).toReal = (1 / 2 : ℝ) ^ Fintype.card α := by
  have he := map_equiv_apply (bits α (1 / 2)) (setEquiv α) S
  change (bits α (1 / 2)).map selected S = bits α (1 / 2) (fromSet S) at he
  rw [he, fair_bits_mass]

lemma fair_mean (f : Finset α → ℝ) :
    mean (bits α (1 / 2)) (fun mask ↦ f (selected mask)) =
      (1 / 2 : ℝ) ^ Fintype.card α * ∑ J, f J := by
  rw [← mean_map (bits α (1 / 2)) selected f]
  unfold mean
  simp_rw [fair_sets_mass]
  rw [Finset.mul_sum]

end
end Lax343628Proofs.MaskSets

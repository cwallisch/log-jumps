import Lax343628Proofs.BirthOn
import Lax343628Proofs.FiniteExchange

namespace Lax343628Proofs.BirthGeometry

open Lax343628.Algorithm Lax343628Proofs.NamedBirth
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.SlotBirth Lax343628Proofs.CountStatistics
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

structure Admissible (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n)) : Prop where
  named_fresh : ∀ a, label a ∉ R
  named_common : ∀ a, label a ∉ C
  common_fresh : Disjoint C R

def combinedEmbedding (label : α ↪ Fin n) (R : Finset (Fin n)) (hR : ∀ a, label a ∉ R) :
    α ⊕ Fin R.card ↪ Fin n where
  toFun := Sum.elim label (freshEmbedding R)
  inj' := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (label.injective hab)
      | inr b =>
        change label a = (R.equivFin.symm b).val at hab
        exact False.elim (hR a (by rw [hab]; exact (R.equivFin.symm b).property))
    | inr a =>
      cases b with
      | inl b =>
        change (R.equivFin.symm a).val = label b at hab
        exact False.elim (hR b (by rw [← hab]; exact (R.equivFin.symm a).property))
      | inr b => exact congrArg Sum.inr ((freshEmbedding R).injective hab)

def realize (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hR : ∀ a, label a ∉ R) (S : Finset (α ⊕ Fin R.card)) : Finset (Fin n) :=
  C ∪ S.map (combinedEmbedding label R hR)

omit [Fintype α] [DecidableEq α] in
lemma realize_insert (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hR : ∀ a, label a ∉ R) (e : Fin n) (S : Finset (α ⊕ Fin R.card)) :
    realize (insert e C) label R hR S = insert e (realize C label R hR S) := by
  unfold realize
  rw [Finset.insert_union]

omit [Fintype α] [DecidableEq α] in
lemma realize_disjSum (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hR : ∀ a, label a ∉ R) (J : Finset α) (F : Finset (Fin R.card)) :
    realize C label R hR (J.disjSum F) = C ∪ J.map label ∪ F.map (freshEmbedding R) := by
  ext j
  simp [realize, Finset.mem_map, combinedEmbedding, Sum.exists]

omit [Fintype α] [DecidableEq α] in
lemma common_disjoint (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) (S : Finset (α ⊕ Fin R.card)) :
    Disjoint C (S.map (combinedEmbedding label R hA.named_fresh)) := by
  apply Finset.disjoint_left.mpr
  intro j hjC hjS
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hjS
  cases a with
  | inl a => exact hA.named_common a hjC
  | inr a => exact Finset.disjoint_left.mp hA.common_fresh hjC (R.equivFin.symm a).property

omit [Fintype α] [DecidableEq α] in
lemma realize_card (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) (S : Finset (α ⊕ Fin R.card)) :
    (realize C label R hA.named_fresh S).card = C.card + S.card := by
  rw [realize, Finset.card_union_of_disjoint (common_disjoint C label R hA S), Finset.card_map]

lemma value_eq_birthMean (k : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hR : ∀ a, label a ∉ R) (h : BitString n → ℝ) :
    BirthOn.value k C label R h =
      birthMean k (fun S ↦ h (fromZeros (realize C label R hR S))) := by
  unfold BirthOn.value birthMean freshMean
  simp_rw [realize_disjSum]

def mass (k : ℕ) (C : Finset (Fin n)) (_label : α ↪ Fin n) : ℝ :=
  Real.exp (-1) * (1 / 2 : ℝ) ^ Fintype.card α * SlotProfiles.beta (Fintype.card α) (k - C.card)

omit [DecidableEq α] in
lemma mass_pos (k : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n) : 0 < mass k C label := by
  unfold mass
  exact mul_pos (mul_pos (Real.exp_pos _) (by positivity)) (SlotProfiles.beta_pos _ _)

lemma value_fixed_size_general {r k : ℕ} (hr : r ≤ k) (C : Finset (Fin n))
    (label : α ↪ Fin n) (R : Finset (Fin n)) (hA : Admissible C label R)
    (hC : C.card ≤ r) (hk : k ≤ R.card)
    (h : BitString n → ℝ) (hsupport : ∀ x, (Sampling.zeros x).card ≠ r → h x = 0) :
    BirthOn.value k C label R h = mass r C label *
      mean (PlacedBase.placedLaw (r - C.card))
        (fun S ↦ h (fromZeros (realize C label R hA.named_fresh S))) := by
  rw [value_eq_birthMean k C label R hA.named_fresh h]
  apply birthMean_fixed_size ((Nat.sub_le _ _).trans hr) (by simpa using hk)
  intro S hS
  apply hsupport
  rw [zeros_fromZeros, realize_card C label R hA S]
  omega

end
end Lax343628Proofs.BirthGeometry

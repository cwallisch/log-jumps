import Lax343628Proofs.BirthOn

namespace Lax343628Proofs.BirthSplit

open Lax343628Proofs.BirthOn
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def pointEquiv {α : Type*} [DecidableEq α] (a0 : α) : {a : α // a ≠ a0} ⊕ Unit ≃ α where
  toFun := Sum.elim Subtype.val (fun _ ↦ a0)
  invFun a := if ha : a = a0 then Sum.inr () else Sum.inl ⟨a, ha⟩
  left_inv := by
    intro a
    cases a with
    | inl a => simp only [Sum.elim_inl, dif_neg a.property]
    | inr a => cases a; simp
  right_inv a := by
    by_cases ha : a = a0 <;> simp [ha]

lemma sum_unit_sets (f : Finset Unit → ℝ) : ∑ B, f B = f ∅ + f {()} := by
  change (∑ B ∈ (Finset.univ : Finset Unit).powerset, f B) = _
  have hu : (Finset.univ : Finset Unit).powerset = {∅, {()}} := by decide
  rw [hu]
  simp

lemma split_point {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (k : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n) (a0 : α)
    (R : Finset (Fin n)) (h : Lax343628.Algorithm.BitString n → ℝ) :
    value k C label R h = (1 / 2 : ℝ) *
      (value k C ((Function.Embedding.subtype (fun a ↦ a ≠ a0)).trans label) R h +
        value k (insert (label a0) C)
          ((Function.Embedding.subtype (fun a ↦ a ≠ a0)).trans label) R h) := by
  let e := pointEquiv a0
  let labelNew := e.toEmbedding.trans label
  have hr := reindex k C labelNew label e (fun _ ↦ rfl) R h
  rw [hr, split_sum, sum_unit_sets]
  simp only [Finset.map_empty, Finset.union_empty, Finset.map_singleton, Fintype.card_unique, pow_one]
  have hleft : Function.Embedding.inl.trans labelNew =
      (Function.Embedding.subtype (fun a ↦ a ≠ a0)).trans label := rfl
  rw [hleft]
  change (1 / 2 : ℝ) * (value k C _ R h + value k (C ∪ {label a0}) _ R h) = _
  rw [Finset.union_singleton]

lemma sum_fin_two_sets (f : Finset (Fin 2) → ℝ) :
    ∑ B, f B = f ∅ + f {0} + f {1} + f {0, 1} := by
  change (∑ B ∈ (Finset.univ : Finset (Fin 2)).powerset, f B) = _
  have hu : (Finset.univ : Finset (Fin 2)).powerset = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hu]
  rw [Finset.sum_insert (by decide : (∅ : Finset (Fin 2)) ∉
    ({{0}, {1}, {0, 1}} : Finset (Finset (Fin 2))))]
  rw [Finset.sum_insert (by decide : ({0} : Finset (Fin 2)) ∉
    ({{1}, {0, 1}} : Finset (Finset (Fin 2))))]
  rw [Finset.sum_pair (by decide : ({1} : Finset (Fin 2)) ≠ {0, 1})]
  ring

lemma split_two {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (k : ℕ) (C : Finset (Fin n)) (label : α ⊕ Fin 2 ↪ Fin n)
    (R : Finset (Fin n)) (h : Lax343628.Algorithm.BitString n → ℝ) :
    value k C label R h = (1 / 4 : ℝ) *
      (value k C (Function.Embedding.inl.trans label) R h +
        value k (insert (label (Sum.inr 0)) C) (Function.Embedding.inl.trans label) R h +
        value k (insert (label (Sum.inr 1)) C) (Function.Embedding.inl.trans label) R h +
        value k (insert (label (Sum.inr 0)) (insert (label (Sum.inr 1)) C))
          (Function.Embedding.inl.trans label) R h) := by
  rw [split_sum, sum_fin_two_sets]
  norm_num only [Fintype.card_fin, show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num,
    Finset.map_empty, Finset.union_empty, Finset.map_singleton, Finset.map_insert,
    Finset.union_singleton, Finset.union_insert]
  rfl

end
end Lax343628Proofs.BirthSplit

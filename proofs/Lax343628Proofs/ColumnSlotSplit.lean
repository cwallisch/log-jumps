import Lax343628Proofs.BirthSplit
import Lax343628Proofs.BirthCouplings

namespace Lax343628Proofs.ColumnSlotSplit

open Lax343628.Algorithm Lax343628Proofs.NamedBirth Lax343628Proofs.BirthOn
open Lax343628Proofs.FiniteDrift Lax343628Proofs.CountStatistics Lax343628Proofs.SlotBirth
open Lax343628Proofs.BirthCouplings
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

lemma fromZeros_insert (S : Finset (Fin n)) (i : Fin n) :
    fromZeros (insert i S) = Function.update (fromZeros S) i 0 := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [fromZeros]
  · simp [fromZeros, hji]

lemma value_congr (k : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (f g : BitString n → ℝ)
    (hfg : ∀ J : Finset α, ∀ F : Finset (Fin R.card),
      f (fromZeros (C ∪ J.map label ∪ F.map (freshEmbedding R))) =
        g (fromZeros (C ∪ J.map label ∪ F.map (freshEmbedding R)))) :
    value k C label R f = value k C label R g := by
  unfold value
  congr 1
  apply Finset.sum_congr rfl
  intro J _
  unfold poissonMean
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  apply congrArg (mean (freshLaw (Fin R.card) w))
  funext F
  exact hfg J F

lemma value_zero (k : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n)) :
    value k C label R (fun _ ↦ 0) = 0 := by
  simp [value, poissonMean, mean_const]

lemma value_insert_common (k : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (i : Fin n) (f : BitString n → ℝ) :
    value k (insert i C) label R f = value k C label R (fun x ↦ f (Function.update x i 0)) := by
  unfold value
  congr 1
  apply Finset.sum_congr rfl
  intro J _
  unfold poissonMean
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  apply congrArg (mean (freshLaw (Fin R.card) w))
  funext F
  rw [Finset.insert_union, Finset.insert_union, fromZeros_insert]

omit [Fintype α] [DecidableEq α] in
lemma constructed_column_one (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    {i : Fin n} (hi : Extra C label R i) (J : Finset α) (F : Finset (Fin R.card)) :
    fromZeros (C ∪ J.map label ∪ F.map (freshEmbedding R)) i = 1 := by
  have hnot : i ∉ C ∪ J.map label ∪ F.map (freshEmbedding R) := by
    simp only [Finset.mem_union, not_or]
    refine ⟨⟨hi.1, ?_⟩, ?_⟩
    · rintro hm
      obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hm
      exact hi.2.2 a ha
    · rintro hm
      obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hm
      have hae : (R.equivFin.symm a).val = i := ha
      exact hi.2.1 (hae ▸ (R.equivFin.symm a).property)
  simp only [fromZeros, if_neg hnot]

lemma zero_without_column (k : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    {i : Fin n} (hi : Extra C label R i) (f : BitString n → ℝ)
    (hf : ∀ x, x i = 1 → f x = 0) : value k C label R f = 0 := by
  calc
    _ = value k C label R (fun _ ↦ 0) :=
      value_congr _ _ _ _ _ _ (fun J F ↦ hf _ (constructed_column_one C label R hi J F))
    _ = 0 := value_zero _ _ _ _

lemma zero_with_column (k : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (i : Fin n) (f : BitString n → ℝ) (hf : ∀ x, x i = 0 → f x = 0) :
    value k (insert i C) label R f = 0 := by
  rw [value_insert_common]
  have hzero : (fun x : BitString n ↦ f (Function.update x i 0)) = (fun _ ↦ 0) := by
    funext x
    exact hf _ (Function.update_self _ _ _)
  rw [hzero, value_zero]

lemma mixed_resident_cancellation (k : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n)
    (a0 : α) (R : Finset (Fin n)) (hiC : label a0 ∉ C) (hiR : label a0 ∉ R)
    (f : BitString n → ℝ) (hf : ∀ x, x (label a0) = 1 → f x = 0) :
    2 * value k C label R f = value k C
      ((Function.Embedding.subtype (fun a ↦ a ≠ a0)).trans label) R
      (fun x ↦ f (Function.update x (label a0) 0)) := by
  let smaller := (Function.Embedding.subtype (fun a ↦ a ≠ a0)).trans label
  have hextra : Extra C smaller R (label a0) := by
    refine ⟨hiC, hiR, ?_⟩
    intro a ha
    exact a.property (label.injective ha)
  rw [BirthSplit.split_point, zero_without_column k C smaller R hextra f hf, zero_add,
    value_insert_common]
  ring

lemma mixed_mutant_cancellation (k : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n)
    (a0 : α) (R : Finset (Fin n)) (f : BitString n → ℝ)
    (hf : ∀ x, x (label a0) = 0 → f x = 0) :
    2 * value k C label R f = value k C
      ((Function.Embedding.subtype (fun a ↦ a ≠ a0)).trans label) R f := by
  rw [BirthSplit.split_point, zero_with_column k C _ R (label a0) f hf, add_zero]
  ring

end
end Lax343628Proofs.ColumnSlotSplit

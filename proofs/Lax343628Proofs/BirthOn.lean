import Lax343628Proofs.PhysicalSlotLaw

namespace Lax343628Proofs.BirthOn

open Lax343628.Algorithm Lax343628Proofs.NamedBirth
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.SlotBirth Lax343628Proofs.CountStatistics
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def value {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (k : ℕ) (C : Finset (Fin n))
    (label : α ↪ Fin n) (R : Finset (Fin n)) (h : BitString n → ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ Fintype.card α * ∑ J : Finset α, poissonMean k (fun w ↦
    mean (freshLaw (Fin R.card) w) (fun F ↦
      h (fromZeros (C ∪ J.map label ∪ F.map (freshEmbedding R)))))

lemma reindex {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {n : ℕ} (k : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n) (label' : β ↪ Fin n)
    (e : α ≃ β) (he : ∀ a, label' (e a) = label a) (R : Finset (Fin n)) (h : BitString n → ℝ) :
    value k C label' R h = value k C label R h := by
  have hemb : e.toEmbedding.trans label' = label := Function.Embedding.ext he
  unfold value
  rw [← Fintype.card_congr e, ← Equiv.sum_comp e.finsetCongr]
  apply congrArg ((1 / 2 : ℝ) ^ Fintype.card α * ·)
  apply Finset.sum_congr rfl
  intro J _
  simp only [Equiv.finsetCongr_apply, Finset.map_map, hemb]

lemma physicalChild_disjSum {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (J : Finset (Differing R x y)) (F : Finset (Fin R.card)) :
    physicalChild R x y (J.disjSum F) = fromZeros
      ((Sampling.zeros x ∩ Sampling.zeros y) ∪ J.map (differingEmbedding R x y) ∪
        F.map (freshEmbedding R)) := by
  unfold physicalChild
  congr 1
  ext j
  simp [Finset.mem_map, birthEmbedding, Sum.exists]

lemma ideal_value {n k : ℕ} (R : Finset (Fin n)) (hk : k ≤ R.card) (x y : BitString n)
    (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1) (h : BitString n → ℝ) :
    GeneralBirthApproximation.idealBirthMean k R x y h =
      value k (Sampling.zeros x ∩ Sampling.zeros y) (differingEmbedding R x y) R h := by
  rw [PhysicalSlotLaw.ideal_eq_birthMean R hk x y hR h]
  unfold birthMean freshMean value
  simp_rw [physicalChild_disjSum]

lemma split_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {n : ℕ} (k : ℕ) (C : Finset (Fin n)) (label : α ⊕ β ↪ Fin n)
    (R : Finset (Fin n)) (h : BitString n → ℝ) :
    value k C label R h = (1 / 2 : ℝ) ^ Fintype.card β *
      ∑ B : Finset β, value k (C ∪ B.map (Function.Embedding.inr.trans label))
        (Function.Embedding.inl.trans label) R h := by
  unfold value
  rw [Fintype.card_sum, pow_add, ← Equiv.sum_comp Finset.sumEquiv.symm.toEquiv, Fintype.sum_prod_type,
    Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro J _
  have hsets (F : Finset (Fin R.card)) :
      C ∪ (J.disjSum B).map label ∪ F.map (freshEmbedding R) =
        (C ∪ B.map (Function.Embedding.inr.trans label)) ∪
          J.map (Function.Embedding.inl.trans label) ∪ F.map (freshEmbedding R) := by
    ext j
    simp [Finset.mem_map, Sum.exists, or_assoc, or_left_comm]
  have hJB : Finset.sumEquiv.symm.toEquiv (J, B) = J.disjSum B := rfl
  rw [hJB]
  simp_rw [hsets]
  ring

end
end Lax343628Proofs.BirthOn

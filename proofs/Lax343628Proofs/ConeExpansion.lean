import Lax343628Proofs.MeanCone
import Lax343628Proofs.QuarterCone
import Lax343628Proofs.BirthSplit
import Lax343628Proofs.ColumnSlotSplit

namespace Lax343628Proofs.ConeExpansion

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.NamedBirth
open Lax343628Proofs.BirthGeometry Lax343628Proofs.BirthCouplings
open Lax343628Proofs.ColumnSlotSplit Lax343628Proofs.ShadowMeans
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

def setValue (K : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (h : Finset (Fin n) → ℝ) : ℝ := BirthOn.value K C label R (fun x ↦ h (zeros x))

lemma normalized {r K : ℕ} (hr : r ≤ K) (C : Finset (Fin n)) (label : α ↪ Fin n)
    (R : Finset (Fin n)) (hA : Admissible C label R) (hC : C.card ≤ r) (hK : K ≤ R.card)
    (h : Finset (Fin n) → ℝ) (hzero : ∀ Z, Z.card ≠ r → h Z = 0) :
    setValue K C label R h = mass r C label *
      expect C label R hA.named_fresh (r - C.card) h := by
  unfold setValue
  rw [value_fixed_size_general hr C label R hA hC hK _ (fun x hx ↦ hzero (zeros x) hx)]
  simp only [zeros_fromZeros]
  rfl

lemma zero_large_common {r K : ℕ} (C : Finset (Fin n)) (label : α ↪ Fin n)
    (R : Finset (Fin n)) (hC : r < C.card) (h : Finset (Fin n) → ℝ)
    (hzero : ∀ Z, Z.card ≠ r → h Z = 0) : setValue K C label R h = 0 := by
  unfold setValue
  calc
    _ = BirthOn.value K C label R (fun _ ↦ 0) := by
      apply value_congr
      intro J F
      rw [zeros_fromZeros]
      apply hzero
      have hsub : C ⊆ C ∪ J.map label ∪ F.map (freshEmbedding R) := by
        intro j hjC
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hjC)))
      have hcard := Finset.card_le_card hsub
      omega
    _ = 0 := value_zero _ _ _ _

omit [DecidableEq α] in
lemma same_card_mass (r : ℕ) (C D : Finset (Fin n)) (hCD : C.card = D.card) (label : α ↪ Fin n) :
    mass r C label = mass r D label := by simp only [mass, hCD]

omit [Fintype α] [DecidableEq α] in
lemma left_admissible (C : Finset (Fin n)) (label : α ⊕ Fin 2 ↪ Fin n)
    (R : Finset (Fin n)) (hA : Admissible C label R) :
    Admissible C (Function.Embedding.inl.trans label) R :=
  ⟨fun a ↦ hA.named_fresh (Sum.inl a), fun a ↦ hA.named_common (Sum.inl a), hA.common_fresh⟩

omit [Fintype α] [DecidableEq α] in
lemma two_extras (C : Finset (Fin n)) (label : α ⊕ Fin 2 ↪ Fin n)
    (R : Finset (Fin n)) (hA : Admissible C label R) :
    Extra C (Function.Embedding.inl.trans label) R (label (Sum.inr 0)) ∧
      Extra C (Function.Embedding.inl.trans label) R (label (Sum.inr 1)) ∧
        label (Sum.inr 0) ≠ label (Sum.inr 1) := by
  refine ⟨⟨hA.named_common _, hA.named_fresh _, ?_⟩,
    ⟨hA.named_common _, hA.named_fresh _, ?_⟩, ?_⟩
  · intro a ha
    have heq : (Sum.inl a : α ⊕ Fin 2) = Sum.inr 0 := label.injective ha
    cases heq
  · intro a ha
    have heq : (Sum.inl a : α ⊕ Fin 2) = Sum.inr 1 := label.injective ha
    cases heq
  · intro ha
    have heq := label.injective ha
    have hfin : (0 : Fin 2) = 1 := Sum.inr.inj heq
    exact (by decide : (0 : Fin 2) ≠ 1) hfin

omit [DecidableEq α] in
lemma four_masses (C : Finset (Fin n)) (label : α ⊕ Fin 2 ↪ Fin n)
    (e g : Fin n) (he : e ∉ C) (hg : g ∉ C) (heg : e ≠ g) (j : ℕ) :
    mass (C.card + j + 1) C label = (1 / 4 : ℝ) *
      (mass (C.card + j + 1) C (Function.Embedding.inl.trans label) +
        2 * mass (C.card + j + 1) (insert e C) (Function.Embedding.inl.trans label) +
        (if j = 0 then 0 else mass (C.card + j + 1) (insert e (insert g C))
          (Function.Embedding.inl.trans label))) := by
  have heG : e ∉ insert g C := by simp [heg, he]
  unfold mass
  rw [Fintype.card_sum, Fintype.card_fin, Finset.card_insert_of_notMem he,
    Finset.card_insert_of_notMem heG, Finset.card_insert_of_notMem hg,
    show C.card + j + 1 - C.card = j + 1 by omega,
    show C.card + j + 1 - (C.card + 1) = j by omega,
    show C.card + j + 1 - (C.card + 1 + 1) = j - 1 by omega,
    pow_add, SlotProfiles.beta_pascal_twice_at]
  by_cases hj : j = 0 <;> simp only [hj, if_true, if_false] <;> ring

end
end Lax343628Proofs.ConeExpansion

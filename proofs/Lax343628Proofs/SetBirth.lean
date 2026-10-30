import Lax343628Proofs.BalancedCone
import Lax343628Proofs.AsymmetricCone
import Lax343628Proofs.PrivatePool

namespace Lax343628Proofs.SetBirth

open Lax343628.Algorithm Lax343628Proofs.ConeExpansion
open Lax343628Proofs.BirthGeometry Lax343628Proofs.BirthCouplings
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def differing (X U : Finset (Fin n)) : Finset (Fin n) := (X \ U) ∪ (U \ X)

def value (K : ℕ) (X U R : Finset (Fin n)) (h : Finset (Fin n) → ℝ) : ℝ :=
  setValue K (X ∩ U) (Function.Embedding.subtype (· ∈ differing X U)) R h

lemma mem_differing {X U : Finset (Fin n)} {a : Fin n} :
    a ∈ differing X U ↔ (a ∈ X ∧ a ∉ U) ∨ (a ∈ U ∧ a ∉ X) := by
  simp [differing]

lemma card_balance (X U : Finset (Fin n)) :
    (differing X U).card + 2 * (X ∩ U).card = X.card + U.card := by
  have hd : Disjoint (X \ U) (U \ X) := by
    simp only [Finset.disjoint_left, Finset.mem_sdiff]
    tauto
  rw [differing, Finset.card_union_of_disjoint hd, Finset.card_sdiff, Finset.card_sdiff,
    Finset.inter_comm U X]
  have hX := Finset.card_le_card (Finset.inter_subset_left (s₁ := X) (s₂ := U))
  have hU := Finset.card_le_card (Finset.inter_subset_right (s₁ := X) (s₂ := U))
  omega

lemma relabel {α : Type*} [Fintype α] [DecidableEq α] (K : ℕ)
    (C D : Finset (Fin n)) (l : α ↪ Fin n) (hl : ∀ x, x ∈ D ↔ ∃ a, l a = x)
    (R : Finset (Fin n)) (h : Finset (Fin n) → ℝ) :
    setValue K C (Function.Embedding.subtype (· ∈ D)) R h = setValue K C l R h := by
  let f : α → D := fun a ↦ ⟨l a, (hl _).mpr ⟨a, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact l.injective (congrArg Subtype.val hab)
    · intro x
      obtain ⟨a, ha⟩ := (hl x.val).mp x.property
      exact ⟨a, Subtype.ext ha⟩
  exact BirthOn.reindex K C l (Function.Embedding.subtype (· ∈ D))
    (Equiv.ofBijective f hf) (fun _ ↦ rfl) R _

lemma admissible (X U R : Finset (Fin n)) (hXR : Disjoint X R) (hUR : Disjoint U R) :
    Admissible (X ∩ U) (Function.Embedding.subtype (· ∈ differing X U)) R := by
  constructor
  · intro a ha
    rcases mem_differing.mp a.property with hx | hu
    · exact Finset.disjoint_left.mp hXR hx.1 ha
    · exact Finset.disjoint_left.mp hUR hu.1 ha
  · intro a ha
    have hi := Finset.mem_inter.mp ha
    rcases mem_differing.mp a.property with hx | hu
    · exact hx.2 hi.2
    · exact hu.2 hi.1
  · exact hXR.mono_left Finset.inter_subset_left

lemma column_extra (X U R : Finset (Fin n)) (i : Fin n)
    (hiX : i ∉ X) (hiU : i ∉ U) (hiR : i ∉ R) :
    Extra (X ∩ U) (Function.Embedding.subtype (· ∈ differing X U)) R i := by
  refine ⟨by simp [hiX], hiR, ?_⟩
  intro a hai
  have hm : i ∈ differing X U := hai ▸ a.property
  simp [mem_differing, hiX, hiU] at hm

lemma map_differing (X U : Finset (Fin n)) (p : Equiv.Perm (Fin n)) :
    differing (X.map p.toEmbedding) (U.map p.toEmbedding) =
      (differing X U).map p.toEmbedding := by
  simp only [differing, Finset.map_sdiff, Finset.map_union]

lemma rename (K : ℕ) (X U R : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (h : Finset (Fin n) → ℝ) :
    value K (X.map p.toEmbedding) (U.map p.toEmbedding) R h =
      setValue K ((X ∩ U).map p.toEmbedding)
        ((Function.Embedding.subtype (· ∈ differing X U)).trans p.toEmbedding) R h := by
  unfold value
  rw [← Finset.map_inter]
  apply relabel
  intro x
  rw [map_differing, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨⟨a, ha⟩, he⟩
  · rintro ⟨a, he⟩
    exact ⟨a.val, a.property, he⟩

lemma private_differing (i : Fin n) (x y : BitString n) (a : Fin n) :
    a ∈ differing ((Sampling.zeros x).erase i) ((Sampling.zeros y).erase i) ↔
      a ≠ i ∧ x a ≠ y a := by
  simp only [mem_differing, Finset.mem_erase, Sampling.mem_zeros]
  by_cases hai : a = i
  · simp [hai]
  · have hx : x a = 0 ∨ x a = 1 := by have h := (x a).isLt; omega
    have hy : y a = 0 ∨ y a = 1 := by have h := (y a).isLt; omega
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hai, hx, hy]

lemma private_formula (K : ℕ) (i : Fin n) (x y : BitString n) (R : Finset (Fin n))
    (f : BitString n → ℝ) :
    BirthOn.value K (PrivatePool.common i x y) (PrivatePool.label i x y) R f =
      value K ((Sampling.zeros x).erase i) ((Sampling.zeros y).erase i) R
        (fun Z ↦ f (NamedBirth.fromZeros Z)) := by
  have hRange (a : Fin n) :
      a ∈ differing ((Sampling.zeros x).erase i) ((Sampling.zeros y).erase i) ↔
        ∃ z, PrivatePool.label i x y z = a := by
    rw [private_differing]
    constructor
    · intro ha; exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨z, rfl⟩; exact z.property
  unfold value
  rw [relabel K _ _ _ hRange]
  simp only [setValue, NamedBirth.fromZeros_zeros, PrivatePool.common_eq_inter]

end
end Lax343628Proofs.SetBirth

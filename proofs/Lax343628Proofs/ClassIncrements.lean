import Lax343628Proofs.ClassChannels

namespace Lax343628Proofs.ClassIncrements

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.TaggedDynamics Lax343628Proofs.ClassChannels
open Lax343628Proofs.PlateauDynamics Lax343628Proofs.Deletion
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def immigration (k : ℕ) (i : Fin n) (P : Population n μ) (E : Event n μ) : Prop :=
  ¬parentsHave i 1 P E.1 ∧ E.2.1 i = 1 ∧ deletedHave i 0 P E.2.2 ∧ onPlateau k E.2.1

def change (k : ℕ) (ψ : BitString n → ℝ) (P : Population n μ) (E : Event n μ) : ℝ :=
  total ψ (next k P E) - total ψ P

def nonImmChange (k : ℕ) (i : Fin n) (ψ : BitString n → ℝ) (P : Population n μ) (E : Event n μ) : ℝ :=
  if immigration k i P E then 0 else change k ψ P E

lemma change_last (ψ : BitString n → ℝ) (P : Population n μ)
    (uv : Fin (μ : ℕ) × Fin (μ : ℕ)) (z : BitString n) :
    change k ψ P (uv, z, Fin.last (μ : ℕ)) = 0 := by
  unfold change next
  split_ifs
  · exact total_replace_last ψ P z
  · ring

lemma change_old (ψ : BitString n → ℝ) (P : Population n μ)
    (uv : Fin (μ : ℕ) × Fin (μ : ℕ)) (z : BitString n) (u : Fin (μ : ℕ)) :
    change k ψ P (uv, z, u.castSucc) = if onPlateau k z then ψ z - ψ (P u) else 0 := by
  unfold change next
  split_ifs
  · exact total_replace_castSucc ψ P z u
  · ring

lemma change_abs (ψ : BitString n → ℝ) (M : ℝ) (hh : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ M)
    (P : Population n μ) (E : Event n μ) : |change k ψ P E| ≤ M := by
  obtain ⟨uv, z, d⟩ := E
  refine Fin.lastCases ?_ (fun u ↦ ?_) d
  · rw [change_last, abs_zero]
    exact (hh z).1.trans (hh z).2
  · rw [change_old]
    split_ifs
    · rw [abs_le]
      constructor <;> linarith [hh z, hh (P u)]
    · simpa using (hh z).1.trans (hh z).2

lemma nonImm_abs (i : Fin n) (ψ : BitString n → ℝ) (M : ℝ)
    (hh : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ M) (P : Population n μ) (E : Event n μ) :
    |nonImmChange k i ψ P E| ≤ M := by
  unfold nonImmChange
  split_ifs
  · simpa using (hh E.2.1).1.trans (hh E.2.1).2
  · exact change_abs ψ M hh P E

lemma mutant_off_channel (i : Fin n) (ψ : BitString n → ℝ)
    (hψ : ∀ x, x i ≠ 1 → ψ x = 0) (P : Population n μ) (E : Event n μ)
    (hC : ¬channel i 1 P E) : nonImmChange k i ψ P E = 0 := by
  unfold nonImmChange
  split_ifs with himm
  · rfl
  · obtain ⟨uv, z, d⟩ := E
    revert himm hC
    refine Fin.lastCases ?_ (fun u ↦ ?_) d
    · intro _ _; exact change_last ψ P uv z
    · intro hC himm
      rw [change_old]
      split_ifs with hz
      · have hnotdel : P u i ≠ 1 := by
          intro hu
          exact hC (Or.inr ⟨u, rfl, hu⟩)
        have hnotparent : ¬parentsHave i 1 P uv := fun h ↦ hC (Or.inl h)
        have hchild : z i ≠ 1 := by
          intro hzi
          have hdel0 : P u i = 0 := by have ht := (P u i).isLt; omega
          exact himm ⟨hnotparent, hzi, ⟨u, rfl, hdel0⟩, hz⟩
        rw [hψ z hchild, hψ (P u) hnotdel, sub_self]
      · rfl

lemma resident_off_channel (i : Fin n) (ψ : BitString n → ℝ)
    (hψ : ∀ x, x i ≠ 0 → ψ x = 0) (P : Population n μ) (E : Event n μ)
    (hC : ¬residentChannel i P E) : change k ψ P E = 0 := by
  obtain ⟨uv, z, d⟩ := E
  revert hC
  refine Fin.lastCases ?_ (fun u ↦ ?_) d
  · intro _; exact change_last ψ P uv z
  · intro hC
    rw [change_old]
    split_ifs with hz
    · have hnotdel : P u i ≠ 0 := by
        intro hu
        exact hC (Or.inl (Or.inr ⟨u, rfl, hu⟩))
      have hnotparent : ¬parentsHave i 0 P uv := fun h ↦ hC (Or.inl (Or.inl h))
      have hfirst : P uv.1 i = 1 := by
        have hne : P uv.1 i ≠ 0 := fun hh ↦ hnotparent (Or.inl hh)
        have ht := (P uv.1 i).isLt
        omega
      have hsecond : P uv.2 i = 1 := by
        have hne : P uv.2 i ≠ 0 := fun hh ↦ hnotparent (Or.inr hh)
        have ht := (P uv.2 i).isLt
        omega
      have hchild : z i ≠ 0 := fun hzi ↦ hC (Or.inr ⟨hfirst, hsecond, hzi⟩)
      rw [hψ z hchild, hψ (P u) hnotdel, sub_self]
    · rfl

lemma resident_nonImm_off_channel (i : Fin n) (ψ : BitString n → ℝ)
    (hψ : ∀ x, x i ≠ 0 → ψ x = 0) (P : Population n μ) (E : Event n μ)
    (hC : ¬residentChannel i P E) : nonImmChange k i ψ P E = 0 := by
  unfold nonImmChange
  split_ifs
  · rfl
  · exact resident_off_channel i ψ hψ P E hC

end
end Lax343628Proofs.ClassIncrements

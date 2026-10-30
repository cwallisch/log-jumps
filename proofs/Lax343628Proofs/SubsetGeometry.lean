import Lax343628Proofs.UniformSubsets

namespace Lax343628Proofs.SubsetGeometry

open Lax343628Proofs.UniformSubsets
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}

def distance (X Y : Rank α r) : ℕ := (X.val \ Y.val).card

lemma distance_symm (X Y : Rank α r) : distance X Y = distance Y X :=
  Finset.card_sdiff_comm (X.property.trans Y.property.symm)

lemma distance_zero_iff (X Y : Rank α r) : distance X Y = 0 ↔ X = Y := by
  constructor
  · intro h
    have hsub := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h)
    exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [X.property, Y.property]))
  · rintro rfl
    simp [distance]

lemma distance_le (X Y : Rank α r) : distance X Y ≤ r := by
  exact (Finset.card_le_card Finset.sdiff_subset).trans_eq X.property

lemma exchange_step (X Y : Rank α r) (hXY : X ≠ Y) :
    ∃ Z : Rank α r, distance X Z = 1 ∧ distance Z Y + 1 = distance X Y := by
  have hdist : 0 < distance X Y := Nat.pos_of_ne_zero (mt (distance_zero_iff X Y).mp hXY)
  have hdist' : 0 < distance Y X := by rwa [← distance_symm X Y]
  obtain ⟨e, he⟩ := Finset.card_pos.mp hdist
  obtain ⟨g, hg⟩ := Finset.card_pos.mp hdist'
  have heX : e ∈ X.val := (Finset.mem_sdiff.mp he).1
  have heY : e ∉ Y.val := (Finset.mem_sdiff.mp he).2
  have hgY : g ∈ Y.val := (Finset.mem_sdiff.mp hg).1
  have hgX : g ∉ X.val := (Finset.mem_sdiff.mp hg).2
  have hge : g ≠ e := by intro h; exact hgX (h ▸ heX)
  let Zset := insert g (X.val.erase e)
  have hZcard : Zset.card = r := by
    rw [Finset.card_insert_of_notMem (show g ∉ X.val.erase e from fun h ↦ hgX (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem heX, X.property]
    have hrpos : 0 < r := by rw [← X.property]; exact Finset.card_pos.mpr ⟨e, heX⟩
    omega
  let Z : Rank α r := ⟨Zset, hZcard⟩
  have hXZ : X.val \ Z.val = {e} := by
    ext z
    simp only [Z, Zset, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨hzX, hz⟩
      by_contra hze
      exact hz (Or.inr ⟨hze, hzX⟩)
    · rintro rfl
      exact ⟨heX, by simp [Ne.symm hge]⟩
  have hZY : Z.val \ Y.val = (X.val \ Y.val).erase e := by
    ext z
    simp only [Z, Zset, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hz | hz, hzY⟩
      · subst z
        exact False.elim (hzY hgY)
      · exact ⟨hz.1, hz.2, hzY⟩
    · rintro ⟨hze, hzX, hzY⟩
      exact ⟨Or.inr ⟨hze, hzX⟩, hzY⟩
  refine ⟨Z, ?_, ?_⟩
  · simp only [distance, hXZ, Finset.card_singleton]
  · rw [distance, hZY, Finset.card_erase_of_mem he]
    change distance X Y - 1 + 1 = distance X Y
    omega

lemma cone_power (rho : ℝ) (hrho : 0 ≤ rho) (h : Rank α r → ℝ)
    (hadj : ∀ X Y, distance X Y = 1 → h Y ≤ rho * h X) (X Y : Rank α r) :
    h Y ≤ rho ^ distance X Y * h X := by
  generalize hd : distance X Y = d
  induction d using Nat.strong_induction_on generalizing X Y with
  | h d ih =>
    by_cases hXY : X = Y
    · subst Y
      simp [distance] at hd
      subst d
      simp
    obtain ⟨Z, hXZ, hZY⟩ := exchange_step X Y hXY
    have hlt : distance Z Y < d := by omega
    have hrec := ih (distance Z Y) hlt Z Y rfl
    have hstep := hadj X Z hXZ
    calc
      h Y ≤ rho ^ distance Z Y * h Z := hrec
      _ ≤ rho ^ distance Z Y * (rho * h X) :=
        mul_le_mul_of_nonneg_left hstep (pow_nonneg hrho _)
      _ = rho ^ d * h X := by rw [← hd, ← hZY, pow_succ]; ring

lemma cone_global (rho : ℝ) (hrho : 1 ≤ rho) (h : Rank α r → ℝ)
    (hnonneg : ∀ X, 0 ≤ h X) (hadj : ∀ X Y, distance X Y = 1 → h Y ≤ rho * h X)
    (X Y : Rank α r) : h Y ≤ rho ^ r * h X := by
  exact (cone_power rho (by linarith) h hadj X Y).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hrho (distance_le X Y)) (hnonneg X))

end
end Lax343628Proofs.SubsetGeometry

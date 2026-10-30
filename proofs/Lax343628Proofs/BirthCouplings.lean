import Lax343628Proofs.BirthGeometry

namespace Lax343628Proofs.BirthCouplings

open Lax343628Proofs.BirthGeometry Lax343628Proofs.FiniteExchange
open Lax343628Proofs.FiniteCoupling Lax343628Proofs.PlacedBase
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

def Extra (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n)) (e : Fin n) : Prop :=
  e ∉ C ∧ e ∉ R ∧ ∀ a, label a ≠ e

omit [Fintype α] [DecidableEq α] in
lemma admissible_insert (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) {e : Fin n} (he : Extra C label R e) :
    Admissible (insert e C) label R := by
  refine ⟨hA.named_fresh, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with ha | ha
    · exact he.2.2 a ha
    · exact hA.named_common a ha
  · apply Finset.disjoint_left.mpr
    intro j hj hjR
    rcases Finset.mem_insert.mp hj with hje | hjC
    · subst j
      exact he.2.1 hjR
    · exact Finset.disjoint_left.mp hA.common_fresh hjC hjR

omit [Fintype α] [DecidableEq α] in
lemma extra_insert (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    {e g : Fin n} (he : Extra C label R e) (heg : e ≠ g) : Extra (insert g C) label R e := by
  exact ⟨by simp [heg, he.1], he.2⟩

omit [Fintype α] [DecidableEq α] in
lemma extra_not_realize (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hR : ∀ a, label a ∉ R) {e : Fin n} (he : Extra C label R e)
    (S : Finset (α ⊕ Fin R.card)) : e ∉ realize C label R hR S := by
  intro hm
  rcases Finset.mem_union.mp hm with heC | heS
  · exact he.1 heC
  · obtain ⟨a, _, ha⟩ := Finset.mem_map.mp heS
    cases a with
    | inl a => exact he.2.2 a ha
    | inr a =>
      have hae : (R.equivFin.symm a).val = e := ha
      exact he.2.1 (hae ▸ (R.equivFin.symm a).property)

def nestedCoupling (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hR : ∀ a, label a ∉ R) (j : ℕ) :
    Coupling
      ((placedLaw (α := α) (β := Fin R.card) j).map (realize C label R hR))
      ((placedLaw (α := α) (β := Fin R.card) (j + 1)).map (realize C label R hR)) :=
  map (placedCoupling j) (realize C label R hR) (realize C label R hR)

lemma nestedCoupling_support (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) {j : ℕ} (hj : j + 1 ≤ R.card)
    (U V : Finset (Fin n)) (h : 0 < (nestedCoupling C label R hA.named_fresh j).mass U V) :
    U ⊆ V ∧ U.card = C.card + j ∧ V.card = C.card + j + 1 := by
  obtain ⟨S, T, hS, hT, hpos⟩ := map_support _ _ _ U V h
  have hnest := placedCoupling_support (by simpa using hj) S T hpos
  have hsub : realize C label R hA.named_fresh S ⊆ realize C label R hA.named_fresh T := by
    unfold realize
    exact Finset.union_subset_union (Finset.Subset.refl C) (Finset.map_subset_map.mpr hnest.1)
  have hSc := realize_card C label R hA S
  have hTc := realize_card C label R hA T
  rw [hnest.2.1] at hSc
  rw [hnest.2.2.1] at hTc
  exact ⟨hS ▸ hT ▸ hsub, hS ▸ hSc, hT ▸ hTc⟩

lemma nestedCoupling_avoids (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hR : ∀ a, label a ∉ R) {i : Fin n} (hi : Extra C label R i) (j : ℕ)
    (U V : Finset (Fin n)) (h : 0 < (nestedCoupling C label R hR j).mass U V) : i ∉ U ∧ i ∉ V := by
  obtain ⟨S, T, hS, hT, _⟩ := map_support _ _ _ U V h
  exact ⟨hS ▸ extra_not_realize C label R hR hi S, hT ▸ extra_not_realize C label R hR hi T⟩

def exchangeCoupling (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hR : ∀ a, label a ∉ R) (e : Fin n) (j : ℕ) :
    Coupling
      ((placedLaw (α := α) (β := Fin R.card) j).map (fun S ↦ insert e (realize C label R hR S)))
      ((placedLaw (α := α) (β := Fin R.card) (j + 1)).map (realize C label R hR)) :=
  map (placedCoupling j) (fun S ↦ insert e (realize C label R hR S)) (realize C label R hR)

lemma exchangeCoupling_support (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) {e : Fin n} (he : Extra C label R e) {j : ℕ} (hj : j + 1 ≤ R.card)
    (U V : Finset (Fin n)) (h : 0 < (exchangeCoupling C label R hA.named_fresh e j).mass U V) :
    Near U V ∧ U.card = C.card + j + 1 ∧ V.card = C.card + j + 1 := by
  obtain ⟨S, T, hS, hT, hpos⟩ := map_support _ _ _ U V h
  have hnest := placedCoupling_support (by simpa using hj) S T hpos
  have hsub : realize C label R hA.named_fresh S ⊆ realize C label R hA.named_fresh T := by
    unfold realize
    exact Finset.union_subset_union (Finset.Subset.refl C) (Finset.map_subset_map.mpr hnest.1)
  have hSc := realize_card C label R hA S
  have hTc := realize_card C label R hA T
  rw [hnest.2.1] at hSc
  rw [hnest.2.2.1] at hTc
  have heS := extra_not_realize C label R hA.named_fresh he S
  have hnear := near_insert_nested hsub (by omega) e heS
  have hUc : U.card = C.card + j + 1 := by rw [← hS, Finset.card_insert_of_notMem heS, hSc]
  exact ⟨hS ▸ hT ▸ hnear, hUc, hT ▸ hTc⟩

def doubleCoupling (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hR : ∀ a, label a ∉ R) (e g : Fin n) (j : ℕ) :
    Coupling
      ((placedLaw (α := α) (β := Fin R.card) (j + 1)).map (fun T ↦ insert e (realize C label R hR T)))
      ((placedLaw (α := α) (β := Fin R.card) j).map
        (fun S ↦ insert e (insert g (realize C label R hR S)))) :=
  map (reverse (placedCoupling j)) (fun T ↦ insert e (realize C label R hR T))
    (fun S ↦ insert e (insert g (realize C label R hR S)))

lemma doubleCoupling_support (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) {e g : Fin n} (he : Extra C label R e) (hg : Extra C label R g)
    (heg : e ≠ g) {j : ℕ} (hj : j + 1 ≤ R.card)
    (U V : Finset (Fin n)) (h : 0 < (doubleCoupling C label R hA.named_fresh e g j).mass U V) :
    Near U V := by
  obtain ⟨T, S, hT, hS, hpos⟩ := map_support _ _ _ U V h
  change 0 < (placedCoupling j).mass S T at hpos
  have hnest := placedCoupling_support (by simpa using hj) S T hpos
  have hsub : realize C label R hA.named_fresh S ⊆ realize C label R hA.named_fresh T := by
    unfold realize
    exact Finset.union_subset_union (Finset.Subset.refl C) (Finset.map_subset_map.mpr hnest.1)
  have hSc := realize_card C label R hA S
  have hTc := realize_card C label R hA T
  rw [hnest.2.1] at hSc
  rw [hnest.2.2.1] at hTc
  have hgS := extra_not_realize C label R hA.named_fresh hg S
  have hnear := near_insert_nested hsub (by omega) g hgS
  have heT := extra_not_realize C label R hA.named_fresh he T
  have heS := extra_not_realize C label R hA.named_fresh he S
  have heGS : e ∉ insert g (realize C label R hA.named_fresh S) := by simp [heg, heS]
  have hboth := near_common_insert hnear e heGS heT
  exact hT ▸ hS ▸ near_symm hboth

end
end Lax343628Proofs.BirthCouplings

import Lax343628Proofs.SetBirth
import Lax343628Proofs.ShadowBirth
import Lax343628Proofs.ShadowGaps

namespace Lax343628Proofs.ShadowParent

open Lax343628Proofs.SetBirth Lax343628Proofs.ConeExpansion
open Lax343628Proofs.BirthGeometry Lax343628Proofs.BirthCouplings
open Lax343628Proofs.ShadowGaps Lax343628Proofs.CurveBounds
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def pointLabel (D : Finset (Fin n)) (e : Fin n) (he : e ∉ D) : D ⊕ Unit ↪ Fin n where
  toFun := Sum.elim Subtype.val (fun _ ↦ e)
  inj' := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext hab)
      | inr b =>
        change a.val = e at hab
        exact False.elim (he (hab ▸ a.property))
    | inr a =>
      cases b with
      | inl b =>
        change e = b.val at hab
        exact False.elim (he (hab.symm ▸ b.property))
      | inr b => congr 1

lemma pointLabel_range (D : Finset (Fin n)) (e : Fin n) (he : e ∉ D) (x : Fin n) :
    x ∈ insert e D ↔ ∃ a, pointLabel D e he a = x := by
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨Sum.inr (), rfl⟩
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    cases a with
    | inl a => exact Finset.mem_insert_of_mem a.property
    | inr a => exact Finset.mem_insert_self _ _

lemma outside_geometry (A U : Finset (Fin n)) {e : Fin n} (heA : e ∉ A) (heU : e ∉ U) :
    insert e A ∩ U = A ∩ U ∧ differing (insert e A) U = insert e (differing A U) ∧
      e ∉ differing A U := by
  refine ⟨?_, ?_, by simp [mem_differing, heA, heU]⟩
  · ext x
    simp only [Finset.mem_insert, Finset.mem_inter]
    by_cases hxe : x = e <;> simp_all
  · ext x
    simp only [mem_differing, Finset.mem_insert]
    by_cases hxe : x = e <;> simp_all

lemma inside_geometry (A U : Finset (Fin n)) {e : Fin n} (heA : e ∉ A) (heU : e ∈ U) :
    insert e A ∩ U = insert e (A ∩ U) ∧
      differing A U = insert e (differing (insert e A) U) ∧
        e ∉ differing (insert e A) U := by
  refine ⟨?_, ?_, by simp [mem_differing, heU]⟩
  · ext x
    simp only [Finset.mem_insert, Finset.mem_inter]
    by_cases hxe : x = e <;> simp_all
  · ext x
    simp only [mem_differing, Finset.mem_insert]
    by_cases hxe : x = e <;> simp_all

lemma mass_profile {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset (Fin n)) (l : α ↪ Fin n) (j : ℕ) :
    mass (C.card + j) C l = Real.exp (-1) * profile (Fintype.card α) j := by
  simp only [mass, Nat.add_sub_cancel_left, profile]
  ring

lemma differing_empty_iff (A U : Finset (Fin n)) : differing A U = ∅ ↔ A = U := by
  simp only [differing, Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset]
  exact ⟨fun h ↦ Finset.Subset.antisymm h.1 h.2, fun h ↦ by simp [h]⟩

lemma outside {r k K : ℕ} (A U R : Finset (Fin n)) {i e : Fin n}
    (hAcard : A.card = r) (hp : U.card = r ∨ U.card = r + 1) (hrk : r ≤ k) (hk : 1 ≤ k)
    (heA : e ∉ A) (heU : e ∉ U) (heR : e ∉ R) (hAR : Disjoint A R) (hUR : Disjoint U R)
    (hiA : i ∉ A) (hiU : i ∉ U) (hiR : i ∉ R) (hie : i ≠ e)
    (hrK : r + 1 ≤ K) (hK : K ≤ R.card)
    (m g : Finset (Fin n) → ℝ) (hmzero : ∀ Z, Z.card ≠ r + 1 → m Z = 0)
    (hgzero : ∀ Z, Z.card ≠ r → g Z = 0)
    (c L : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hmin : ∀ Z, Z.card = r → i ∉ Z → L ≤ g Z)
    (hdom : ∀ Z W, Z ⊆ W → Z.card = r → W.card = r + 1 → i ∉ W → c * g Z ≤ m W) :
    c * (value K A U R g + (if A = U then 0 else delta k) * L) ≤ value K (insert e A) U R m := by
  let C := A ∩ U
  let D := differing A U
  have geom := outside_geometry A U heA heU
  have heD : e ∉ D := geom.2.2
  let l := pointLabel D e heD
  let j := r - C.card
  have hCr : C.card ≤ r := (Finset.card_le_card Finset.inter_subset_left).trans_eq hAcard
  have hr : C.card + j = r := by omega
  have hjk : j ≤ k := (Nat.sub_le r C.card).trans hrk
  have hv : Fintype.card D = 2 * j ∨ Fintype.card D = 2 * j + 1 := by
    have hb := card_balance A U
    have hd : Fintype.card D = D.card := Fintype.card_coe D
    change D.card + 2 * C.card = A.card + U.card at hb
    omega
  have hnewR : Disjoint (insert e A) R := by simpa using And.intro heR hAR
  have hnewA := SetBirth.admissible (insert e A) U R hnewR hUR
  have hRange (x : Fin n) : x ∈ differing (insert e A) U ↔ ∃ a, l a = x := by
    rw [geom.2.1]
    exact pointLabel_range D e heD x
  have hAll : Admissible C l R := by
    rw [geom.1] at hnewA
    exact ⟨fun a ↦ hnewA.named_fresh ⟨l a, (hRange _).mpr ⟨a, rfl⟩⟩,
      fun a ↦ hnewA.named_common ⟨l a, (hRange _).mpr ⟨a, rfl⟩⟩, hnewA.common_fresh⟩
  have hiAll : Extra C l R i := by
    refine ⟨by simp [C, hiA], hiR, ?_⟩
    intro a hai
    have hm := (hRange i).mpr ⟨a, hai⟩
    simp [mem_differing, hiA, hiU, hie] at hm
  have hOld : value K A U R g = setValue K C (Function.Embedding.inl.trans l) R g := rfl
  have hNew : value K (insert e A) U R m = setValue K C l R m := by
    unfold value
    rw [geom.1]
    exact SetBirth.relabel K C _ l hRange R m
  have hnonneg : 0 ≤ (if A = U then 0 else delta k) := by split_ifs; rfl; exact (delta_pos hk).le
  have hmass0 : mass (C.card + j) C (Function.Embedding.inl.trans l) =
      Real.exp (-1) * profile (Fintype.card D) j := mass_profile _ _ _
  have hmass1 : mass (C.card + j + 1) C (Function.Embedding.inl.trans l) =
      Real.exp (-1) * profile (Fintype.card D) (j + 1) := by
    rw [show C.card + j + 1 = C.card + (j + 1) by omega, mass_profile]
  have hrise : mass (C.card + j) C (Function.Embedding.inl.trans l) ≤
      mass (C.card + j + 1) C (Function.Embedding.inl.trans l) := by
    rw [hmass0, hmass1]
    have hh := outside_nonneg hv
    nlinarith [mul_nonneg (Real.exp_pos (-1)).le hh]
  have hsurplus : (if A = U then 0 else delta k) ≤
      (mass (C.card + j + 1) C (Function.Embedding.inl.trans l) -
        mass (C.card + j) C (Function.Embedding.inl.trans l)) / 2 := by
    rw [hmass0, hmass1, ← mul_sub]
    by_cases hAU : A = U
    · rw [if_pos hAU]
      exact div_nonneg (mul_nonneg (Real.exp_pos (-1)).le (outside_nonneg hv)) (by norm_num)
    · rw [if_neg hAU]
      apply outside_lower hk hjk hv
      by_cases hj : 1 ≤ j
      · exact Or.inl hj
      · right
        rcases hv with hv | hv
        · have hD0 : D.card = 0 := by have hd := Fintype.card_coe D; omega
          exact False.elim (hAU ((differing_empty_iff A U).mp (Finset.card_eq_zero.mp hD0)))
        · exact hv
  rw [hOld, hNew]
  apply ShadowBirth.outside C l R hAll hiAll hK (by omega) m g _ _ c L _ hc hL hnonneg
    _ _ hrise hsurplus
  all_goals first
    | simpa only [hr] using hmzero
    | simpa only [hr] using hgzero
    | simpa only [hr] using hmin
    | simpa only [hr] using hdom

lemma inside {r k K : ℕ} (A U R : Finset (Fin n)) {i e : Fin n}
    (hAcard : A.card = r) (hp : U.card = r ∨ U.card = r + 1) (hrk : r ≤ k) (hk : 1 ≤ k)
    (heA : e ∉ A) (heU : e ∈ U) (_heR : e ∉ R) (hAR : Disjoint A R) (hUR : Disjoint U R)
    (hiA : i ∉ A) (hiU : i ∉ U) (hiR : i ∉ R) (hie : i ≠ e)
    (hrK : r + 1 ≤ K) (hK : K ≤ R.card)
    (m g : Finset (Fin n) → ℝ) (hmzero : ∀ Z, Z.card ≠ r + 1 → m Z = 0)
    (hgzero : ∀ Z, Z.card ≠ r → g Z = 0)
    (c L : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hmin : ∀ Z, Z.card = r → i ∉ Z → L ≤ g Z)
    (hdom : ∀ Z W, Z ⊆ W → Z.card = r → W.card = r + 1 → i ∉ W → c * g Z ≤ m W) :
    c * (value K A U R g + delta k * L) ≤ value K (insert e A) U R m := by
  let C := A ∩ U
  let D := differing (insert e A) U
  have geom := inside_geometry A U heA heU
  have heD : e ∉ D := geom.2.2
  let l := pointLabel D e heD
  let l0 := Function.Embedding.inl.trans l
  let j := r - C.card
  have heC : e ∉ C := by simp [C, heA]
  have hCr : C.card ≤ r := (Finset.card_le_card Finset.inter_subset_left).trans_eq hAcard
  have hr : C.card + j = r := by omega
  have hjk : j ≤ k := (Nat.sub_le r C.card).trans hrk
  have hcc : (insert e C).card = C.card + 1 := Finset.card_insert_of_notMem heC
  have hv : Fintype.card D = 2 * j ∨ Fintype.card D + 1 = 2 * j := by
    have hb := card_balance (insert e A) U
    rw [geom.1, Finset.card_insert_of_notMem heA, hAcard, hcc] at hb
    have hd : Fintype.card D = D.card := Fintype.card_coe D
    change D.card + 2 * (C.card + 1) = r + 1 + U.card at hb
    omega
  have hOldA := SetBirth.admissible A U R hAR hUR
  have hRange (x : Fin n) : x ∈ differing A U ↔ ∃ a, l a = x := by
    rw [geom.2.1]
    exact pointLabel_range D e heD x
  have hAll : Admissible C l R :=
    ⟨fun a ↦ hOldA.named_fresh ⟨l a, (hRange _).mpr ⟨a, rfl⟩⟩,
      fun a ↦ hOldA.named_common ⟨l a, (hRange _).mpr ⟨a, rfl⟩⟩, hOldA.common_fresh⟩
  have hiAll : Extra C l R i := by
    refine ⟨by simp [C, hiA], hiR, ?_⟩
    intro a hai
    have hm := (hRange i).mpr ⟨a, hai⟩
    simp [mem_differing, hiA, hiU] at hm
  have hOld : value K A U R g = setValue K C l R g :=
    SetBirth.relabel K C _ l hRange R g
  have hNew : value K (insert e A) U R m = setValue K (insert e C) l0 R m := by
    unfold value
    rw [geom.1]
    rfl
  have hmass0 : mass (C.card + j) C l0 = Real.exp (-1) * profile (Fintype.card D) j :=
    mass_profile _ _ _
  have hgap := inside_lower hk hjk hv
  have hdel := (delta_pos hk).le
  rw [hOld, hNew]
  by_cases hj : j = 0
  · have hr' : C.card = r := by omega
    have hsurplus : delta k ≤ mass C.card C l0 / 2 := by
      rw [hj, if_pos rfl, sub_zero] at hgap
      have hh : mass C.card C l0 = Real.exp (-1) * profile (Fintype.card D) 0 := by
        simpa only [hj, Nat.add_zero] using hmass0
      rw [hh]
      exact hgap
    apply ShadowBirth.inside_zero C l R hAll hiAll hK (by omega) m g _ _ c L _ hc hL hdel
      _ _ hsurplus
    all_goals first
      | simpa only [hr'] using hmzero
      | simpa only [hr'] using hgzero
      | simpa only [hr'] using hmin
      | simpa only [hr'] using hdom
  · have hj' : 1 ≤ j := by omega
    have hmassPrev : mass (C.card + j) (insert e C) l0 =
        Real.exp (-1) * profile (Fintype.card D) (j - 1) := by
      unfold mass profile
      rw [hcc, show C.card + j - (C.card + 1) = j - 1 by omega]
      ring
    rw [if_neg hj, mul_sub] at hgap
    have hsurplus : delta k ≤ (mass (C.card + j) C l0 - mass (C.card + j) (insert e C) l0) / 2 := by
      rw [hmass0, hmassPrev]
      exact hgap
    have hrise : mass (C.card + j) (insert e C) l0 ≤ mass (C.card + j) C l0 := by
      linarith
    apply ShadowBirth.inside_positive C l R hAll hiAll hj' hK (by omega) m g _ _ c L _ hc hL hdel
      _ _ hrise hsurplus
    all_goals first
      | simpa only [hr] using hmzero
      | simpa only [hr] using hgzero
      | simpa only [hr] using hmin
      | simpa only [hr] using hdom

lemma comparison {r k K : ℕ} (A U R : Finset (Fin n)) {i e : Fin n}
    (hAcard : A.card = r) (hp : U.card = r ∨ U.card = r + 1) (hrk : r ≤ k) (hk : 1 ≤ k)
    (heA : e ∉ A) (heR : e ∉ R) (hAR : Disjoint A R) (hUR : Disjoint U R)
    (hiA : i ∉ A) (hiU : i ∉ U) (hiR : i ∉ R) (hie : i ≠ e)
    (hrK : r + 1 ≤ K) (hK : K ≤ R.card)
    (m g : Finset (Fin n) → ℝ) (hmzero : ∀ Z, Z.card ≠ r + 1 → m Z = 0)
    (hgzero : ∀ Z, Z.card ≠ r → g Z = 0)
    (c L : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hmin : ∀ Z, Z.card = r → i ∉ Z → L ≤ g Z)
    (hdom : ∀ Z W, Z ⊆ W → Z.card = r → W.card = r + 1 → i ∉ W → c * g Z ≤ m W) :
    c * (value K A U R g + (if A = U then 0 else delta k) * L) ≤ value K (insert e A) U R m := by
  by_cases heU : e ∈ U
  · have hAU : A ≠ U := by intro hEq; exact heA (hEq.symm ▸ heU)
    rw [if_neg hAU]
    exact inside A U R hAcard hp hrk hk heA heU heR hAR hUR hiA hiU hiR hie hrK hK
      m g hmzero hgzero c L hc hL hmin hdom
  · exact outside A U R hAcard hp hrk hk heA heU heR hAR hUR hiA hiU hiR hie hrK hK
      m g hmzero hgzero c L hc hL hmin hdom

end
end Lax343628Proofs.ShadowParent

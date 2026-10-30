import Lax343628Proofs.ParentExchange

namespace Lax343628Proofs.ParentCone

open Lax343628Proofs.SetBirth Lax343628Proofs.ParentExchange
open Lax343628Proofs.ConeExpansion Lax343628Proofs.BirthGeometry
open Lax343628Proofs.BirthCouplings Lax343628Proofs.MeanCone
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

lemma asymmetric {r K : ℕ} (S U R : Finset (Fin n)) {i e g : Fin n}
    (heS : e ∉ S) (hgS : g ∉ S) (heU : e ∈ U) (hgU : g ∉ U)
    (hsrc : (insert e S).card = r)
    (hp : U.card = r ∨ U.card = r + 1 ∨ U.card + 1 = r)
    (hSR : Disjoint S R) (hUR : Disjoint U R) (_heR : e ∉ R) (hgR : g ∉ R)
    (hiS : i ∉ S) (hie : i ≠ e) (hig : i ≠ g) (hiU : i ∉ U) (hiR : i ∉ R)
    (hrK : r ≤ K) (hK : K ≤ R.card) (rho : ℝ) (hrho : 2 ≤ rho)
    (h : Finset (Fin n) → ℝ) (hnonneg : ∀ Z, 0 ≤ h Z)
    (hzero : ∀ Z, Z.card ≠ r → h Z = 0) (hc : Cone i r rho h) :
    value K (insert g S) U R h ≤ rho * value K (insert e S) U R h ∧
      value K (insert e S) U R h ≤ rho * value K (insert g S) U R h := by
  let C := S ∩ U
  let D := differing (insert e S) U
  have geom := asymmetric_geometry S U heS hgS heU hgU
  have heD : e ∉ D := geom.2.2.2.1
  have hgD : g ∉ D := geom.2.2.2.2.1
  have heg : e ≠ g := geom.2.2.2.2.2
  let l := twoLabel D e g heD hgD heg
  have heC : e ∉ C := by simp [C, heS]
  have hcc : C.card + 1 ≤ r := by
    have hh := Finset.card_le_card (Finset.inter_subset_left (s₁ := insert e S) (s₂ := U))
    rw [geom.1, Finset.card_insert_of_notMem heC, hsrc] at hh
    exact hh
  let j := r - C.card - 1
  have hr : C.card + j + 1 = r := by omega
  have hv : Fintype.card D = 2 * j ∨ Fintype.card D = 2 * j + 1 ∨
      Fintype.card D + 1 = 2 * j := by
    have hb := card_balance (insert e S) U
    rw [geom.1, Finset.card_insert_of_notMem heC, hsrc] at hb
    have hD : Fintype.card D = D.card := Fintype.card_coe D
    change D.card + 2 * (C.card + 1) = r + U.card at hb
    omega
  have hnewR : Disjoint (insert g S) R := by simpa using And.intro hgR hSR
  have hnewA := SetBirth.admissible (insert g S) U R hnewR hUR
  have hRange (x : Fin n) : x ∈ differing (insert g S) U ↔ ∃ a, l a = x := by
    rw [geom.2.2.1]
    exact twoLabel_range D e g heD hgD heg x
  have hAll : Admissible C l R := by
    rw [geom.2.1] at hnewA
    refine ⟨fun a ↦ hnewA.named_fresh ⟨l a, (hRange _).mpr ⟨a, rfl⟩⟩,
      fun a ↦ hnewA.named_common ⟨l a, (hRange _).mpr ⟨a, rfl⟩⟩, hnewA.common_fresh⟩
  have hiAll : Extra C l R i := by
    refine ⟨by simp [C, hiS], hiR, ?_⟩
    intro a hai
    have hm : i ∈ differing (insert g S) U := (hRange i).mpr ⟨a, hai⟩
    simp [mem_differing, hiS, hiU, hig] at hm
  have hNew : value K (insert g S) U R h = setValue K C l R h := by
    unfold value
    rw [geom.2.1]
    exact SetBirth.relabel K C _ l hRange R h
  have hOld : value K (insert e S) U R h =
      setValue K (insert (l (Sum.inr 0)) C) (Function.Embedding.inl.trans l) R h := by
    unfold value
    rw [geom.1]
    rfl
  rw [hNew, hOld]
  apply AsymmetricCone.comparison C l R hAll hiAll (by omega) hK hv rho hrho h hnonneg
  · simpa only [hr] using hzero
  · simpa only [hr] using hc

lemma balanced {r K : ℕ} (S U R : Finset (Fin n)) {i e g : Fin n}
    (heS : e ∉ S) (hgS : g ∉ S) (hu : e ∈ U ↔ g ∈ U)
    (hsrc : (insert e S).card = r)
    (hSR : Disjoint S R) (hUR : Disjoint U R) (heR : e ∉ R) (hgR : g ∉ R)
    (hiS : i ∉ S) (hie : i ≠ e) (hig : i ≠ g) (hiU : i ∉ U) (hiR : i ∉ R)
    (hrK : r ≤ K) (hK : K ≤ R.card) (rho : ℝ) (h : Finset (Fin n) → ℝ)
    (hzero : ∀ Z, Z.card ≠ r → h Z = 0) (hc : Cone i r rho h) :
    value K (insert g S) U R h ≤ rho * value K (insert e S) U R h ∧
      value K (insert e S) U R h ≤ rho * value K (insert g S) U R h := by
  have hXR : Disjoint (insert e S) R := by simpa using And.intro heR hSR
  have hA := SetBirth.admissible (insert e S) U R hXR hUR
  have hi := SetBirth.column_extra (insert e S) U R i (by simp [hie, hiS]) hiU hiR
  have hh := BalancedCone.comparison hrK (insert e S ∩ U)
    (Function.Embedding.subtype (· ∈ differing (insert e S) U)) R hA
    (by rw [← hsrc]; exact Finset.card_le_card Finset.inter_subset_left) hK
    hi hie hig heR hgR rho h hzero hc
  have heq : value K (insert g S) U R h =
      setValue K ((insert e S ∩ U).map (Equiv.swap e g).toEmbedding)
        ((Function.Embedding.subtype (· ∈ differing (insert e S) U)).trans
          (Equiv.swap e g).toEmbedding) R h := by
    have hn := SetBirth.rename K (insert e S) U R (Equiv.swap e g) h
    rw [swap_insert S heS hgS, swap_partner U hu] at hn
    exact hn
  rw [heq]
  exact hh

lemma exchange {r K : ℕ} (S U R : Finset (Fin n)) {i e g : Fin n}
    (heS : e ∉ S) (hgS : g ∉ S) (hsrc : (insert e S).card = r)
    (hp : U.card = r ∨ U.card = r + 1 ∨ U.card + 1 = r)
    (hSR : Disjoint S R) (hUR : Disjoint U R) (heR : e ∉ R) (hgR : g ∉ R)
    (hiS : i ∉ S) (hie : i ≠ e) (hig : i ≠ g) (hiU : i ∉ U) (hiR : i ∉ R)
    (hrK : r ≤ K) (hK : K ≤ R.card) (rho : ℝ) (hrho : 2 ≤ rho)
    (h : Finset (Fin n) → ℝ) (hnonneg : ∀ Z, 0 ≤ h Z)
    (hzero : ∀ Z, Z.card ≠ r → h Z = 0) (hc : Cone i r rho h) :
    value K (insert g S) U R h ≤ rho * value K (insert e S) U R h ∧
      value K (insert e S) U R h ≤ rho * value K (insert g S) U R h := by
  by_cases heU : e ∈ U <;> by_cases hgU : g ∈ U
  · exact balanced S U R heS hgS (by simp [heU, hgU]) hsrc
      hSR hUR heR hgR hiS hie hig hiU hiR hrK hK rho h hzero hc
  · exact asymmetric S U R heS hgS heU hgU hsrc hp
      hSR hUR heR hgR hiS hie hig hiU hiR hrK hK rho hrho h hnonneg hzero hc
  · have hsrc' : (insert g S).card = r := by
      rw [Finset.card_insert_of_notMem heS] at hsrc
      rw [Finset.card_insert_of_notMem hgS, hsrc]
    exact (asymmetric S U R hgS heS hgU heU hsrc' hp
      hSR hUR hgR heR hiS hig hie hiU hiR hrK hK rho hrho h hnonneg hzero hc).symm
  · exact balanced S U R heS hgS (by simp [heU, hgU]) hsrc
      hSR hUR heR hgR hiS hie hig hiU hiR hrK hK rho h hzero hc

lemma adjacent_representation (X Y : Finset (Fin n)) (hcard : X.card = Y.card)
    (hstep : (X \ Y).card = 1) :
    ∃ e g, e ∉ X ∩ Y ∧ g ∉ X ∩ Y ∧ X = insert e (X ∩ Y) ∧ Y = insert g (X ∩ Y) := by
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hstep
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp
    (show (Y \ X).card = 1 by rw [Finset.card_sdiff_comm hcard.symm, hstep])
  have heX : e ∈ X ∧ e ∉ Y := Finset.mem_sdiff.mp (by rw [he]; simp)
  have hgY : g ∈ Y ∧ g ∉ X := Finset.mem_sdiff.mp (by rw [hg]; simp)
  refine ⟨e, g, by simp [heX.2], by simp [hgY.2], ?_, ?_⟩
  · ext a
    constructor
    · intro ha
      by_cases haY : a ∈ Y
      · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨ha, haY⟩)
      · have hmem : a ∈ X \ Y := Finset.mem_sdiff.mpr ⟨ha, haY⟩
        rw [he, Finset.mem_singleton] at hmem
        exact Finset.mem_insert.mpr (Or.inl hmem)
    · intro ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact heX.1
      · exact (Finset.mem_inter.mp ha).1
  · ext a
    constructor
    · intro ha
      by_cases haX : a ∈ X
      · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨haX, ha⟩)
      · have hmem : a ∈ Y \ X := Finset.mem_sdiff.mpr ⟨ha, haX⟩
        rw [hg, Finset.mem_singleton] at hmem
        exact Finset.mem_insert.mpr (Or.inl hmem)
    · intro ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hgY.1
      · exact (Finset.mem_inter.mp ha).2

lemma adjacent {r K : ℕ} (X Y U R : Finset (Fin n)) {i : Fin n}
    (hX : X.card = r) (hY : Y.card = r) (hstep : (X \ Y).card = 1)
    (hp : U.card = r ∨ U.card = r + 1 ∨ U.card + 1 = r)
    (hXR : Disjoint X R) (hYR : Disjoint Y R) (hUR : Disjoint U R)
    (hiX : i ∉ X) (hiY : i ∉ Y) (hiU : i ∉ U) (hiR : i ∉ R)
    (hrK : r ≤ K) (hK : K ≤ R.card) (rho : ℝ) (hrho : 2 ≤ rho)
    (h : Finset (Fin n) → ℝ) (hnonneg : ∀ Z, 0 ≤ h Z)
    (hzero : ∀ Z, Z.card ≠ r → h Z = 0) (hc : Cone i r rho h) :
    value K Y U R h ≤ rho * value K X U R h ∧
      value K X U R h ≤ rho * value K Y U R h := by
  obtain ⟨e, g, he, hg, hXe, hYg⟩ := adjacent_representation X Y (hX.trans hY.symm) hstep
  have heX : e ∈ X := by rw [hXe]; simp
  have hgY : g ∈ Y := by rw [hYg]; simp
  have hh := exchange (X ∩ Y) U R he hg (hXe ▸ hX) hp
    (hXR.mono_left Finset.inter_subset_left) hUR
    (Finset.disjoint_left.mp hXR heX) (Finset.disjoint_left.mp hYR hgY)
    (fun hm ↦ hiX (Finset.mem_inter.mp hm).1)
    (fun hei ↦ hiX (hei.symm ▸ heX)) (fun hgi ↦ hiY (hgi.symm ▸ hgY))
    hiU hiR hrK hK rho hrho h hnonneg hzero hc
  simpa only [← hXe, ← hYg] using hh

end
end Lax343628Proofs.ParentCone

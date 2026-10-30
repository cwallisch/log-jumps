import Lax343628Proofs.GeneralBirthApproximation

namespace Lax343628Proofs.NamedBirth

open Lax343628.Algorithm
open Lax343628Proofs.BitProduct Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.SplitBirth Lax343628Proofs.GeneralBirthApproximation
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

abbrev Differing {n : ℕ} (R : Finset (Fin n)) (x y : BitString n) :=
  {j : {j : Fin n // j ∉ R} // x j.val ≠ y j.val}

def outsideFromBits {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (mask : Differing R x y → Fin 2) : {j : Fin n // j ∉ R} → Fin 2 :=
  join (fun j : {j : Fin n // j ∉ R} ↦ x j.val ≠ y j.val)
    mask (fun j ↦ x j.val.val)

lemma outsideLaw_mean {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (f : ({j : Fin n // j ∉ R} → Fin 2) → ℝ) :
    mean (outsideLaw R x y) f = mean (bits (Differing R x y) (1 / 2))
      (fun mask ↦ f (outsideFromBits R x y mask)) := by
  unfold outsideLaw
  have hs := product_split_mean
    (fun j : {j : Fin n // j ∉ R} ↦ if x j = y j then PMF.pure (x j) else coin (1 / 2))
    (fun j ↦ x j.val ≠ y j.val) f
  refine hs.trans ?_
  have hi : (fun j : Differing R x y ↦
      if x j.val = y j.val then PMF.pure (x j.val) else coin (1 / 2)) =
      (fun _ ↦ coin (1 / 2)) := by
    funext j
    simp only [if_neg j.property]
  have ho : (fun j : {j : {j : Fin n // j ∉ R} // ¬x j.val = y j.val → False} ↦
      if x j.val.val = y j.val.val then PMF.pure (x j.val.val) else coin (1 / 2)) =
      (fun j ↦ PMF.pure (x j.val.val)) := by
    funext j
    have heq : x j.val.val = y j.val.val := by
      by_contra hn
      exact j.property hn
    rw [if_pos heq]
  rw [hi, ho, product_pure]
  simp only [mean_pure]
  rfl

lemma fair_flip {ι : Type*} [Fintype ι] :
    (bits ι (1 / 2)).map (fun mask j ↦ 1 - mask j) = bits ι (1 / 2) := by
  have hc : (coin (1 / 2)).map (fun b ↦ 1 - b) = coin (1 / 2) := by
    ext b
    rw [PMF.map_apply, tsum_fintype, Fin.sum_univ_two]
    fin_cases b <;> norm_num [coin]
  have h := map_product ι (fun _ ↦ coin (1 / 2)) (fun _ b ↦ 1 - b)
  simp_rw [hc] at h
  exact h

lemma outsideLaw_zero_mean {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (f : ({j : Fin n // j ∉ R} → Fin 2) → ℝ) :
    mean (outsideLaw R x y) f = mean (bits (Differing R x y) (1 / 2))
      (fun mask ↦ f (outsideFromBits R x y (fun j ↦ 1 - mask j))) := by
  rw [outsideLaw_mean]
  have h := mean_map (bits (Differing R x y) (1 / 2)) (fun mask j ↦ 1 - mask j)
    (fun mask ↦ f (outsideFromBits R x y mask))
  rw [fair_flip] at h
  exact h

def differingEmbedding {n : ℕ} (R : Finset (Fin n)) (x y : BitString n) : Differing R x y ↪ Fin n where
  toFun j := j.val.val
  inj' _ _ hab := Subtype.ext (Subtype.ext hab)

def inheritedSet {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (mask : Differing R x y → Fin 2) : Finset (Fin n) :=
  (Finset.univ.filter (fun j ↦ mask j = 1)).map (differingEmbedding R x y)

lemma mem_inheritedSet {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (mask : Differing R x y → Fin 2) (j : Fin n) :
    j ∈ inheritedSet R x y mask ↔ ∃ hj : j ∉ R, ∃ hd : x j ≠ y j, mask ⟨⟨j, hj⟩, hd⟩ = 1 := by
  simp only [inheritedSet, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, haj⟩
    have hj : j ∉ R := by rw [← haj]; exact a.val.property
    have hd : x j ≠ y j := by rw [← haj]; exact a.property
    refine ⟨hj, hd, ?_⟩
    have heq : a = ⟨⟨j, hj⟩, hd⟩ := Subtype.ext (Subtype.ext haj)
    rwa [← heq]
  · rintro ⟨hj, hd, hm⟩
    exact ⟨⟨⟨j, hj⟩, hd⟩, hm, rfl⟩

def freshEmbedding {n : ℕ} (R : Finset (Fin n)) : Fin R.card ↪ Fin n where
  toFun j := (R.equivFin.symm j).val
  inj' _ _ hab := R.equivFin.symm.injective (Subtype.ext hab)

def freshPositions {n : ℕ} (R : Finset (Fin n)) (mask : BitString R.card) : Finset (Fin n) :=
  (MaskCounts.onesSet mask).map (freshEmbedding R)

lemma mem_freshPositions {n : ℕ} (R : Finset (Fin n)) (mask : BitString R.card) (j : Fin n) :
    j ∈ freshPositions R mask ↔ ∃ hj : j ∈ R, mask (R.equivFin ⟨j, hj⟩) = 1 := by
  constructor
  · intro hj
    obtain ⟨a, ha, haj⟩ := Finset.mem_map.mp hj
    have hjR : j ∈ R := by rw [← haj]; exact (R.equivFin.symm a).property
    refine ⟨hjR, ?_⟩
    have heq : R.equivFin.symm a = ⟨j, hjR⟩ := Subtype.ext haj
    rw [← heq, R.equivFin.apply_symm_apply]
    exact (Finset.mem_filter.mp ha).2
  · rintro ⟨hj, hm⟩
    apply Finset.mem_map.mpr
    refine ⟨R.equivFin ⟨j, hj⟩, by simpa only [MaskCounts.onesSet, Finset.mem_filter,
      Finset.mem_univ, true_and] using hm, ?_⟩
    simp [freshEmbedding]

def child {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (inherited : Differing R x y → Fin 2) (fresh : BitString R.card) : BitString n :=
  freshChild R (outsideFromBits R x y (fun j ↦ 1 - inherited j)) fresh

lemma one_sub_eq_zero (b : Fin 2) : (1 - b = 0) ↔ b = 1 := by fin_cases b <;> decide

lemma child_zeros {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1)
    (inherited : Differing R x y → Fin 2) (fresh : BitString R.card) :
    Sampling.zeros (child R x y inherited fresh) =
      (Sampling.zeros x ∩ Sampling.zeros y) ∪ inheritedSet R x y inherited ∪ freshPositions R fresh := by
  ext j
  simp only [Sampling.mem_zeros, Finset.mem_union, Finset.mem_inter, mem_inheritedSet, mem_freshPositions]
  by_cases hj : j ∈ R
  · have hx := (hR j hj).1
    have hy := (hR j hj).2
    simp [child, freshChild, join, hj, hx, hy, one_sub_eq_zero]
  · by_cases hxy : x j = y j
    · simp [child, freshChild, outsideFromBits, join, hj, hxy]
    · simp [child, freshChild, outsideFromBits, join, hj, hxy, one_sub_eq_zero]
      intro hx hy
      exact False.elim (hxy (hx.trans hy.symm))

def fromZeros {n : ℕ} (S : Finset (Fin n)) : BitString n := fun j ↦ if j ∈ S then 0 else 1

@[simp] lemma zeros_fromZeros {n : ℕ} (S : Finset (Fin n)) : Sampling.zeros (fromZeros S) = S := by
  ext j
  simp [Sampling.mem_zeros, fromZeros]

@[simp] lemma fromZeros_zeros {n : ℕ} (x : BitString n) : fromZeros (Sampling.zeros x) = x := by
  funext j
  by_cases hx : x j = 0
  · simp [fromZeros, Sampling.mem_zeros, hx]
  · have hx1 : x j = 1 := by have hj := (x j).isLt; omega
    simp [fromZeros, Sampling.mem_zeros, hx1]

def birthEmbedding {n : ℕ} (R : Finset (Fin n)) (x y : BitString n) :
    (Differing R x y ⊕ Fin R.card) ↪ Fin n where
  toFun := Sum.elim (differingEmbedding R x y) (freshEmbedding R)
  inj' := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((differingEmbedding R x y).injective hab)
      | inr b =>
        change a.val.val = (R.equivFin.symm b).val at hab
        exact False.elim (a.val.property (by rw [hab]; exact (R.equivFin.symm b).property))
    | inr a =>
      cases b with
      | inl b =>
        change (R.equivFin.symm a).val = b.val.val at hab
        exact False.elim (b.val.property (by rw [← hab]; exact (R.equivFin.symm a).property))
      | inr b => exact congrArg Sum.inr ((freshEmbedding R).injective hab)

def physicalChild {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (S : Finset (Differing R x y ⊕ Fin R.card)) : BitString n :=
  fromZeros ((Sampling.zeros x ∩ Sampling.zeros y) ∪ S.map (birthEmbedding R x y))

lemma child_eq_physicalChild {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1)
    (inherited : Differing R x y → Fin 2) (fresh : BitString R.card) :
    child R x y inherited fresh = physicalChild R x y
      ((Finset.univ.filter (fun j ↦ inherited j = 1)).disjSum (MaskCounts.onesSet fresh)) := by
  rw [← fromZeros_zeros (child R x y inherited fresh), child_zeros R x y hR]
  unfold physicalChild inheritedSet freshPositions
  congr 1
  ext j
  simp [Finset.mem_map, birthEmbedding, Sum.exists]

end
end Lax343628Proofs.NamedBirth

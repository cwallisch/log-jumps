import Lax343628Proofs.BaseRanks

namespace Lax343628Proofs.BaseSubsets

open Lax343628Proofs.FiniteCoupling Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α]

def subsetLaw (r : Fin (Fintype.card α + 1)) : PMF (Finset α) :=
  (UniformSubsets.rankLaw r.val (by omega)).map Subtype.val

lemma subsetLaw_mass (r : Fin (Fintype.card α + 1)) (J : Finset α) :
    (subsetLaw r J).toReal =
      if J.card = r.val then (Fintype.card α |>.choose r.val : ℝ)⁻¹ else 0 := by
  rw [subsetLaw, map_mass]
  by_cases hJ : J.card = r.val
  · rw [if_pos hJ, Finset.sum_eq_single (⟨J, hJ⟩ : UniformSubsets.Rank α r.val)]
    · simp only [ite_true]
      exact UniformSubsets.rankLaw_mass _ _ _
    · intro K _ hK
      have hval : K.val ≠ J := fun h ↦ hK (Subtype.ext h)
      simp only [if_neg hval]
    · simp
  · rw [if_neg hJ]
    apply Finset.sum_eq_zero
    intro K _
    have hval : K.val ≠ J := by intro h; exact hJ (h ▸ K.property)
    simp only [if_neg hval]

lemma subsetLaw_support (r : Fin (Fintype.card α + 1)) (J : Finset α)
    (h : 0 < (subsetLaw r J).toReal) : J.card = r.val := by
  rw [subsetLaw_mass] at h
  split_ifs at h with hJ
  · exact hJ
  · exact False.elim (lt_irrefl _ h)

def subsetCoupling (s t : Fin (Fintype.card α + 1)) :
    Coupling (subsetLaw (α := α) s) (subsetLaw t) := by
  by_cases heq : s = t
  · subst t
    exact identity _
  · by_cases hnext : t.val = s.val + 1
    · have hs : s.val < Fintype.card α := by have ht := t.isLt; omega
      have heqt : t = ⟨s.val + 1, by omega⟩ := Fin.ext hnext
      rw [heqt]
      exact map (UniformSubsets.upperCoupling (α := α) hs) Subtype.val Subtype.val
    · exact independent _ _

lemma subsetCoupling_support (s t : Fin (Fintype.card α + 1))
    (hst : s.val ≤ t.val ∧ t.val ≤ s.val + 1) (J K : Finset α)
    (h : 0 < (subsetCoupling s t).mass J K) :
    J ⊆ K ∧ K.card ≤ J.card + 1 := by
  by_cases heq : s = t
  · subst t
    simp only [subsetCoupling] at h
    change 0 < (if K = J then (subsetLaw s J).toReal else 0) at h
    split_ifs at h with hK
    · subst K
      exact ⟨Finset.Subset.refl _, by omega⟩
    · exact False.elim (lt_irrefl _ h)
  · have hnext : t.val = s.val + 1 := by
      have hne : s.val ≠ t.val := fun he ↦ heq (Fin.ext he)
      omega
    have hs : s.val < Fintype.card α := by have ht := t.isLt; omega
    have heqt : t = ⟨s.val + 1, by omega⟩ := Fin.ext hnext
    have hmap : 0 < (map (UniformSubsets.upperCoupling (α := α) hs) Subtype.val Subtype.val).mass J K := by
      rw [heqt] at h
      simpa [subsetCoupling, show s ≠ (⟨s.val + 1, by omega⟩ : Fin (Fintype.card α + 1)) by
        intro he; have hv := congrArg Fin.val he; simp only at hv; omega] using h
    obtain ⟨JJ, KK, hJ, hK, hpos⟩ := map_support _ _ _ J K hmap
    have hsub := UniformSubsets.upperCoupling_support hs JJ KK hpos
    exact ⟨hJ ▸ hK ▸ hsub.1, by rw [← hJ, ← hK, JJ.property, KK.property]⟩

def baseLaw (j : ℕ) : PMF (Finset α) :=
  (BaseRanks.rankLaw (Fintype.card α) j).bind subsetLaw

def baseWeight (j : ℕ) (J : Finset α) : ℝ :=
  if J.card ≤ j then 1 / ((j - J.card).factorial : ℝ) else 0

lemma baseLaw_mass (j : ℕ) (J : Finset α) :
    (baseLaw j J).toReal = baseWeight j J / BaseRanks.rankMass (Fintype.card α) j := by
  have hc : J.card ≤ Fintype.card α := Finset.card_le_univ J
  let r : Fin (Fintype.card α + 1) := ⟨J.card, by omega⟩
  rw [baseLaw, bind_mass, Finset.sum_eq_single r]
  · rw [subsetLaw_mass, if_pos rfl, BaseRanks.rankLaw_mass]
    have hchoose : (0 : ℝ) < (Fintype.card α).choose J.card := by exact_mod_cast Nat.choose_pos hc
    dsimp [r, baseWeight]
    unfold BaseRanks.rankWeight
    split_ifs <;> field_simp; simp
  · intro s _ hsr
    have hcard : J.card ≠ s.val := by intro he; exact hsr (Fin.ext he.symm)
    rw [subsetLaw_mass, if_neg hcard, mul_zero]
  · simp

lemma baseLaw_support (j : ℕ) (J : Finset α) (h : 0 < (baseLaw j J).toReal) : J.card ≤ j := by
  rw [baseLaw_mass] at h
  by_contra hn
  simp [baseWeight, hn] at h

def baseCoupling (j : ℕ) : Coupling (baseLaw (α := α) j) (baseLaw (α := α) (j + 1)) :=
  bind (BaseRanks.adjacentCoupling (Fintype.card α) j) (subsetLaw (α := α)) subsetLaw subsetCoupling

lemma baseCoupling_support (j : ℕ) (J K : Finset α)
    (h : 0 < (baseCoupling j).mass J K) : J ⊆ K ∧ K.card ≤ J.card + 1 := by
  obtain ⟨s, t, hst, hJK⟩ := bind_support _ _ _ _ J K h
  exact subsetCoupling_support s t (BaseRanks.adjacentCoupling_support _ _ s t hst) J K hJK

lemma baseCoupling_sizes (j : ℕ) (J K : Finset α)
    (h : 0 < (baseCoupling j).mass J K) : J.card ≤ j ∧ K.card ≤ j + 1 := by
  obtain ⟨s, t, hst, hJK⟩ := bind_support _ _ _ _ J K h
  have hstpos := positive_marginals _ s t hst
  have hJKpos := positive_marginals _ J K hJK
  exact ⟨(subsetLaw_support s J hJKpos.1).trans_le
    (BaseRanks.rankLaw_support _ _ s hstpos.1),
    (subsetLaw_support t K hJKpos.2).trans_le
    (BaseRanks.rankLaw_support _ _ t hstpos.2)⟩

end
end Lax343628Proofs.BaseSubsets

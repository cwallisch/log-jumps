import Lax343628Proofs.BaseSubsets
import Mathlib.Data.Finset.Sum

namespace Lax343628Proofs.PlacedBase

open Lax343628Proofs.FiniteCoupling Lax343628Proofs.BaseSubsets
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def freshRank (j : ℕ) (J : Finset α) : Fin (Fintype.card β + 1) :=
  ⟨min (j - J.card) (Fintype.card β), by omega⟩

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
lemma freshRank_val {j : ℕ} (hj : j ≤ Fintype.card β) (J : Finset α) :
    (freshRank (β := β) j J).val = j - J.card := by
  dsimp [freshRank]
  omega

def fillLaw (j : ℕ) (J : Finset α) : PMF (Finset (α ⊕ β)) :=
  (subsetLaw (freshRank (β := β) j J)).map (fun F ↦ J.disjSum F)

def placedLaw (j : ℕ) : PMF (Finset (α ⊕ β)) := (baseLaw j).bind (fillLaw j)

def fillCoupling (j : ℕ) (J K : Finset α) :
    Coupling (fillLaw (β := β) j J) (fillLaw (β := β) (j + 1) K) :=
  map (subsetCoupling (freshRank (β := β) j J) (freshRank (β := β) (j + 1) K))
    (fun F ↦ J.disjSum F) (fun G ↦ K.disjSum G)

def placedCoupling (j : ℕ) :
    Coupling (placedLaw (α := α) (β := β) j) (placedLaw (α := α) (β := β) (j + 1)) :=
  bind (baseCoupling j) (fillLaw j) (fillLaw (j + 1)) (fillCoupling j)

lemma fillCoupling_support {j : ℕ} (hj : j + 1 ≤ Fintype.card β)
    (J K : Finset α) (hJ : J.card ≤ j) (hK : K.card ≤ j + 1)
    (hsub : J ⊆ K) (hstep : K.card ≤ J.card + 1)
    (S T : Finset (α ⊕ β)) (h : 0 < (fillCoupling j J K).mass S T) :
    S ⊆ T ∧ S.card = j ∧ T.card = j + 1 := by
  obtain ⟨F, G, hF, hG, hpos⟩ := map_support _ _ _ S T h
  have hcard : J.card ≤ K.card := Finset.card_le_card hsub
  have hfresh : (freshRank (β := β) j J).val ≤ (freshRank (β := β) (j + 1) K).val ∧
      (freshRank (β := β) (j + 1) K).val ≤ (freshRank (β := β) j J).val + 1 := by
    rw [freshRank_val (by omega), freshRank_val (by omega)]
    omega
  have hFG := subsetCoupling_support _ _ hfresh F G hpos
  have hprob := positive_marginals _ F G hpos
  have hFc := subsetLaw_support _ F hprob.1
  have hGc := subsetLaw_support _ G hprob.2
  rw [freshRank_val (by omega)] at hFc hGc
  have hSc : S.card = j := by rw [← hF, Finset.card_disjSum, hFc]; omega
  have hTc : T.card = j + 1 := by rw [← hG, Finset.card_disjSum, hGc]; omega
  exact ⟨hF ▸ hG ▸ Finset.disjSum_mono hsub hFG.1, hSc, hTc⟩

lemma placedCoupling_support {j : ℕ} (hj : j + 1 ≤ Fintype.card β)
    (S T : Finset (α ⊕ β)) (h : 0 < (placedCoupling j).mass S T) :
    S ⊆ T ∧ S.card = j ∧ T.card = j + 1 ∧ (T \ S).card = 1 := by
  obtain ⟨J, K, hJK, hST⟩ := bind_support _ _ _ _ S T h
  have hsub := baseCoupling_support j J K hJK
  have hsizes := baseCoupling_sizes j J K hJK
  have h := fillCoupling_support hj J K hsizes.1 hsizes.2 hsub.1 hsub.2 S T hST
  exact ⟨h.1, h.2.1, h.2.2, by rw [Finset.card_sdiff_of_subset h.1, h.2.1, h.2.2]; omega⟩

end
end Lax343628Proofs.PlacedBase

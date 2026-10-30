import Lax343628Proofs.FiniteCoupling
import Mathlib.Data.Fintype.Powerset

namespace Lax343628Proofs.UniformSubsets

open Lax343628Proofs.FiniteCoupling
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Rank (α : Type*) [Fintype α] (r : ℕ) := {J : Finset α // J.card = r}

omit [DecidableEq α] in
lemma rank_nonempty {r : ℕ} (hr : r ≤ Fintype.card α) : Nonempty (Rank α r) := by
  obtain ⟨J, hJ⟩ := Finset.powersetCard_nonempty.mpr
    (by simpa only [Finset.card_univ] using hr : r ≤ (Finset.univ : Finset α).card)
  exact ⟨J, (Finset.mem_powersetCard.mp hJ).2⟩

def rankLaw (r : ℕ) (hr : r ≤ Fintype.card α) : PMF (Rank α r) :=
  letI : Nonempty (Rank α r) := rank_nonempty hr
  PMF.uniformOfFintype (Rank α r)

omit [DecidableEq α] in
lemma rankLaw_mass (r : ℕ) (hr : r ≤ Fintype.card α) (J : Rank α r) :
    (rankLaw r hr J).toReal = (Fintype.card α |>.choose r : ℝ)⁻¹ := by
  simp only [rankLaw, PMF.uniformOfFintype_apply, Fintype.card_finset_len,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

omit [DecidableEq α] in
lemma count_rank_filter (r : ℕ) (P : Finset α → Prop) [DecidablePred P] :
    Fintype.card {J : Rank α r // P J.val} =
      (((Finset.univ : Finset α).powersetCard r).filter P).card := by
  let e : {J : Rank α r // P J.val} ≃
      {J : Finset α // J ∈ (((Finset.univ : Finset α).powersetCard r).filter P)} :=
    { toFun := fun J ↦ ⟨J.val.val, by simp only [Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]; exact ⟨J.val.property, J.property⟩⟩
      invFun := fun J ↦ ⟨⟨J.val, (Finset.mem_powersetCard.mp (Finset.mem_filter.mp J.property).1).2⟩,
        (Finset.mem_filter.mp J.property).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr e

lemma upper_neighbors {r : ℕ} (J : Rank α r) :
    Fintype.card {K : Rank α (r + 1) // J.val ⊆ K.val} = Fintype.card α - r := by
  rw [count_rank_filter (r + 1) (fun K ↦ J.val ⊆ K),
    Finset.card_filter_powersetCard_subset J.val Finset.univ (r + 1)
    (Finset.subset_univ _) (by rw [J.property]; omega), Finset.card_univ, J.property]
  simp

lemma lower_neighbors {r : ℕ} (K : Rank α (r + 1)) :
    Fintype.card {J : Rank α r // J.val ⊆ K.val} = r + 1 := by
  rw [count_rank_filter r (fun J ↦ J ⊆ K.val)]
  have heq : (((Finset.univ : Finset α).powersetCard r).filter (fun J ↦ J ⊆ K.val)) =
      K.val.powersetCard r := by
    ext J
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    tauto
  rw [heq, Finset.card_powersetCard, K.property, Nat.choose_succ_self_right]

def upperMass (r : ℕ) (J : Rank α r) (K : Rank α (r + 1)) : ℝ :=
  if J.val ⊆ K.val then
    ((Fintype.card α |>.choose r : ℝ) * ((Fintype.card α - r : ℕ) : ℝ))⁻¹ else 0

def upperCoupling {r : ℕ} (hr : r < Fintype.card α) :
    Coupling (rankLaw r hr.le) (rankLaw (r + 1) (Nat.succ_le_of_lt hr)) where
  mass := upperMass r
  nonneg _ _ := by unfold upperMass; split_ifs <;> positivity
  row J := by
    rw [rankLaw_mass]
    unfold upperMass
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Fintype.card_subtype, upper_neighbors]
    have hchoose : (0 : ℝ) < (Fintype.card α).choose r := by exact_mod_cast Nat.choose_pos hr.le
    have hdiff : (0 : ℝ) < (Fintype.card α - r : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hr
    field_simp
  col K := by
    rw [rankLaw_mass]
    unfold upperMass
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Fintype.card_subtype, lower_neighbors]
    have hchoose : (0 : ℝ) < (Fintype.card α).choose r := by exact_mod_cast Nat.choose_pos hr.le
    have hchoose' : (0 : ℝ) < (Fintype.card α).choose (r + 1) := by
      exact_mod_cast Nat.choose_pos (Nat.succ_le_of_lt hr)
    have hdiff : (0 : ℝ) < (Fintype.card α - r : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hr
    have hidentity : ((Fintype.card α).choose (r + 1) : ℝ) * ((r : ℝ) + 1) =
        ((Fintype.card α).choose r : ℝ) * (Fintype.card α - r : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq (Fintype.card α) r
    field_simp
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith

lemma upperCoupling_support {r : ℕ} (hr : r < Fintype.card α)
    (J : Rank α r) (K : Rank α (r + 1)) (h : 0 < (upperCoupling hr).mass J K) :
    J.val ⊆ K.val ∧ (K.val \ J.val).card = 1 := by
  change 0 < upperMass r J K at h
  unfold upperMass at h
  split_ifs at h with hJK
  · exact ⟨hJK, by rw [Finset.card_sdiff_of_subset hJK, K.property, J.property]; omega⟩
  · exact False.elim (lt_irrefl _ h)

end
end Lax343628Proofs.UniformSubsets

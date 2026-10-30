import Lax343628Proofs.SubsetGeometry

namespace Lax343628Proofs.FiniteExchange

open scoped Classical

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def Near (S T : Finset α) : Prop := S.card = T.card ∧ (S \ T).card ≤ 1

lemma near_symm {S T : Finset α} (h : Near S T) : Near T S := by
  exact ⟨h.1.symm, by rw [Finset.card_sdiff_comm h.1.symm]; exact h.2⟩

lemma near_eq_or_exchange {S T : Finset α} (h : Near S T) :
    S = T ∨ (S \ T).card = 1 := by
  by_cases hz : (S \ T).card = 0
  · exact Or.inl (Finset.eq_of_subset_of_card_le
      (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hz)) h.1.ge)
  · exact Or.inr (by have := h.2; omega)

lemma near_union {S T C : Finset α} (h : Near S T)
    (hCS : Disjoint C S) (hCT : Disjoint C T) : Near (C ∪ S) (C ∪ T) := by
  constructor
  · rw [Finset.card_union_of_disjoint hCS, Finset.card_union_of_disjoint hCT, h.1]
  · have hsub : (C ∪ S) \ (C ∪ T) ⊆ S \ T := by
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hj ⊢
      exact ⟨hj.1.resolve_left hj.2.1, hj.2.2⟩
    exact (Finset.card_le_card hsub).trans h.2

lemma near_swap (S : Finset α) (e g : α) (he : e ∉ S) (hg : g ∉ S) :
    Near (insert e S) (insert g S) := by
  constructor
  · rw [Finset.card_insert_of_notMem he, Finset.card_insert_of_notMem hg]
  · have hsub : insert e S \ insert g S ⊆ {e} := by
      intro j hj
      have hmem := Finset.mem_insert.mp (Finset.mem_sdiff.mp hj).1
      have hnot := (Finset.mem_sdiff.mp hj).2
      exact Finset.mem_singleton.mpr (hmem.resolve_right (fun hjS ↦ hnot (Finset.mem_insert_of_mem hjS)))
    exact (Finset.card_le_card hsub).trans (by simp)

lemma near_insert_nested {S T : Finset α} (hsub : S ⊆ T) (hcard : T.card = S.card + 1)
    (e : α) (he : e ∉ S) : Near (insert e S) T := by
  constructor
  · rw [Finset.card_insert_of_notMem he, hcard]
  · have hsmall : insert e S \ T ⊆ {e} := by
      intro j hj
      have hmem := Finset.mem_insert.mp (Finset.mem_sdiff.mp hj).1
      have hnot := (Finset.mem_sdiff.mp hj).2
      exact Finset.mem_singleton.mpr (hmem.resolve_right (fun hjS ↦ hnot (hsub hjS)))
    exact (Finset.card_le_card hsmall).trans (by simp)

lemma near_common_insert {S T : Finset α} (h : Near S T) (e : α) (heS : e ∉ S) (heT : e ∉ T) :
    Near (insert e S) (insert e T) := by
  have hC := near_union (C := {e}) h (by simpa) (by simpa)
  simpa using hC

end Lax343628Proofs.FiniteExchange

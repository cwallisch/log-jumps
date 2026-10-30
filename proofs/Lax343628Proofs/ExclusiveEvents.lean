import Lax343628Proofs.FiniteEvents

namespace Lax343628Proofs.ExclusiveEvents

open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α ι : Type*} [Fintype α] [Fintype ι]

lemma sum_le_one (p : PMF α) (E : ι → Set α)
    (hunique : ∀ x i j, x ∈ E i → x ∈ E j → i = j) :
    (∑ i, p.toOuterMeasure (E i)) ≤ 1 := by
  simp only [PMF.toOuterMeasure_apply_fintype]
  rw [Finset.sum_comm]
  have hh : (∑ x, ∑ i, (E i).indicator p x) ≤ ∑ x, p x := by
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : ∃ i, x ∈ E i
    · obtain ⟨i, hi⟩ := hx
      rw [Finset.sum_eq_single i]
      · simp only [Set.indicator_of_mem hi, le_refl]
      · intro j _ hji
        have hj : x ∉ E j := fun hj ↦ hji (hunique x j i hj hi)
        exact Set.indicator_of_notMem hj p
      · intro hn
        exact False.elim (hn (Finset.mem_univ i))
    · have hnone : ∀ i, x ∉ E i := by simpa only [not_exists] using hx
      simp only [Set.indicator_of_notMem (hnone _), Finset.sum_const_zero, zero_le]
  apply hh.trans
  simpa only [tsum_fintype] using p.tsum_coe.le

end
end Lax343628Proofs.ExclusiveEvents

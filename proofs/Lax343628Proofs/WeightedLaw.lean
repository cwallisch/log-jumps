import Lax343628Proofs.FiniteOrder

namespace Lax343628Proofs.WeightedLaw

open Lax343628Proofs.FiniteOrder
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def normalized {α : Type*} [Fintype α] (a : α → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hpos : 0 < ∑ x, a x) : PMF α :=
  PMF.ofFintype (fun x ↦ ENNReal.ofReal (a x / ∑ y, a y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ div_nonneg (ha x) hpos.le),
      ← Finset.sum_div, div_self hpos.ne', ENNReal.ofReal_one])

lemma normalized_mass {α : Type*} [Fintype α] (a : α → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hpos : 0 < ∑ x, a x) (x : α) :
    (normalized a ha hpos x).toReal = a x / ∑ y, a y :=
  ENNReal.toReal_ofReal (div_nonneg (ha x) hpos.le)

lemma normalized_cumulative {N : ℕ} (a : Fin N → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hpos : 0 < ∑ x, a x) (r : ℕ) :
    cumulative (normalized a ha hpos) r = lowerSum a r / ∑ x, a x := by
  unfold cumulative lowerSum
  simp_rw [normalized_mass]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < r <;> simp [hi]

lemma likelihood_order {N : ℕ} (a b : Fin N → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hapos : 0 < ∑ x, a x) (hbpos : 0 < ∑ x, b x)
    (horder : ∀ i j, i < j → b i * a j ≤ a i * b j) (r : ℕ) :
    cumulative (normalized b hb hbpos) r ≤ cumulative (normalized a ha hapos) r := by
  rw [normalized_cumulative, normalized_cumulative]
  exact likelihood_cumulative a b hapos hbpos horder r

end
end Lax343628Proofs.WeightedLaw

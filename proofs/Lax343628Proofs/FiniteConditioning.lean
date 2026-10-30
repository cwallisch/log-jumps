import Lax343628Proofs.EmpiricalSampling

namespace Lax343628Proofs.FiniteConditioning

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.FiniteProduct
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

def fill (j : ι) (rest : {k : ι // k ≠ j} → β) (x : β) (k : ι) : β :=
  if hk : k = j then x else rest ⟨k, hk⟩

omit [DecidableEq β] in
lemma coordinate_mean (p : ι → PMF β) (j : ι) (f : (ι → β) → ℝ) :
    mean (distribution p) f =
      mean (distribution (fun k : {k : ι // k ≠ j} ↦ p k)) (fun rest ↦
        mean (p j) (fun x ↦ f (fill j rest x))) := by
  let e := Equiv.funSplitAt j β
  have hefill (x : β) (rest : {k : ι // k ≠ j} → β) : e.symm (x, rest) = fill j rest x := by
    funext k
    by_cases hk : k = j
    · subst k; simp [e, Equiv.funSplitAt, Equiv.piSplitAt, fill]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, fill, hk]
  unfold mean
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hefill]
  simp only [distribution_apply, ENNReal.toReal_prod, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  apply Finset.sum_congr rfl
  intro x _
  have hp := Fintype.prod_eq_mul_prod_compl j (fun k ↦ (p k (fill j rest x k)).toReal)
  rw [Finset.prod_subtype (p := fun k ↦ k ≠ j) ({j}ᶜ : Finset ι) (by intro k; simp) _] at hp
  have hj : fill j rest x j = x := by simp [fill]
  have hk (k : {k : ι // k ≠ j}) : fill j rest x k = rest k := by simp [fill, k.property]
  simp_rw [hj, hk] at hp
  rw [hp]
  ring

omit [DecidableEq β] in
lemma conditional_bound (p : ι → PMF β) (j : ι) (f : (ι → β) → ℝ) (B : ℝ)
    (h : ∀ rest, mean (p j) (fun x ↦ f (fill j rest x)) ≤ B) :
    mean (distribution p) f ≤ B := by
  rw [coordinate_mean p j f]
  exact (mean_mono _ h).trans_eq (mean_const _ B)

end
end Lax343628Proofs.FiniteConditioning

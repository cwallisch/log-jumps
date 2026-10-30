import Lax343628Proofs.FiniteCoupling

namespace Lax343628Proofs.CouplingTests

open Lax343628Proofs.FiniteCoupling Lax343628Proofs.FiniteDrift
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma map_positive {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq γ] [DecidableEq δ] {p : PMF α} {q : PMF β}
    (C : Coupling p q) (f : α → γ) (g : β → δ) (a : α) (b : β) (h : 0 < C.mass a b) :
    0 < (map C f g).mass (f a) (g b) := by
  have hsingle := Finset.single_le_sum
    (s := (Finset.univ : Finset (α × β)))
    (f := fun ab ↦ if f ab.1 = f a ∧ g ab.2 = g b then C.mass ab.1 ab.2 else 0)
    (fun ab _ ↦ by split_ifs; exact C.nonneg _ _; exact le_rfl)
    (Finset.mem_univ (a, b))
  simp only at hsingle
  exact h.trans_le hsingle

lemma comparable_means {α β : Type*} [Fintype α] [Fintype β] {p : PMF α} {q : PMF β}
    (C : Coupling p q) (f : α → ℝ) (g : β → ℝ) (rho : ℝ)
    (h : ∀ a b, 0 < C.mass a b → g b ≤ rho * f a ∧ f a ≤ rho * g b) :
    mean q g ≤ rho * mean p f ∧ mean p f ≤ rho * mean q g := by
  constructor
  · have ht := test_le C (fun a ↦ rho * f a) g (fun a b hab ↦ (h a b hab).1)
    rwa [mean_mul] at ht
  · have ht := test_le (reverse C) (fun b ↦ rho * g b) f (fun b a hab ↦ (h a b hab).2)
    rwa [mean_mul] at ht

end
end Lax343628Proofs.CouplingTests

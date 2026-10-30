import Lax343628Proofs.FiniteComparison

namespace Lax343628Proofs.KernelProjection

open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α β : Type*}

lemma law_map (K : α → PMF α) (L : β → PMF β) (f : α → β)
    (hK : ∀ x, (K x).map f = L (f x)) (p : PMF α) (t : ℕ) :
    (law K p t).map f = law L (p.map f) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [law_succ, PMF.map_bind]
    simp_rw [hK]
    rw [law_succ, ← ih, PMF.bind_map]
    rfl

lemma stopped_map (K : α → PMF α) (L : β → PMF β) (f : α → β) (A : Set β)
    (hK : ∀ x, f x ∈ A → (K x).map f = L (f x)) (x : α) :
    (stopped K (f ⁻¹' A) x).map f = stopped L A (f x) := by
  by_cases hx : f x ∈ A
  · simp only [stopped, Set.mem_preimage, if_pos hx]
    exact hK x hx
  · simp only [stopped, Set.mem_preimage, if_neg hx, PMF.pure_map]

lemma stopped_law (K : α → PMF α) (L : β → PMF β) (f : α → β) (A : Set β)
    (hK : ∀ x, f x ∈ A → (K x).map f = L (f x)) (p : PMF α) (t : ℕ) :
    (law (stopped K (f ⁻¹' A)) p t).map f = law (stopped L A) (p.map f) t :=
  law_map _ _ f (stopped_map K L f A hK) p t

end
end Lax343628Proofs.KernelProjection

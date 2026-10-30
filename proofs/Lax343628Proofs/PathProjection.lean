import Lax343628Proofs.KilledSampling
import Lax343628Proofs.Trajectories

namespace Lax343628Proofs.PathProjection

open Lax343628Proofs.FiniteDrift Lax343628Proofs.Trajectories
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α β γ : Type*}

lemma bind_on_support (p : PMF α) (K L : α → PMF β) (h : ∀ x ∈ p.support, K x = L x) :
    p.bind K = p.bind L := by
  apply PMF.ext
  intro y
  rw [PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro x
  by_cases hx : p x = 0
  · simp only [hx, zero_mul]
  · rw [h x hx]

lemma map (K : α → PMF α) (L : β → PMF β) (f : α → β)
    (hK : ∀ x, (K x).map f = L (f x)) (p : PMF α) (H : ℕ) :
    (pathLaw K p H).map (fun h ↦ f ∘ h) = pathLaw L (p.map f) H := by
  induction H with
  | zero => simp only [pathLaw, PMF.map_comp, Function.comp_def]
  | succ H ih =>
    simp only [pathLaw, PMF.map_bind, PMF.map_comp]
    have hstep (h : Fin (H + 1) → α) :
        (K (h (Fin.last H))).map ((fun h ↦ f ∘ h) ∘ Fin.snoc h) =
          (L (f (h (Fin.last H)))).map (Fin.snoc (f ∘ h)) := by
      have heq : ((fun h ↦ f ∘ h) ∘ Fin.snoc h) = Fin.snoc (f ∘ h) ∘ f := by
        funext x
        exact Fin.comp_snoc f h x
      rw [heq, ← PMF.map_comp, hK]
    simp_rw [hstep]
    rw [← ih, PMF.bind_map]
    rfl

lemma stop_invariant (K : α → PMF α) (p : PMF α) (A : Set α)
    (hp : ∀ x ∈ p.support, x ∈ A) (hK : ∀ x ∈ A, ∀ y ∈ (K x).support, y ∈ A) (H : ℕ) :
    pathLaw (stopped K A) p H = pathLaw K p H := by
  induction H with
  | zero => rfl
  | succ H ih =>
    simp only [pathLaw, ih]
    apply bind_on_support
    intro h hh
    have hlast := path_invariant K p A hp hK h hh (Fin.last H)
    rw [stopped, if_pos hlast]

lemma path_bind (K : β → PMF β) (p : PMF α) (F : α → PMF β) (H : ℕ) :
    pathLaw K (p.bind F) H = p.bind (fun x ↦ pathLaw K (F x) H) := by
  induction H with
  | zero => simp only [pathLaw, PMF.map_bind]
  | succ H ih => simp only [pathLaw, ih, PMF.bind_bind]

lemma mixture (K : α → PMF α) (p : PMF α) (H : ℕ) :
    p.bind (fun x ↦ pathLaw K (PMF.pure x) H) = pathLaw K p H := by
  rw [← path_bind, PMF.bind_pure]

lemma law_invariant (K : α → PMF α) (p : PMF α) (A : Set α)
    (hp : ∀ x ∈ p.support, x ∈ A) (hK : ∀ x ∈ A, ∀ y ∈ (K x).support, y ∈ A) (H : ℕ) :
    ∀ x ∈ (FiniteChain.law K p H).support, x ∈ A := by
  intro x hx
  rw [← pathLaw_last] at hx
  obtain ⟨h, hh, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  exact path_invariant K p A hp hK h hh (Fin.last H)

end
end Lax343628Proofs.PathProjection

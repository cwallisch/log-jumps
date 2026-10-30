import Lax343628Proofs.PathWindows

namespace Lax343628Proofs.PathContinuation

open Lax343628Proofs.Trajectories Lax343628Proofs.FiniteChain
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*}

def continuation (K : α → PMF α) (s : ℕ) (h : Fin (s + 1) → α) :
    (t : ℕ) → PMF (Fin (s + t + 1) → α)
  | 0 => PMF.pure h
  | t + 1 => (continuation K s h t).bind
      (fun g ↦ (K (g (Fin.last (s + t)))).map (Fin.snoc g))

lemma pathLaw_add (K : α → PMF α) (p : PMF α) (s t : ℕ) :
    pathLaw K p (s + t) = (pathLaw K p s).bind (fun h ↦ continuation K s h t) := by
  induction t with
  | zero => simp only [Nat.add_zero, continuation, PMF.bind_pure]
  | succ t ih =>
    change (pathLaw K p (s + t)).bind (fun g : Fin (s + t + 1) → α ↦
        (K (g (Fin.last (s + t)))).map (fun x : α ↦ Fin.snoc (α := fun _ : Fin (s + t + 2) ↦ α) g x)) =
      (pathLaw K p s).bind (fun h : Fin (s + 1) → α ↦ (continuation K s h t).bind
        (fun g : Fin (s + t + 1) → α ↦ (K (g (Fin.last (s + t)))).map (fun x : α ↦ Fin.snoc (α := fun _ : Fin (s + t + 2) ↦ α) g x)))
    rw [ih, PMF.bind_bind]

lemma prefix_law (K : α → PMF α) (s : ℕ) (h : Fin (s + 1) → α) (t : ℕ) :
    (continuation K s h t).map (initialSegment s t) = PMF.pure h := by
  induction t with
  | zero =>
    have heq : initialSegment s 0 = (id : (Fin (s + 1) → α) → (Fin (s + 1) → α)) := rfl
    rw [continuation, heq, PMF.map_id]
  | succ t ih =>
    simp only [continuation, PMF.map_bind, PMF.map_comp, Function.comp_def, initialSegment_snoc]
    calc
      _ = (continuation K s h t).bind (fun g ↦ PMF.pure (initialSegment s t g)) := by
        congr 1
        funext g
        exact PMF.map_const _ _
      _ = _ := ih

lemma prefix_support (K : α → PMF α) (s : ℕ) (h : Fin (s + 1) → α) (t : ℕ)
    (g : Fin (s + t + 1) → α) (hg : g ∈ (continuation K s h t).support) : initialSegment s t g = h := by
  have hh : initialSegment s t g ∈ ((continuation K s h t).map (initialSegment s t)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨g, hg, rfl⟩
  rw [prefix_law] at hh
  exact (PMF.mem_support_pure_iff _ _).mp hh

lemma segment_law (K : α → PMF α) (s : ℕ) (h : Fin (s + 1) → α) (t : ℕ) :
    (continuation K s h t).map (segment s t) = pathLaw K (PMF.pure (h (Fin.last s))) t := by
  induction t with
  | zero =>
    simp only [continuation, PMF.pure_map, pathLaw]
    congr 1
    funext j
    have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    subst j
    rfl
  | succ t ih =>
    simp only [continuation, PMF.map_bind, PMF.map_comp, Function.comp_def, segment_snoc, pathLaw]
    calc
      _ = ((continuation K s h t).map (segment s t)).bind
          (fun g ↦ (K (g (Fin.last t))).map (Fin.snoc g)) := by
        rw [PMF.bind_map]
        rfl
      _ = _ := by rw [ih]

end
end Lax343628Proofs.PathContinuation

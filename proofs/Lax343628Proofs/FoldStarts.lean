import Lax343628Proofs.HistoryFold
import Lax343628Proofs.AdaptiveWindow
import Mathlib.Order.Fin.Basic

namespace Lax343628Proofs.FoldStarts

open Lax343628Proofs.HistoryFold
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α β : Type*}

lemma monotone_epoch (init : α → β) (step : β → α → β) (epoch : β → ℕ)
    (hstep : ∀ q x, epoch q ≤ epoch (step q x)) {H : ℕ} (h : Fin (H + 1) → α) :
    Monotone (fun t ↦ epoch (atTime init step h t)) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro t
  rw [at_succ]
  exact hstep _ _

lemma unique (init : α → β) (step : β → α → β) (epoch : β → ℕ) (isStart : β → Prop)
    (hstep : ∀ q x, epoch q ≤ epoch (step q x))
    (henter : ∀ q x, isStart (step q x) → epoch q < epoch (step q x))
    {H : ℕ} (h : Fin (H + 1) → α) (s t : Fin (H + 1))
    (hs : isStart (atTime init step h s)) (ht : isStart (atTime init step h t))
    (heq : epoch (atTime init step h s) = epoch (atTime init step h t)) : s = t := by
  have hm := monotone_epoch init step epoch hstep h
  have hstrict (u v : Fin (H + 1)) (huv : u < v) (hv : isStart (atTime init step h v)) :
      epoch (atTime init step h u) < epoch (atTime init step h v) := by
    let j : Fin H := ⟨v.val - 1, by have := v.isLt; have := Fin.lt_def.mp huv; omega⟩
    have hj : j.succ = v := Fin.ext (by have := Fin.lt_def.mp huv; dsimp [j]; omega)
    have huj : u ≤ j.castSucc := Fin.le_iff_val_le_val.mpr (by have := Fin.lt_def.mp huv; dsimp [j]; omega)
    have hnew : isStart (step (atTime init step h j.castSucc) (h j.succ)) := by
      rw [← at_succ init step h j, hj]
      exact hv
    have he := henter (atTime init step h j.castSucc) (h j.succ) hnew
    rw [← at_succ init step h j, hj] at he
    exact (hm huj).trans_lt he
  rcases lt_trichotomy s t with hlt | he | hgt
  · have hh := hstrict s t hlt ht
    omega
  · exact he
  · have hh := hstrict t s hgt hs
    omega

def starts (B : ℕ) (init : α → β) (step : β → α → β) (epoch : β → ℕ) (isStart : β → Prop)
    (j : ℕ) (s : Fin (B + 1)) : Set (Fin (s.val + 1) → α) :=
  {h | isStart (fold init step h) ∧ epoch (fold init step h) = j}

lemma unique_history (B R : ℕ) (init : α → β) (step : β → α → β) (epoch : β → ℕ) (isStart : β → Prop)
    (hstep : ∀ q x, epoch q ≤ epoch (step q x))
    (henter : ∀ q x, isStart (step q x) → epoch q < epoch (step q x)) (j : ℕ)
    (h : Fin (B + R + 1) → α) (s t : Fin (B + 1))
    (hs : AdaptiveWindow.history s h ∈ starts B init step epoch isStart j s)
    (ht : AdaptiveWindow.history t h ∈ starts B init step epoch isStart j t) : s = t := by
  let s' : Fin (B + R + 1) := ⟨s.val, by have := s.isLt; omega⟩
  let t' : Fin (B + R + 1) := ⟨t.val, by have := t.isLt; omega⟩
  have he := unique init step epoch isStart hstep henter h s' t' hs.1 ht.1 (hs.2.trans ht.2.symm)
  exact Fin.ext (congrArg (fun q : Fin (B + R + 1) ↦ q.val) he)

end
end Lax343628Proofs.FoldStarts

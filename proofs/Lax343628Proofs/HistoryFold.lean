import Lax343628Proofs.Trajectories

namespace Lax343628Proofs.HistoryFold

open Lax343628Proofs.Trajectories
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α β : Type*}

def fold (init : α → β) (step : β → α → β) : {t : ℕ} → (Fin (t + 1) → α) → β
  | 0, h => init (h 0)
  | t + 1, h => step (fold init step (Fin.init h)) (h (Fin.last (t + 1)))

def atTime (init : α → β) (step : β → α → β) {H : ℕ} (h : Fin (H + 1) → α) (t : Fin (H + 1)) : β :=
  fold init step (before H t.val (Nat.le_of_lt_succ t.isLt) h)

lemma at_succ (init : α → β) (step : β → α → β) {H : ℕ} (h : Fin (H + 1) → α) (t : Fin H) :
    atTime init step h t.succ = step (atTime init step h t.castSucc) (h t.succ) := by
  rfl

end
end Lax343628Proofs.HistoryFold

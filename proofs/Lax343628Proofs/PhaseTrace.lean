import Lax343628Proofs.PolicyTransitions

namespace Lax343628Proofs.PhaseTrace

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PolicyPaths
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {β γ : Type*} {H : ℕ}

def Segment (q : Fin (H + 1) → β) (age : β → ℕ) (key : β → γ) (s t : Fin (H + 1)) : Prop :=
  s ≤ t ∧ age (q s) = 0 ∧ key (q s) = key (q t) ∧ t.val = s.val + age (q t) ∧
    ∀ j, s ≤ j → j ≤ t → key (q j) = key (q t) ∧ j.val = s.val + age (q j)

lemma zero (q : Fin (H + 1) → β) (age : β → ℕ) (key : β → γ) (t : Fin (H + 1))
    (hage : age (q t) = 0) : Segment q age key t t := by
  refine ⟨le_rfl, hage, rfl, by omega, ?_⟩
  intro j htj hjt
  have heq : j = t := le_antisymm hjt htj
  subst j
  exact ⟨rfl, by omega⟩

lemma origin (q : Fin (H + 1) → β) (age : β → ℕ) (key : β → γ) (active : β → Prop)
    (hzero : age (q 0) = 0)
    (hprev : ∀ j : Fin H, active (q j.succ) → active (q j.castSucc))
    (hstep : ∀ j : Fin H, active (q j.succ) → 0 < age (q j.succ) →
      key (q j.succ) = key (q j.castSucc) ∧ age (q j.succ) = age (q j.castSucc) + 1) :
    ∀ t, active (q t) → ∃ s, Segment q age key s t := by
  intro t
  refine Fin.induction ?_ (fun j ih ↦ ?_) t
  · intro _; exact ⟨0, zero q age key 0 hzero⟩
  · intro ha
    by_cases hz : age (q j.succ) = 0
    · exact ⟨j.succ, zero q age key j.succ hz⟩
    · have hp : 0 < age (q j.succ) := by omega
      obtain ⟨s, hst, hs0, hkey, htime, hband⟩ := ih (hprev j ha)
      have hh := hstep j ha hp
      have hnewtime : j.succ.val = s.val + age (q j.succ) := by
        have hv : j.succ.val = j.castSucc.val + 1 := rfl
        omega
      refine ⟨s, Fin.le_iff_val_le_val.mpr (by have := Fin.le_iff_val_le_val.mp hst; simp only [Fin.val_succ, Fin.val_castSucc] at *; omega),
        hs0, hkey.trans hh.1.symm, hnewtime, ?_⟩
      intro v hsv hvj
      by_cases heq : v = j.succ
      · subst v; exact ⟨rfl, hnewtime⟩
      · have hprevj : v ≤ j.castSucc := Fin.le_iff_val_le_val.mpr (by
          have hv := Fin.le_iff_val_le_val.mp hvj
          have hne : v.val ≠ j.succ.val := fun he ↦ heq (Fin.ext he)
          simp only [Fin.val_succ, Fin.val_castSucc] at *
          omega)
        have hv := hband v hsv hprevj
        exact ⟨hv.1.trans hh.1.symm, hv.2⟩

variable {n : ℕ} {mu : ℕ+}

lemma policy_origin (astar theta omega : ℝ) (M Rw Rs : ℕ) (h : Fin (H + 1) → State n mu)
    (t : Fin (H + 1)) (ha : PolicyClock.active (configuration astar theta omega M Rw Rs h t)) :
    ∃ s, Segment (configuration astar theta omega M Rw Rs h) Config.age PolicyTransitions.key s t := by
  apply origin _ Config.age PolicyTransitions.key PolicyClock.active _ _ _ t ha
  · exact setup_age astar M (h 0).1 Finset.univ 0
  · intro j hj
    exact PolicyClock.active_prev astar theta omega M Rw Rs _ _ hj
  · intro j hj hage
    exact PolicyTransitions.positive_age astar theta omega M Rw Rs _ _ hj hage

end
end Lax343628Proofs.PhaseTrace

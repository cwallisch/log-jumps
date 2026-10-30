import Lax343628Proofs.PolicyHistory
import Lax343628Proofs.WaitingCore

namespace Lax343628Proofs.PolicyTimeout

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PolicyPaths
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n H r : ℕ} {mu : ℕ+}

lemma waiting (astar theta omega : ℝ) (M Rw Rs : ℕ) (hath : astar < theta)
    (hRw : 0 < Rw) (hRs : 0 < Rs) (h : Fin (H + 1) → State n mu)
    (hcap : ColumnBlock.cap omega (h 0).1)
    (hplat : ∀ t u, (Sampling.zeros ((h t).1 u)).card = r + 1) (t : Fin H)
    (hwait : (configuration astar theta omega M Rw Rs h t.castSucc).stage = Stage.waiting)
    (htime : Rw ≤ (configuration astar theta omega M Rw Rs h t.castSucc).age + 1)
    (hready : ¬(ready (configuration astar theta omega M Rw Rs h t.castSucc).unprocessed M (h t.succ).1).Nonempty)
    (hflat : PolicyInvariant.flat theta (h t.succ).1 (configuration astar theta omega M Rw Rs h t.castSucc).unprocessed) :
    ∃ s : Fin (H + 1), s ≤ t.castSucc ∧
      isWaitStart (configuration astar theta omega M Rw Rs h s) ∧
      t.succ.val = s.val + Rw ∧
      ∀ j : Fin (H + 1), s ≤ j → j ≤ t.succ →
        (h j).1 ∈ CoreCounts.waiting r (configuration astar theta omega M Rw Rs h s).unprocessed M theta := by
  let q := configuration astar theta omega M Rw Rs h
  have hv := PolicyInvariant.path_valid astar theta omega M Rw Rs hath hRw hRs h hcap
  have hvt := hv t.castSucc
  simp only [PolicyInvariant.Valid, hwait] at hvt
  obtain ⟨s, hst, hs0, hkey, hclock, hband⟩ := PhaseTrace.policy_origin astar theta omega M Rw Rs h t.castSucc (Or.inl hwait)
  have hskey := PolicyHistory.key_unprocessed _ _ hkey
  have hswait := (PolicyHistory.key_stage _ _ hkey).trans hwait
  have hdeadline : t.succ.val = s.val + Rw := by
    have hage := hvt.2.2.1
    simp only [Fin.val_castSucc, Fin.val_succ] at *
    omega
  refine ⟨s, hst, ⟨hswait, hs0⟩, hdeadline, ?_⟩
  intro j hsj hjt
  by_cases hj : j = t.succ
  · subst j
    rw [hskey]
    exact ⟨hplat _, WaitingCore.missing_small _ _ _ hready, hflat⟩
  · have hjprev : j ≤ t.castSucc := Fin.le_iff_val_le_val.mpr (by
      have hh := Fin.le_iff_val_le_val.mp hjt
      have hn : j.val ≠ t.succ.val := fun he ↦ hj (Fin.ext he)
      simp only [Fin.val_succ, Fin.val_castSucc] at *
      omega)
    have hk := (hband j hsj hjprev).1
    have hjwait := (PolicyHistory.key_stage _ _ hk).trans hwait
    have hvj := hv j
    simp only [PolicyInvariant.Valid, hjwait] at hvj
    have heq := (PolicyHistory.key_unprocessed _ _ hkey).trans (PolicyHistory.key_unprocessed _ _ hk).symm
    rw [heq]
    exact ⟨hplat _, WaitingCore.missing_small _ _ _ hvj.2.1, hvj.2.2.2.2⟩

lemma serving (astar theta omega : ℝ) (M Rw Rs : ℕ) (hath : astar < theta)
    (hRw : 0 < Rw) (hRs : 0 < Rs) (h : Fin (H + 1) → State n mu)
    (hcap : ColumnBlock.cap omega (h 0).1) (t : Fin H) (i : Fin n)
    (hserve : (configuration astar theta omega M Rw Rs h t.castSucc).stage = Stage.serving i)
    (htime : Rs ≤ (configuration astar theta omega M Rw Rs h t.castSucc).age + 1)
    (hfrac : astar < ClassChannels.fraction i 0 (h t.succ).1)
    (hcaplast : ColumnBlock.cap omega (h t.succ).1) :
    ∃ s : Fin (H + 1), s ≤ t.castSucc ∧
      M ≤ CoreCounts.missingCount i (h s).1 ∧ t.succ.val = s.val + Rs ∧
      ∀ j : Fin (H + 1), s ≤ j → j ≤ t.succ →
        astar < ClassChannels.fraction i 0 (h j).1 ∧ ColumnBlock.cap omega (h j).1 := by
  have hv := PolicyInvariant.path_valid astar theta omega M Rw Rs hath hRw hRs h hcap
  have hvt := hv t.castSucc
  simp only [PolicyInvariant.Valid, hserve] at hvt
  obtain ⟨s, hst, hs0, hkey, hclock, hband⟩ := PhaseTrace.policy_origin astar theta omega M Rw Rs h t.castSucc (Or.inr ⟨i, hserve⟩)
  have hsserve := (PolicyHistory.key_stage _ _ hkey).trans hserve
  have hseed := PolicyHistory.fresh_service astar theta omega M Rw Rs h s i hsserve hs0
  have hdeadline : t.succ.val = s.val + Rs := by
    have hage := hvt.2.2.1
    simp only [Fin.val_castSucc, Fin.val_succ] at *
    omega
  refine ⟨s, hst, hseed, hdeadline, ?_⟩
  intro j hsj hjt
  by_cases hj : j = t.succ
  · subst j; exact ⟨hfrac, hcaplast⟩
  · have hjprev : j ≤ t.castSucc := Fin.le_iff_val_le_val.mpr (by
      have hh := Fin.le_iff_val_le_val.mp hjt
      have hn : j.val ≠ t.succ.val := fun he ↦ hj (Fin.ext he)
      simp only [Fin.val_succ, Fin.val_castSucc] at *
      omega)
    have hk := (hband j hsj hjprev).1
    have hjserve := (PolicyHistory.key_stage _ _ hk).trans hserve
    have hvj := hv j
    simp only [PolicyInvariant.Valid, hjserve] at hvj
    exact ⟨hvj.2.1, hvj.2.2.2.1⟩

end
end Lax343628Proofs.PolicyTimeout

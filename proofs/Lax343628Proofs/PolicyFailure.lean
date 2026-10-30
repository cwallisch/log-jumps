import Lax343628Proofs.GlobalWait
import Lax343628Proofs.GlobalService
import Lax343628Proofs.GlobalProtection

namespace Lax343628Proofs.PolicyFailure

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PhaseParameters Lax343628Proofs.EntropyLedger
open Lax343628Proofs.PolicyPaths Lax343628Proofs.BlockParameters
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r H : ℕ} {mu : ℕ+}

lemma contains (S : ℕ+) (delta : ℝ) (Rw K : ℕ) (hRw : 0 < Rw)
    (hRs : 0 < rounds mu * horizon (S : ℕ) mu) (h : Fin (H + 1) → State n mu)
    (hplat : ∀ t u, (Sampling.zeros ((h t).1 u)).card = r + 1)
    (hK : (ColumnMarks.refresh Finset.univ (processed S (r + 1)) (h 0).1).card ≤ K)
    (hfail : (configuration (processed S (r + 1)) (theta S) (1 / 125)
      (seedSize S n (r + 1) mu delta) Rw (rounds mu * horizon (S : ℕ) mu) h (Fin.last H)).stage = Stage.failure) :
    (∃ t, ¬ColumnBlock.cap (1 / 125) (h t).1) ∨
      h ∈ GlobalProtection.failure S H (r + 1) (1 / 125) ∨
      (∃ e : Fin (2 * K + 2), h ∈ GlobalWait.failure H (r + 1) (processed S (r + 1)) (theta S) (1 / 125)
        (seedSize S n (r + 1) mu delta) Rw (rounds mu * horizon (S : ℕ) mu) e.val) ∨
      (∃ i : Fin n, ∃ s : Fin (H + 1), h ∈ GlobalService.failure H (rounds mu * horizon (S : ℕ) mu)
        (r + 1) (seedSize S n (r + 1) mu delta) (processed S (r + 1)) (1 / 125) i s) := by
  let a := processed S (r + 1)
  let th := theta S
  let M := seedSize S n (r + 1) mu delta
  let Rs := rounds mu * horizon (S : ℕ) mu
  let q := configuration a th (1 / 125) M Rw Rs h
  by_cases hbadcap : ∃ t, ¬ColumnBlock.cap (1 / 125) (h t).1
  · exact Or.inl hbadcap
  have hcap : ∀ t, ColumnBlock.cap (1 / 125) (h t).1 := by simpa only [not_exists, not_not] using hbadcap
  right
  obtain ⟨t, _, hprev, hnew⟩ := PolicyHistory.first_failure a th (1 / 125) M Rw Rs h (Fin.last H) hfail
  have hc := PolicyTransitions.failure_cases a th (1 / 125) M Rw Rs (q t.castSucc) (h t.succ) hprev hnew
  rcases hc with hbad | hbad | hwait | hserve
  · exact False.elim (hbad (hcap t.succ))
  · left
    obtain ⟨i, hi, hhigh⟩ := hbad
    obtain ⟨b, hbt, hsmall⟩ := PolicyHistory.processed a th (1 / 125) M Rw Rs h t.castSucc i hi
    exact ⟨i, b, t.succ, hbt.trans (Fin.le_iff_val_le_val.mpr (by simp)), hsmall, hhigh,
      fun j _ ↦ hplat j, fun j _ ↦ hcap j⟩
  · right; left
    obtain ⟨hw, htime, hready, _, hflat⟩ := hwait
    obtain ⟨s, hst, hstart, htime', hwindow⟩ := PolicyTimeout.waiting a th (1 / 125) M Rw Rs
      (PolicyWaitBound.processed_lt_theta S (r + 1)) hRw hRs h (hcap 0) hplat t hw htime hready hflat
    have he := epoch_bound a th (1 / 125) M Rw Rs h K hK s
    change (q s).epoch ≤ 2 * K + 1 at he
    refine ⟨⟨(q s).epoch, by omega⟩, s, ?_, hstart, rfl, hcap 0, hplat s, ?_⟩
    · have hv := t.succ.isLt
      omega
    · intro j
      have hj : s.val + j.val < H + 1 := by have := j.isLt; have := t.succ.isLt; omega
      have hs : s ≤ (⟨s.val + j.val, hj⟩ : Fin (H + 1)) := Fin.le_iff_val_le_val.mpr (by simp)
      have ht : (⟨s.val + j.val, hj⟩ : Fin (H + 1)) ≤ t.succ := Fin.le_iff_val_le_val.mpr (by change s.val + j.val ≤ t.succ.val; have := j.isLt; omega)
      have hh := hwindow ⟨s.val + j.val, hj⟩ hs ht
      simpa only [Nat.add_sub_cancel, PathWindows.window_apply, a, th, M, Rs] using hh
  · right; right
    obtain ⟨i, hi, htime, hf, hlast, _⟩ := hserve
    obtain ⟨s, hst, hseed, htime', hwindow⟩ := PolicyTimeout.serving a th (1 / 125) M Rw Rs
      (PolicyWaitBound.processed_lt_theta S (r + 1)) hRw hRs h (hcap 0) t i hi htime hf hlast
    refine ⟨i, s, ?_, ⟨hplat s, ?_, hseed⟩, ?_⟩
    · have hv := t.succ.isLt
      omega
    · exact (hwindow s le_rfl (hst.trans (Fin.le_iff_val_le_val.mpr (by simp)))).1
    · intro j
      have hj : s.val + j.val < H + 1 := by have := j.isLt; have := t.succ.isLt; omega
      have hs : s ≤ (⟨s.val + j.val, hj⟩ : Fin (H + 1)) := Fin.le_iff_val_le_val.mpr (by simp)
      have ht : (⟨s.val + j.val, hj⟩ : Fin (H + 1)) ≤ t.succ := Fin.le_iff_val_le_val.mpr (by change s.val + j.val ≤ t.succ.val; have := j.isLt; omega)
      exact hwindow ⟨s.val + j.val, hj⟩ hs ht

end
end Lax343628Proofs.PolicyFailure

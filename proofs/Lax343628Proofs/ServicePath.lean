import Lax343628Proofs.ServiceGeometry
import Lax343628Proofs.FiniteGrowth
import Lax343628Proofs.PathWindows

namespace Lax343628Proofs.ServicePath

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ColumnBlock Lax343628Proofs.ColumnEndpoint Lax343628Proofs.ServiceGeometry
open Lax343628Proofs.Trajectories Lax343628Proofs.PathWindows Lax343628Proofs.DrivenPaths
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k N R : ℕ} {mu : ℕ+}

lemma reach (i : Fin n) (a omega : ℝ) (ha : 0 < a)
    (h : Fin (N * R + 1) → State n mu) (hO0 : 0 < Odds.value i (h 0).1)
    (hlarge : finalOdds a < (8 : ℝ) ^ N * Odds.value i (h 0).1)
    (hgood : ∀ s : ℕ, ∀ hs : s + R ≤ N * R,
      a < fraction i 0 (population h s) → Odds.value i (h 0).1 ≤ Odds.value i (population h s) →
      good i (Odds.value i (population h s) / (4 * (3 : ℝ) ^ k))
        (target a (Odds.value i (population h s))) omega
        (frozen {T | active k i (Odds.value i (population h s) / (4 * (3 : ℝ) ^ k))
          (target a (Odds.value i (population h s))) omega T.1}
          (window (N * R) R s hs h))) :
    ∃ t : Fin (N * R + 1), fraction i 0 (h t).1 ≤ a ∨ ¬cap omega (h t).1 := by
  let P := population h
  let done : Population n mu → Prop := fun Q ↦ fraction i 0 Q ≤ a ∨ ¬cap omega Q
  have hP0 : P 0 = (h 0).1 := by change (extend h 0).1 = _; rw [extend_at h 0 (by omega)]; rfl
  have hupper (s : ℕ) (_ : s ≤ N * R) (hs : ¬done (P s)) : Odds.value i (P s) ≤ finalOdds a := by
    exact (odds_below_final i (P s) a ha (lt_of_not_ge (fun hh ↦ hs (Or.inl hh)))).le
  have hblock (s : ℕ) (hs : s + R ≤ N * R) (hO : Odds.value i (P 0) ≤ Odds.value i (P s))
      (hd : ¬done (P s)) : ∃ t, t ≤ s + R ∧ (done (P t) ∨ 8 * Odds.value i (P s) ≤ Odds.value i (P t)) := by
    have ha' : a < fraction i 0 (P s) := lt_of_not_ge (fun hh ↦ hd (Or.inl hh))
    have hg := hgood s hs ha' (by rwa [← hP0])
    obtain ⟨j, hj⟩ := good_progress k i a omega ha (extend h s) (window (N * R) R s hs h) hg
    have he : (window (N * R) R s hs h j).1 = P (s + j.val) := by
      change (h ⟨s + j.val, _⟩).1 = (extend h (s + j.val)).1
      rw [extend_at h (s + j.val) (by have := j.isLt; omega)]
    rw [he] at hj
    refine ⟨s + j.val, by have := j.isLt; omega, ?_⟩
    rcases hj with hdone | hcap | hmult
    · exact Or.inl (Or.inl hdone)
    · exact Or.inl (Or.inr hcap)
    · exact Or.inr hmult
  have ht := FiniteGrowth.reach P done (Odds.value i) N R (finalOdds a)
    (by rwa [hP0]) hupper hblock (by rwa [hP0])
  obtain ⟨t, ht, hd⟩ := ht
  refine ⟨⟨t, by omega⟩, ?_⟩
  change done (h ⟨t, by omega⟩).1
  change done (extend h t).1 at hd
  rwa [extend_at h t ht] at hd

end
end Lax343628Proofs.ServicePath

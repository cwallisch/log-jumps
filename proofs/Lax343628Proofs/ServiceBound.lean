import Lax343628Proofs.ServiceWindows

namespace Lax343628Proofs.ServiceBound

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ColumnBlock Lax343628Proofs.ColumnEndpoint Lax343628Proofs.ServiceGeometry
open Lax343628Proofs.ServiceWindows Lax343628Proofs.Trajectories Lax343628Proofs.PathWindows
open Lax343628Proofs.DrivenPaths Lax343628Proofs.FiniteEvents
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k N R : ℕ} {mu : ℕ+}

lemma bound (hkn : k ≤ n) (pc a omega : ℝ) (ha : 0 < a) (i : Fin n)
    (S0 : State n mu) (hS0 : ∀ v, (Sampling.zeros (S0.1 v)).card = k)
    (hO0 : 0 < Odds.value i S0.1)
    (hlarge : finalOdds a < (8 : ℝ) ^ N * Odds.value i S0.1)
    (q : ℝ) (hq : 0 ≤ q)
    (hblock : ∀ S ∈ starts (mu := mu) k i a (Odds.value i S0.1),
      (pathLaw (driver k pc) (PMF.pure S) R).toOuterMeasure
        (blockFailure (R := R) k i a omega S) ≤ ENNReal.ofReal q) :
    (pathLaw (driver k pc) (PMF.pure S0) (N * R)).toOuterMeasure
      {h | ∀ t, a < fraction i 0 (h t).1 ∧ cap omega (h t).1} ≤
      ENNReal.ofReal ((((N * R : ℕ) : ℝ) + 1) * q) := by
  apply le_trans _ (ServiceWindows.union_bound k pc a (Odds.value i S0.1) omega i q hq hblock (PMF.pure S0))
  apply event_mono_on_support
  intro h hh hfail
  by_contra hn
  have hnone : ∀ s : Fin (N * R + 1), h ∉ windowFailure (N * R) R k i a (Odds.value i S0.1) omega s := by
    intro s hs
    exact hn ⟨s, hs⟩
  have hstart := path_pure_start (driver k pc) S0 h hh
  have hplateau := DrivenPlateau.path hkn pc S0 hS0 h hh
  have hgood (s : ℕ) (hs : s + R ≤ N * R)
      (ha' : a < fraction i 0 (population h s))
      (hO : Odds.value i (h 0).1 ≤ Odds.value i (population h s)) :
      good i (Odds.value i (population h s) / (4 * (3 : ℝ) ^ k))
        (target a (Odds.value i (population h s))) omega
        (frozen {T | active k i (Odds.value i (population h s) / (4 * (3 : ℝ) ^ k))
          (target a (Odds.value i (population h s))) omega T.1}
          (window (N * R) R s hs h)) := by
    let s' : Fin (N * R + 1) := ⟨s, by omega⟩
    have hpop : population h s = (h s').1 := by
      change (extend h s).1 = _
      rw [extend_at h s (by omega)]
    have hw0 : window (N * R) R s hs h 0 = h s' := by rfl
    have hstarts : window (N * R) R s hs h 0 ∈ starts k i a (Odds.value i S0.1) := by
      rw [hw0]
      refine ⟨hplateau s', ?_, ?_⟩
      · rwa [← hpop]
      · rw [← hpop]
        rwa [hstart] at hO
    by_contra hbad
    apply hnone s'
    refine ⟨hs, hstarts, ?_⟩
    change ¬good i _ _ _ _
    rw [hw0, ← hpop]
    exact hbad
  obtain ⟨t, ht⟩ := ServicePath.reach i a omega ha h (by rwa [hstart]) (by rwa [hstart]) hgood
  rcases ht with ha' | hcap
  · exact (not_le_of_gt (hfail t).1) ha'
  · exact hcap (hfail t).2

end
end Lax343628Proofs.ServiceBound

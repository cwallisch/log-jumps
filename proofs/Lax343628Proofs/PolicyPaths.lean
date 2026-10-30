import Lax343628Proofs.PolicyRank

namespace Lax343628Proofs.PolicyPaths

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.HistoryFold
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n H : ℕ} {mu : ℕ+}

def configuration (astar theta omega : ℝ) (M Rw Rs : ℕ) (h : Fin (H + 1) → State n mu) (t : Fin (H + 1)) : Config n :=
  atTime (initial astar M) (tick astar theta omega M Rw Rs) h t

lemma at_succ (astar theta omega : ℝ) (M Rw Rs : ℕ) (h : Fin (H + 1) → State n mu) (t : Fin H) :
    configuration astar theta omega M Rw Rs h t.succ =
      tick astar theta omega M Rw Rs (configuration astar theta omega M Rw Rs h t.castSucc) (h t.succ) := rfl

lemma valid (astar theta omega : ℝ) (M Rw Rs : ℕ) (h : Fin (H + 1) → State n mu) :
    ∀ t, PolicyRank.valid (configuration astar theta omega M Rw Rs h t) := by
  intro t
  refine Fin.induction ?_ (fun j hj ↦ ?_) t
  · exact PolicyRank.setup_valid astar M (h 0).1 Finset.univ 0
  · rw [at_succ]
    exact PolicyRank.tick_valid astar theta omega M Rw Rs _ _ hj

lemma combined_antitone (astar theta omega : ℝ) (M Rw Rs : ℕ) (h : Fin (H + 1) → State n mu) :
    Antitone (fun t ↦ (configuration astar theta omega M Rw Rs h t).epoch +
      PolicyRank.rank (configuration astar theta omega M Rw Rs h t)) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro t
  rw [at_succ]
  exact PolicyRank.step astar theta omega M Rw Rs _ _ (valid astar theta omega M Rw Rs h t.castSucc)

lemma epoch_bound (astar theta omega : ℝ) (M Rw Rs : ℕ) (h : Fin (H + 1) → State n mu)
    (K : ℕ) (hK : (ColumnMarks.refresh Finset.univ astar (h 0).1).card ≤ K) (t : Fin (H + 1)) :
    (configuration astar theta omega M Rw Rs h t).epoch ≤ 2 * K + 1 := by
  have hh := combined_antitone astar theta omega M Rw Rs h (Fin.zero_le t)
  dsimp only at hh
  have hinit := PolicyRank.setup_rank astar M (h 0).1 Finset.univ 0
  have hepoch : (configuration astar theta omega M Rw Rs h 0).epoch = 0 := setup_epoch _ _ _ _ _
  have hrank : PolicyRank.rank (configuration astar theta omega M Rw Rs h 0) ≤ 2 * K + 1 := by
    exact hinit.trans (by omega)
  rw [hepoch] at hh
  omega

lemma unique_wait (B R : ℕ) (astar theta omega : ℝ) (M Rw Rs e : ℕ)
    (h : Fin (B + R + 1) → State n mu) (s t : Fin (B + 1))
    (hs : AdaptiveWindow.history s h ∈ FoldStarts.starts B (initial astar M)
      (tick astar theta omega M Rw Rs) Config.epoch isWaitStart e s)
    (ht : AdaptiveWindow.history t h ∈ FoldStarts.starts B (initial astar M)
      (tick astar theta omega M Rw Rs) Config.epoch isWaitStart e t) : s = t :=
  FoldStarts.unique_history B R (initial astar M) (tick astar theta omega M Rw Rs) Config.epoch isWaitStart
    (PolicyCounters.epoch_monotone astar theta omega M Rw Rs)
    (PolicyCounters.wait_enter astar theta omega M Rw Rs) e h s t hs ht

end
end Lax343628Proofs.PolicyPaths

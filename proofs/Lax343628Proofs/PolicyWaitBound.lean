import Lax343628Proofs.WaitingCore
import Lax343628Proofs.AdaptiveSeed
import Lax343628Proofs.PhaseConditions

namespace Lax343628Proofs.PolicyWaitBound

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PhaseParameters Lax343628Proofs.EntropyLedger Lax343628Proofs.HistoryFold
open Lax343628Proofs.Trajectories
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {mu : ℕ+}

def starts (B k : ℕ) (astar theta omega : ℝ) (M Rw Rs e : ℕ) (s : Fin (B + 1)) :
    Set (Fin (s.val + 1) → State n mu) :=
  {h | let q := fold (initial astar M) (tick astar theta omega M Rw Rs) h
    isWaitStart q ∧ q.epoch = e ∧ ColumnBlock.cap omega (h 0).1 ∧
      ∀ u, (Sampling.zeros ((h (Fin.last s.val)).1 u)).card = k}

def core (astar theta omega : ℝ) (M Rw Rs : ℕ) {s : ℕ} (h : Fin (s + 1) → State n mu) : Finset (Fin n) :=
  (fold (initial astar M) (tick astar theta omega M Rw Rs) h).unprocessed

lemma processed_lt_theta (S : ℕ+) (k : ℕ) : processed S k < theta S := by
  have hu := (lower_bounds S k).1
  have hD : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hrel : theta S = 16 * (3 : ℝ) ^ k * lowerZero S k := by unfold lowerZero; field_simp
  have hh := mul_le_mul_of_nonneg_right hD hu.le
  unfold processed
  nlinarith

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (r : ℕ) (hr : 1 ≤ r)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (B Rw Rs e : ℕ) (hRw : 0 < Rw) (hRs : 0 < Rs) (p : PMF (State n mu)) :
    (pathLaw (driver (r + 1) pc) p (B + Rw)).toOuterMeasure
      {h | ∃ s : Fin (B + 1), AdaptiveWindow.history s h ∈ starts B (r + 1)
          (processed S (r + 1)) (theta S) (1 / 125) (seedSize S n (r + 1) mu delta) Rw Rs e s ∧
        ∀ j : Fin (Rw + 1), (AdaptiveWindow.tail s h j).1 ∈ CoreCounts.waiting r
          (core (processed S (r + 1)) (theta S) (1 / 125) (seedSize S n (r + 1) mu delta) Rw Rs (AdaptiveWindow.history s h))
          (seedSize S n (r + 1) mu delta) (theta S)} ≤
      ENNReal.ofReal ((((n : ℝ) + (mu : ℕ)) * ((S : ℕ) : ℝ) ^ 254 * logarithms n mu delta) / ((Rw : ℝ) + 1)) := by
  let astar := processed S (r + 1)
  let M := seedSize S n (r + 1) mu delta
  let C := starts (n := n) (mu := mu) B (r + 1) astar (theta S) (1 / 125) M Rw Rs e
  let cores := fun (s : Fin (B + 1)) (h : Fin (s.val + 1) → State n mu) ↦ core astar (theta S) (1 / 125) M Rw Rs h
  have hc := PhaseConditions.of_size S hS n (r + 1) mu delta (by omega) hrS hD hd hmu hn
  apply AdaptiveSeed.bound S hS hr hc.dimension hrS hD pc delta hpc hd hmu hn C cores
  · intro s h hh
    have hv := PolicyInvariant.path_valid astar (theta S) (1 / 125) M Rw Rs (processed_lt_theta S (r + 1))
      hRw hRs h hh.2.2.1 (Fin.last s.val)
    change PolicyInvariant.Valid astar (theta S) (1 / 125) M Rw Rs (h (Fin.last s.val)).1
      (fold (initial astar M) (tick astar (theta S) (1 / 125) M Rw Rs) h) at hv
    have hsmall : (r + 1 : ℝ) * M / (mu : ℕ) < 1 / 125 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hc.coreSmall
    have hp := WaitingCore.policy astar (theta S) (1 / 125) M Rw Rs (h (Fin.last s.val)).1
      (fold (initial astar M) (tick astar (theta S) (1 / 125) M Rw Rs) h) hh.2.2.2 hv hh.1.1 (by norm_num) hsmall
    exact ⟨hp.1, hp.2.1⟩
  · intro h s t hs ht
    apply PolicyPaths.unique_wait B Rw astar (theta S) (1 / 125) M Rw Rs e h s t
    · exact ⟨hs.1, hs.2.1⟩
    · exact ⟨ht.1, ht.2.1⟩

end
end Lax343628Proofs.PolicyWaitBound

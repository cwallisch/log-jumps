import Lax343628Proofs.PolicyWaitBound
import Lax343628Proofs.PolicyTimeout

namespace Lax343628Proofs.GlobalWait

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PhaseParameters Lax343628Proofs.EntropyLedger
open Lax343628Proofs.Trajectories Lax343628Proofs.FiniteEvents Lax343628Proofs.PolicyPaths
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r H : ℕ} {mu : ℕ+}

def failure (H k : ℕ) (astar theta omega : ℝ) (M Rw Rs e : ℕ) :
    Set (Fin (H + 1) → State n mu) :=
  {h | ∃ s : Fin (H + 1), ∃ hs : s.val + Rw ≤ H,
    isWaitStart (configuration astar theta omega M Rw Rs h s) ∧
    (configuration astar theta omega M Rw Rs h s).epoch = e ∧
    ColumnBlock.cap omega (h 0).1 ∧ (∀ u, (Sampling.zeros ((h s).1 u)).card = k) ∧
    ∀ j : Fin (Rw + 1), (PathWindows.window H Rw s.val hs h j).1 ∈ CoreCounts.waiting (k - 1)
      (configuration astar theta omega M Rw Rs h s).unprocessed M theta}

lemma episode (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (Rw Rs e : ℕ) (hRw : 0 < Rw) (hRs : 0 < Rs) (p : PMF (State n mu)) :
    (pathLaw (driver (r + 1) pc) p H).toOuterMeasure
      (failure H (r + 1) (processed S (r + 1)) (theta S) (1 / 125)
        (seedSize S n (r + 1) mu delta) Rw Rs e) ≤
      ENNReal.ofReal ((((n : ℝ) + (mu : ℕ)) * ((S : ℕ) : ℝ) ^ 254 * logarithms n mu delta) / ((Rw : ℝ) + 1)) := by
  by_cases hR : Rw ≤ H
  · obtain ⟨B, hB⟩ : ∃ B, H = B + Rw := ⟨H - Rw, by omega⟩
    subst H
    apply le_trans _ (PolicyWaitBound.bound S hS r hr hrS hD pc delta hpc hd hmu hn B Rw Rs e hRw hRs p)
    apply (pathLaw (driver (r + 1) pc) p (B + Rw)).toOuterMeasure.mono
    intro h hh
    obtain ⟨s, hs, hstart, he, hcap, hplat, hwindow⟩ := hh
    let s' : Fin (B + 1) := ⟨s.val, by omega⟩
    refine ⟨s', ⟨hstart, he, hcap, hplat⟩, ?_⟩
    change ∀ j : Fin (Rw + 1), (PathWindows.window (B + Rw) Rw s.val hs h j).1 ∈
      CoreCounts.waiting r (configuration (processed S (r + 1)) (theta S) (1 / 125)
        (seedSize S n (r + 1) mu delta) Rw Rs h s).unprocessed (seedSize S n (r + 1) mu delta) (theta S)
    simpa only [Nat.add_sub_cancel] using hwindow
  · rw [event_zero_of_support (pathLaw (driver (r + 1) pc) p H)
        (failure H (r + 1) (processed S (r + 1)) (theta S) (1 / 125)
          (seedSize S n (r + 1) mu delta) Rw Rs e) (by
        intro h _ hh
        obtain ⟨s, hs, _⟩ := hh
        omega)]
    exact zero_le

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (Rw Rs E : ℕ) (hRw : 0 < Rw) (hRs : 0 < Rs) (p : PMF (State n mu)) :
    (pathLaw (driver (r + 1) pc) p H).toOuterMeasure
      {h | ∃ e : Fin E, h ∈ failure H (r + 1) (processed S (r + 1)) (theta S) (1 / 125)
        (seedSize S n (r + 1) mu delta) Rw Rs e.val} ≤
      ENNReal.ofReal ((E : ℝ) * ((((n : ℝ) + (mu : ℕ)) * ((S : ℕ) : ℝ) ^ 254 * logarithms n mu delta) / ((Rw : ℝ) + 1))) := by
  have hq : 0 ≤ (((n : ℝ) + (mu : ℕ)) * ((S : ℕ) : ℝ) ^ 254 * logarithms n mu delta) / ((Rw : ℝ) + 1) := by
    have hW := (logarithms_bounds n mu delta hd).1
    positivity
  have hh := finite_union_bound (pathLaw (driver (r + 1) pc) p H) (Finset.univ : Finset (Fin E))
    (fun e ↦ failure H (r + 1) (processed S (r + 1)) (theta S) (1 / 125)
      (seedSize S n (r + 1) mu delta) Rw Rs e.val) _ hq
    (fun e _ ↦ episode S hS hr hrS hD pc delta hpc hd hmu hn Rw Rs e.val hRw hRs p)
  simpa only [Finset.mem_univ, true_and, Finset.card_univ, Fintype.card_fin] using hh

end
end Lax343628Proofs.GlobalWait

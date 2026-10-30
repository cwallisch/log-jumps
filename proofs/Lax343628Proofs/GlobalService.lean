import Lax343628Proofs.ServiceEstimate
import Lax343628Proofs.PhaseConditions

namespace Lax343628Proofs.GlobalService

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ColumnBlock Lax343628Proofs.BlockParameters Lax343628Proofs.EntropyLedger
open Lax343628Proofs.PhaseParameters Lax343628Proofs.Trajectories Lax343628Proofs.FiniteEvents
open Lax343628Proofs.PathWindows
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r H : ℕ} {mu : ℕ+}

def starts (k M : ℕ) (astar : ℝ) (i : Fin n) : Set (State n mu) :=
  {S | (∀ v, (Sampling.zeros (S.1 v)).card = k) ∧
    astar < fraction i 0 S.1 ∧ M ≤ CoreCounts.missingCount i S.1}

def failure (H R k M : ℕ) (astar omega : ℝ) (i : Fin n) (s : Fin (H + 1)) :
    Set (Fin (H + 1) → State n mu) :=
  {h | ∃ hs : s.val + R ≤ H,
    let w := window H R s.val hs h
    w 0 ∈ starts k M astar i ∧ ∀ j, astar < fraction i 0 (w j).1 ∧ cap omega (w j).1}

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc omega delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1)
    (hw : 1 / (S : ℕ) ≤ omega ∧ omega ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (p : PMF (State n mu)) :
    (pathLaw (driver (r + 1) pc) p H).toOuterMeasure
      {h | ∃ i : Fin n, ∃ s : Fin (H + 1), h ∈ failure H (rounds mu * horizon (S : ℕ) mu)
        (r + 1) (seedSize S n (r + 1) mu delta) (processed S (r + 1)) omega i s} ≤
      ENNReal.ofReal ((n : ℝ) * (((H : ℝ) + 1) *
        ((((rounds mu * horizon (S : ℕ) mu : ℕ) : ℝ) + 1) * delta))) := by
  let R := rounds mu * horizon (S : ℕ) mu
  let M := seedSize S n (r + 1) mu delta
  let a := processed S (r + 1)
  let q : ℝ := ((R : ℝ) + 1) * delta
  have hq : 0 ≤ q := mul_nonneg (by positivity) hd.1.le
  have hc := PhaseConditions.of_size S hS n (r + 1) mu delta (by omega) hrS hD hd hmu hn
  have ha := processed_bounds S (r + 1)
  have hmass := PhaseScale.mass_available S n mu delta hd hmu
  have hblock (i : Fin n) (T : State n mu) (hT : T ∈ starts (r + 1) M a i) :
      (pathLaw (driver (r + 1) pc) (PMF.pure T) R).toOuterMeasure
        {h | ∀ j, a < fraction i 0 (h j).1 ∧ cap omega (h j).1} ≤ ENNReal.ofReal q := by
    apply ServiceEstimate.bound S hS hr hc.dimension hrS hD pc omega a delta hpc hw hd
      ⟨hc.processedLower, ha.2⟩ (rounds_lower mu) hmass hc.serviceMass hc.serviceDimension i T hT.1
      (ha.1.trans hT.2.1)
    rw [CoreCounts.missing_fraction, mul_div_cancel₀ _ (by exact_mod_cast (ne_of_gt mu.pos))]
    have hseed := seed_lower S n (r + 1) mu delta
    have hcount : (M : ℝ) ≤ CoreCounts.missingCount i T.1 := by exact_mod_cast hT.2.2
    have hnonneg : 0 ≤ (3 : ℝ) ^ (r + 1) * mass S n mu delta := by
      have hm := mass_one S n mu delta hd
      positivity
    dsimp only [M] at hcount
    linarith
  have hcolumn (i : Fin n) :
      (pathLaw (driver (r + 1) pc) p H).toOuterMeasure
        {h | ∃ s : Fin (H + 1), h ∈ failure H R (r + 1) M a omega i s} ≤
          ENNReal.ofReal (((H : ℝ) + 1) * q) := by
    have hh := finite_union_bound (pathLaw (driver (r + 1) pc) p H)
      (Finset.univ : Finset (Fin (H + 1))) (failure H R (r + 1) M a omega i) q hq (by
        intro s _
        by_cases hs : s.val + R ≤ H
        · apply le_trans _ (window_dependent_bound (driver (r + 1) pc) p H R s.val hs
            (starts (r + 1) M a i) (fun _ ↦ {h | ∀ j, a < fraction i 0 (h j).1 ∧ cap omega (h j).1}) _ (hblock i))
          apply (pathLaw (driver (r + 1) pc) p H).toOuterMeasure.mono
          intro h hh
          exact hh.2
        · rw [event_zero_of_support (pathLaw (driver (r + 1) pc) p H)
            (failure H R (r + 1) M a omega i s) (by intro h _ hh; exact hs hh.1)]
          exact zero_le)
    simpa only [Finset.mem_univ, true_and, Finset.card_univ, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one] using hh
  have hh := finite_union_bound (pathLaw (driver (r + 1) pc) p H)
    (Finset.univ : Finset (Fin n)) (fun i ↦ {h | ∃ s, h ∈ failure H R (r + 1) M a omega i s})
    (((H : ℝ) + 1) * q) (mul_nonneg (by positivity) hq) (fun i _ ↦ hcolumn i)
  simpa only [Finset.mem_univ, true_and, Finset.card_univ, Fintype.card_fin, Set.mem_ofPred_eq, R, M, a, q] using hh

end
end Lax343628Proofs.GlobalService

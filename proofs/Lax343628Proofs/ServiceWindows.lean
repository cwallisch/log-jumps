import Lax343628Proofs.ServicePath
import Lax343628Proofs.DrivenPlateau

namespace Lax343628Proofs.ServiceWindows

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ColumnBlock Lax343628Proofs.ColumnEndpoint Lax343628Proofs.ColumnBudget
open Lax343628Proofs.ServiceGeometry Lax343628Proofs.Trajectories Lax343628Proofs.PathWindows
open Lax343628Proofs.FiniteEvents Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k r H R ell : ℕ} {mu rs : ℕ+}

def starts (k : ℕ) (i : Fin n) (a O0 : ℝ) : Set (State n mu) :=
  {S | (∀ v, (Sampling.zeros (S.1 v)).card = k) ∧
    a < fraction i 0 S.1 ∧ O0 ≤ Odds.value i S.1}

def blockFailure (k : ℕ) (i : Fin n) (a omega : ℝ) (S : State n mu) :
    Set (Fin (R + 1) → State n mu) :=
  {h | ¬good i (Odds.value i S.1 / (4 * (3 : ℝ) ^ k)) (target a (Odds.value i S.1)) omega
    (frozen {T | active k i (Odds.value i S.1 / (4 * (3 : ℝ) ^ k))
      (target a (Odds.value i S.1)) omega T.1} h)}

lemma uniform_block (hr : 1 ≤ r) (pc alpha a O0 omega L : ℝ)
    (ha : 0 < a) (hO0 : 0 < O0) (i : Fin n)
    (hb : ∀ S : State n mu, S ∈ starts (r + 1) i a O0 →
      Budget n (r + 1) R ell mu rs pc alpha
        (Odds.lowerMass (Odds.value i S.1 / (4 * (3 : ℝ) ^ (r + 1))))
        (Odds.upperMass (target a (Odds.value i S.1)))
        (Odds.lowerMass (target a (Odds.value i S.1))) omega L 8)
    (S : State n mu) (hS : S ∈ starts (r + 1) i a O0) :
    (pathLaw (driver (r + 1) pc) (PMF.pure S) R).toOuterMeasure
      (blockFailure (R := R) (r + 1) i a omega S) ≤
      ENNReal.ofReal ((4 * (Fintype.card (Net n (r + 1) R (count R ell) rs) : ℝ) *
        ((R : ℝ) + 1) + 1) * Real.exp (-L)) := by
  have hO := hO0.trans_le hS.2.2
  have hf := Odds.positive_fractions i S.1 hO
  have ht := target_bounds a _ hO (odds_below_final i S.1 a ha hS.2.1)
  exact original_failure_bound hr pc alpha omega L 8 (target a (Odds.value i S.1)) i S hS.1
    (by intro b; fin_cases b <;> tauto) (by norm_num) ht.1 ht.2 (hb S hS)

def windowFailure (H R k : ℕ) (i : Fin n) (a O0 omega : ℝ) (s : Fin (H + 1)) :
    Set (Fin (H + 1) → State n mu) :=
  {h | ∃ hs : s.val + R ≤ H,
    let w := window H R s.val hs h
    w 0 ∈ starts k i a O0 ∧ w ∈ blockFailure (R := R) k i a omega (w 0)}

lemma union_bound (k : ℕ) (pc a O0 omega : ℝ) (i : Fin n) (q : ℝ) (hq : 0 ≤ q)
    (hblock : ∀ S ∈ starts (mu := mu) k i a O0,
      (pathLaw (driver k pc) (PMF.pure S) R).toOuterMeasure
        (blockFailure (R := R) k i a omega S) ≤ ENNReal.ofReal q)
    (p : PMF (State n mu)) :
    (pathLaw (driver k pc) p H).toOuterMeasure
      {h | ∃ s : Fin (H + 1), h ∈ windowFailure H R k i a O0 omega s} ≤
      ENNReal.ofReal (((H : ℝ) + 1) * q) := by
  have hh := finite_union_bound (pathLaw (driver k pc) p H)
    (Finset.univ : Finset (Fin (H + 1))) (windowFailure H R k i a O0 omega) q hq
    (by
      intro s _
      by_cases hs : s.val + R ≤ H
      · apply le_trans _ (window_dependent_bound (driver k pc) p H R s.val hs
          (starts k i a O0) (blockFailure (R := R) k i a omega) _ hblock)
        apply event_mono_on_support
        intro h _ hbad
        obtain ⟨hs', hstart, hf⟩ := hbad
        exact ⟨hstart, hf⟩
      · rw [event_zero_of_support (pathLaw (driver k pc) p H)
          (windowFailure H R k i a O0 omega s) (by intro h _ hbad; exact hs hbad.1)]
        exact zero_le)
  simpa only [Finset.mem_univ, true_and, Finset.card_univ, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one] using hh

end
end Lax343628Proofs.ServiceWindows

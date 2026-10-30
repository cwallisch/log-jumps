import Lax343628Proofs.ProtectionGeometry
import Lax343628Proofs.PathWindows
import Lax343628Proofs.LastExit

namespace Lax343628Proofs.ProtectionWindows

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ColumnBlock Lax343628Proofs.ColumnEndpoint Lax343628Proofs.ColumnBudget
open Lax343628Proofs.Trajectories Lax343628Proofs.PathWindows Lax343628Proofs.FiniteEvents
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k r R J ell : ℕ} {mu rs : ℕ+}

def starts (k : ℕ) (i : Fin n) (u : ℝ) : Set (State n mu) :=
  {S | (∀ v, (Sampling.zeros (S.1 v)).card = k) ∧
    u ≤ fraction i 0 S.1 ∧ fraction i 0 S.1 ≤ 2 * u}

def blockFailure (k : ℕ) (i : Fin n) (omega : ℝ) (S : State n mu) :
    Set (Fin (R + 1) → State n mu) :=
  {h | ¬good i (Odds.value i S.1 / (4 * (3 : ℝ) ^ k)) (8 * Odds.value i S.1) omega
    (frozen {T | active k i (Odds.value i S.1 / (4 * (3 : ℝ) ^ k))
      (8 * Odds.value i S.1) omega T.1} h)}

lemma uniform_block (hr : 1 ≤ r) (pc a u omega L : ℝ)
    (hu : 0 < u) (huquarter : u ≤ 1 / 4) (i : Fin n)
    (hb : ∀ S : State n mu, S ∈ starts (r + 1) i u →
      Budget n (r + 1) R ell mu rs pc a
        (Odds.lowerMass (Odds.value i S.1 / (4 * (3 : ℝ) ^ (r + 1))))
        (Odds.upperMass (8 * Odds.value i S.1))
        (Odds.lowerMass (8 * Odds.value i S.1)) omega L 8)
    (S : State n mu) (hS : S ∈ starts (r + 1) i u) :
    (pathLaw (driver (r + 1) pc) (PMF.pure S) R).toOuterMeasure
      (blockFailure (R := R) (r + 1) i omega S) ≤
      ENNReal.ofReal ((4 * (Fintype.card (Net n (r + 1) R (count R ell) rs) : ℝ) *
        ((R : ℝ) + 1) + 1) * Real.exp (-L)) := by
  have ha : 0 < fraction i 0 S.1 := hu.trans_le hS.2.1
  have hf : 0 < fraction i 1 S.1 := by
    have hh := ClassMeanDynamics.fraction_sum i S.1
    linarith [hS.2.2]
  have hO : 0 < Odds.value i S.1 := div_pos hf ha
  exact original_failure_bound hr pc a omega L 8 (8 * Odds.value i S.1) i S hS.1
    (by intro b; fin_cases b <;> assumption) (by norm_num) (by linarith) le_rfl (hb S hS)

def windowFailure (J R k : ℕ) (i : Fin n) (u omega : ℝ) (s : Fin (J + 1)) :
    Set (Fin (J + R + 1) → State n mu) :=
  {h | let w := window (J + R) R s.val (by have := s.isLt; omega) h
    w 0 ∈ starts k i u ∧ w ∈ blockFailure (R := R) k i omega (w 0)}

lemma union_bound (hr : 1 ≤ r) (pc a u omega L : ℝ)
    (hu : 0 < u) (huquarter : u ≤ 1 / 4) (i : Fin n)
    (hb : ∀ S : State n mu, S ∈ starts (r + 1) i u →
      Budget n (r + 1) R ell mu rs pc a
        (Odds.lowerMass (Odds.value i S.1 / (4 * (3 : ℝ) ^ (r + 1))))
        (Odds.upperMass (8 * Odds.value i S.1))
        (Odds.lowerMass (8 * Odds.value i S.1)) omega L 8)
    (p : PMF (State n mu)) :
    (pathLaw (driver (r + 1) pc) p (J + R)).toOuterMeasure
      {h | ∃ s : Fin (J + 1), h ∈ windowFailure J R (r + 1) i u omega s} ≤
      ENNReal.ofReal (((J : ℝ) + 1) *
        ((4 * (Fintype.card (Net n (r + 1) R (count R ell) rs) : ℝ) *
          ((R : ℝ) + 1) + 1) * Real.exp (-L))) := by
  have hh := finite_union_bound (pathLaw (driver (r + 1) pc) p (J + R))
    (Finset.univ : Finset (Fin (J + 1))) (windowFailure J R (r + 1) i u omega)
    ((4 * (Fintype.card (Net n (r + 1) R (count R ell) rs) : ℝ) *
      ((R : ℝ) + 1) + 1) * Real.exp (-L)) (by positivity)
    (fun s _ ↦ window_dependent_bound (driver (r + 1) pc) p (J + R) R s.val
      (by have := s.isLt; omega) (starts (r + 1) i u) (blockFailure (R := R) (r + 1) i omega) _
      (uniform_block hr pc a u omega L hu huquarter i hb))
  simpa only [Finset.mem_univ, true_and, Finset.card_univ, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one] using hh

end
end Lax343628Proofs.ProtectionWindows

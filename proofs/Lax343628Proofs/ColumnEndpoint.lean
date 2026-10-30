import Lax343628Proofs.ColumnBlock
import Lax343628Proofs.DrivenStop

namespace Lax343628Proofs.ColumnEndpoint

open Lax343628.Algorithm Lax343628Proofs.ColumnBudget Lax343628Proofs.ColumnBlock
open Lax343628Proofs.DrivenNoise Lax343628Proofs.DrivenPaths Lax343628Proofs.DrivenStop
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain Lax343628Proofs.Trajectories
open Lax343628Proofs.ClassChannels Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r R ell : ℕ} {mu rs : ℕ+}

lemma constant_after_inactive {k : ℕ} (pc : ℝ) (active : Population n mu → Prop) [DecidablePred active]
    (p : PMF (State n mu)) (h : Fin (R + 1) → State n mu)
    (hh : h ∈ (pathLaw (stopped (driver k pc) {S | active S.1}) p R).support)
    (H : Fin (R + 1)) (hnot : ¬active (population h H.val)) :
    ∀ t, H.val ≤ t → t ≤ R → extend h t = extend h H.val := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro _; rfl
  | succ t ht ih =>
    intro htR
    have he := ih (by omega)
    have hnot' : ¬active (population h t) := by change ¬active (extend h t).1; rw [he]; exact hnot
    have hs := extend_step_support (stopped (driver k pc) {S | active S.1}) p h hh t (by omega)
    rw [stopped] at hs
    simp only [Set.mem_ofPred_eq, if_neg hnot'] at hs
    exact ((PMF.mem_support_pure_iff _ _).mp hs).trans he

lemma population_last {k : ℕ} (pc : ℝ) (active : Population n mu → Prop) [DecidablePred active]
    (p : PMF (State n mu)) (h : Fin (R + 1) → State n mu)
    (hh : h ∈ (Trajectories.pathLaw (FiniteDrift.stopped (driver k pc) {S | active S.1}) p R).support) :
    (h (Fin.last R)).1 = population h (time active h).val := by
  have hext : extend h R = h (Fin.last R) := by rw [extend_at h R le_rfl]; rfl
  by_cases he : (time active h).val = R
  · rw [he]
    exact congrArg Prod.fst hext.symm
  · have hnot := (time_spec active h).resolve_left he
    have hc := constant_after_inactive pc active p h hh (time active h) hnot R
      (Nat.le_of_lt_succ (time active h).isLt) le_rfl
    rw [hext] at hc
    exact congrArg Prod.fst hc

def good (i : Fin n) (lo hi omega : ℝ) (S : State n mu) : Prop :=
  lo < Odds.value i S.1 ∧ (hi ≤ Odds.value i S.1 ∨ ¬cap omega S.1)

lemma failure_bound (hr : 1 ≤ r) (pc a omega L B hi : ℝ) (i : Fin n)
    (S0 : State n mu) (hP0 : ∀ u, (Sampling.zeros (S0.1 u)).card = r + 1)
    (hf0 : ∀ b : Fin 2, 0 < fraction i b S0.1) (hB : 0 < B)
    (hhi : Odds.value i S0.1 < hi) (hupper : hi ≤ B * Odds.value i S0.1)
    (hb : Budget n (r + 1) R ell mu rs pc a
      (Odds.lowerMass (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))))
      (Odds.upperMass hi) (Odds.lowerMass hi) omega L B) :
    (law (stopped (driver (r + 1) pc)
      {S | active (r + 1) i (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))) hi omega S.1}) (PMF.pure S0) R).toOuterMeasure
      {S | ¬good i (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))) hi omega S} ≤
      ENNReal.ofReal ((4 * (Fintype.card (Net n (r + 1) R (count R ell) rs) : ℝ) * ((R : ℝ) + 1) + 1) * Real.exp (-L)) := by
  let lo := Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))
  let A : Population n mu → Prop := active (r + 1) i lo hi omega
  rw [← pathLaw_last, PMF.toOuterMeasure_map_apply]
  apply le_trans _ (ColumnBlock.failure_bound hr pc a omega L B hi i S0 hP0 hf0 hB hhi hupper hb)
  apply FiniteEvents.event_mono_on_support
  intro h hh hbad
  have he := population_last pc A (PMF.pure S0) h hh
  change ¬(lo < Odds.value i (h (Fin.last R)).1 ∧ (hi ≤ Odds.value i (h (Fin.last R)).1 ∨ ¬cap omega (h (Fin.last R)).1)) at hbad
  rw [he] at hbad
  exact hbad

lemma original_failure_bound (hr : 1 ≤ r) (pc a omega L B hi : ℝ) (i : Fin n)
    (S0 : State n mu) (hP0 : ∀ u, (Sampling.zeros (S0.1 u)).card = r + 1)
    (hf0 : ∀ b : Fin 2, 0 < fraction i b S0.1) (hB : 0 < B)
    (hhi : Odds.value i S0.1 < hi) (hupper : hi ≤ B * Odds.value i S0.1)
    (hb : Budget n (r + 1) R ell mu rs pc a
      (Odds.lowerMass (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))))
      (Odds.upperMass hi) (Odds.lowerMass hi) omega L B) :
    (pathLaw (driver (r + 1) pc) (PMF.pure S0) R).toOuterMeasure
      {h | ¬good i (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))) hi omega
        (frozen {S | active (r + 1) i (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))) hi omega S.1} h)} ≤
      ENNReal.ofReal ((4 * (Fintype.card (Net n (r + 1) R (count R ell) rs) : ℝ) * ((R : ℝ) + 1) + 1) * Real.exp (-L)) := by
  let lo := Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))
  let A : Set (State n mu) := {S | active (r + 1) i lo hi omega S.1}
  change (pathLaw (driver (r + 1) pc) (PMF.pure S0) R).toOuterMeasure
    ((frozen A) ⁻¹' {S | ¬good i lo hi omega S}) ≤ _
  rw [← PMF.toOuterMeasure_map_apply, frozen_pathLaw]
  exact failure_bound hr pc a omega L B hi i S0 hP0 hf0 hB hhi hupper hb

end
end Lax343628Proofs.ColumnEndpoint

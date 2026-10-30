import Lax343628Proofs.ColumnEndpoint

namespace Lax343628Proofs.ServiceGeometry

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.ClassMeanDynamics
open Lax343628Proofs.DrivenNoise Lax343628Proofs.ColumnBlock Lax343628Proofs.ColumnEndpoint
open Lax343628Proofs.Trajectories
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n R : ℕ} {mu : ℕ+}

def finalOdds (a : ℝ) : ℝ := (1 - a) / a

def target (a O : ℝ) : ℝ := min (8 * O) (finalOdds a)

lemma odds_below_final (i : Fin n) (P : Population n mu) (a : ℝ) (ha : 0 < a)
    (hP : a < fraction i 0 P) : Odds.value i P < finalOdds a := by
  have hp : 0 < fraction i 0 P := ha.trans hP
  unfold Odds.value finalOdds
  apply (div_lt_div_iff₀ hp ha).mpr
  have hs := fraction_sum i P
  nlinarith

lemma final_of_odds (i : Fin n) (P : Population n mu) (a : ℝ) (ha : 0 < a)
    (hO : finalOdds a ≤ Odds.value i P) : fraction i 0 P ≤ a := by
  by_contra hn
  exact (not_lt_of_ge hO) (odds_below_final i P a ha (lt_of_not_ge hn))

lemma target_bounds (a O : ℝ) (hO : 0 < O) (hfinal : O < finalOdds a) :
    O < target a O ∧ target a O ≤ 8 * O := by
  exact ⟨lt_min (by linarith) hfinal, min_le_left _ _⟩

lemma target_progress (i : Fin n) (P : Population n mu) (a O : ℝ) (ha : 0 < a)
    (hO : target a O ≤ Odds.value i P) :
    fraction i 0 P ≤ a ∨ 8 * O ≤ Odds.value i P := by
  by_cases hfin : finalOdds a ≤ 8 * O
  · left
    apply final_of_odds i P a ha
    simpa only [target, min_eq_right hfin] using hO
  · right
    simpa only [target, min_eq_left (le_of_not_ge hfin)] using hO

lemma mutant_mono (i : Fin n) (P Q : Population n mu)
    (hP : 0 < fraction i 0 P) (hQ : 0 < fraction i 0 Q)
    (hO : Odds.value i P ≤ Odds.value i Q) : fraction i 1 P ≤ fraction i 1 Q := by
  have hOp : 0 ≤ Odds.value i P := div_nonneg (fraction_bounds i 1 P).1 hP.le
  have hh := Odds.lowerMass_mono hOp hO
  rwa [(Odds.exact_fractions i P hP).1, (Odds.exact_fractions i Q hQ).1] at hh

lemma good_progress (k : ℕ) (i : Fin n) (a omega : ℝ) (ha : 0 < a)
    (S : State n mu) (h : Fin (R + 1) → State n mu)
    (hg : good i (Odds.value i S.1 / (4 * (3 : ℝ) ^ k)) (target a (Odds.value i S.1)) omega
      (frozen {T | active k i (Odds.value i S.1 / (4 * (3 : ℝ) ^ k))
        (target a (Odds.value i S.1)) omega T.1} h)) :
    ∃ j, fraction i 0 (h j).1 ≤ a ∨ ¬cap omega (h j).1 ∨
      8 * Odds.value i S.1 ≤ Odds.value i (h j).1 := by
  obtain ⟨j, hj⟩ := frozen_mem_range
    {T : State n mu | active k i (Odds.value i S.1 / (4 * (3 : ℝ) ^ k))
      (target a (Odds.value i S.1)) omega T.1} h
  rw [hj] at hg
  refine ⟨j, ?_⟩
  rcases hg.2 with htarget | hcap
  · rcases target_progress i (h j).1 a _ ha htarget with hdone | hmult
    · exact Or.inl hdone
    · exact Or.inr (Or.inr hmult)
  · exact Or.inr (Or.inl hcap)

end
end Lax343628Proofs.ServiceGeometry

import Lax343628Proofs.PolicyCounters

namespace Lax343628Proofs.PolicyRank

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {mu : ℕ+}

def valid (q : Config n) : Prop := ∀ i, q.stage = Stage.serving i → i ∈ q.unprocessed

def rank (q : Config n) : ℕ := 2 * q.unprocessed.card + if q.stage = Stage.waiting then 1 else 0

lemma rank_upper (q : Config n) : rank q ≤ 2 * q.unprocessed.card + 1 := by
  unfold rank
  split_ifs <;> omega

lemma setup_valid (astar : ℝ) (M : ℕ) (P : Population n mu) (U : Finset (Fin n)) (e : ℕ) :
    valid (setup astar M P U e) := by
  intro i hi
  exact (setup_serving astar M P U e i hi).1

lemma tick_valid (astar theta omega : ℝ) (M Rw Rs : ℕ) (q : Config n) (S : State n mu) (hqv : valid q) :
    valid (tick astar theta omega M Rw Rs q S) := by
  intro i hserve
  cases hq : q.stage <;>
    simp only [tick, hq, reduceCtorEq, or_false, or_true, if_true, if_false] at hserve ⊢
  all_goals try split_ifs at hserve ⊢
  all_goals try simp_all only [stop, reduceCtorEq]
  all_goals first
    | exact (setup_serving _ _ _ _ _ i hserve).1
    | exact hqv i (by assumption)

lemma setup_rank (astar : ℝ) (M : ℕ) (P : Population n mu) (U : Finset (Fin n)) (e : ℕ) :
    rank (setup astar M P U e) ≤ 2 * (ColumnMarks.refresh U astar P).card + 1 := by
  have hh := rank_upper (setup astar M P U e)
  rwa [setup_unprocessed] at hh

lemma waiting_decreases (astar : ℝ) (M : ℕ) (P : Population n mu) (U : Finset (Fin n)) (e : ℕ)
    (hready : (ready U M P).Nonempty) : rank (setup astar M P U e) + 1 ≤ 2 * U.card + 1 := by
  have hrank := setup_rank astar M P U e
  have hsub := ColumnMarks.refresh_subset U astar P
  have hcard := Finset.card_le_card hsub
  by_cases hlt : (ColumnMarks.refresh U astar P).card < U.card
  · omega
  · have heq : ColumnMarks.refresh U astar P = U := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hnot : (setup astar M P U e).stage ≠ Stage.waiting := by
      intro hw
      have hh := (setup_waiting astar M P U e hw).2
      rw [setup_unprocessed, heq] at hh
      exact hh hready
    unfold rank
    rw [setup_unprocessed, if_neg hnot]
    omega

lemma serving_decreases (astar : ℝ) (M : ℕ) (P : Population n mu) (U : Finset (Fin n)) (e : ℕ)
    (i : Fin n) (hi : i ∈ U) (hprocess : ClassChannels.fraction i 0 P ≤ astar) :
    rank (setup astar M P U e) + 1 ≤ 2 * U.card := by
  have hrank := setup_rank astar M P U e
  have hcard := ColumnMarks.refresh_removed U astar P i hi hprocess
  omega

lemma stop_rank (q : Config n) (stage : Stage n) (hstage : stage ≠ Stage.waiting) : rank (stop q stage) ≤ rank q := by
  unfold rank stop
  simp only [if_neg hstage]
  split_ifs <;> omega

lemma stop_combined (q : Config n) (stage : Stage n) (hstage : stage ≠ Stage.waiting) :
    (stop q stage).epoch + rank (stop q stage) ≤ q.epoch + rank q := by
  change q.epoch + rank (stop q stage) ≤ q.epoch + rank q
  exact Nat.add_le_add_left (stop_rank q stage hstage) _

lemma step (astar theta omega : ℝ) (M Rw Rs : ℕ) (q : Config n) (S : State n mu) (hqv : valid q) :
    (tick astar theta omega M Rw Rs q S).epoch + rank (tick astar theta omega M Rw Rs q S) ≤ q.epoch + rank q := by
  cases hq : q.stage <;>
    simp only [tick, hq, reduceCtorEq, or_false, or_true, if_true, if_false]
  all_goals try split_ifs
  all_goals first
    | exact le_rfl
    | exact stop_combined q Stage.success (by intro hh; cases hh)
    | exact stop_combined q Stage.failure (by intro hh; cases hh)
    | (simp only [rank, hq, reduceCtorEq, if_true, if_false]; omega)
    | (have hh := waiting_decreases astar M S.1 q.unprocessed (q.epoch + 1) (by assumption)
       rw [setup_epoch]
       have hr : rank q = 2 * q.unprocessed.card + 1 := by simp only [rank, hq, if_true]
       omega)
    | (have hh := serving_decreases astar M S.1 q.unprocessed (q.epoch + 1) _ (hqv _ hq) (by assumption)
       rw [setup_epoch]
       have hr : rank q = 2 * q.unprocessed.card := by simp only [rank, hq, reduceCtorEq, if_false, add_zero]
       omega)

end
end Lax343628Proofs.PolicyRank

import Lax343628Proofs.ColumnMarks
import Lax343628Proofs.HistoryFold

namespace Lax343628Proofs.AttemptPolicy

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.CoreCounts
open Lax343628Proofs.ColumnBlock Lax343628Proofs.DrivenNoise
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive Stage (n : ℕ) where
  | waiting
  | serving (i : Fin n)
  | terminal
  | success
  | failure
  deriving DecidableEq

structure Config (n : ℕ) where
  unprocessed : Finset (Fin n)
  stage : Stage n
  age : ℕ
  epoch : ℕ

variable {n : ℕ} {mu : ℕ+}

def ready (U : Finset (Fin n)) (M : ℕ) (P : Population n mu) : Finset (Fin n) :=
  U.filter (fun i ↦ M ≤ missingCount i P)

def setup (astar : ℝ) (M : ℕ) (P : Population n mu) (U : Finset (Fin n)) (epoch : ℕ) : Config n :=
  let V := ColumnMarks.refresh U astar P
  if _hV : V.Nonempty then
    if hR : (ready V M P).Nonempty then ⟨V, Stage.serving ((ready V M P).min' hR), 0, epoch⟩
    else ⟨V, Stage.waiting, 0, epoch⟩
  else ⟨V, Stage.terminal, 0, epoch⟩

def stop (q : Config n) (stage : Stage n) : Config n := {q with stage := stage, age := 0}

def tick (astar theta omega : ℝ) (M Rw Rs : ℕ) (q : Config n) (S : State n mu) : Config n :=
  if q.stage = Stage.success ∨ q.stage = Stage.failure then q
  else if S.2.2.1 = optimum n then stop q Stage.success
  else if ¬cap omega S.1 then stop q Stage.failure
  else if ∃ i, i ∉ q.unprocessed ∧ theta ≤ fraction i 0 S.1 then stop q Stage.failure
  else match q.stage with
    | Stage.waiting =>
        if (ready q.unprocessed M S.1).Nonempty then setup astar M S.1 q.unprocessed (q.epoch + 1)
        else if Rw ≤ q.age + 1 then stop q Stage.failure
        else {q with age := q.age + 1}
    | Stage.serving i =>
        if fraction i 0 S.1 ≤ astar then setup astar M S.1 q.unprocessed (q.epoch + 1)
        else if Rs ≤ q.age + 1 then stop q Stage.failure
        else {q with age := q.age + 1}
    | _ => q

def initial (astar : ℝ) (M : ℕ) (S : State n mu) : Config n := setup astar M S.1 Finset.univ 0

def isWaitStart (q : Config n) : Prop := q.stage = Stage.waiting ∧ q.age = 0

lemma setup_unprocessed (astar : ℝ) (M : ℕ) (P : Population n mu) (U : Finset (Fin n)) (e : ℕ) :
    (setup astar M P U e).unprocessed = ColumnMarks.refresh U astar P := by
  dsimp only [setup]
  split_ifs <;> rfl

lemma setup_epoch (astar : ℝ) (M : ℕ) (P : Population n mu) (U : Finset (Fin n)) (e : ℕ) :
    (setup astar M P U e).epoch = e := by dsimp only [setup]; split_ifs <;> rfl

lemma setup_age (astar : ℝ) (M : ℕ) (P : Population n mu) (U : Finset (Fin n)) (e : ℕ) :
    (setup astar M P U e).age = 0 := by dsimp only [setup]; split_ifs <;> rfl

lemma setup_waiting (astar : ℝ) (M : ℕ) (P : Population n mu) (U : Finset (Fin n)) (e : ℕ)
    (hwait : (setup astar M P U e).stage = Stage.waiting) :
    (setup astar M P U e).unprocessed.Nonempty ∧
      ¬(ready (setup astar M P U e).unprocessed M P).Nonempty := by
  rw [setup_unprocessed]
  dsimp only [setup] at hwait
  split_ifs at hwait with hV hR
  exact ⟨hV, hR⟩

lemma setup_serving (astar : ℝ) (M : ℕ) (P : Population n mu) (U : Finset (Fin n)) (e : ℕ)
    (i : Fin n) (hserve : (setup astar M P U e).stage = Stage.serving i) :
    i ∈ (setup astar M P U e).unprocessed ∧ astar < fraction i 0 P ∧ M ≤ missingCount i P := by
  rw [setup_unprocessed]
  dsimp only [setup] at hserve
  split_ifs at hserve with hV hR
  have hi : (ready (ColumnMarks.refresh U astar P) M P).min' hR = i := by injection hserve
  have hm := Finset.min'_mem (ready (ColumnMarks.refresh U astar P) M P) hR
  rw [hi] at hm
  have hh := Finset.mem_filter.mp hm
  exact ⟨hh.1, (Finset.mem_filter.mp hh.1).2, hh.2⟩

end
end Lax343628Proofs.AttemptPolicy

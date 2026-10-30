import Lax343628Proofs.SparseNoise

namespace Lax343628Proofs.UniformNoise

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open Lax343628Proofs.SparseNoise Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ClassChannels Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteChain Lax343628Proofs.Trajectories Lax343628Proofs.PathNoise
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {rs mu : ℕ+}

lemma mutant_uniform (hk : 2 ≤ k) (hn : 4 * k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (i : Fin n) (a : ℝ) (ha : 0 ≤ a) (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (ref : ColumnClass n k i 1) (fmin : ℝ) (hfmin : 0 < fmin)
    (active : Population n mu → Prop) [DecidablePred active]
    (hP : ∀ P, active P → ∀ u, (Sampling.zeros (P u)).card = k)
    (hf : ∀ P, active P → fmin ≤ fraction i 1 P) (p : PMF (State n mu))
    (bound L : ℝ) (hbound : 0 < bound) (hL : 0 < L)
    (hstep : 2 * (4 * ((3 : ℝ) ^ k) ^ 2 / ((mu : ℕ) * fmin)) * L ≤ bound)
    (hvar : 4 * R * (3 * ((3 : ℝ) ^ k) ^ 4 / (((mu : ℕ) : ℝ) ^ 2 * fmin)) * L ≤ bound ^ 2) :
    (pathLaw (stopped (driver k pc) {S | active S.1}) p R).toOuterMeasure {h |
      ∃ sigma : Net n k R (count R ell) rs, ∃ T : Fin (R + 1), bound ≤
        |accumulate (increment (noise sigma pc i 1 a) active R) T.val
          (before R T.val (by have := T.isLt; omega) h)|} ≤
      ENNReal.ofReal (2 * (Fintype.card (Net n k R (count R ell) rs) : ℝ) * ((R : ℝ) + 1) * Real.exp (-L)) := by
  apply budget_noise_bound k pc p (fun sigma ↦ noise sigma pc i 1 a) active R
    (4 * ((3 : ℝ) ^ k) ^ 2 / ((mu : ℕ) * fmin))
    (3 * ((3 : ℝ) ^ k) ^ 4 / (((mu : ℕ) : ℝ) ^ 2 * fmin)) bound L
    (by positivity) hbound hL hstep hvar
  · intro sigma t P _ _
    exact mean_noise sigma pc i 1 a t P
  · intro sigma t P E _ hact
    exact (mutant_bounds hk hn sigma pc hpc i a ha horizon P (hP P hact) ref fmin hfmin (hf P hact) t).1 E
  · intro sigma t P _ hact
    exact (mutant_bounds hk hn sigma pc hpc i a ha horizon P (hP P hact) ref fmin hfmin (hf P hact) t).2

lemma resident_uniform (hk : 2 ≤ k) (hn : 4 * k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (i : Fin n) (a : ℝ) (ha : 0 ≤ a) (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (ref : ColumnClass n k i 0) (amin : ℝ) (hamin : 0 < amin)
    (active : Population n mu → Prop) [DecidablePred active]
    (hP : ∀ P, active P → ∀ u, (Sampling.zeros (P u)).card = k)
    (hf : ∀ P, active P → amin ≤ fraction i 0 P)
    (himm : ∀ P, active P → fraction i 1 P / n ≤ fraction i 0 P) (p : PMF (State n mu))
    (bound L : ℝ) (hbound : 0 < bound) (hL : 0 < L)
    (hstep : 2 * (5 * ((3 : ℝ) ^ k) ^ 2 / ((mu : ℕ) * amin)) * L ≤ bound)
    (hvar : 4 * R * (4 * ((3 : ℝ) ^ k) ^ 4 / (((mu : ℕ) : ℝ) ^ 2 * amin)) * L ≤ bound ^ 2) :
    (pathLaw (stopped (driver k pc) {S | active S.1}) p R).toOuterMeasure {h |
      ∃ sigma : Net n k R (count R ell) rs, ∃ T : Fin (R + 1), bound ≤
        |accumulate (increment (noise sigma pc i 0 a) active R) T.val
          (before R T.val (by have := T.isLt; omega) h)|} ≤
      ENNReal.ofReal (2 * (Fintype.card (Net n k R (count R ell) rs) : ℝ) * ((R : ℝ) + 1) * Real.exp (-L)) := by
  apply budget_noise_bound k pc p (fun sigma ↦ noise sigma pc i 0 a) active R
    (5 * ((3 : ℝ) ^ k) ^ 2 / ((mu : ℕ) * amin))
    (4 * ((3 : ℝ) ^ k) ^ 4 / (((mu : ℕ) : ℝ) ^ 2 * amin)) bound L
    (by positivity) hbound hL hstep hvar
  · intro sigma t P _ _
    exact mean_noise sigma pc i 0 a t P
  · intro sigma t P E _ hact
    exact (resident_bounds hk hn sigma pc hpc i a ha horizon P (hP P hact) ref amin hamin (hf P hact) (himm P hact) t).1 E
  · intro sigma t P _ hact
    exact (resident_bounds hk hn sigma pc hpc i a ha horizon P (hP P hact) ref amin hamin (hf P hact) (himm P hact) t).2

end
end Lax343628Proofs.UniformNoise

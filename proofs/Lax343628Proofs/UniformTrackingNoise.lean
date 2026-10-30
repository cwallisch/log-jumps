import Lax343628Proofs.UniformNoise
import Lax343628Proofs.ChannelCounts

namespace Lax343628Proofs.UniformTrackingNoise

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups Lax343628Proofs.SparseNoise
open Lax343628Proofs.DrivenNoise Lax343628Proofs.FiniteChain Lax343628Proofs.PathNoise
open Lax343628Proofs.ClassChannels Lax343628Proofs.Trajectories Lax343628Proofs.FiniteDrift
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {rs mu : ℕ+}

def noiseBad (pc : ℝ) (i : Fin n) (b : Fin 2) (a bound : ℝ)
    (active : Population n mu → Prop) [DecidablePred active] : Set (Fin (R + 1) → State n mu) :=
  {h | ∃ sigma : Net n k R (count R ell) rs, ∃ T : Fin (R + 1), bound ≤
    |accumulate (increment (noise sigma pc i b a) active R) T.val
      (before R T.val (by have := T.isLt; omega) h)|}

def countBad (i : Fin n) (fmax L : ℝ) (active : Population n mu → Prop) [DecidablePred active] :
    Set (Fin (R + 1) → State n mu) :=
  {h | 6 * R * fmax + 2 * L ≤ accumulate (ChannelCounts.tick i 1 active R) R h}

lemma joint_bound (hk : 2 ≤ k) (hn : 4 * k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (i : Fin n) (a : ℝ) (ha : 0 ≤ a) (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (refM : ColumnClass n k i 1) (refR : ColumnClass n k i 0)
    (fmin amin fmax : ℝ) (hfmin : 0 < fmin) (hamin : 0 < amin) (hfmax : 0 ≤ fmax)
    (active : Population n mu → Prop) [DecidablePred active]
    (hP : ∀ P, active P → ∀ u, (Sampling.zeros (P u)).card = k)
    (hf : ∀ P, active P → fmin ≤ fraction i 1 P)
    (har : ∀ P, active P → amin ≤ fraction i 0 P)
    (hupper : ∀ P, active P → fraction i 1 P ≤ fmax)
    (himm : ∀ P, active P → fraction i 1 P / n ≤ fraction i 0 P)
    (p : PMF (State n mu)) (bound L : ℝ) (hbound : 0 < bound) (hL : 0 < L)
    (hstepM : 2 * (4 * ((3 : ℝ) ^ k) ^ 2 / ((mu : ℕ) * fmin)) * L ≤ bound)
    (hvarM : 4 * R * (3 * ((3 : ℝ) ^ k) ^ 4 / (((mu : ℕ) : ℝ) ^ 2 * fmin)) * L ≤ bound ^ 2)
    (hstepR : 2 * (5 * ((3 : ℝ) ^ k) ^ 2 / ((mu : ℕ) * amin)) * L ≤ bound)
    (hvarR : 4 * R * (4 * ((3 : ℝ) ^ k) ^ 4 / (((mu : ℕ) : ℝ) ^ 2 * amin)) * L ≤ bound ^ 2) :
    (pathLaw (stopped (driver k pc) {S | active S.1}) p R).toOuterMeasure
      (noiseBad (k := k) (ell := ell) (rs := rs) pc i 1 a bound active ∪
        noiseBad (k := k) (ell := ell) (rs := rs) pc i 0 a bound active ∪ countBad i fmax L active) ≤
      ENNReal.ofReal ((4 * (Fintype.card (Net n k R (count R ell) rs) : ℝ) * ((R : ℝ) + 1) + 1) * Real.exp (-L)) := by
  have hM := UniformNoise.mutant_uniform (ell := ell) (rs := rs) hk hn pc hpc i a ha horizon refM fmin hfmin active hP hf p bound L hbound hL hstepM hvarM
  have hR := UniformNoise.resident_uniform (ell := ell) (rs := rs) hk hn pc hpc i a ha horizon refR amin hamin active hP har himm p bound L hbound hL hstepR hvarR
  have hC := ChannelCounts.tail (k := k) pc hpc i 1 active fmax hfmax hupper R L p
  let Q := pathLaw (stopped (driver k pc) {S | active S.1}) p R
  change Q.toOuterMeasure _ ≤ _
  calc
    _ ≤ Q.toOuterMeasure (noiseBad (k := k) (ell := ell) (rs := rs) pc i 1 a bound active ∪
        noiseBad (k := k) (ell := ell) (rs := rs) pc i 0 a bound active) + Q.toOuterMeasure (countBad i fmax L active) :=
      MeasureTheory.measure_union_le _ _
    _ ≤ (Q.toOuterMeasure (noiseBad (k := k) (ell := ell) (rs := rs) pc i 1 a bound active) +
        Q.toOuterMeasure (noiseBad (k := k) (ell := ell) (rs := rs) pc i 0 a bound active)) + Q.toOuterMeasure (countBad i fmax L active) :=
      add_le_add (MeasureTheory.measure_union_le _ _) (le_refl _)
    _ ≤ (ENNReal.ofReal (2 * (Fintype.card (Net n k R (count R ell) rs) : ℝ) * ((R : ℝ) + 1) * Real.exp (-L)) +
        ENNReal.ofReal (2 * (Fintype.card (Net n k R (count R ell) rs) : ℝ) * ((R : ℝ) + 1) * Real.exp (-L))) +
        ENNReal.ofReal (Real.exp (-L)) := add_le_add (add_le_add hM hR) hC
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end
end Lax343628Proofs.UniformTrackingNoise

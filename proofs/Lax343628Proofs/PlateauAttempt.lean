import Lax343628Proofs.ShiftedAttempt
import Lax343628Proofs.SpeciesEstimate
import Lax343628Proofs.AttemptError

namespace Lax343628Proofs.PlateauAttempt

open Lax343628.Algorithm Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PlateauDynamics Lax343628Proofs.Trajectories Lax343628Proofs.FiniteChain
open Lax343628Proofs.AttemptLengths Lax343628Proofs.EntropyLedger
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+}

lemma ledger (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1 / 64) :
    ENNReal.ofReal (1 / 64) + (ENNReal.ofReal (1 / 64) + ENNReal.ofReal a + ENNReal.ofReal (1 / 16) + ENNReal.ofReal b) +
      ENNReal.ofReal (1 / 64) ≤ ENNReal.ofReal (1 / 8) := by
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 64) ha,
    ← ENNReal.ofReal_add (by positivity : 0 ≤ (1 / 64 : ℝ) + a) (by norm_num : (0 : ℝ) ≤ 1 / 16),
    ← ENNReal.ofReal_add (by positivity : 0 ≤ (1 / 64 : ℝ) + a + 1 / 16) hb,
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 64) (by positivity : 0 ≤ (1 / 64 : ℝ) + a + 1 / 16 + b),
    ← ENNReal.ofReal_add (by positivity : 0 ≤ (1 / 64 : ℝ) + (1 / 64 + a + 1 / 16 + b)) (by norm_num : (0 : ℝ) ≤ 1 / 64)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu (AttemptError.delta n mu) ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu (AttemptError.delta n mu) ≤ n)
    (P : Population n mu) (hP : plateauPopulation (r + 1) P) :
    (law (step (jump (r + 1)) pc) (PMF.pure P)
      (SpeciesEstimate.length S n mu (AttemptError.delta n mu))).toOuterMeasure Dynamics.missing ≤ ENNReal.ofReal (1 / 8) := by
  let d := AttemptError.delta n mu
  let u : Fin (mu : ℕ) := ⟨0, mu.pos⟩
  let T : State n mu := (P, ((u, u), P u, Fin.last (mu : ℕ)))
  let L := decision S n mu d + terminal S
  let R := service S mu
  have hd := AttemptError.delta_bounds n mu
  have hc := PhaseConditions.of_size S hS n (r + 1) mu d (by omega) hrS hD hd hmu hn
  have hkn : r + 1 ≤ n := by have := hc.dimension; omega
  have hchild : T.2.2.1 ≠ optimum n := KilledSampling.plateau_missing (by omega) hkn P hP u
  have hcap := SpeciesEstimate.bound S hS n (r + 1) mu pc d (by omega) hrS hD hpc hd hmu hn T hP
  have hshift := ShiftedAttempt.bound S hS hr hrS hD pc d hpc hd hmu hn T hP hchild (SpeciesParameters.entry n mu)
    (ENNReal.ofReal (1 / 64)) hcap
  have htime := TimeAbsorption.total S hS n mu d hd hmu hn
  have hL : (L : ℝ) ≤ (mu : ℕ) * (n : ℝ) := by dsimp [L]; nlinarith
  have hbudget := AttemptError.bound n L R mu (by have := hc.dimension; omega) hL (AttemptError.service_le S n mu d)
  have hdp : 0 < d := hd.1
  apply hshift.trans
  apply ledger _ _ (by positivity) (by positivity)
  simpa only [mul_assoc] using hbudget

end
end Lax343628Proofs.PlateauAttempt

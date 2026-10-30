import Lax343628Proofs.SpeciesEntropy
import Lax343628Proofs.SpeciesConditions
import Lax343628Proofs.SpeciesTagged

namespace Lax343628Proofs.SpeciesEstimate

open Lax343628.Algorithm Lax343628Proofs.DrivenNoise
open Lax343628Proofs.SpeciesParameters Lax343628Proofs.EntropyLedger Lax343628Proofs.AttemptLengths
open Lax343628Proofs.Trajectories Lax343628Proofs.PlateauDynamics
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

def length (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) : ℕ := entry n mu + (decision S n mu delta + terminal S)

lemma time (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n : ℕ) (mu : ℕ+) (delta : ℝ)
    (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n) :
    (length S n mu delta : ℝ) ≤ 67108864 * (mu : ℕ) * (n : ℝ) := by
  have ht := TimeAbsorption.total S hS n mu delta hd hmu hn
  have he := entry_time n mu
  have hm : (0 : ℝ) ≤ (mu : ℕ) := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  unfold length
  rw [Nat.cast_add]
  nlinarith

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n k : ℕ) (mu : ℕ+) (pc delta : ℝ)
    (hk : 1 ≤ k) (hks : k ≤ (S : ℕ)) (hD : (3 : ℝ) ^ k ≤ (S : ℕ))
    (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (T : State n mu) (hT : plateauPopulation k T.1) :
    (pathLaw (driver k pc) (PMF.pure T) (length S n mu delta)).toOuterMeasure
      {h | ∃ t, entry n mu ≤ t.val ∧ ¬ColumnBlock.cap (1 / 125) (h t).1} ≤ ENNReal.ofReal (1 / 64) := by
  let s : ℝ := (S : ℕ)
  let W := logarithms n mu delta
  let J := length S n mu delta
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hb := logarithms_bounds n mu delta hd
  have hc := SpeciesConditions.of_size S hS n k mu delta pc hk hks hD hpc.1 hd hn
  have hmp := SpeciesExponents.threshold_mass S hS k n mu delta hk hks hd hmu
  have hp := threshold_bounds k hk
  have hpc0 : 0 ≤ pc := (by positivity : (0 : ℝ) ≤ 1 / s).trans hpc.1
  have hkn : k ≤ n := by have := hc.1.entry.dimension_four_jump; omega
  have hnp : 1 ≤ n := by have := hc.1.entry.dimension_two; omega
  have hcap := SpeciesTagged.bound hc.1 hc.2 (by linarith) (by linarith [hp.2.1]) ⟨hpc0, hpc.2⟩ T hT
    (entry n mu) J (by dsimp [J, length]; omega)
  have hent := entry_bound n k mu hnp hk
  have hfailure := SpeciesExponents.bound S hS k n mu pc delta hk hks hpc.1 hd hmu
  have hcount := SpeciesEntropy.genotypes n k s W hnp (by dsimp [s]; exact_mod_cast hks) hb.2.1 (by linarith [hb.1])
  have hlog := SpeciesEntropy.horizon_log n J mu s W hs hb.1 hb.2.1 hb.2.2.1 (time S hS n mu delta hd hmu hn)
  have herr := SpeciesEntropy.error s W (mu : ℕ) (Fintype.card (Genotypes.Genotype n k)) ((J : ℝ) + 1)
    hs hb.1 hmu (by positivity) (by positivity) hcount hlog
  have hactual : (Fintype.card (Genotypes.Genotype n k) : ℝ) * ((J : ℝ) + 1) ^ 2 *
      (SpeciesReentry.countFailure k mu pc (threshold k) + SpeciesReentry.ratioFailure mu pc (threshold k)) ≤ 1 / 128 :=
    (mul_le_mul_of_nonneg_left hfailure (by positivity : (0 : ℝ) ≤
      (Fintype.card (Genotypes.Genotype n k) : ℝ) * ((J : ℝ) + 1) ^ 2)).trans herr
  apply hcap.trans
  apply ENNReal.ofReal_le_ofReal
  linarith

end
end Lax343628Proofs.SpeciesEstimate

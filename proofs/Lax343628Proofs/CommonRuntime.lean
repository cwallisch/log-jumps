import Lax343628Proofs.ArrivalRuntime
import Lax343628Proofs.PlateauAttempt
import Lax343628Proofs.SingleJump
import Lax343628Proofs.TwoStage
import Lax343628Proofs.RuntimeBridge

namespace Lax343628Proofs.CommonRuntime

open Lax343628.Algorithm Lax343628.Runtime Lax343628Proofs.Sampling Lax343628Proofs.Dynamics
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain Lax343628Proofs.ArrivalFitness
open Lax343628Proofs.EntropyLedger Lax343628Proofs.PlateauDynamics
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

def arrivalLength (n : ℕ) (mu : ℕ+) (pc : ℝ) : ℕ := Nat.ceil ((16384 / pc) * (mu : ℕ) * (n : ℝ))

lemma arrival_time (hn : 2 ≤ n) (pc : ℝ) (hp : 0 < pc ∧ pc ≤ 1) (mu : ℕ+) :
    (arrivalLength n mu pc : ℝ) ≤ (16385 / pc) * (mu : ℕ) * (n : ℝ) := by
  have hpp := hp.1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (1 : ℝ) ≤ (mu : ℕ) := by exact_mod_cast mu.pos
  have hbase : 1 ≤ ((mu : ℕ) : ℝ) * n / pc := by
    apply (le_div_iff₀ hp.1).mpr
    nlinarith [mul_le_mul_of_nonneg_right hm (show (0 : ℝ) ≤ n by positivity)]
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ (16384 / pc) * (mu : ℕ) * (n : ℝ) by positivity)).le
  change (arrivalLength n mu pc : ℝ) ≤ _ at hc
  linear_combination hc + hbase

lemma from_plateau (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hk : 1 ≤ k) (hkn : 2 * k ≤ n)
    (hks : k ≤ (S : ℕ)) (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (pc : ℝ)
    (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu (AttemptError.delta n mu) ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu (AttemptError.delta n mu) ≤ n)
    (L : ℕ) (hL : 0 < L) (hLt : (L : ℝ) ≤ (67108864 / pc) * (mu : ℕ) * (n : ℝ))
    (hplateau : ∀ P : Population n mu, plateauPopulation k P →
      (law (step (jump k) pc) (PMF.pure P) L).toOuterMeasure missing ≤ ENNReal.ofReal (1 / 8)) :
    expectedRuntime n k mu pc ≤ ENNReal.ofReal ((268435456 / pc) * (mu : ℕ) * (n : ℝ)) := by
  let K := step (jump k) pc (n := n) (μ := mu)
  let T := arrivalLength n mu pc
  have hsp : (0 : ℝ) < (S : ℕ) := by exact_mod_cast S.pos
  have hp : 0 < pc := (div_pos (by norm_num) hsp).trans_le hpc.1
  have hblock (P : Population n mu) :
      (law K (PMF.pure P) (T + L)).toOuterMeasure missing ≤ ENNReal.ofReal (1 / 2) := by
    have harr := ArrivalRuntime.tail S hS hk hkn hks hD pc (AttemptError.delta n mu) hpc
      (AttemptError.delta_bounds n mu) hmu hn (PMF.pure P) T
    have harr' : (law K (PMF.pure P) T).toOuterMeasure (active k) ≤ ENNReal.ofReal (1 / 4) := by
      apply harr.trans
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (T : ℝ) + 1)).mpr
      have hc : (16384 / pc) * (mu : ℕ) * (n : ℝ) ≤ (T : ℝ) := Nat.le_ceil _
      linear_combination hc / 4
    rw [law_add]
    have hs := TwoStage.split (law K (PMF.pure P) T) (fun Q ↦ law K (PMF.pure Q) L)
      missing (active k) (ENNReal.ofReal (1 / 8)) (by
        intro Q hQ
        by_cases hm : Q ∈ missing
        · have hpl : plateauPopulation k Q := by
            by_contra hn
            exact hQ ⟨hm, hn⟩
          exact hplateau Q hpl
        · rw [event_law_eq_zero K missing (step_missing_eq_zero (by omega) pc) L Q hm]
          exact zero_le)
    apply hs.trans ((add_le_add harr' le_rfl).trans ?_)
    rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (0 : ℝ) ≤ 1 / 8)]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hh := RuntimeBridge.expectedRuntime_le_of_block n k mu pc (by omega) (T + L) (by omega)
    (ENNReal.ofReal (1 / 2)) (fun P _ ↦ hblock P)
  have hfactor : (1 - ENNReal.ofReal (1 / 2))⁻¹ = (2 : ℝ≥0∞) := by
    rw [← (ENNReal.ofReal_ofNat 2), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 - 1 / 2)]
    congr 1
    norm_num
  rw [hfactor] at hh
  have hcast : ((T + L : ℕ) : ℝ≥0∞) * 2 = ENNReal.ofReal (2 * ((T + L : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast, mul_comm]
  rw [hcast] at hh
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hT := arrival_time (by omega : 2 ≤ n) pc ⟨hp, hpc.2⟩ mu
  change (T : ℝ) ≤ _ at hT
  rw [Nat.cast_add]
  have hz : 0 ≤ ((mu : ℕ) : ℝ) * n / pc := by positivity
  linear_combination 2 * hT + 2 * hLt + 134184958 * hz

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hk : 1 ≤ k) (hkn : 2 * k ≤ n)
    (hks : k ≤ (S : ℕ)) (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (pc : ℝ)
    (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu (AttemptError.delta n mu) ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu (AttemptError.delta n mu) ≤ n) :
    expectedRuntime n k mu pc ≤ ENNReal.ofReal ((268435456 / pc) * (mu : ℕ) * (n : ℝ)) := by
  have hsp : (0 : ℝ) < (S : ℕ) := by exact_mod_cast S.pos
  have hp : 0 < pc := (div_pos (by norm_num) hsp).trans_le hpc.1
  by_cases hk1 : k = 1
  · subst k
    apply from_plateau S hS hk hkn hks hD pc hpc hmu hn (SingleJump.length n pc)
      (SingleJump.length_pos (by omega) pc hp) _ (SingleJump.block (by omega) pc ⟨hp, hpc.2⟩)
    have hh := SingleJump.time (by omega : 2 ≤ n) pc ⟨hp, hpc.2⟩ mu
    apply hh.trans
    have hz : 0 ≤ ((mu : ℕ) : ℝ) * n / pc := by positivity
    linear_combination 67107840 * hz
  · obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
    let L := SpeciesEstimate.length S n mu (AttemptError.delta n mu)
    have hLp : 0 < L := by
      unfold L SpeciesEstimate.length SpeciesParameters.entry
      have hn0 : 0 < n := by omega
      positivity
    apply from_plateau S hS hk hkn hks hD pc hpc hmu hn L hLp _
      (PlateauAttempt.bound S hS (by omega : 1 ≤ r) hks hD pc hpc hmu hn)
    have hh := SpeciesEstimate.time S hS n mu (AttemptError.delta n mu) (AttemptError.delta_bounds n mu) hmu hn
    apply hh.trans
    have hinv : 1 ≤ 1 / pc := (le_div_iff₀ hp).mpr (by simpa only [one_mul] using hpc.2)
    have hm := mul_le_mul_of_nonneg_right hinv (show (0 : ℝ) ≤ 67108864 * (mu : ℕ) * n by positivity)
    linear_combination hm

end
end Lax343628Proofs.CommonRuntime

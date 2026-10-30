import Lax343628Proofs.RuntimeEscape
import Lax343628Proofs.AttemptLengths
import Lax343628Proofs.ColumnMarks
import Lax343628Proofs.DrivenNoise

namespace Lax343628Proofs.FlatSampling

open Lax343628.Algorithm Lax343628Proofs.DrivenNoise Lax343628Proofs.TaggedDynamics
open Lax343628Proofs.ClassChannels Lax343628Proofs.PhaseParameters Lax343628Proofs.Trajectories
open Lax343628Proofs.FiniteChain
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

def safe (k : ℕ) (theta : ℝ) : Set (State n mu) :=
  {T | (∀ u, (Sampling.zeros (T.1 u)).card = k) ∧
    (∀ i, fraction i 0 T.1 < theta) ∧ T.2.2.1 ≠ optimum n}

lemma child_probability (k : ℕ) (pc : ℝ) (T : State n mu) :
    (driver k pc T).toOuterMeasure {U | U.2.2.1 = optimum n} = Sampling.offspring pc T.1 (optimum n) := by
  rw [driver, PMF.toOuterMeasure_map_apply, ← PMF.toOuterMeasure_apply_singleton,
    ← eventLaw_child, PMF.toOuterMeasure_map_apply]
  rfl

lemma count_flat (hk : 0 < k) (theta : ℝ) (hth : theta ≤ 1 / (2 * (k : ℝ)))
    (P : Population n mu) (hflat : ∀ i, fraction i 0 P < theta) :
    ∀ i, 2 * k * Flatness.columnCount P i ≤ (mu : ℕ) := by
  intro i
  have hm : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hh := (hflat i).le.trans hth
  rw [ColumnMarks.zero_fraction] at hh
  have hh' := (div_le_div_iff₀ hm (show (0 : ℝ) < 2 * (k : ℝ) by positivity)).mp hh
  norm_num only [one_mul] at hh'
  have hreal : 2 * (k : ℝ) * Flatness.columnCount P i ≤ (mu : ℕ) := by nlinarith
  exact_mod_cast hreal

lemma numerical (s pc t : ℝ) (hs : 16 ≤ s) (hpc : 1 / s ≤ pc) (ht : 0 < t) (hts : t ≤ s ^ 2) :
    1 / s ^ 4 ≤ pc / 16 * t⁻¹ := by
  have hsp : 0 < s := by linarith
  have hden : 16 * s * t ≤ s ^ 4 := by
    have h1 := mul_le_mul_of_nonneg_left hts (show 0 ≤ 16 * s by positivity)
    have h2 := mul_le_mul_of_nonneg_right hs (show 0 ≤ s ^ 3 by positivity)
    nlinarith
  calc
    1 / s ^ 4 ≤ 1 / (16 * s * t) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = (1 / s) / 16 * t⁻¹ := by field_simp
    _ ≤ pc / 16 * t⁻¹ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hpc (by norm_num)) (by positivity)

lemma success_lower (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hk : 0 < k) (hn : 2 ≤ n)
    (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (pc : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1)
    (hth : theta S ≤ 1 / (2 * (k : ℝ))) (T : State n mu)
    (hT : ∀ u, (Sampling.zeros (T.1 u)).card = k) (hf : ∀ i, fraction i 0 T.1 < theta S) :
    ENNReal.ofReal (1 / ((S : ℕ) : ℝ) ^ 4) ≤ (driver k pc T).toOuterMeasure {U | U.2.2.1 = optimum n} := by
  have hs : (16777216 : ℝ) ≤ (S : ℕ) := by exact_mod_cast hS
  have hp : 0 ≤ pc := (by positivity : (0 : ℝ) ≤ 1 / ((S : ℕ) : ℝ)).trans hpc.1
  have hfour : (4 : ℝ) ^ k ≤ ((S : ℕ) : ℝ) ^ 2 := by
    have hh : (4 : ℝ) ^ k ≤ ((3 : ℝ) ^ 2) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
    have heq : ((3 : ℝ) ^ 2) ^ k = ((3 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [heq] at hh
    exact hh.trans (pow_le_pow_left₀ (by positivity) hD 2)
  have hnum := numerical (S : ℕ) pc ((4 : ℝ) ^ k) (by linarith) hpc.1 (by positivity) hfour
  have hprob := Plateau.flat_offspring_success hn pc ⟨hp, hpc.2⟩ T.1 hT (count_flat hk (theta S) hth T.1 hf)
  rw [child_probability]
  apply le_trans (ENNReal.ofReal_le_ofReal hnum)
  have heq : ENNReal.ofReal (pc / 16 * ((4 : ℝ) ^ k)⁻¹) = ENNReal.ofReal (pc / 16) * (4 : ℝ≥0∞)⁻¹ ^ k := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ pc / 16), ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < (4 : ℝ) ^ k),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat, ENNReal.inv_pow]
  rw [heq]
  exact hprob

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hk : 0 < k) (hn : 2 ≤ n)
    (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (pc : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1)
    (hth : theta S ≤ 1 / (2 * (k : ℝ))) (p : PMF (State n mu)) :
    (pathLaw (driver k pc) p (AttemptLengths.terminal S)).toOuterMeasure
      {h | ∀ j, h j ∈ safe k (theta S)} ≤ ENNReal.ofReal (1 / 64) := by
  have hs : (1 : ℝ) ≤ (S : ℕ) := by exact_mod_cast S.pos
  have hW : 1 ≤ ((S : ℕ) : ℝ) ^ 4 := one_le_pow₀ hs
  have hh := RuntimeEscape.bound (driver k pc) (safe (mu := mu) k (theta S)) p
    (((S : ℕ) : ℝ) ^ 4) hW (by
      intro T hT
      have hsuccess := success_lower S hS hk hn hD pc hpc hth T hT.1 hT.2.1
      have hmono : (driver k pc T).toOuterMeasure (safe k (theta S)) ≤
          (driver k pc T).toOuterMeasure {U | U.2.2.1 = optimum n}ᶜ := by
        apply (driver k pc T).toOuterMeasure.mono
        intro U hU
        exact hU.2.2
      apply ENNReal.le_sub_of_add_le_right (by simp)
      exact (add_le_add hmono hsuccess).trans_eq (by
        rw [add_comm]
        exact event_add_compl _ _)) (AttemptLengths.terminal S)
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (AttemptLengths.terminal S : ℝ) + 1)).mpr
  simp only [AttemptLengths.terminal, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  linarith

end
end Lax343628Proofs.FlatSampling

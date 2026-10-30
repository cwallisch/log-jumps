import Lax343628Proofs.ServiceBound
import Lax343628Proofs.CoreCounts

namespace Lax343628Proofs.ServiceRounds

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.ClassMeanDynamics
open Lax343628Proofs.ServiceGeometry
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {mu : ℕ+}

lemma odds_lower (i : Fin n) (P : Population n mu) (hf : 0 < fraction i 1 P)
    (ha : 0 < fraction i 0 P) : 1 / (mu : ℕ) ≤ Odds.value i P := by
  have hm : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hc : 1 ≤ CoreCounts.missingCount i P := by
    by_contra hn
    have hz : CoreCounts.missingCount i P = 0 := by omega
    rw [CoreCounts.missing_fraction, hz, Nat.cast_zero, zero_div] at hf
    exact (lt_irrefl _ hf)
  have hfr : 1 / (mu : ℕ) ≤ fraction i 1 P := by
    rw [CoreCounts.missing_fraction]
    apply div_le_div_of_nonneg_right _ hm.le
    exact_mod_cast hc
  apply hfr.trans
  unfold Odds.value
  apply (le_div_iff₀ ha).mpr
  exact mul_le_of_le_one_right (fraction_bounds i 1 P).1 (fraction_bounds i 0 P).2

lemma final_upper (a : ℝ) (ha : 1 / (mu : ℕ) ≤ a) : finalOdds a ≤ (mu : ℕ) := by
  have hm : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have ha0 : 0 < a := (div_pos (by norm_num) hm).trans_le ha
  have hmul := (div_le_iff₀ hm).mp ha
  unfold finalOdds
  apply (div_le_iff₀ ha0).mpr
  nlinarith

lemma power_large (N : ℕ) (hN : 16 * Real.log ((mu : ℕ) : ℝ) + 1 ≤ (N : ℝ)) :
    ((mu : ℕ) : ℝ) ^ 2 < (8 : ℝ) ^ N := by
  have hm : (1 : ℝ) ≤ (mu : ℕ) := by exact_mod_cast mu.pos
  have hm0 : (0 : ℝ) < (mu : ℕ) := by linarith
  have hlog := Real.log_nonneg hm
  have hlog8 : (1 / 4 : ℝ) < Real.log 8 :=
    ColumnExit.log_four_gt.trans_le (Real.log_le_log (by norm_num) (by norm_num))
  have hNp : (0 : ℝ) < N := by linarith
  apply (Real.log_lt_log_iff (by positivity : (0 : ℝ) < ((mu : ℕ) : ℝ) ^ 2)
    (by positivity : (0 : ℝ) < (8 : ℝ) ^ N)).mp
  rw [Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith [mul_pos hNp (sub_pos.mpr hlog8)]

lemma enough (N : ℕ) (hN : 16 * Real.log ((mu : ℕ) : ℝ) + 1 ≤ (N : ℝ))
    (a O : ℝ) (ha : 1 / (mu : ℕ) ≤ a) (hO : 1 / (mu : ℕ) ≤ O) :
    finalOdds a < (8 : ℝ) ^ N * O := by
  have hm : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hh : ((mu : ℕ) : ℝ) < (8 : ℝ) ^ N / (mu : ℕ) := by
    apply (lt_div_iff₀ hm).mpr
    simpa only [pow_two] using power_large (mu := mu) N hN
  have hscaled := mul_le_mul_of_nonneg_left hO (show (0 : ℝ) ≤ (8 : ℝ) ^ N by positivity)
  have hfinal := final_upper (mu := mu) a ha
  have htarget : (8 : ℝ) ^ N / (mu : ℕ) ≤ (8 : ℝ) ^ N * O := by
    simpa only [mul_one_div] using hscaled
  exact hfinal.trans_lt (hh.trans_le htarget)

end
end Lax343628Proofs.ServiceRounds

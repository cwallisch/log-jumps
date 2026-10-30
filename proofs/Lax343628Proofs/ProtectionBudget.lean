import Lax343628Proofs.BlockMass
import Lax343628Proofs.UniformBlockBudget
import Lax343628Proofs.ProtectionWindows

namespace Lax343628Proofs.ProtectionBudget

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ColumnBudget Lax343628Proofs.BlockParameters
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

lemma uniform (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hk : 2 ≤ k) (hn : 4 * k ≤ n)
    (hkS : k ≤ (S : ℕ)) (hDS : (3 : ℝ) ^ k ≤ (S : ℕ))
    (pc omega L u theta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1)
    (hw : 1 / (S : ℕ) ≤ omega ∧ omega ≤ 1) (hL : 1 ≤ L)
    (hu : 0 < u ∧ u ≤ 1 / 4) (htheta : theta = 16 * (3 : ℝ) ^ k * u) (htheta1 : theta ≤ 1)
    (hmu : 2 * (((S : ℕ) : ℝ) ^ 64 * L) ≤ (mu : ℕ))
    (hresident : ((S : ℕ) : ℝ) ^ 64 * L ≤ (mu : ℕ) * (u / 9))
    (hdimension : ((S : ℕ) : ℝ) ^ 40 ≤ (n : ℝ) * (u / 9))
    (i : Fin n) (T : State n mu) (hT : T ∈ ProtectionWindows.starts k i u) :
    Budget n k (horizon (S : ℕ) mu) (groupSize (S : ℕ) mu) mu (samples S)
      pc (pc / ((mu : ℕ) + 1 : ℝ))
      (Odds.lowerMass (Odds.value i T.1 / (4 * (3 : ℝ) ^ k)))
      (Odds.upperMass (8 * Odds.value i T.1))
      (Odds.lowerMass (8 * Odds.value i T.1)) omega L 8 := by
  let D : ℝ := (3 : ℝ) ^ k
  let M : ℝ := ((S : ℕ) : ℝ) ^ 64 * L
  have hD : 1 ≤ D := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hDp : 0 < D := by linarith
  have hMp : 0 < M := by
    dsimp [M]
    have hLp : 0 < L := by linarith
    positivity
  have hup : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hu0 := hu.1
  have hOlower := ProtectionGeometry.initial_odds_lower i T.1 u hu.1 hu.2 hT.2
  have hO : 0 < Odds.value i T.1 := (by positivity : 0 < 1 / (4 * u)).trans_le hOlower
  have hthreshold := ProtectionGeometry.protection_thresholds i T.1 u theta D hu.1 hu.2 hDp htheta hT.2
  have hthetap : 0 < theta := by rw [htheta]; positivity
  have hlo : 1 ≤ Odds.value i T.1 / (4 * D) :=
    ((one_le_div hthetap).mpr htheta1).trans hthreshold.1
  have hmin := BlockMass.protection_mutant _ hlo
  have hfmin : M ≤ (mu : ℕ) * Odds.lowerMass (Odds.value i T.1 / (4 * D)) := by
    have hh := mul_le_mul_of_nonneg_left hmin hup.le
    nlinarith
  have hres := BlockMass.protection_resident i T.1 u hu.1 (by linarith) hT.2.1
  have hA1 : Odds.upperMass (8 * Odds.value i T.1) ≤ 1 := by
    have hh := Odds.upperMass_antitone (show (0 : ℝ) ≤ 0 by norm_num)
      (show 0 ≤ 8 * Odds.value i T.1 by positivity)
    simpa only [Odds.upperMass, add_zero, div_one] using hh
  exact UniformBlockBudget.budget S hS hk hn hkS hDS pc omega L _ _ _ hpc hw hL
    (by linarith : M ≤ (mu : ℕ)) hfmin
    (hresident.trans (mul_le_mul_of_nonneg_left hres hup.le)) hA1
    (Odds.lowerMass_pos (show 0 < 8 * Odds.value i T.1 by positivity)).le
    (BlockMass.block_ratio _ _ D hO hD (by linarith) le_rfl)
    (hdimension.trans (mul_le_mul_of_nonneg_left hres (show (0 : ℝ) ≤ n by positivity)))

end
end Lax343628Proofs.ProtectionBudget

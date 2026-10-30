import Lax343628Proofs.BlockMass
import Lax343628Proofs.UniformBlockBudget
import Lax343628Proofs.ServiceWindows

namespace Lax343628Proofs.ServiceBudget

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ColumnBudget Lax343628Proofs.BlockParameters Lax343628Proofs.ServiceGeometry
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

lemma uniform (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hk : 2 ≤ k) (hn : 4 * k ≤ n)
    (hkS : k ≤ (S : ℕ)) (hDS : (3 : ℝ) ^ k ≤ (S : ℕ))
    (pc omega L astar : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1)
    (hw : 1 / (S : ℕ) ≤ omega ∧ omega ≤ 1) (hL : 1 ≤ L) (ha : 0 < astar ∧ astar ≤ 1 / 2)
    (hmu : ((S : ℕ) : ℝ) ^ 64 * L ≤ (mu : ℕ))
    (hresident : ((S : ℕ) : ℝ) ^ 64 * L ≤ (mu : ℕ) * astar)
    (hdimension : ((S : ℕ) : ℝ) ^ 40 ≤ (n : ℝ) * astar)
    (i : Fin n) (P0 : Population n mu) (hP0a : 0 < fraction i 0 P0)
    (hmutant : 4 * (3 : ℝ) ^ k * (((S : ℕ) : ℝ) ^ 64 * L) ≤ (mu : ℕ) * fraction i 1 P0)
    (T : State n mu) (hT : T ∈ ServiceWindows.starts k i astar (Odds.value i P0)) :
    Budget n k (horizon (S : ℕ) mu) (groupSize (S : ℕ) mu) mu (samples S)
      pc (pc / ((mu : ℕ) + 1 : ℝ))
      (Odds.lowerMass (Odds.value i T.1 / (4 * (3 : ℝ) ^ k)))
      (Odds.upperMass (target astar (Odds.value i T.1)))
      (Odds.lowerMass (target astar (Odds.value i T.1))) omega L 8 := by
  let D : ℝ := (3 : ℝ) ^ k
  let M : ℝ := ((S : ℕ) : ℝ) ^ 64 * L
  have hMp : 0 < M := by
    dsimp [M]
    have hLp : 0 < L := by linarith
    positivity
  have hup : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hD : 1 ≤ D := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hDp : 0 < D := by linarith
  have hf0 : 0 < fraction i 1 P0 := by
    have hh : 0 < (mu : ℕ) * fraction i 1 P0 :=
      (show 0 < 4 * D * M by positivity).trans_le hmutant
    exact ((mul_pos_iff.mp hh).resolve_right (by rintro ⟨hneg, _⟩; linarith)).2
  have hO0 : 0 < Odds.value i P0 := div_pos hf0 hP0a
  have hO : 0 < Odds.value i T.1 := hO0.trans_le hT.2.2
  have hTa : 0 < fraction i 0 T.1 := ha.1.trans hT.2.1
  have hmono := mutant_mono i P0 T.1 hP0a hTa hT.2.2
  have hmin := mul_le_mul_of_nonneg_left (BlockMass.service_mutant i T.1 D hD hTa) hup.le
  have hmut : M ≤ (mu : ℕ) * Odds.lowerMass (Odds.value i T.1 / (4 * D)) := by
    have hroot : M ≤ (mu : ℕ) * fraction i 1 P0 / (4 * D) := by
      apply (le_div_iff₀ (by positivity : 0 < 4 * D)).mpr
      nlinarith only [hmutant]
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hup.le)
      (show 0 ≤ 4 * D by positivity)
    have hmin' : (mu : ℕ) * fraction i 1 T.1 / (4 * D) ≤
        (mu : ℕ) * Odds.lowerMass (Odds.value i T.1 / (4 * D)) := by
      convert hmin using 1 <;> first | rfl | ring
    exact hroot.trans (hh.trans hmin')
  have htarget := target_bounds astar _ hO (odds_below_final i T.1 astar ha.1 hT.2.1)
  have hhi : 0 < target astar (Odds.value i T.1) := hO.trans htarget.1
  have hres := BlockMass.service_resident astar (Odds.value i T.1) ha.1 (by linarith) hO.le
  have hA1 : Odds.upperMass (target astar (Odds.value i T.1)) ≤ 1 := by
    have hh := Odds.upperMass_antitone (show (0 : ℝ) ≤ 0 by norm_num) hhi.le
    simpa only [Odds.upperMass, add_zero, div_one] using hh
  exact UniformBlockBudget.budget S hS hk hn hkS hDS pc omega L _ _ _ hpc hw hL hmu hmut
    (hresident.trans (mul_le_mul_of_nonneg_left hres hup.le)) hA1
    (Odds.lowerMass_pos hhi).le (BlockMass.block_ratio _ _ D hO hD htarget.1 htarget.2)
    (hdimension.trans (mul_le_mul_of_nonneg_left hres (show (0 : ℝ) ≤ n by positivity)))

end
end Lax343628Proofs.ServiceBudget

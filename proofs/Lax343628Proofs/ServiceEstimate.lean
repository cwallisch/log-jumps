import Lax343628Proofs.ServiceBudget
import Lax343628Proofs.ServiceRounds
import Lax343628Proofs.BlockError

namespace Lax343628Proofs.ServiceEstimate

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ColumnBlock Lax343628Proofs.BlockParameters Lax343628Proofs.EntropyLedger
open Lax343628Proofs.Trajectories
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r N : ℕ} {mu : ℕ+}

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (hrS : r + 1 ≤ (S : ℕ)) (hDS : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc omega astar delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1)
    (hw : 1 / (S : ℕ) ≤ omega ∧ omega ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (ha : 1 / (mu : ℕ) ≤ astar ∧ astar ≤ 1 / 2)
    (hN : 16 * Real.log ((mu : ℕ) : ℝ) + 1 ≤ (N : ℝ))
    (hmu : mass S n mu delta ≤ (mu : ℕ))
    (hresident : mass S n mu delta ≤ (mu : ℕ) * astar)
    (hdimension : ((S : ℕ) : ℝ) ^ 40 ≤ (n : ℝ) * astar)
    (i : Fin n) (S0 : State n mu) (hP0 : ∀ v, (Sampling.zeros (S0.1 v)).card = r + 1)
    (hP0a : 0 < fraction i 0 S0.1)
    (hmutant : 4 * (3 : ℝ) ^ (r + 1) * mass S n mu delta ≤ (mu : ℕ) * fraction i 1 S0.1) :
    (pathLaw (driver (r + 1) pc) (PMF.pure S0) (N * horizon (S : ℕ) mu)).toOuterMeasure
      {h | ∀ t, astar < fraction i 0 (h t).1 ∧ cap omega (h t).1} ≤
      ENNReal.ofReal ((((N * horizon (S : ℕ) mu : ℕ) : ℝ) + 1) * delta) := by
  have hmp : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hap : 0 < astar := (div_pos (by norm_num) hmp).trans_le ha.1
  have hM := mass_one S n mu delta hd
  have hMp : 0 < mass S n mu delta := by linarith
  have hf0 : 0 < fraction i 1 S0.1 := by
    have hh : 0 < (mu : ℕ) * fraction i 1 S0.1 := (by positivity : 0 < 4 * (3 : ℝ) ^ (r + 1) * mass S n mu delta).trans_le hmutant
    exact ((mul_pos_iff.mp hh).resolve_right (by rintro ⟨hneg, _⟩; linarith)).2
  have hO0 := div_pos hf0 hP0a
  have hlarge := ServiceRounds.enough N hN astar (Odds.value i S0.1) ha.1 (ServiceRounds.odds_lower i S0.1 hf0 hP0a)
  apply ServiceBound.bound (by omega) pc astar omega hap i S0 hP0 hO0 hlarge delta hd.1.le
  intro T hT
  have hb := ServiceBudget.uniform S hS (by omega) hn hrS hDS pc omega (level S n mu delta) astar hpc hw
    (level_one S n mu delta hd) ⟨hap, ha.2⟩ hmu hresident hdimension i S0.1 hP0a hmutant
  have hblock := ServiceWindows.uniform_block hr pc (pc / ((mu : ℕ) + 1 : ℝ)) astar (Odds.value i S0.1)
    omega (level S n mu delta) hap hO0 i hb T hT
  have he := BlockError.bound S hS n (r + 1) mu (by omega) (by omega) hrS (group_condition S n mu delta hd hmu) delta hd
  exact hblock.trans (ENNReal.ofReal_le_ofReal he)

end
end Lax343628Proofs.ServiceEstimate

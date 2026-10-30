import Lax343628Proofs.ProtectionHistory
import Lax343628Proofs.ProtectionBudget
import Lax343628Proofs.PhaseConditions
import Lax343628Proofs.BlockError

namespace Lax343628Proofs.GlobalProtection

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ColumnBlock Lax343628Proofs.BlockParameters Lax343628Proofs.EntropyLedger
open Lax343628Proofs.PhaseParameters Lax343628Proofs.Trajectories Lax343628Proofs.FiniteEvents
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r J : ℕ} {mu : ℕ+}

lemma column (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc omega delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1)
    (hw : 1 / (S : ℕ) ≤ omega ∧ omega ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (i : Fin n) (p : PMF (State n mu)) :
    (pathLaw (driver (r + 1) pc) p J).toOuterMeasure
      (ProtectionHistory.failure J (r + 1) i (lowerZero S (r + 1)) (theta S) omega) ≤
      ENNReal.ofReal (((J : ℝ) + 1) * delta) := by
  have hc := PhaseConditions.of_size S hS n (r + 1) mu delta (by omega) hrS hD hd hmu hn
  have hu := lower_bounds S (r + 1)
  have hD1 : (1 : ℝ) ≤ (3 : ℝ) ^ (r + 1) := one_le_pow₀ (by norm_num)
  have hrel : theta S = 16 * (3 : ℝ) ^ (r + 1) * lowerZero S (r + 1) := by
    unfold lowerZero
    field_simp
  have hutheta : lowerZero S (r + 1) ≤ theta S := by
    have hmul := mul_le_mul_of_nonneg_right hD1 hu.1.le
    nlinarith
  have hstep : 1 / ((mu : ℕ) : ℝ) ≤ lowerZero S (r + 1) := by
    have hh := hc.processedLower
    unfold processed at hh
    linarith
  have hb := ProtectionBudget.uniform S hS (by omega) hc.dimension hrS hD pc omega (level S n mu delta)
    (lowerZero S (r + 1)) (theta S) hpc hw (level_one S n mu delta hd) ⟨hu.1, by linarith⟩ hrel
    (theta_bounds S).2 hc.twice hc.protectionMass hc.protectionDimension i
  have ht := ProtectionHistory.bound (J := J) hr pc (pc / ((mu : ℕ) + 1 : ℝ))
    (lowerZero S (r + 1)) (theta S) omega (level S n mu delta) hu.1 (by linarith) hutheta hrel hstep i hb p
  have hmass := PhaseScale.mass_available S n mu delta hd hmu
  have he := BlockError.bound S hS n (r + 1) mu (by have := hc.dimension; omega) (by have := hc.dimension; omega)
    hrS (group_condition S n mu delta hd hmass) delta hd
  exact ht.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ J + 1 by positivity)))

def failure (S : ℕ+) (J k : ℕ) (omega : ℝ) : Set (Fin (J + 1) → State n mu) :=
  {h | ∃ i : Fin n, ∃ b t : Fin (J + 1), b ≤ t ∧ fraction i 0 (h b).1 ≤ processed S k ∧
    theta S ≤ fraction i 0 (h t).1 ∧
    (∀ j, j ≤ t → ∀ v, (Sampling.zeros ((h j).1 v)).card = k) ∧
    (∀ j, j ≤ t → cap omega (h j).1)}

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc omega delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1)
    (hw : 1 / (S : ℕ) ≤ omega ∧ omega ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (p : PMF (State n mu)) :
    (pathLaw (driver (r + 1) pc) p J).toOuterMeasure (failure S J (r + 1) omega) ≤
      ENNReal.ofReal ((n : ℝ) * (((J : ℝ) + 1) * delta)) := by
  have hh := finite_union_bound (pathLaw (driver (r + 1) pc) p J) (Finset.univ : Finset (Fin n))
    (fun i ↦ ProtectionHistory.failure J (r + 1) i (lowerZero S (r + 1)) (theta S) omega)
    (((J : ℝ) + 1) * delta) (mul_nonneg (by positivity) hd.1.le)
    (fun i _ ↦ column S hS hr hrS hD pc omega delta hpc hw hd hmu hn i p)
  have hmono : (pathLaw (driver (r + 1) pc) p J).toOuterMeasure (failure S J (r + 1) omega) ≤
      (pathLaw (driver (r + 1) pc) p J).toOuterMeasure
        {h | ∃ i ∈ (Finset.univ : Finset (Fin n)), h ∈
          ProtectionHistory.failure J (r + 1) i (lowerZero S (r + 1)) (theta S) omega} := by
    apply (pathLaw (driver (r + 1) pc) p J).toOuterMeasure.mono
    intro h hbad
    obtain ⟨i, b, t, hbt, hb, ht, hp, hcap⟩ := hbad
    refine ⟨i, Finset.mem_univ _, b, t, hbt, ?_, ht, hp, hcap⟩
    have hu := (lower_bounds S (r + 1)).1
    unfold processed at hb
    linarith
  apply hmono.trans
  simpa only [Finset.card_univ, Fintype.card_fin] using hh

end
end Lax343628Proofs.GlobalProtection

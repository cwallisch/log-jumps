import Lax343628Proofs.SeedBudget

namespace Lax343628Proofs.SeedEstimate

open Lax343628.Algorithm Lax343628Proofs.PhaseParameters Lax343628Proofs.EntropyLedger
open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+} {i : Fin n}

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hsize : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r) (p : PMF (Population n mu)) :
    (∑' t, (law (stopped (PlateauDynamics.auxiliaryStep (r + 1) pc)
      (CoreCounts.waiting r C (seedSize S n (r + 1) mu delta) (theta S))) p t).toOuterMeasure
        (CoreCounts.waiting r C (seedSize S n (r + 1) mu delta) (theta S))) ≤
      ENNReal.ofReal ((seedSize S n (r + 1) mu delta : ℝ) /
        (pc * (1 / 4 : ℝ) ^ (r + 1) / (64 * n)) +
        (mu : ℕ) * seedSize S n (r + 1) mu delta /
          (pc * Real.exp (-1) / (256 * (r + 1 : ℝ) ^ 2))) := by
  have hs : (16777216 : ℝ) ≤ (S : ℕ) := by exact_mod_cast hS
  have hsp : (0 : ℝ) < (S : ℕ) := by exact_mod_cast S.pos
  have hpcp : 0 < pc := (div_pos (by norm_num) hsp).trans_le hpc.1
  have hk : (1 : ℝ) ≤ r + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  have hkS : (r + 1 : ℝ) ≤ (S : ℕ) := by exact_mod_cast hrS
  have hn300 := PhaseScale.dimension S n mu delta hd hsize
  have hrho := PhaseScale.core_fraction S hS n (r + 1) mu delta hrS hD hd hmu
  norm_num only [Nat.cast_add, Nat.cast_one] at hrho
  have hsmall := SeedBudget.rho_small ((S : ℕ) : ℝ) _ hs hrho
  have hcost := SeedBudget.cost ((S : ℕ) : ℝ) (r + 1 : ℝ)
    ((r + 1 : ℝ) * seedSize S n (r + 1) mu delta / (mu : ℕ)) n hs hk hkS hrho hn300
  have hmutation := SeedBudget.mutation ((S : ℕ) : ℝ) (r + 1 : ℝ) n pc hs hk hkS hn300 hpc.1
  exact CoreWaitingBound.bound hr hn pc ⟨hpcp, hpc.2⟩ C hi hC
    (seedSize S n (r + 1) mu delta) (theta S) (theta_bounds S).1.le hsmall hcost hmutation p

end
end Lax343628Proofs.SeedEstimate

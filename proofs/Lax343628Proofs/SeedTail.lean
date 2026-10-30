import Lax343628Proofs.SeedTimeBound
import Lax343628Proofs.KernelProjection
import Lax343628Proofs.RuntimeTail

namespace Lax343628Proofs.SeedTail

open Lax343628.Algorithm Lax343628Proofs.PhaseParameters Lax343628Proofs.EntropyLedger
open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift Lax343628Proofs.DrivenNoise
open Lax343628Proofs.Trajectories
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+} {i : Fin n}

lemma projection (hkn : r + 1 ≤ n) (pc : ℝ) (C : Finset (Fin n)) (M : ℕ) (theta : ℝ)
    (p : PMF (State n mu)) (t : ℕ) :
    (law (stopped (driver (r + 1) pc) (Prod.fst ⁻¹' CoreCounts.waiting r C M theta)) p t).map Prod.fst =
      law (stopped (PlateauDynamics.auxiliaryStep (r + 1) pc) (CoreCounts.waiting r C M theta)) (p.map Prod.fst) t := by
  apply KernelProjection.stopped_law
  intro S hS
  apply driver_population hkn pc S
  intro v
  exact PlateauKernelApproximation.plateau_of_zero_card hkn _ (hS.1 v)

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hsize : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r) (p : PMF (State n mu)) (T : ℕ) :
    (pathLaw (driver (r + 1) pc) p T).toOuterMeasure
      {h | ∀ j, (h j).1 ∈ CoreCounts.waiting r C (seedSize S n (r + 1) mu delta) (theta S)} ≤
      ENNReal.ofReal ((((n : ℝ) + (mu : ℕ)) * ((S : ℕ) : ℝ) ^ 254 * logarithms n mu delta) / ((T : ℝ) + 1)) := by
  let A : Set (Population n mu) := CoreCounts.waiting r C (seedSize S n (r + 1) mu delta) (theta S)
  let W := ((n : ℝ) + (mu : ℕ)) * ((S : ℕ) : ℝ) ^ 254 * logarithms n mu delta
  have hW0 : 0 ≤ logarithms n mu delta := by have hh := (logarithms_bounds n mu delta hd).1; linarith
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hsum := SeedEstimate.bound S hS hr hn hrS hD pc delta hpc hd hmu hsize C hi hC (p.map Prod.fst)
  have htime := SeedTimeBound.bound S hS n (r + 1) mu delta pc (by omega) hD hrS hd hpc.1
  norm_num only [Nat.cast_add, Nat.cast_one] at htime
  have hsum' : (∑' t, (law (stopped (driver (r + 1) pc) (Prod.fst ⁻¹' A)) p t).toOuterMeasure (Prod.fst ⁻¹' A)) ≤
      ENNReal.ofReal W := by
    have heq (t : ℕ) : (law (stopped (driver (r + 1) pc) (Prod.fst ⁻¹' A)) p t).toOuterMeasure (Prod.fst ⁻¹' A) =
        (law (stopped (PlateauDynamics.auxiliaryStep (r + 1) pc) A) (p.map Prod.fst) t).toOuterMeasure A := by
      rw [← PMF.toOuterMeasure_map_apply]
      rw [projection (by omega : r + 1 ≤ n) pc C (seedSize S n (r + 1) mu delta) (theta S)]
    simp_rw [heq]
    exact hsum.trans (ENNReal.ofReal_le_ofReal htime)
  exact RuntimeTail.stay_le (driver (r + 1) pc) (Prod.fst ⁻¹' A) p W hW hsum' T

end
end Lax343628Proofs.SeedTail

import Lax343628Proofs.SeedTail
import Lax343628Proofs.AdaptiveWindow

namespace Lax343628Proofs.AdaptiveSeed

open Lax343628.Algorithm Lax343628Proofs.PhaseParameters Lax343628Proofs.EntropyLedger
open Lax343628Proofs.DrivenNoise Lax343628Proofs.Trajectories
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r B R : ℕ} {mu : ℕ+}

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hsize : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (C : (s : Fin (B + 1)) → Set (Fin (s.val + 1) → State n mu))
    (core : (s : Fin (B + 1)) → (Fin (s.val + 1) → State n mu) → Finset (Fin n))
    (hcore : ∀ s, ∀ h ∈ C s, (core s h).Nonempty ∧ (core s h).card ≤ r)
    (hunique : ∀ h : Fin (B + R + 1) → State n mu, ∀ s t,
      AdaptiveWindow.history s h ∈ C s → AdaptiveWindow.history t h ∈ C t → s = t)
    (p : PMF (State n mu)) :
    (pathLaw (driver (r + 1) pc) p (B + R)).toOuterMeasure
      {h | ∃ s : Fin (B + 1), AdaptiveWindow.history s h ∈ C s ∧
        ∀ j : Fin (R + 1), (AdaptiveWindow.tail s h j).1 ∈
          CoreCounts.waiting r (core s (AdaptiveWindow.history s h))
            (seedSize S n (r + 1) mu delta) (theta S)} ≤
      ENNReal.ofReal ((((n : ℝ) + (mu : ℕ)) * ((S : ℕ) : ℝ) ^ 254 * logarithms n mu delta) / ((R : ℝ) + 1)) := by
  let E := fun (s : Fin (B + 1)) (h : Fin (s.val + 1) → State n mu) ↦
    {g : Fin (R + 1) → State n mu | ∀ j, (g j).1 ∈ CoreCounts.waiting r (core s h)
      (seedSize S n (r + 1) mu delta) (theta S)}
  apply AdaptiveWindow.bound (driver (r + 1) pc) p C E _ _ hunique
  intro s h hh
  obtain ⟨i, hi⟩ := (hcore s h hh).1
  exact SeedTail.bound S hS hr hn hrS hD pc delta hpc hd hmu hsize (core s h) hi (hcore s h hh).2
    (PMF.pure (h (Fin.last s.val))) R

end
end Lax343628Proofs.AdaptiveSeed

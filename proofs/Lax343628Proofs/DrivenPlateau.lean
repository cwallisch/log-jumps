import Lax343628Proofs.RunBoundary

namespace Lax343628Proofs.DrivenPlateau

open Lax343628.Algorithm Lax343628Proofs.DrivenNoise Lax343628Proofs.Trajectories
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k H : ℕ} {mu : ℕ+}

lemma path (hkn : k ≤ n) (pc : ℝ) (S : State n mu)
    (hS : ∀ v, (Sampling.zeros (S.1 v)).card = k)
    (h : Fin (H + 1) → State n mu)
    (hh : h ∈ (pathLaw (driver k pc) (PMF.pure S) H).support) :
    ∀ j, ∀ v, (Sampling.zeros ((h j).1 v)).card = k := by
  apply path_invariant (driver k pc) (PMF.pure S) {T | ∀ v, (Sampling.zeros (T.1 v)).card = k} _ _ h hh
  · intro T hT
    have heq := (PMF.mem_support_pure_iff _ _).mp hT
    subst T
    exact hS
  · intro T hT U hU
    obtain ⟨E, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hU
    exact RunBoundary.next_zero_card hkn T.1 hT E

end
end Lax343628Proofs.DrivenPlateau

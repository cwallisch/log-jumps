import Lax343628Proofs.PolicyInvariant
import Lax343628Proofs.CoreSpecies

namespace Lax343628Proofs.WaitingCore

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.AttemptPolicy
open Lax343628Proofs.CoreCounts Lax343628Proofs.SeedGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k r : ℕ} {mu : ℕ+}

lemma missing_small (C : Finset (Fin n)) (M : ℕ) (P : Population n mu)
    (hready : ¬(ready C M P).Nonempty) : ∀ i ∈ C, missingCount i P < M := by
  intro i hi
  by_contra hn
  apply hready
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, by omega⟩⟩

lemma small (C : Finset (Fin n)) (M : ℕ) (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = k)
    (omega : ℝ) (hw : omega ≤ 1) (hcap : ColumnBlock.cap omega P)
    (hready : ¬(ready C M P).Nonempty) (hsmall : (k : ℝ) * M / (mu : ℕ) < omega) : C.card < k := by
  have hmissing := missing_small C M P hready
  by_contra hn
  obtain ⟨D, hDC, hD⟩ := Finset.exists_subset_card_eq (show k ≤ C.card by omega)
  have hrho := rho_le D P M (fun i hi ↦ hmissing i (hDC hi))
  rw [hD] at hrho
  have hrho' : rho D P < omega := by
    have heq : (k : ℝ) * ((M : ℝ) / (mu : ℕ)) = (k : ℝ) * M / (mu : ℕ) := by ring
    rw [heq] at hrho
    exact hrho.trans_lt hsmall
  have hh := CoreSpecies.small_core D P hP omega hw hcap hrho'
  omega

lemma policy (astar theta omega : ℝ) (M Rw Rs : ℕ) (P : Population n mu) (q : Config n)
    (hP : ∀ u, (zeros (P u)).card = r + 1)
    (hv : PolicyInvariant.Valid astar theta omega M Rw Rs P q) (hwait : q.stage = Stage.waiting)
    (hw : omega ≤ 1) (hsmall : (r + 1 : ℝ) * M / (mu : ℕ) < omega) :
    q.unprocessed.Nonempty ∧ q.unprocessed.card ≤ r ∧ P ∈ CoreCounts.waiting r q.unprocessed M theta := by
  simp only [PolicyInvariant.Valid, hwait] at hv
  have hc := small q.unprocessed M P hP omega hw hv.2.2.2.1 hv.2.1
    (by simpa only [Nat.cast_add, Nat.cast_one] using hsmall)
  exact ⟨hv.1, by omega, hP, missing_small _ _ _ hv.2.1, hv.2.2.2.2⟩

end
end Lax343628Proofs.WaitingCore

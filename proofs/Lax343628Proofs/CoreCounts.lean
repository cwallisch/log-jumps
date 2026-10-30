import Lax343628Proofs.SeedCount
import Lax343628Proofs.SeedOverlap

namespace Lax343628Proofs.CoreCounts

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.SeedGeometry
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison Lax343628Proofs.ClassChannels
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+}

def missingCount (i : Fin n) (P : Population n mu) : ℕ :=
  (Finset.univ.filter (fun u ↦ P u i = 1)).card

lemma missing_fraction (i : Fin n) (P : Population n mu) :
    fraction i 1 P = (missingCount i P : ℝ) / (mu : ℕ) := by
  unfold fraction missingCount
  rw [Deletion.uniform_mean, Fintype.card_fin, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma family_le (C : Finset (Fin n)) (i : Fin n) (P : Population n mu) :
    SeedCount.count (r := r) C i P ≤ missingCount i P := by
  apply Finset.card_le_card
  intro u hu
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.2.2⟩

lemma rho_le (C : Finset (Fin n)) (P : Population n mu) (M : ℕ)
    (hM : ∀ j ∈ C, missingCount j P < M) :
    rho C P ≤ C.card * ((M : ℝ) / (mu : ℕ)) := by
  apply (SeedOverlap.rho_le_missing C P).trans
  have hh := Finset.sum_le_sum (s := C) (fun j hj ↦ show fraction j 1 P ≤ (M : ℝ) / (mu : ℕ) by
    rw [missing_fraction]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (hM j hj).le)
  simpa only [Finset.sum_const, nsmul_eq_mul] using hh

def waiting (r : ℕ) (C : Finset (Fin n)) (M : ℕ) (theta : ℝ) : Set (Population n mu) :=
  {P | (∀ u, (zeros (P u)).card = r + 1) ∧
    (∀ j ∈ C, missingCount j P < M) ∧ (∀ j, j ∉ C → fraction j 0 P < theta)}

end
end Lax343628Proofs.CoreCounts

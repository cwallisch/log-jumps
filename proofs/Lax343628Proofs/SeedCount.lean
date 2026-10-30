import Lax343628Proofs.SeedFounding

namespace Lax343628Proofs.SeedCount

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.SeedGeometry
open Lax343628Proofs.ColumnKernels Lax343628Proofs.SeedIdeal Lax343628Proofs.SeedMutation
open Lax343628Proofs.FiniteDrift Lax343628Proofs.Deletion Lax343628Proofs.TaggedDynamics
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+} {i : Fin n}

def count (C : Finset (Fin n)) (i : Fin n) (P : Population n mu) : ℕ :=
  (Finset.univ.filter (fun u ↦ (zeros (P u)).card = r + 1 ∧ family C i (P u))).card

lemma total_eq (C : Finset (Fin n)) (P : Population n mu) :
    total (liftClass (familyClass (r := r) (i := i) C)) P = (count (r := r) C i P : ℝ) := by
  unfold total count
  simp_rw [SeedFounding.family_indicator]
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma total_nonneg (C : Finset (Fin n)) (P : Population n mu) :
    0 ≤ total (liftClass (familyClass (r := r) (i := i) C)) P := by
  rw [total_eq]
  positivity

lemma total_discrete (C : Finset (Fin n)) (P : Population n mu) :
    total (liftClass (familyClass (r := r) (i := i) C)) P = 0 ∨
      1 ≤ total (liftClass (familyClass (r := r) (i := i) C)) P := by
  rw [total_eq]
  by_cases hh : count (r := r) C i P = 0
  · left; simp only [hh, Nat.cast_zero]
  · right; exact_mod_cast (show 1 ≤ count (r := r) C i P by omega)

lemma total_phi (C : Finset (Fin n)) (P : Population n mu)
    (hP : ∀ u, (zeros (P u)).card = r + 1) :
    total (liftClass (familyClass (r := r) (i := i) C)) P = (mu : ℕ) * phi C i P := by
  rw [← family_average C P hP]
  unfold ClassBirthEstimates.average
  rw [Deletion.uniform_mean, Fintype.card_fin]
  have hm : ((mu : ℕ) : ℝ) ≠ 0 := by exact_mod_cast mu.ne_zero
  unfold total
  field_simp

lemma next_le (C : Finset (Fin n)) (M : ℕ) (P : Population n mu)
    (hP : count (r := r) C i P < M) (E : Event n mu) :
    total (liftClass (familyClass (r := r) (i := i) C)) (next (r + 1) P E) ≤ M := by
  have hh := (abs_le.mp (ClassIncrements.change_abs (k := r + 1)
    (liftClass (familyClass (r := r) (i := i) C)) 1 (family_bounds C) P E)).2
  unfold ClassIncrements.change at hh
  simp_rw [total_eq] at hh ⊢
  have hm : (count (r := r) C i P : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hP
  linarith

end
end Lax343628Proofs.SeedCount

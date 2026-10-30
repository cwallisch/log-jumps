import Lax343628Proofs.GeneralBirthApproximation
import Lax343628Proofs.ColumnKernels

namespace Lax343628Proofs.ColumnApproximation

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.ColumnKernels Lax343628Proofs.GeneralBirthApproximation
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def idealAction {n k : ℕ} {i : Fin n} {b : Fin 2} (S : Finset (Fin n)) (partner : BitString n)
    (h : ColumnClass n k i b → ℝ) (source : ColumnClass n k i b) : ℝ :=
  classFactor i b partner * idealBirthMean k (freshSet S) source.val partner (liftClass h)

lemma liftClass_abs {n k : ℕ} {i : Fin n} {b : Fin 2}
    (h : ColumnClass n k i b → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hh : ∀ child, 0 ≤ h child ∧ h child ≤ M) (x : BitString n) :
    |liftClass h x| ≤ M := by
  unfold liftClass
  split_ifs with hx
  · rw [abs_of_nonneg (hh ⟨x, hx⟩).1]
    exact (hh _).2
  · simpa using hM

lemma liftClass_support {n k : ℕ} {i : Fin n} {b : Fin 2}
    (h : ColumnClass n k i b → ℝ) (x : BitString n) (hx : k < (zeros x).card) :
    liftClass h x = 0 := by
  unfold liftClass
  rw [dif_neg (by omega : ¬((zeros x).card = k ∧ x i = b))]

lemma action_ideal_error {n k : ℕ} {i : Fin n} {b : Fin 2}
    (hk : 1 ≤ k) (hn : 4 * k ≤ n) (S : Finset (Fin n)) (hS : S.card ≤ 3 * k)
    (source : ColumnClass n k i b) (partner : BitString n)
    (hx : zeros source.val ⊆ S) (hy : zeros partner ⊆ S)
    (h : ColumnClass n k i b → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hh : ∀ child, 0 ≤ h child ∧ h child ≤ M) :
    |action partner h source - idealAction S partner h source| ≤
      128 * M * (k : ℝ) ^ 2 / n := by
  have herror := named_physical_error hk hn S hS source.val partner hx hy (liftClass h) M hM
    (liftClass_abs h M hM hh) (liftClass_support h)
  rw [action_eq_mean, idealAction, ← mul_sub, abs_mul,
    abs_of_nonneg (classFactor_bounds i b partner).1]
  calc
    _ ≤ classFactor i b partner * (64 * M * (k : ℝ) ^ 2 / n) :=
      mul_le_mul_of_nonneg_left herror (classFactor_bounds i b partner).1
    _ ≤ 2 * (64 * M * (k : ℝ) ^ 2 / n) :=
      mul_le_mul_of_nonneg_right (classFactor_bounds i b partner).2 (by positivity)
    _ = _ := by ring

end
end Lax343628Proofs.ColumnApproximation

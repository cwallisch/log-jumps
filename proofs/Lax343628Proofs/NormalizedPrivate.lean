import Lax343628Proofs.PrivateKernelFormula
import Lax343628Proofs.CatalystBounds

namespace Lax343628Proofs.NormalizedPrivate

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.NamedBirth
open Lax343628Proofs.PrivatePool Lax343628Proofs.PrivateKernelFormula
open Lax343628Proofs.ColumnKernels Lax343628Proofs.BirthGeometry
open Lax343628Proofs.CurveBounds Lax343628Proofs.FiniteDrift
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma resident_private_size {n r : ℕ} {i : Fin n} (x : ColumnClass n (r + 1) i 0) :
    ((zeros x.val).erase i).card = r := by
  rw [Finset.card_erase_of_mem (by rw [mem_zeros]; exact x.property.2), x.property.1]
  omega

lemma mutant_private_size {n r : ℕ} {i : Fin n} (x : ColumnClass n r i 1) :
    ((zeros x.val).erase i).card = r := by
  rw [Finset.erase_eq_of_notMem (by simp [mem_zeros, x.property.2]), x.property.1]

lemma liftClass_exact_support {n k : ℕ} {i : Fin n} {b : Fin 2}
    (h : ColumnClass n k i b → ℝ) (x : BitString n) (hx : (zeros x).card ≠ k) : liftClass h x = 0 := by
  unfold liftClass
  rw [dif_neg (fun h ↦ hx h.1)]

lemma resident_normalized {n r : ℕ} {i : Fin n} (S : Finset (Fin n))
    (hk : r + 1 ≤ (GeneralBirthApproximation.freshSet S).card) (hi : i ∈ S)
    (source : ColumnClass n (r + 1) i 0) (partner : BitString n)
    (hx : zeros source.val ⊆ S) (hy : zeros partner ⊆ S)
    (h : ColumnClass n (r + 1) i 0 → ℝ) :
    ColumnApproximation.idealAction S partner h source =
      mass r (common i source.val partner) (label i source.val partner) *
      mean (PlacedBase.placedLaw (r - (common i source.val partner).card))
        (fun Z ↦ test i 0 (liftClass h) (fromZeros (realize (common i source.val partner)
          (label i source.val partner) (GeneralBirthApproximation.freshSet S)
          (admissible _ i source.val partner
            (GeneralBirthApproximation.freshSet_common_ones S source.val partner hx hy)).named_fresh Z))) := by
  rw [column_ideal_private S hk hi source partner hx hy h]
  have hC : (common i source.val partner).card ≤ r :=
    (common_card_le i source.val partner).trans_eq (resident_private_size source)
  apply value_fixed_size_general (Nat.le_succ r) _ _ _
    (admissible _ i source.val partner (GeneralBirthApproximation.freshSet_common_ones S source.val partner hx hy))
    hC hk
  exact test_resident_support i (liftClass h) (liftClass_exact_support h)

lemma mutant_normalized {n r : ℕ} {i : Fin n} (S : Finset (Fin n))
    (hk : r ≤ (GeneralBirthApproximation.freshSet S).card) (hi : i ∈ S)
    (source : ColumnClass n r i 1) (partner : BitString n)
    (hx : zeros source.val ⊆ S) (hy : zeros partner ⊆ S) (h : ColumnClass n r i 1 → ℝ) :
    ColumnApproximation.idealAction S partner h source =
      mass r (common i source.val partner) (label i source.val partner) *
      mean (PlacedBase.placedLaw (r - (common i source.val partner).card))
        (fun Z ↦ test i 1 (liftClass h) (fromZeros (realize (common i source.val partner)
          (label i source.val partner) (GeneralBirthApproximation.freshSet S)
          (admissible _ i source.val partner
            (GeneralBirthApproximation.freshSet_common_ones S source.val partner hx hy)).named_fresh Z))) := by
  rw [column_ideal_private S hk hi source partner hx hy h]
  have hC : (common i source.val partner).card ≤ r :=
    (common_card_le i source.val partner).trans_eq (mutant_private_size source)
  apply value_fixed_size_general le_rfl _ _ _
    (admissible _ i source.val partner (GeneralBirthApproximation.freshSet_common_ones S source.val partner hx hy))
    hC hk
  exact test_mutant_support i (liftClass h) (liftClass_exact_support h)

lemma balanced_mass {n r : ℕ} (i : Fin n) (x y : BitString n)
    (hx : ((zeros x).erase i).card = r) (hy : ((zeros y).erase i).card = r) :
    mass r (common i x y) (label i x y) = Real.exp (-1) * q (r - (common i x y).card) := by
  have hC : (common i x y).card ≤ r := (common_card_le i x y).trans_eq hx
  have hbalance := pool_card_balance i x y
  rw [hx, hy] at hbalance
  have hv : Fintype.card (Pool i x y) = 2 * (r - (common i x y).card) := by omega
  unfold mass q profile
  rw [hv]
  ring

lemma upper_unbalanced_mass {n r : ℕ} (i : Fin n) (x y : BitString n)
    (hx : ((zeros x).erase i).card = r + 1) (hy : ((zeros y).erase i).card = r) :
    mass (r + 1) (common i x y) (label i x y) = Real.exp (-1) * t (r - (common i x y).card) := by
  have hc : common i x y = common i y x := by unfold common; rw [Finset.inter_comm]
  have hC : (common i x y).card ≤ r := hc ▸ (common_card_le i y x).trans_eq hy
  have hbalance := pool_card_balance i x y
  rw [hx, hy] at hbalance
  have hv : Fintype.card (Pool i x y) = 2 * (r - (common i x y).card) + 1 := by omega
  have hj : r + 1 - (common i x y).card = (r - (common i x y).card) + 1 := by omega
  unfold mass t profile
  rw [hv, hj]
  ring

end
end Lax343628Proofs.NormalizedPrivate

import Lax343628Proofs.PrivateColumns
import Lax343628Proofs.NormalizedPrivate
import Lax343628Proofs.ParentCone

namespace Lax343628Proofs.ClassTest

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.NamedBirth
open Lax343628Proofs.ColumnKernels Lax343628Proofs.PrivateColumns
open Lax343628Proofs.FiniteExchange Lax343628Proofs.MeanCone
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {i : Fin n} {b : Fin 2}

def size (k : ℕ) (b : Fin 2) : ℕ := if b = 0 then k - 1 else k

def test (h : ColumnClass n k i b → ℝ) (Z : Finset (Fin n)) : ℝ :=
  PrivatePool.test i b (liftClass h) (fromZeros Z)

lemma private_card (_hk : 1 ≤ k) (x : ColumnClass n k i b) :
    ((zeros x.val).erase i).card = size k b := by
  fin_cases b
  · rw [Finset.card_erase_of_mem (by rw [mem_zeros]; exact x.property.2), x.property.1]
    rfl
  · rw [Finset.erase_eq_of_notMem (by simp [mem_zeros, x.property.2]), x.property.1]
    rfl

lemma test_nonneg (h : ColumnClass n k i b → ℝ) (hh : ∀ x, 0 ≤ h x) (Z : Finset (Fin n)) :
    0 ≤ test h Z := by
  unfold test PrivatePool.test liftClass
  split_ifs <;> first | exact hh _ | rfl

lemma test_support (hk : 1 ≤ k) (h : ColumnClass n k i b → ℝ) (Z : Finset (Fin n))
    (hZ : Z.card ≠ size k b) : test h Z = 0 := by
  fin_cases b
  · have hk' : k - 1 + 1 = k := by omega
    exact PrivatePool.test_resident_support (r := k - 1) i (liftClass h)
      (fun x hx ↦ NormalizedPrivate.liftClass_exact_support h x (by simpa [hk'] using hx))
      (fromZeros Z) (by simpa [size] using hZ)
  · exact PrivatePool.test_mutant_support i (liftClass h)
      (NormalizedPrivate.liftClass_exact_support h) (fromZeros Z) (by simpa [size] using hZ)

lemma full_card (hk : 1 ≤ k) (Z : Finset (Fin n)) (hZ : Z.card = size k b) (hi : i ∉ Z) :
    (if b = 0 then insert i Z else Z).card = k := by
  fin_cases b
  · change Z.card = k - 1 at hZ
    change (insert i Z).card = k
    rw [Finset.card_insert_of_notMem hi, hZ]
    omega
  · simpa [size] using hZ

def encode (hk : 1 ≤ k) (Z : Finset (Fin n)) (hZ : Z.card = size k b) (hi : i ∉ Z) :
    ColumnClass n k i b :=
  ⟨fromZeros (if b = 0 then insert i Z else Z), by
    rw [zeros_fromZeros]; exact full_card hk Z hZ hi,
    by fin_cases b <;> simp [fromZeros, hi]⟩

lemma encode_private (hk : 1 ≤ k) (Z : Finset (Fin n)) (hZ : Z.card = size k b) (hi : i ∉ Z) :
    ((zeros (encode hk Z hZ hi).val).erase i) = Z := by
  unfold encode
  rw [zeros_fromZeros]
  fin_cases b <;> simp [hi]

lemma test_encode (hk : 1 ≤ k) (h : ColumnClass n k i b → ℝ) (Z : Finset (Fin n))
    (hZ : Z.card = size k b) (hi : i ∉ Z) : test h Z = h (encode hk Z hZ hi) := by
  have hbit : fromZeros Z i = 1 := by simp [fromZeros, hi]
  have hu : Function.update (fromZeros Z) i b = (encode hk Z hZ hi).val := by
    fin_cases b
    · exact (ColumnSlotSplit.fromZeros_insert Z i).symm
    · change Function.update (fromZeros Z) i 1 = fromZeros Z
      rw [← hbit, Function.update_eq_self]
  unfold test PrivatePool.test
  rw [if_pos hbit, hu, liftClass_self]

lemma encode_distance (hk : 1 ≤ k) (U V : Finset (Fin n))
    (hU : U.card = size k b) (hV : V.card = size k b) (hiU : i ∉ U) (hiV : i ∉ V) :
    classDistance (encode hk U hU hiU) (encode hk V hV hiV) = (U \ V).card := by
  unfold classDistance encode
  simp only [zeros_fromZeros]
  fin_cases b
  · change (insert i U \ insert i V).card = (U \ V).card
    congr 1
    ext a
    by_cases ha : a = i <;> simp [ha, hiU, hiV]
  · rfl

lemma test_cone (hk : 1 ≤ k) (rho : ℝ) (hrho : 1 ≤ rho)
    (h : ColumnClass n k i b → ℝ) (hn : ∀ x, 0 ≤ h x)
    (hc : ∀ x y, classDistance x y = 1 → h y ≤ rho * h x) :
    Cone i (size k b) rho (test h) := by
  intro U V hU hiU hiV hNear
  have hV := hNear.1.symm.trans hU
  rcases near_eq_or_exchange hNear with hEq | hStep
  · subst V
    nlinarith [test_nonneg h hn U]
  · rw [test_encode hk h U hU hiU, test_encode hk h V hV hiV]
    exact hc _ _ (by rw [encode_distance]; exact hStep)

lemma private_distance (x y : ColumnClass n k i b) :
    (((zeros x.val).erase i) \ ((zeros y.val).erase i)).card = classDistance x y := by
  unfold classDistance
  congr 1
  ext a
  by_cases hai : a = i
  · subst a
    simp only [Finset.mem_sdiff, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
      mem_zeros, x.property.2, y.property.2, and_not_self]
  · simp [hai]

end
end Lax343628Proofs.ClassTest

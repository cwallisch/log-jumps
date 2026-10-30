import Lax343628Proofs.Sampling
import Mathlib.Data.Fintype.Powerset

namespace Lax343628Proofs.MaskCounts

open Lax343628.Algorithm Lax343628Proofs.Sampling
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def onesSet {n : ℕ} (mask : BitString n) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ mask j = 1)

def fromSet {n : ℕ} (S : Finset (Fin n)) : BitString n := fun j ↦ if j ∈ S then 1 else 0

@[simp] lemma card_onesSet {n : ℕ} (mask : BitString n) : (onesSet mask).card = ones mask :=
  (ones_eq_count mask).symm

@[simp] lemma onesSet_fromSet {n : ℕ} (S : Finset (Fin n)) : onesSet (fromSet S) = S := by
  ext j
  simp [onesSet, fromSet]

@[simp] lemma fromSet_onesSet {n : ℕ} (mask : BitString n) : fromSet (onesSet mask) = mask := by
  funext j
  by_cases hj : mask j = 1
  · simp [fromSet, onesSet, hj]
  · have hj0 : mask j = 0 := by have h := (mask j).isLt; omega
    simp [fromSet, onesSet, hj0]

@[simp] lemma ones_fromSet {n : ℕ} (S : Finset (Fin n)) : ones (fromSet S) = S.card := by
  rw [← card_onesSet, onesSet_fromSet]

def weightEquiv (n w : ℕ) : {mask : BitString n // ones mask = w} ≃
    {S : Finset (Fin n) // S.card = w} where
  toFun mask := ⟨onesSet mask.val, by rw [card_onesSet, mask.property]⟩
  invFun S := ⟨fromSet S.val, by rw [ones_fromSet, S.property]⟩
  left_inv mask := Subtype.ext (fromSet_onesSet mask.val)
  right_inv S := Subtype.ext (onesSet_fromSet S.val)

lemma count_masks (n w : ℕ) : Fintype.card {mask : BitString n // ones mask = w} = n.choose w := by
  rw [Fintype.card_congr (weightEquiv n w), Fintype.card_finset_len, Fintype.card_fin]

lemma independentBits_weight {n : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (mask : BitString n) :
    independentBits n p mask = ENNReal.ofReal p ^ ones mask *
      ENNReal.ofReal (1 - p) ^ (n - ones mask) := by
  have hprod : independentBits n p mask = ∏ j : Fin n,
      if j ∈ onesSet mask then ENNReal.ofReal p else ENNReal.ofReal (1 - p) := by
    rw [independentBits_apply]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : mask j = 1
    · simp [onesSet, hj, coin_one p hp]
    · have hj0 : mask j = 0 := by have h := (mask j).isLt; omega
      simp [onesSet, hj0, coin_zero p hp]
  have hcomp : (Finset.univ.filter (fun j ↦ j ∉ onesSet mask)).card = n - ones mask := by
    have heq : Finset.univ.filter (fun j ↦ j ∉ onesSet mask) = zeros mask := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, onesSet, mem_zeros]
      have hj : mask j = 0 ∨ mask j = 1 := by have h := (mask j).isLt; omega
      rcases hj with hj | hj <;> simp [hj]
    rw [heq, card_zeros]
  rw [hprod, Finset.prod_ite]
  simp only [Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter, card_onesSet, hcomp]

lemma independentBits_count_probability (n w : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (independentBits n p).toOuterMeasure {mask | ones mask = w} =
      (n.choose w : ℝ≥0∞) * ENNReal.ofReal p ^ w * ENNReal.ofReal (1 - p) ^ (n - w) := by
  have hevent : {mask : BitString n | ones mask = w} =
      ((Finset.univ.filter (fun mask : BitString n ↦ ones mask = w)) : Set (BitString n)) := by
    ext mask
    simp
  rw [hevent, PMF.toOuterMeasure_apply_finset]
  have hcard : (Finset.univ.filter (fun mask : BitString n ↦ ones mask = w)).card = n.choose w := by
    rw [← Fintype.card_subtype]
    exact count_masks n w
  calc
    _ = ∑ _mask ∈ Finset.univ.filter (fun mask : BitString n ↦ ones mask = w),
        ENNReal.ofReal p ^ w * ENNReal.ofReal (1 - p) ^ (n - w) := by
      apply Finset.sum_congr rfl
      intro mask hmask
      rw [independentBits_weight p hp, (Finset.mem_filter.mp hmask).2]
    _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_assoc]

lemma independentBits_count_real (n w : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ((independentBits n p).toOuterMeasure {mask | ones mask = w}).toReal =
      (n.choose w : ℝ) * p ^ w * (1 - p) ^ (n - w) := by
  rw [independentBits_count_probability n w p hp]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hp.1, ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)]

lemma ones_le_length {n : ℕ} (mask : BitString n) : ones mask ≤ n := by
  rw [← card_onesSet]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)

def weightLaw (n : ℕ) (p : ℝ) : PMF (Fin (n + 1)) :=
  (independentBits n p).map (fun mask ↦ ⟨ones mask, Nat.lt_succ_of_le (ones_le_length mask)⟩)

def weightFiber (n : ℕ) (w : Fin (n + 1)) : Finset (BitString n) :=
  Finset.univ.filter (fun mask ↦ ones mask = w.val)

lemma weightFiber_card (n : ℕ) (w : Fin (n + 1)) : (weightFiber n w).card = n.choose w.val := by
  rw [weightFiber, ← Fintype.card_subtype]
  exact count_masks n w

lemma weightFiber_nonempty (n : ℕ) (w : Fin (n + 1)) : (weightFiber n w).Nonempty := by
  rw [← Finset.card_pos, weightFiber_card]
  exact Nat.choose_pos (Nat.le_of_lt_succ w.isLt)

def uniformWeight (n : ℕ) (w : Fin (n + 1)) : PMF (BitString n) :=
  PMF.uniformOfFinset (weightFiber n w) (weightFiber_nonempty n w)

lemma uniformWeight_apply (n : ℕ) (w : Fin (n + 1)) (mask : BitString n) :
    uniformWeight n w mask = if ones mask = w.val then (n.choose w.val : ℝ≥0∞)⁻¹ else 0 := by
  rw [uniformWeight, PMF.uniformOfFinset_apply, weightFiber_card]
  simp only [weightFiber, Finset.mem_filter, Finset.mem_univ, true_and]

lemma weightLaw_apply (n : ℕ) (p : ℝ) (w : Fin (n + 1)) :
    weightLaw n p w = (independentBits n p).toOuterMeasure {mask | ones mask = w.val} := by
  rw [← PMF.toOuterMeasure_apply_singleton, weightLaw, PMF.toOuterMeasure_map_apply]
  congr 1
  ext mask
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff, Set.mem_ofPred_eq]

lemma independentBits_mixture (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (weightLaw n p).bind (uniformWeight n) = independentBits n p := by
  ext mask
  rw [PMF.bind_apply]
  let w : Fin (n + 1) := ⟨ones mask, Nat.lt_succ_of_le (ones_le_length mask)⟩
  rw [tsum_eq_single w]
  · rw [weightLaw_apply, independentBits_count_probability n w.val p hp, uniformWeight_apply,
      if_pos (show ones mask = w.val from rfl)]
    have hc : (n.choose w.val : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_of_lt_succ w.isLt)).ne'
    rw [mul_right_comm _ _ ((n.choose w.val : ℝ≥0∞)⁻¹),
      mul_right_comm _ _ ((n.choose w.val : ℝ≥0∞)⁻¹),
      ENNReal.mul_inv_cancel hc (by simp), one_mul]
    exact (independentBits_weight p hp mask).symm
  · intro w' hw'
    have hne : ones mask ≠ w'.val := by
      intro heq
      exact hw' (Fin.ext heq.symm)
    rw [uniformWeight_apply, if_neg hne, mul_zero]

lemma weightLaw_zero (n : ℕ) : weightLaw n 0 = PMF.pure 0 := by
  ext w
  rw [weightLaw_apply, independentBits_count_probability n w.val 0 (by norm_num)]
  by_cases hw : w.val = 0
  · have hw' : w = 0 := Fin.ext hw
    simp [hw']
  · have hw' : w ≠ 0 := fun h ↦ hw (congrArg Fin.val h)
    simp [zero_pow hw, PMF.pure_apply_of_ne _ _ hw']

lemma weightLaw_one (n : ℕ) :
    weightLaw n 1 = PMF.pure (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := by
  ext w
  rw [weightLaw_apply, independentBits_count_probability n w.val 1 (by norm_num)]
  by_cases hw : w.val = n
  · have hw' : w = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := Fin.ext hw
    simp [hw']
  · have hsub : n - w.val ≠ 0 := by have h := w.isLt; omega
    have hw' : w ≠ (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) :=
      fun h ↦ hw (congrArg Fin.val h)
    simp [zero_pow hsub, PMF.pure_apply_of_ne _ _ hw']

end
end Lax343628Proofs.MaskCounts

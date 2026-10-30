import Lax343628Proofs.Sampling
import Mathlib.Tactic.Linarith

namespace Lax343628Proofs.Flatness

open Lax343628.Algorithm Lax343628Proofs.Sampling
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def columnCount {n : ℕ} {μ : ℕ+} (P : Population n μ) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun i ↦ P i j = 0)).card

lemma columnCount_eq_sum {n : ℕ} {μ : ℕ+} (P : Population n μ) (j : Fin n) :
    columnCount P j = ∑ i : Fin (μ : ℕ), if P i j = 0 then 1 else 0 := by
  simp only [columnCount, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma intersection_eq_sum {n : ℕ} (x y : BitString n) :
    ((zeros x) ∩ (zeros y)).card = ∑ j : Fin n, if x j = 0 ∧ y j = 0 then 1 else 0 := by
  have heq : zeros x ∩ zeros y = Finset.univ.filter (fun j ↦ x j = 0 ∧ y j = 0) := by
    ext j
    simp
  rw [heq, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma sum_columnCount {n k : ℕ} {μ : ℕ+} (P : Population n μ)
    (hP : ∀ i, (zeros (P i)).card = k) : ∑ j : Fin n, columnCount P j = (μ : ℕ) * k := by
  simp only [columnCount_eq_sum]
  rw [Finset.sum_comm]
  calc
    (∑ i : Fin (μ : ℕ), ∑ j : Fin n, if P i j = 0 then 1 else 0) =
        ∑ i : Fin (μ : ℕ), (zeros (P i)).card := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [zeros, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = (μ : ℕ) * k := by simp [hP]

lemma sum_intersections {n : ℕ} {μ : ℕ+} (P : Population n μ) :
    (∑ u : Fin (μ : ℕ), ∑ v : Fin (μ : ℕ), (zeros (P u) ∩ zeros (P v)).card) =
      ∑ j : Fin n, columnCount P j ^ 2 := by
  simp only [intersection_eq_sum]
  calc
    (∑ u : Fin (μ : ℕ), ∑ v : Fin (μ : ℕ), ∑ j : Fin n,
        if P u j = 0 ∧ P v j = 0 then 1 else 0) =
        ∑ j : Fin n, ∑ u : Fin (μ : ℕ), ∑ v : Fin (μ : ℕ),
          if P u j = 0 ∧ P v j = 0 then 1 else 0 := by
      simp_rw [Finset.sum_comm (s := Finset.univ (α := Fin (μ : ℕ)))
        (t := Finset.univ (α := Fin n))]
    _ = ∑ j : Fin n, columnCount P j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [columnCount_eq_sum, pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hu : P u j = 0 <;> by_cases hv : P v j = 0 <;> simp [hu, hv]

lemma bad_pairs_le_intersections {n : ℕ} {μ : ℕ+} (P : Population n μ) :
    (∑ u : Fin (μ : ℕ), ∑ v : Fin (μ : ℕ),
      if Disjoint (zeros (P u)) (zeros (P v)) then 0 else 1) ≤
        ∑ j : Fin n, columnCount P j ^ 2 := by
  rw [← sum_intersections]
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  split_ifs with h
  · exact Nat.zero_le _
  · have hne : zeros (P u) ∩ zeros (P v) ≠ ∅ := by simpa [Finset.disjoint_iff_inter_eq_empty] using h
    exact Nat.one_le_iff_ne_zero.mpr (by simpa using hne)

lemma bad_pairs_le_half {n k : ℕ} {μ : ℕ+} (P : Population n μ)
    (hP : ∀ i, (zeros (P i)).card = k)
    (hflat : ∀ j, 2 * k * columnCount P j ≤ (μ : ℕ)) :
    2 * (∑ u : Fin (μ : ℕ), ∑ v : Fin (μ : ℕ),
      if Disjoint (zeros (P u)) (zeros (P v)) then 0 else 1) ≤ (μ : ℕ) ^ 2 := by
  by_cases hk : k = 0
  · have hempty : ∀ i, zeros (P i) = ∅ := fun i ↦
      Finset.card_eq_zero.mp (by simpa only [hk] using hP i)
    simp [hempty]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hsq : 2 * k * (∑ j : Fin n, columnCount P j ^ 2) ≤ (μ : ℕ) ^ 2 * k := by
    calc
      2 * k * (∑ j : Fin n, columnCount P j ^ 2) =
          ∑ j : Fin n, (2 * k * columnCount P j) * columnCount P j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ j : Fin n, (μ : ℕ) * columnCount P j :=
        Finset.sum_le_sum fun j _ ↦ Nat.mul_le_mul_right _ (hflat j)
      _ = (μ : ℕ) ^ 2 * k := by rw [← Finset.mul_sum, sum_columnCount P hP]; ring
  have hsum : 2 * k * (∑ u : Fin (μ : ℕ), ∑ v : Fin (μ : ℕ),
      if Disjoint (zeros (P u)) (zeros (P v)) then 0 else 1) ≤ (μ : ℕ) ^ 2 * k :=
    (Nat.mul_le_mul_left _ (bad_pairs_le_intersections P)).trans hsq
  have hsum' : (2 * (∑ u : Fin (μ : ℕ), ∑ v : Fin (μ : ℕ),
      if Disjoint (zeros (P u)) (zeros (P v)) then 0 else 1)) * k ≤ (μ : ℕ) ^ 2 * k := by
    simpa only [Nat.mul_right_comm] using hsum
  exact Nat.le_of_mul_le_mul_right hsum' hkpos

def complementary {n : ℕ} {μ : ℕ+} (P : Population n μ) :
    Set (Fin (μ : ℕ) × Fin (μ : ℕ)) :=
  {uv | Disjoint (zeros (P uv.1)) (zeros (P uv.2))}

lemma twice_good_pairs {n k : ℕ} {μ : ℕ+} (P : Population n μ)
    (hP : ∀ i, (zeros (P i)).card = k)
    (hflat : ∀ j, 2 * k * columnCount P j ≤ (μ : ℕ)) :
    (μ : ℕ) ^ 2 ≤ 2 * Fintype.card (complementary P) := by
  have hgood : Fintype.card (complementary P) =
      ∑ u : Fin (μ : ℕ), ∑ v : Fin (μ : ℕ),
        if Disjoint (zeros (P u)) (zeros (P v)) then 1 else 0 := by
    rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_prod_type]
    simp only [complementary, Set.mem_ofPred_eq]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : Disjoint (zeros (P u)) (zeros (P v))
    · simp only [if_pos h]
    · simp only [if_neg h]
  have htotal : Fintype.card (complementary P) +
      (∑ u : Fin (μ : ℕ), ∑ v : Fin (μ : ℕ),
        if Disjoint (zeros (P u)) (zeros (P v)) then 0 else 1) = (μ : ℕ) ^ 2 := by
    rw [hgood, ← Finset.sum_add_distrib]
    calc
      (∑ u : Fin (μ : ℕ), ((∑ v : Fin (μ : ℕ),
          if Disjoint (zeros (P u)) (zeros (P v)) then 1 else 0) +
          (∑ v : Fin (μ : ℕ), if Disjoint (zeros (P u)) (zeros (P v)) then 0 else 1))) =
          ∑ _u : Fin (μ : ℕ), ∑ _v : Fin (μ : ℕ), 1 := by
        apply Finset.sum_congr rfl
        intro u _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> rfl
      _ = (μ : ℕ) ^ 2 := by simp [pow_two]
  have hbad := bad_pairs_le_half P hP hflat
  omega

lemma complementary_probability {n k : ℕ} {μ : ℕ+} (P : Population n μ)
    (hP : ∀ i, (zeros (P i)).card = k)
    (hflat : ∀ j, 2 * k * columnCount P j ≤ (μ : ℕ)) :
    (2 : ℝ≥0∞)⁻¹ ≤ (PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ))).toOuterMeasure
      (complementary P) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, Fintype.card_prod, Fintype.card_fin]
  have hcount : ((μ : ℕ) : ℝ≥0∞) ^ 2 ≤ 2 * (Fintype.card (complementary P) : ℝ≥0∞) := by
    exact_mod_cast twice_good_pairs P hP hflat
  have hμ : ((μ : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast μ.ne_zero
  rw [Nat.cast_mul]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hμ hμ))
    (Or.inl (ENNReal.mul_ne_top (by simp) (by simp)))).mpr
  calc
    (2 : ℝ≥0∞)⁻¹ * ((μ : ℕ) * (μ : ℕ)) ≤
        (2 : ℝ≥0∞)⁻¹ * (2 * (Fintype.card (complementary P) : ℝ≥0∞)) :=
      mul_le_mul_right (by simpa only [pow_two] using hcount) _
    _ = (Fintype.card (complementary P) : ℝ≥0∞) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by simp), one_mul]

end
end Lax343628Proofs.Flatness

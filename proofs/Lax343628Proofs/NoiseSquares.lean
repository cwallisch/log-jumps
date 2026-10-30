import Lax343628Proofs.SparseDynamics
import Lax343628Proofs.WeightedFieldControl

namespace Lax343628Proofs.NoiseSquares

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassChannels Lax343628Proofs.WeightedFieldControl
open Lax343628Proofs.TaggedDynamics Lax343628Proofs.NormalizedClassNoise
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu rs : ℕ+}

lemma mutant_channel_bound (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k) (i : Fin n)
    (h : ColumnClass n k i 1 → ℝ) (D y : ℝ) (hD : 0 ≤ D) (hy : 0 < y)
    (hh : ∀ x, 0 ≤ h x) (hratio : ∀ x z, h z ≤ D * h x)
    (havg : average P (liftClass h) ≤ y) (hf : 0 < fraction i 1 P) (E : Event n mu) :
    |fieldNoise (k := k) pc P i (liftClass h) y E| ≤
      D / ((mu : ℕ) * fraction i 1 P) * (if channel i 1 P E then 1 else 0) + 3 * D / (mu : ℕ) := by
  let M := D * y / fraction i 1 P
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbound (x : ColumnClass n k i 1) : 0 ≤ h x ∧ h x ≤ M :=
    ⟨hh x, child_bound P hP h D y hD hratio havg hf x⟩
  have hb := (ClassNoise.mutant_noise (k := k) pc hpc i (liftClass h) M hM
    (ColumnFieldBounds.lift_bounds h M hM hbound) (ColumnFieldBounds.lift_bit h) P).1 E
  have hm : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  unfold fieldNoise NoiseNormalization.noise
  rw [abs_div, abs_of_pos (mul_pos hm hy)]
  have hb' := div_le_div_of_nonneg_right hb (mul_nonneg hm.le hy.le)
  apply hb'.trans_eq
  dsimp [M]
  field_simp

lemma mutant_square (hk : 2 ≤ k) (hn : 4 * k ≤ n)
    (sigma : Net n k R (count R ell) rs) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (i : Fin n) {a : ℝ} (ha : 0 ≤ a) (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (t : ℕ) (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (fmin : ℝ) (hfmin : 0 < fmin) (hf : fmin ≤ fraction i 1 P) (E : Event n mu) :
    SparseNoise.noise sigma pc i 1 a t P E ^ 2 ≤
      2 * ((3 : ℝ) ^ k / ((mu : ℕ) * fmin)) ^ 2 * (if channel i 1 P E then 1 else 0) +
        18 * ((3 : ℝ) ^ k / (mu : ℕ)) ^ 2 := by
  by_cases ht : t < sigma.1.val
  · have hfpos : 0 < fraction i 1 P := hfmin.trans_le hf
    have hy : 0 < average P (liftClass (field sigma i 1 a t)) := hfpos.trans_le
      (GroupSampling.average_one_lower P hP _ (field_one sigma i 1 ha t))
    have hb := mutant_channel_bound pc hpc P hP i (field sigma i 1 a (t + 1)) ((3 : ℝ) ^ k) _
      (by positivity) hy (fun x ↦ le_trans (by norm_num : (0 : ℝ) ≤ 1) (field_one sigma i 1 ha (t + 1) x))
      (field_ratio hk hn sigma i 1 ha horizon (t + 1)) (average_field_step P sigma i 1 ha t ht) hfpos E
    have hm : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
    have hden : (3 : ℝ) ^ k / ((mu : ℕ) * fraction i 1 P) ≤ (3 : ℝ) ^ k / ((mu : ℕ) * fmin) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hm hfmin) (mul_le_mul_of_nonneg_left hf hm.le)
    have hI : (0 : ℝ) ≤ if channel i 1 P E then 1 else 0 := by split_ifs <;> norm_num
    have hb' := hb.trans (add_le_add (mul_le_mul_of_nonneg_right hden hI) (le_refl _))
    have hnoise : SparseNoise.noise sigma pc i 1 a t P E = fieldNoise (k := k) pc P i
        (liftClass (field sigma i 1 a (t + 1))) (average P (liftClass (field sigma i 1 a t))) E := by
      simp only [SparseNoise.noise, if_pos ht]
    rw [hnoise]
    have hnsq : (fieldNoise (k := k) pc P i (liftClass (field sigma i 1 a (t + 1)))
        (average P (liftClass (field sigma i 1 a t))) E) ^ 2 ≤
        ((3 : ℝ) ^ k / ((mu : ℕ) * fmin) * (if channel i 1 P E then 1 else 0) + 3 * (3 : ℝ) ^ k / (mu : ℕ)) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb'
    simp only [mul_div_assoc] at hnsq
    by_cases hc : channel i 1 P E
    · simp only [if_pos hc, mul_one] at hnsq ⊢
      have hsq := sq_nonneg ((3 : ℝ) ^ k / ((mu : ℕ) * fmin) - 3 * ((3 : ℝ) ^ k / (mu : ℕ)))
      nlinarith
    · simp only [if_neg hc, mul_zero, zero_add] at hnsq ⊢
      nlinarith [sq_nonneg ((3 : ℝ) ^ k / (mu : ℕ))]
  · simp only [SparseNoise.noise, if_neg ht, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity

lemma mutant_sum (hk : 2 ≤ k) (hn : 4 * k ≤ n)
    (sigma : Net n k R (count R ell) rs) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (i : Fin n) {a : ℝ} (ha : 0 ≤ a) (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : ℕ → Population n mu) (E : ℕ → Event n mu) (H : ℕ)
    (hP : ∀ t, t < H → ∀ u, (Sampling.zeros (P t u)).card = k)
    (fmin : ℝ) (hfmin : 0 < fmin) (hf : ∀ t, t < H → fmin ≤ fraction i 1 (P t)) :
    (∑ t ∈ Finset.range H, SparseNoise.noise sigma pc i 1 a t (P t) (E t) ^ 2) ≤
      2 * ((3 : ℝ) ^ k / ((mu : ℕ) * fmin)) ^ 2 *
        (∑ t ∈ Finset.range H, if channel i 1 (P t) (E t) then 1 else 0) +
        18 * H * ((3 : ℝ) ^ k / (mu : ℕ)) ^ 2 := by
  have hh := Finset.sum_le_sum (s := Finset.range H) (fun t ht ↦
    mutant_square hk hn sigma pc hpc i ha horizon t (P t) (hP t (Finset.mem_range.mp ht))
      fmin hfmin (hf t (Finset.mem_range.mp ht)) (E t))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hh

lemma mutant_abs (hk : 2 ≤ k) (hn : 4 * k ≤ n)
    (sigma : Net n k R (count R ell) rs) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (i : Fin n) {a : ℝ} (ha : 0 ≤ a) (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (t : ℕ) (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (fmin : ℝ) (hfmin : 0 < fmin) (hf : fmin ≤ fraction i 1 P) (E : Event n mu) :
    |SparseNoise.noise sigma pc i 1 a t P E| ≤
      (3 : ℝ) ^ k / ((mu : ℕ) * fmin) + 3 * (3 : ℝ) ^ k / (mu : ℕ) := by
  by_cases ht : t < sigma.1.val
  · have hfpos : 0 < fraction i 1 P := hfmin.trans_le hf
    have hy : 0 < average P (liftClass (field sigma i 1 a t)) := hfpos.trans_le
      (GroupSampling.average_one_lower P hP _ (field_one sigma i 1 ha t))
    have hb := mutant_channel_bound pc hpc P hP i (field sigma i 1 a (t + 1)) ((3 : ℝ) ^ k) _
      (by positivity) hy (fun x ↦ le_trans (by norm_num : (0 : ℝ) ≤ 1) (field_one sigma i 1 ha (t + 1) x))
      (field_ratio hk hn sigma i 1 ha horizon (t + 1)) (average_field_step P sigma i 1 ha t ht) hfpos E
    have hm : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
    have hden : (3 : ℝ) ^ k / ((mu : ℕ) * fraction i 1 P) ≤ (3 : ℝ) ^ k / ((mu : ℕ) * fmin) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hm hfmin) (mul_le_mul_of_nonneg_left hf hm.le)
    simp only [SparseNoise.noise, if_pos ht]
    apply hb.trans
    by_cases hc : channel i 1 P E
    · simp only [if_pos hc, mul_one]
      linarith
    · simp only [if_neg hc, mul_zero, zero_add]
      have hnon : (0 : ℝ) ≤ 3 ^ k / ((mu : ℕ) * fmin) := by positivity
      linarith
  · simp only [SparseNoise.noise, if_neg ht, abs_zero]
    positivity

end
end Lax343628Proofs.NoiseSquares

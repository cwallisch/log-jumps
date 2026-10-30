import Lax343628Proofs.ChannelNoise

namespace Lax343628Proofs.EmpiricalSampling

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.FiniteProduct Lax343628Proofs.ChannelNoise
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α]

def samples (p : PMF α) (r : ℕ) : PMF (Fin r → α) := distribution (fun _ ↦ p)

def sampleSum (f : α → ℝ) {r : ℕ} (x : Fin r → α) : ℝ := ∑ j, f (x j)

def sampleMean (f : α → ℝ) {r : ℕ} (x : Fin r → α) : ℝ := sampleSum f x / r

omit [Fintype α] [DecidableEq α] in
lemma sum_cons (f : α → ℝ) {r : ℕ} (a : α) (x : Fin r → α) :
    sampleSum f (Fin.cons a x) = f a + sampleSum f x := by
  simp only [sampleSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

omit [DecidableEq α] in
lemma mean_sampleSum (p : PMF α) (f : α → ℝ) (r : ℕ) :
    mean (samples p r) (sampleSum f) = r * mean p f := by
  induction r with
  | zero =>
    have hz : (sampleSum f : (Fin 0 → α) → ℝ) = fun _ ↦ 0 := by funext x; simp [sampleSum]
    rw [hz, mean_const]
    norm_num
  | succ r ih =>
    unfold samples
    rw [mean_distribution_cons]
    simp_rw [sum_cons, mean_add, mean_const]
    change mean p f + mean (samples p r) (sampleSum f) = _
    rw [ih]
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring

omit [DecidableEq α] in
lemma centered_sum_second (p : PMF α) (f : α → ℝ) (hf : mean p f = 0) (r : ℕ) :
    mean (samples p r) (fun x ↦ sampleSum f x ^ 2) = r * mean p (fun a ↦ f a ^ 2) := by
  induction r with
  | zero => simp [sampleSum, mean_const]
  | succ r ih =>
    unfold samples
    rw [mean_distribution_cons]
    simp_rw [sum_cons]
    have heq (a : α) : (fun x : Fin r → α ↦ (f a + sampleSum f x) ^ 2) =
        (fun x ↦ (f a ^ 2 + (2 * f a) * sampleSum f x) + sampleSum f x ^ 2) := by
      funext x; ring
    simp_rw [heq, mean_add, mean_const, mean_mul]
    change (mean p (fun a ↦ f a ^ 2) + mean p (fun a ↦ (2 * f a) * mean (samples p r) (sampleSum f))) +
      mean (samples p r) (fun x ↦ sampleSum f x ^ 2) = _
    rw [mean_sampleSum, hf, mul_zero, ih]
    simp only [mul_zero, mean_const, add_zero]
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring

lemma mean_mul_right {β : Type*} [Fintype β] (p : PMF β) (f : β → ℝ) (c : ℝ) :
    mean p (fun x ↦ f x * c) = mean p f * c := by
  have heq : (fun x ↦ f x * c) = (fun x ↦ c * f x) := by funext x; ring
  rw [heq, mean_mul, mul_comm]

omit [DecidableEq α] in
lemma average_second (p : PMF α) (f : α → ℝ) {r : ℕ} (hr : 1 ≤ r) :
    mean (samples p r) (fun x ↦ (sampleMean f x - mean p f) ^ 2) =
      mean p (fun a ↦ centered p f a ^ 2) / r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hpoint (x : Fin r → α) : sampleMean f x - mean p f = sampleSum (centered p f) x / r := by
    unfold sampleMean sampleSum centered
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [hpoint, div_pow]
  have heq : (fun x : Fin r → α ↦ sampleSum (centered p f) x ^ 2 / (r : ℝ) ^ 2) =
      (fun x ↦ sampleSum (centered p f) x ^ 2 * ((r : ℝ) ^ 2)⁻¹) := by funext x; ring
  rw [heq, mean_mul_right, centered_sum_second p _ (mean_centered p f) r]
  field_simp

omit [DecidableEq α] in
lemma variance_range (p : PMF α) (f : α → ℝ) (M : ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    mean p (fun x ↦ centered p f x ^ 2) ≤ M ^ 2 / 4 := by
  have ht := mean_mono p (fun x ↦ show f x ^ 2 ≤ M * f x by nlinarith [hf x])
  rw [mean_mul] at ht
  rw [variance_identity]
  nlinarith [sq_nonneg (mean p f - M / 2)]

lemma mean_abs_sq {β : Type*} [Fintype β] (p : PMF β) (f : β → ℝ) :
    (mean p (fun x ↦ |f x|)) ^ 2 ≤ mean p (fun x ↦ f x ^ 2) := by
  have ht := mean_nonneg p (fun x ↦ sq_nonneg (centered p (fun y ↦ |f y|) x))
  rw [variance_identity] at ht
  simp only [sq_abs] at ht
  linarith

omit [DecidableEq α] in
lemma sample_error (p : PMF α) (f : α → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) {r : ℕ} (hr : 1 ≤ r) :
    mean (samples p r) (fun x ↦ |sampleMean f x - mean p f|) ≤ M / (2 * Real.sqrt r) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrR
  have hvar := div_le_div_of_nonneg_right (variance_range p f M hf) hrR.le
  have hcs := mean_abs_sq (samples p r) (fun x ↦ sampleMean f x - mean p f)
  rw [average_second p f hr] at hcs
  have hsq : (M / (2 * Real.sqrt (r : ℝ))) ^ 2 = (M ^ 2 / 4) / r := by
    rw [div_pow, mul_pow, Real.sq_sqrt hrR.le]
    ring
  have hrhs : 0 ≤ M / (2 * Real.sqrt (r : ℝ)) := by positivity
  nlinarith

end
end Lax343628Proofs.EmpiricalSampling

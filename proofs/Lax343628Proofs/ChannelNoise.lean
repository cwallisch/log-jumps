import Lax343628Proofs.FiniteComparison

namespace Lax343628Proofs.ChannelNoise

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α]

def centered (p : PMF α) (f : α → ℝ) (x : α) : ℝ := f x - mean p f

lemma mean_centered (p : PMF α) (f : α → ℝ) : mean p (centered p f) = 0 := by
  unfold centered
  rw [mean_sub, mean_const, sub_self]

lemma variance_identity (p : PMF α) (f : α → ℝ) :
    mean p (fun x ↦ centered p f x ^ 2) = mean p (fun x ↦ f x ^ 2) - (mean p f) ^ 2 := by
  have heq : (fun x ↦ centered p f x ^ 2) =
      (fun x ↦ (f x ^ 2 - (2 * mean p f) * f x) + (mean p f) ^ 2) := by
    funext x
    unfold centered
    ring
  rw [heq, mean_add, mean_sub, mean_mul, mean_const]
  ring

lemma mean_abs_channel (p : PMF α) (A : Set α) (f : α → ℝ) (B q : ℝ)
    (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hz : ∀ x, x ∉ A → f x = 0)
    (hp : mean p (fun x ↦ if x ∈ A then 1 else 0) ≤ q) :
    mean p (fun x ↦ |f x|) ≤ B * q := by
  have hh := mean_mono p (fun x ↦
    show |f x| ≤ B * (if x ∈ A then 1 else 0) by
      by_cases hx : x ∈ A
      · simpa only [if_pos hx, mul_one] using hb x
      · simp [hx, hz x hx])
  rw [mean_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hp hB)

lemma second_moment_channel (p : PMF α) (A : Set α) (f : α → ℝ) (B q : ℝ)
    (_hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hz : ∀ x, x ∉ A → f x = 0)
    (hp : mean p (fun x ↦ if x ∈ A then 1 else 0) ≤ q) :
    mean p (fun x ↦ f x ^ 2) ≤ B ^ 2 * q := by
  have hh := mean_mono p (fun x ↦
    show f x ^ 2 ≤ B ^ 2 * (if x ∈ A then 1 else 0) by
      by_cases hx : x ∈ A
      · rw [if_pos hx, mul_one]
        have ht := abs_le.mp (hb x)
        nlinarith
      · simp [hx, hz x hx])
  rw [mean_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hp (sq_nonneg B))

lemma centered_channel_bound (p : PMF α) (A : Set α) (f : α → ℝ) (B q : ℝ)
    (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hz : ∀ x, x ∉ A → f x = 0)
    (hp : mean p (fun x ↦ if x ∈ A then 1 else 0) ≤ q) (x : α) :
    |centered p f x| ≤ B * ((if x ∈ A then 1 else 0) + q) := by
  have hm : |mean p f| ≤ B * q := (abs_mean_le p f).trans (mean_abs_channel p A f B q hB hb hz hp)
  have hx : |f x| ≤ B * (if x ∈ A then 1 else 0) := by
    by_cases hxA : x ∈ A
    · simpa only [if_pos hxA, mul_one] using hb x
    · simp [hxA, hz x hxA]
  have ht := abs_sub (f x) (mean p f)
  unfold centered
  nlinarith

lemma centered_variance_bound (p : PMF α) (A : Set α) (f : α → ℝ) (B q : ℝ)
    (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hz : ∀ x, x ∉ A → f x = 0)
    (hp : mean p (fun x ↦ if x ∈ A then 1 else 0) ≤ q) :
    mean p (fun x ↦ centered p f x ^ 2) ≤ B ^ 2 * q := by
  rw [variance_identity]
  have ht := second_moment_channel p A f B q hB hb hz hp
  nlinarith [sq_nonneg (mean p f)]

end
end Lax343628Proofs.ChannelNoise

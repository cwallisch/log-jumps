import Lax343628Proofs.ReproductiveValues
import Lax343628Proofs.Barrier

namespace Lax343628Proofs.ReproductiveLocality

open Lax343628Proofs.ReproductiveValues
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α]

lemma value_congr_interval (A B : ℕ → Kernel α) (a : ℝ) (s H : ℕ)
    (hAB : ∀ t, s ≤ t → t < s + H → A t = B t) : value A a s H = value B a s H := by
  induction H generalizing s with
  | zero => rfl
  | succ H ih =>
    have hs := hAB s (by omega) (by omega)
    have ht : value A a (s + 1) H = value B a (s + 1) H :=
      ih (s + 1) (fun t hlo hhi ↦ hAB t (by omega) (by omega))
    simp only [value, hs, ht]

lemma tail_difference (A : ℕ → Kernel α) {a : ℝ} (ha : 0 ≤ a) (s u R : ℕ)
    (M : ℝ) (hM : 0 ≤ M) (hterminal : ∀ x, value A a (s + u) R x ≤ M) (x : α) :
    0 ≤ value A a s (u + R) x - value A a (s + u) R x ∧
      value A a s (u + R) x - value A a (s + u) R x ≤ ((1 + a) ^ u - 1) * M := by
  induction u generalizing s x with
  | zero => simp
  | succ u ih =>
    have hterminal' : ∀ y, value A a ((s + 1) + u) R y ≤ M := by
      simpa only [show s + 1 + u = s + (u + 1) by omega] using hterminal
    have hh := ih (s + 1) hterminal' x
    have hv : ∀ y, value A a (s + 1) (u + R) y ≤ (1 + a) ^ u * M := by
      intro y
      have hi := (ih (s + 1) hterminal' y).2
      nlinarith [hterminal' y]
    have haM := action_le (A s) (value A a (s + 1) (u + R)) ((1 + a) ^ u * M)
      (mul_nonneg (pow_nonneg (by linarith) _) hM) hv x
    have ha0 := action_nonneg (A s) (value A a (s + 1) (u + R)) (value_nonneg A ha (s + 1) (u + R)) x
    rw [show u + 1 + R = (u + R) + 1 by omega]
    change 0 ≤ (value A a (s + 1) (u + R) x + a * action (A s) (value A a (s + 1) (u + R)) x) -
        value A a (s + (u + 1)) R x ∧ _
    rw [show s + (u + 1) = (s + 1) + u by omega]
    constructor
    · nlinarith [mul_nonneg ha ha0]
    · rw [value, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left haM ha]

lemma pow_small_growth {a : ℝ} (ha : 0 ≤ a) (u : ℕ) (hu : (u : ℝ) * a ≤ 1) :
    (1 + a) ^ u - 1 ≤ 2 * u * a := by
  have he : 1 + a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + a) he u
  rw [← Real.exp_nat_mul] at hp
  have hnonneg : 0 ≤ (u : ℝ) * a := mul_nonneg (Nat.cast_nonneg u) ha
  have hq := Lax343628Proofs.Barrier.exp_quadratic (show |(u : ℝ) * a| ≤ 1 by
    rw [abs_of_nonneg hnonneg]; exact hu)
  have hs : ((u : ℝ) * a) ^ 2 ≤ (u : ℝ) * a := by nlinarith
  nlinarith

lemma tail_small_difference (A : ℕ → Kernel α) {a : ℝ} (ha : 0 ≤ a) (s u R : ℕ)
    (hu : (u : ℝ) * a ≤ 1) (M : ℝ) (hM : 0 ≤ M)
    (hterminal : ∀ x, value A a (s + u) R x ≤ M) (x : α) :
    0 ≤ value A a s (u + R) x - value A a (s + u) R x ∧
      value A a s (u + R) x - value A a (s + u) R x ≤ 2 * u * a * M := by
  have ht := tail_difference A ha s u R M hM hterminal x
  exact ⟨ht.1, ht.2.trans (mul_le_mul_of_nonneg_right (pow_small_growth ha u hu) hM)⟩

end
end Lax343628Proofs.ReproductiveLocality

import Lax343628Proofs.PhysicalShadow
import Lax343628Proofs.ReproductiveComparison

namespace Lax343628Proofs.MixedShadow

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.ColumnKernels Lax343628Proofs.PhysicalShadow
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {i : Fin n}

lemma mean_mul_right {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    mean p (fun x ↦ f x * c) = mean p f * c := by
  simp_rw [mul_comm (f _) c]
  rw [mean_mul, mul_comm]

lemma bonus_mean_lower (partners : PMF (BitString n))
    (hp : ∀ u ∈ partners.support, (zeros u).card = r + 1)
    (y : ColumnClass n (r + 1) i 0) (omega : ℝ) (hcap : (partners y.val).toReal ≤ 1 - omega) :
    ShadowGaps.delta (r + 1) * omega ≤ mean partners (bonus y) := by
  have hdel := (ShadowGaps.delta_pos (show 1 ≤ r + 1 by omega)).le
  have ht : mean partners (fun u ↦ ShadowGaps.delta (r + 1) * (1 - if u = y.val then 1 else 0)) ≤
      mean partners (bonus y) := by
    apply mean_mono_on_support
    intro u hu
    rw [bonus_eq y u (hp u hu)]
    split_ifs <;> simp
  rw [mean_mul, mean_sub, mean_const, mean_pick, mul_one] at ht
  have hbound := mul_le_mul_of_nonneg_left hcap hdel
  nlinarith

lemma birth_comparison (hn : 4 * (r + 1) ≤ n) (partners : PMF (BitString n))
    (hp : ∀ u ∈ partners.support, (zeros u).card = r + 1)
    (omega : ℝ) (hcap : ∀ y : ColumnClass n (r + 1) i 0, (partners y.val).toReal ≤ 1 - omega) :
    ReproductiveComparison.BirthComparison (Related (r := r) (i := i))
      (mixedKernel partners) (mixedKernel partners)
      (ShadowGaps.delta (r + 1) * omega) (128 * (r + 1 : ℝ) ^ 2 / n) := by
  intro m g c hc hm hg hdom L U V hL hmin hM hG x y hxy
  rw [mixed_action, mixed_action]
  have hb := bonus_mean_lower partners hp y omega (hcap y)
  have ht := mean_mono_on_support partners (fun u hu ↦ action_unconditional hn x y u (hp u hu) hxy
    m g c L U V hc hL hmin (fun z ↦ ⟨hm z, hM z⟩) (fun z ↦ ⟨hg z, hG z⟩) hdom)
  have heq : mean partners (fun u ↦ c * (action u g y + bonus y u * L -
        128 * (r + 1 : ℝ) ^ 2 / n * V) - 128 * (r + 1 : ℝ) ^ 2 / n * U) =
      c * (mean partners (fun u ↦ action u g y) + mean partners (bonus y) * L -
        128 * (r + 1 : ℝ) ^ 2 / n * V) - 128 * (r + 1 : ℝ) ^ 2 / n * U := by
    rw [mean_sub, mean_mul, mean_sub, mean_add, mean_mul_right, mean_const, mean_const]
  rw [heq] at ht
  have hscaled := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hL) hc
  linarith

end
end Lax343628Proofs.MixedShadow

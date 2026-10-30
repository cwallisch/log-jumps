import Lax343628Proofs.CrossoverCount
import Lax343628Proofs.ElementaryBounds

namespace Lax343628Proofs.MutationLower

open Lax343628.Algorithm Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.Sampling Lax343628Proofs.PhysicalOffspring
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

lemma mean_lower (x y : BitString n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (f : BitString n → ℝ) (hf : ∀ z, 0 ≤ f z) :
    mean (pairMutation x y 0) f * (1 - p) ^ n ≤ mean (pairMutation x y p) f := by
  let q := (PMF.uniformOfFintype (BitString n)).map (crossover x y)
  have hkernel (z : BitString n) : q z * ENNReal.ofReal (1 - p) ^ n ≤ pairMutation x y p z := by
    have hh := mutation_preserves_mass p hp q z
    simpa only [q, PMF.map, PMF.bind_bind, PMF.pure_bind, pairMutation, Function.comp_apply] using hh
  rw [CrossoverCount.no_mutation]
  change mean q f * (1 - p) ^ n ≤ _
  unfold mean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z _
  have hh := ENNReal.toReal_mono ((pairMutation x y p).apply_ne_top z) (hkernel z)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)] at hh
  calc
    _ = ((q z).toReal * (1 - p) ^ n) * f z := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hh (hf z)

lemma standard (hn : 2 ≤ n) (x y : BitString n) (f : BitString n → ℝ) (hf : ∀ z, 0 ≤ f z) :
    mean (pairMutation x y 0) f / 8 ≤ mean (pairMutation x y (1 / n)) f := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1 :=
    ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  have hh := mul_le_mul_of_nonneg_left (ElementaryBounds.no_mutation_lower n hn)
    (mean_nonneg (pairMutation x y 0) hf)
  have hm := mean_lower x y (1 / n) hp f hf
  have hh' : mean (pairMutation x y 0) f / 8 ≤ mean (pairMutation x y 0) f * (1 - 1 / (n : ℝ)) ^ n := by
    simpa only [div_eq_mul_inv, one_mul] using hh
  exact hh'.trans hm

end
end Lax343628Proofs.MutationLower

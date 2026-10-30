import Lax343628Proofs.FiniteDrift
import Lax343628Proofs.FiniteProduct

namespace Lax343628Proofs.FiniteComparison

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteProduct
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} [Fintype α] [Fintype β]

lemma mean_map (p : PMF α) (g : α → β) (f : β → ℝ) :
    mean (p.map g) f = mean p (fun x ↦ f (g x)) := by
  rw [← PMF.bind_pure_comp, mean_bind]
  simp only [Function.comp_apply, mean_pure]

lemma injective_sum_le_indicator (p : PMF β) (e : α → β) (he : Function.Injective e)
    (P : β → Prop) [DecidablePred P] (hP : ∀ a, P (e a)) :
    (∑ a, (p (e a)).toReal) ≤ mean p (fun b ↦ if P b then 1 else 0) := by
  classical
  have himage : (∑ a, (p (e a)).toReal) =
      ∑ b ∈ Finset.univ.image e, (p b).toReal := by
    rw [Finset.sum_image (fun a _ b _ h ↦ he h)]
  rw [himage]
  unfold mean
  calc
    _ = ∑ b ∈ Finset.univ.image e, (p b).toReal * (if P b then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
      simp only [if_pos (hP a), mul_one]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ ↦ by split_ifs <;> positivity)

lemma abs_mean_le (p : PMF α) (f : α → ℝ) :
    |mean p f| ≤ mean p (fun x ↦ |f x|) := by
  unfold mean
  calc
    _ ≤ ∑ x, |(p x).toReal * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]

lemma mean_abs_le (p : PMF α) (f : α → ℝ) (M : ℝ) (h : ∀ x, |f x| ≤ M) :
    |mean p f| ≤ M := by
  exact (abs_mean_le p f).trans ((mean_mono p h).trans_eq (mean_const p M))

lemma exceptional_comparison (p : PMF α) (f g : α → ℝ) (A : Set α) (M : ℝ)
    (heq : ∀ x ∉ A, f x = g x) (hbound : ∀ x ∈ A, |f x - g x| ≤ M) :
    |mean p f - mean p g| ≤ M * (p.toOuterMeasure A).toReal := by
  rw [← mean_sub]
  apply (abs_mean_le p _).trans
  have hpoint : ∀ x, |f x - g x| ≤ M * (if x ∈ A then 1 else 0) := by
    intro x
    by_cases hx : x ∈ A
    · simpa only [if_pos hx, mul_one] using hbound x hx
    · simp only [heq x hx, sub_self, abs_zero, if_neg hx, mul_zero, le_refl]
  exact (mean_mono p hpoint).trans_eq (by rw [mean_mul, mean_indicator])

omit [Fintype α] in
lemma weighted_sum_error (s : Finset α) (a b f : α → ℝ) (M : ℝ)
    (hf : ∀ x ∈ s, |f x| ≤ M) :
    |(∑ x ∈ s, a x * f x) - ∑ x ∈ s, b x * f x| ≤
      M * ∑ x ∈ s, |a x - b x| := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    _ ≤ ∑ x ∈ s, |a x * f x - b x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      rw [← sub_mul, abs_mul, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hf x hx) (abs_nonneg _)

lemma mean_distribution_cons {n : ℕ} {γ : Fin (n + 1) → Type*}
    [∀ i, Fintype (γ i)] (p : ∀ i, PMF (γ i)) (f : (∀ i, γ i) → ℝ) :
    mean (distribution p) f = mean (p 0) (fun a ↦
      mean (distribution (fun i : Fin n ↦ p i.succ)) (fun x ↦ f (Fin.cons a x))) := by
  unfold mean
  simp only [distribution_apply, ENNReal.toReal_prod]
  rw [← Equiv.sum_comp (Fin.consEquiv γ), Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro x _
  dsimp only [Fin.consEquiv, Equiv.coe_fn_mk]
  ring

lemma mean_uniform [Nonempty α] (f : α → ℝ) :
    mean (PMF.uniformOfFintype α) f = (Fintype.card α : ℝ)⁻¹ * ∑ x, f x := by
  unfold mean
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  exact (Finset.mul_sum _ _ _).symm

lemma mean_coin (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (f : Fin 2 → ℝ) :
    mean (Lax343628.Algorithm.coin p) f = p * f 1 + (1 - p) * f 0 := by
  unfold mean
  rw [Fin.sum_univ_two]
  simp only [Lax343628Proofs.Sampling.coin_zero p hp, Lax343628Proofs.Sampling.coin_one p hp,
    ENNReal.toReal_ofReal hp.1, ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)]
  ring

lemma mean_single_lower (p : PMF α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (x : α) :
    (p x).toReal * f x ≤ mean p f :=
  Finset.single_le_sum (fun y _ ↦ mul_nonneg ENNReal.toReal_nonneg (hf y)) (Finset.mem_univ x)

lemma mean_pick [DecidableEq α] (p : PMF α) (a : α) (c : ℝ) :
    mean p (fun x ↦ if x = a then c else 0) = (p a).toReal * c := by
  unfold mean
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true]
  · intro x _ hx
    exact if_neg hx
  · intro h
    exact False.elim (h (Finset.mem_univ a))

end
end Lax343628Proofs.FiniteComparison

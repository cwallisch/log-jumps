import Lax343628Proofs.Sampling
import Lax343628Proofs.BitProduct
import Mathlib.Tactic.FinCases

namespace Lax343628Proofs.PhysicalOffspring

open Lax343628.Algorithm Lax343628Proofs.Sampling
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def pairMutation {n : ℕ} (x y : BitString n) (p : ℝ) : PMF (BitString n) :=
  (PMF.uniformOfFintype (BitString n)).bind fun mask ↦
    (independentBits n p).bind fun mask' ↦ PMF.pure (mutate (crossover x y mask) mask')

lemma pairMutation_self {n : ℕ} (x : BitString n) (p : ℝ) :
    pairMutation x x p = (independentBits n p).map (mutate x) := by
  have hc (mask : BitString n) : crossover x x mask = x := by
    funext j
    simp [Lax343628.Algorithm.crossover]
  simp only [pairMutation, hc, PMF.bind_const]
  rfl

lemma offspring_split {n : ℕ} {μ : ℕ+} (p_c : ℝ) (P : Population n μ) :
    offspring p_c P = (coin p_c).bind (fun b ↦ if b = 1 then
      (PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ))).bind
        (fun uv ↦ pairMutation (P uv.1) (P uv.2) (1 / n))
      else (PMF.uniformOfFintype (Fin (μ : ℕ))).bind
        (fun u ↦ pairMutation (P u) (P u) (1 / n))) := by
  simp only [offspring, parents, Bind.bind, Pure.pure, PMF.bind_bind]
  congr 1
  funext b
  split_ifs
  · simp only [PMF.bind_bind, PMF.pure_bind, pairMutation]
  · simp only [PMF.bind_bind, PMF.pure_bind, pairMutation_self, PMF.map, Function.comp_def]

def siteProbability (x y target : Fin 2) (p : ℝ) : ℝ≥0∞ :=
  if x = y then if target = x then ENNReal.ofReal (1 - p) else ENNReal.ofReal p
  else (2 : ℝ≥0∞)⁻¹

lemma site_probability_sum (x y target : Fin 2) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (∑ b : Fin 2, coin (1 / 2) b *
      (∑ b' : Fin 2, coin p b' *
        (if (if b' = 1 then 1 - (if b = 1 then x else y) else (if b = 1 then x else y)) =
          target then 1 else 0))) = siteProbability x y target p := by
  have hsum : ENNReal.ofReal (1 - p) + ENNReal.ofReal p = 1 := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp.2) hp.1]
    ring_nf
    norm_num
  have hfair : ∀ b : Fin 2, coin (1 / 2) b = (2 : ℝ≥0∞)⁻¹ := by
    intro b
    fin_cases b <;> norm_num [coin, ENNReal.ofReal_div_of_pos]
  simp only [Fin.sum_univ_two, hfair, coin_zero p hp, coin_one p hp]
  fin_cases x <;> fin_cases y <;> fin_cases target <;>
    norm_num [siteProbability] <;>
    first
    | rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    | rw [← mul_add, hsum, mul_one]
    | rw [← mul_add, add_comm (ENNReal.ofReal p), hsum, mul_one]

lemma pairMutation_apply {n : ℕ} (x y target : BitString n) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    pairMutation x y p target = ∏ j, siteProbability (x j) (y j) (target j) p := by
  rw [pairMutation, uniform_bits_eq]
  change ((independentBits n (1 / 2)).bind fun mask ↦
    (independentBits n p).bind fun mask' ↦ PMF.pure (fun j ↦
      if mask' j = 1 then 1 - (if mask j = 1 then x j else y j)
      else (if mask j = 1 then x j else y j))) target = _
  rw [independent_pair_transform_apply (1 / 2) p
    (fun j b b' ↦ if b' = 1 then 1 - (if b = 1 then x j else y j)
      else (if b = 1 then x j else y j)) target]
  apply Finset.prod_congr rfl
  intro j _
  exact site_probability_sum (x j) (y j) (target j) p hp

def siteLaw (x y : Fin 2) (p : ℝ) : PMF (Fin 2) :=
  (coin (1 / 2)).bind fun b ↦ (coin p).bind fun b' ↦ PMF.pure
    (if b' = 1 then 1 - (if b = 1 then x else y) else (if b = 1 then x else y))

lemma siteLaw_apply (x y target : Fin 2) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    siteLaw x y p target = siteProbability x y target p := by
  have hpure : ∀ a b : Fin 2, PMF.pure a b = if a = b then 1 else 0 := by
    intro a b
    by_cases hab : a = b
    · subst b
      simp only [PMF.pure_apply_self, ite_true]
    · rw [PMF.pure_apply_of_ne a b (Ne.symm hab), if_neg hab]
  unfold siteLaw
  simp_rw [PMF.bind_apply, tsum_fintype, hpure]
  exact site_probability_sum x y target p hp

lemma pairMutation_eq_product {n : ℕ} (x y : BitString n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    pairMutation x y p = Lax343628Proofs.BitProduct.product (Fin n) (fun j ↦ siteLaw (x j) (y j) p) := by
  ext target
  rw [pairMutation_apply x y target p hp, Lax343628Proofs.BitProduct.product_apply]
  apply Finset.prod_congr rfl
  intro j _
  rw [siteLaw_apply (x j) (y j) (target j) p hp]

lemma siteLaw_common (x : Fin 2) (p : ℝ) :
    siteLaw x x p = (coin p).map (fun b ↦ if b = 1 then 1 - x else x) := by
  simp [siteLaw, PMF.map, Function.comp_def]

lemma siteLaw_different (x y : Fin 2) (hxy : x ≠ y) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    siteLaw x y p = coin (1 / 2) := by
  ext target
  rw [siteLaw_apply x y target p hp]
  simp only [siteProbability, if_neg hxy]
  fin_cases target <;> norm_num [coin, ENNReal.ofReal_div_of_pos]

end
end Lax343628Proofs.PhysicalOffspring

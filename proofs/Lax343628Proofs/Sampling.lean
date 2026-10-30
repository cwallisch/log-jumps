import Lax343628.Algorithm
import Mathlib.Tactic.NormNum

namespace Lax343628Proofs.Sampling

open Lax343628.Algorithm
open scoped ENNReal Classical BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

def parents {n : ℕ} {μ : ℕ+} (p_c : ℝ) (P : Population n μ) : PMF (BitString n) := do
  let b ← coin p_c
  if b = 1 then do
    let (u, v) ← PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ))
    let mask ← PMF.uniformOfFintype (BitString n)
    pure (crossover (P u) (P v) mask)
  else do
    let u ← PMF.uniformOfFintype (Fin (μ : ℕ))
    pure (P u)

def offspring {n : ℕ} {μ : ℕ+} (p_c : ℝ) (P : Population n μ) : PMF (BitString n) := do
  let y ← parents p_c P
  let mask ← independentBits n (1 / (n : ℝ))
  pure (mutate y mask)

def insert {n : ℕ} {μ : ℕ+} (fitness : BitString n → ℝ) (P : Population n μ)
    (z : BitString n) : PMF (Population n μ) := do
  let d ← deletionIndex fitness (Fin.lastCases z P)
  pure (if h : d.val < (μ : ℕ) then Function.update P ⟨d.val, h⟩ z else P)

lemma step_eq {n : ℕ} {μ : ℕ+} (fitness : BitString n → ℝ) (p_c : ℝ)
    (P : Population n μ) : step fitness p_c P =
      (offspring p_c P).bind (fun z ↦ insert fitness P z) := by
  simp only [step, offspring, parents, insert, Bind.bind, Pure.pure, PMF.bind_bind,
    PMF.pure_bind]
  congr 1
  funext b
  split_ifs <;> simp only [PMF.bind_bind, PMF.pure_bind]

@[simp] lemma coin_one (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : coin p 1 = ENNReal.ofReal p := by
  simp [coin, hp]

@[simp] lemma coin_zero (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    coin p 0 = ENNReal.ofReal (1 - p) := by
  simp [coin, hp]

lemma independentBits_apply (n : ℕ) (p : ℝ) (mask : BitString n) :
    independentBits n p mask = ∏ j, coin p (mask j) := rfl

lemma uniform_bits_eq (n : ℕ) :
    PMF.uniformOfFintype (BitString n) = independentBits n (1 / 2) := by
  ext mask
  rw [PMF.uniformOfFintype_apply, independentBits_apply]
  have hc : ∀ j : Fin n, coin (1 / 2) (mask j) = (2 : ℝ≥0∞)⁻¹ := by
    intro j
    have h := (mask j).isLt
    have hcases : mask j = 0 ∨ mask j = 1 := by omega
    rcases hcases with h | h <;> rw [h] <;> norm_num [coin, ENNReal.ofReal_div_of_pos]
  simp only [Fintype.card_fun, Fintype.card_fin, hc, Finset.prod_const, Finset.card_univ,
    ENNReal.inv_pow, Nat.cast_pow, Nat.cast_ofNat]

lemma product_indicator {n : ℕ} (p : ℝ) (f : Fin n → Fin 2 → Fin 2)
    (target mask : BitString n) :
    (∏ j, coin p (mask j)) * (if (fun j ↦ f j (mask j)) = target then 1 else 0) =
      ∏ j, coin p (mask j) * (if f j (mask j) = target j then 1 else 0) := by
  by_cases h : (fun j ↦ f j (mask j)) = target
  · have hj : ∀ j, f j (mask j) = target j := congrFun h
    simp only [if_pos h, if_pos (hj _), mul_one]
  · have hj : ∃ j, f j (mask j) ≠ target j := by
      simpa only [funext_iff, not_forall] using h
    obtain ⟨j, hj⟩ := hj
    rw [if_neg h, mul_zero]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj, mul_zero])

lemma independent_transform_apply {n : ℕ} (p : ℝ) (f : Fin n → Fin 2 → Fin 2)
    (target : BitString n) :
    ((independentBits n p).bind fun mask ↦ PMF.pure (fun j ↦ f j (mask j))) target =
      ∏ j, ∑ b : Fin 2, coin p b * (if f j b = target j then 1 else 0) := by
  rw [PMF.bind_apply, tsum_fintype, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro mask _
  rw [independentBits_apply, PMF.pure_apply]
  have h := product_indicator p f target mask
  by_cases heq : (fun j ↦ f j (mask j)) = target
  · have heq' := heq.symm
    simpa only [if_pos heq, if_pos heq'] using h
  · have heq' : target ≠ (fun j ↦ f j (mask j)) := Ne.symm heq
    simpa only [if_neg heq, if_neg heq'] using h

lemma independent_weighted_sum {n : ℕ} (p : ℝ) (f : Fin n → Fin 2 → ℝ≥0∞) :
    (∑ mask : BitString n, independentBits n p mask * ∏ j, f j (mask j)) =
      ∏ j, ∑ b : Fin 2, coin p b * f j b := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro mask _
  rw [independentBits_apply, Finset.prod_mul_distrib]

lemma independent_pair_transform_apply {n : ℕ} (p q : ℝ)
    (f : Fin n → Fin 2 → Fin 2 → Fin 2) (target : BitString n) :
    ((independentBits n p).bind fun mask ↦ (independentBits n q).bind fun mask' ↦
      PMF.pure (fun j ↦ f j (mask j) (mask' j))) target =
      ∏ j, ∑ b : Fin 2, coin p b *
        (∑ b' : Fin 2, coin q b' * (if f j b b' = target j then 1 else 0)) := by
  rw [PMF.bind_apply, tsum_fintype]
  rw [← independent_weighted_sum p (fun j b ↦
    ∑ b' : Fin 2, coin q b' * (if f j b b' = target j then 1 else 0))]
  apply Finset.sum_congr rfl
  intro mask _
  rw [independent_transform_apply q (fun j b' ↦ f j (mask j) b') target]

lemma ones_eq_count {n : ℕ} (x : BitString n) :
    ones x = (Finset.univ.filter (fun j ↦ x j = 1)).card := by
  rw [ones, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  have hc : x j = 0 ∨ x j = 1 := by have h := (x j).isLt; omega
  rcases hc with h | h <;> simp [h]

lemma zeros_eq_count {n : ℕ} (x : BitString n) :
    (Finset.univ.filter (fun j ↦ x j = 0)).card = n - ones x := by
  have hpartition : (Finset.univ.filter (fun j ↦ x j = 0)).card +
      (Finset.univ.filter (fun j ↦ x j = 1)).card = n := by
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.sum_filter,
      Finset.sum_filter, ← Finset.sum_add_distrib]
    calc
      ∑ j : Fin n, ((if x j = 0 then 1 else 0) + (if x j = 1 then 1 else 0)) =
          ∑ _ : Fin n, 1 := by
        apply Finset.sum_congr rfl
        intro j _
        have hc : x j = 0 ∨ x j = 1 := by have h := (x j).isLt; omega
        rcases hc with h | h <;> simp [h]
      _ = n := by simp
  rw [← ones_eq_count] at hpartition
  omega

def zeros {n : ℕ} (x : BitString n) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ x j = 0)

@[simp] lemma mem_zeros {n : ℕ} (x : BitString n) (j : Fin n) :
    j ∈ zeros x ↔ x j = 0 := by simp [zeros]

@[simp] lemma card_zeros {n : ℕ} (x : BitString n) : (zeros x).card = n - ones x :=
  zeros_eq_count x

lemma crossover_optimum {n : ℕ} (x y : BitString n) (hd : Disjoint (zeros x) (zeros y)) :
    ((PMF.uniformOfFintype (BitString n)).bind fun mask ↦
      PMF.pure (crossover x y mask)) (optimum n) =
        (2 : ℝ≥0∞)⁻¹ ^ ((zeros x).card + (zeros y).card) := by
  rw [uniform_bits_eq]
  change ((independentBits n (1 / 2)).bind fun mask ↦
    PMF.pure (fun j ↦ if mask j = 1 then x j else y j)) (optimum n) = _
  rw [independent_transform_apply (1 / 2) (fun j b ↦ if b = 1 then x j else y j)
    (optimum n)]
  have hprod : (∏ j, ∑ b : Fin 2, coin (1 / 2) b *
      (if (if b = 1 then x j else y j) = optimum n j then 1 else 0)) =
      ∏ j : Fin n, if j ∈ zeros x ∪ zeros y then (2 : ℝ≥0∞)⁻¹ else 1 := by
    apply Finset.prod_congr rfl
    intro j _
    have hxy : ¬ (x j = 0 ∧ y j = 0) := by
      intro h
      exact Finset.disjoint_left.mp hd (by simpa using h.1) (by simpa using h.2)
    have hx : x j = 0 ∨ x j = 1 := by have h := (x j).isLt; omega
    have hy : y j = 0 ∨ y j = 1 := by have h := (y j).isLt; omega
    rw [Fin.sum_univ_two]
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      simp only [Finset.mem_union, mem_zeros, hx, hy] at hxy ⊢ <;>
      first | contradiction | norm_num [coin, optimum, ENNReal.ofReal_div_of_pos]
    simpa only [one_div] using ENNReal.add_halves (1 : ℝ≥0∞)
  rw [hprod, Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_union_of_disjoint hd]

lemma bind_apply_lower {α β : Type*} (p : PMF α) (f : α → PMF β) (a : α) (b : β) :
    p a * f a b ≤ (p.bind f) b := by
  rw [PMF.bind_apply]
  exact ENNReal.le_tsum a

lemma no_mutation_probability (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    independentBits n p (fun _ ↦ 0) = ENNReal.ofReal (1 - p) ^ n := by
  simp [independentBits_apply, coin_zero p hp]

lemma mutate_zero {n : ℕ} (x : BitString n) : mutate x (fun _ ↦ 0) = x := by
  funext j
  simp [mutate]

lemma mutation_preserves_mass {n : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (q : PMF (BitString n))
    (x : BitString n) : q x * ENNReal.ofReal (1 - p) ^ n ≤
      (q.bind fun y ↦ (independentBits n p).bind fun mask ↦ PMF.pure (mutate y mask)) x := by
  have hinner := bind_apply_lower (independentBits n p)
    (fun mask ↦ PMF.pure (mutate x mask)) (fun _ ↦ 0) x
  rw [mutate_zero, PMF.pure_apply_self, mul_one, no_mutation_probability n p hp] at hinner
  exact (mul_le_mul' le_rfl hinner).trans (bind_apply_lower q _ x x)

end
end Lax343628Proofs.Sampling

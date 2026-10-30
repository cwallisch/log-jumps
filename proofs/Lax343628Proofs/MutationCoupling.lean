import Lax343628Proofs.FiniteComparison
import Lax343628Proofs.PhysicalOffspring
import Lax343628Proofs.ElementaryBounds

namespace Lax343628Proofs.MutationCoupling

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.BitProduct
open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.PhysicalOffspring
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def hits {n : ℕ} (S : Finset (Fin n)) : Set (BitString n) :=
  {mask | restrictToFin S mask ≠ fun _ ↦ 0}

lemma no_hits {n : ℕ} (S : Finset (Fin n)) (mask : BitString n)
    (h : mask ∉ hits S) (j : Fin n) (hj : j ∈ S) : mask j = 0 := by
  have heq : restrictToFin S mask = fun _ ↦ 0 := by simpa only [hits, Set.mem_ofPred_eq,
    not_not] using h
  have hpoint := congrFun heq (S.equivFin ⟨j, hj⟩)
  simpa only [restrictToFin, Equiv.symm_apply_apply] using hpoint

lemma no_hit_probability {n : ℕ} (S : Finset (Fin n)) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    ((independentBits n p).toOuterMeasure (hits S)ᶜ).toReal = (1 - p) ^ S.card := by
  have heq : (hits S)ᶜ = (restrictToFin S) ⁻¹' {fun _ ↦ 0} := by
    ext mask
    simp [hits]
  rw [heq, ← PMF.toOuterMeasure_map_apply, independentBits_restrict,
    PMF.toOuterMeasure_apply_singleton, independentBits_apply]
  simp only [coin_zero p hp, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)]

lemma hit_probability {n : ℕ} (S : Finset (Fin n)) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    ((independentBits n p).toOuterMeasure (hits S)).toReal ≤ S.card * p := by
  have hsum := event_add_compl (independentBits n p) (hits S)
  have hne (A : Set (BitString n)) : (independentBits n p).toOuterMeasure A ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) (event_le_one _ _)
  have hsumR := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (hne _) (hne _), ENNReal.toReal_one, no_hit_probability S p hp] at hsumR
  have hbern := one_add_mul_le_pow (a := -p) (by linarith [hp.2] : (-2 : ℝ) ≤ -p) S.card
  have hbern' : 1 - (S.card : ℝ) * p ≤ (1 - p) ^ S.card := by
    simpa only [sub_eq_add_neg, mul_neg] using hbern
  linarith

def suppressedMask {n : ℕ} (S : Finset (Fin n)) (mask : BitString n) : BitString n :=
  fun j ↦ if j ∈ S then 0 else mask j

lemma suppressed_eq_of_no_hits {n : ℕ} (S : Finset (Fin n)) (mask : BitString n)
    (h : mask ∉ hits S) : suppressedMask S mask = mask := by
  funext j
  by_cases hj : j ∈ S
  · simp only [suppressedMask, if_pos hj, no_hits S mask h j hj]
  · simp only [suppressedMask, if_neg hj]

lemma suppressed_mutation_comparison {n : ℕ} (S : Finset (Fin n)) (x : BitString n)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (f : BitString n → ℝ) (M : ℝ)
    (hf : ∀ child, |f child| ≤ M) :
    |mean (independentBits n p) (fun mask ↦ f (mutate x mask)) -
      mean (independentBits n p) (fun mask ↦ f (mutate x (suppressedMask S mask)))| ≤
        2 * M * S.card * p := by
  have hM : 0 ≤ M := (abs_nonneg (f x)).trans (hf x)
  have h := exceptional_comparison (independentBits n p)
    (fun mask ↦ f (mutate x mask))
    (fun mask ↦ f (mutate x (suppressedMask S mask))) (hits S) (2 * M)
    (fun mask hm ↦ by rw [suppressed_eq_of_no_hits S mask hm])
    (fun mask _ ↦ (abs_sub _ _).trans (by
      have h1 := hf (mutate x mask)
      have h2 := hf (mutate x (suppressedMask S mask))
      linarith))
  have hb := mul_le_mul_of_nonneg_left (hit_probability S p hp)
    (show 0 ≤ 2 * M by positivity)
  exact h.trans (hb.trans_eq (by ring))

def suppressedPair {n : ℕ} (S : Finset (Fin n)) (x y : BitString n) (p : ℝ) :
    PMF (BitString n) :=
  (PMF.uniformOfFintype (BitString n)).bind fun mask ↦
    (independentBits n p).map fun mask' ↦ mutate (crossover x y mask) (suppressedMask S mask')

lemma pair_suppression_comparison {n : ℕ} (S : Finset (Fin n)) (x y : BitString n)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (f : BitString n → ℝ) (M : ℝ)
    (hf : ∀ child, |f child| ≤ M) :
    |mean (pairMutation x y p) f - mean (suppressedPair S x y p) f| ≤
      2 * M * S.card * p := by
  unfold pairMutation suppressedPair
  rw [mean_bind, mean_bind]
  simp only [mean_bind, mean_pure, mean_map]
  rw [← mean_sub]
  exact (abs_mean_le _ _).trans ((mean_mono _ (fun mask ↦
    suppressed_mutation_comparison S (crossover x y mask) p hp f M hf)).trans_eq
      (mean_const _ _))

def repair {n : ℕ} (S : Finset (Fin n)) (x child : BitString n) : BitString n :=
  fun j ↦ if j ∈ S then x j else child j

lemma repair_mutation {n : ℕ} (S : Finset (Fin n)) (x y mask mask' : BitString n)
    (hS : ∀ j ∈ S, x j = y j) :
    repair S x (mutate (crossover x y mask) mask') =
      mutate (crossover x y mask) (suppressedMask S mask') := by
  funext j
  by_cases hj : j ∈ S
  · simp [repair, suppressedMask, mutate, crossover, hj, hS j hj]
  · simp [repair, suppressedMask, mutate, hj]

lemma suppressedPair_eq_repair {n : ℕ} (S : Finset (Fin n)) (x y : BitString n)
    (p : ℝ) (hS : ∀ j ∈ S, x j = y j) :
    suppressedPair S x y p = (pairMutation x y p).map (repair S x) := by
  simp only [pairMutation, PMF.map_bind, PMF.pure_map, repair_mutation S x y _ _ hS]
  rfl

lemma suppressed_product {n : ℕ} (S : Finset (Fin n)) (x y : BitString n)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hS : ∀ j ∈ S, x j = y j) :
    suppressedPair S x y p = product (Fin n)
      (fun j ↦ if j ∈ S then PMF.pure (x j) else siteLaw (x j) (y j) p) := by
  rw [suppressedPair_eq_repair S x y p hS, pairMutation_eq_product x y p hp]
  have h := map_product (Fin n) (fun j ↦ siteLaw (x j) (y j) p)
    (fun j b ↦ if j ∈ S then x j else b)
  have hfamily : (fun j : Fin n ↦ (siteLaw (x j) (y j) p).map
      (fun b ↦ if j ∈ S then x j else b)) =
      (fun j ↦ if j ∈ S then PMF.pure (x j) else siteLaw (x j) (y j) p) := by
    funext j
    by_cases hj : j ∈ S
    · simp only [if_pos hj]
      exact PMF.map_const _ _
    · simp only [if_neg hj]
      exact PMF.map_id _
  rw [hfamily] at h
  exact h

end
end Lax343628Proofs.MutationCoupling

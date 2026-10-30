import Lax343628Proofs.PairCloneLower
import Lax343628Proofs.SeedMutation

namespace Lax343628Proofs.SwapMutation

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.NamedBirth Lax343628Proofs.SeedGeometry
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

def swapZero (x : BitString n) (i g : Fin n) : BitString n :=
  fromZeros (insert g ((zeros x).erase i))

lemma swap_zeros (x : BitString n) (i g : Fin n) :
    zeros (swapZero x i g) = insert g ((zeros x).erase i) := zeros_fromZeros _

lemma swap_card (x : BitString n) (hx : (zeros x).card = k) (i g : Fin n)
    (hi : i ∈ zeros x) (hg : g ∉ zeros x) : (zeros (swapZero x i g)).card = k := by
  rw [swap_zeros, Finset.card_insert_of_notMem (fun hh ↦ hg (Finset.mem_of_mem_erase hh)),
    Finset.card_erase_of_mem hi, hx]
  have hk : 0 < k := hx ▸ Finset.card_pos.mpr ⟨i, hi⟩
  omega

lemma swap_family (C : Finset (Fin n)) (x : BitString n) (i g : Fin n)
    (hC : ordinary C x) (hi : i ∈ C) (hg : g ∉ zeros x) : family C i (swapZero x i g) := by
  constructor
  · rw [swap_zeros]
    intro j hj
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hj).1, hC (Finset.mem_of_mem_erase hj)⟩)
  · have hgi : g ≠ i := fun hh ↦ hg (hh ▸ hC hi)
    simp only [swapZero, fromZeros, Finset.mem_insert, Finset.notMem_erase,
      or_false, if_neg (Ne.symm hgi)]

lemma swap_injective (x : BitString n) (i : Fin n) :
    Set.InjOn (swapZero x i) {g | g ∉ zeros x} := by
  intro g hg h hh heq
  have hz := congrArg zeros heq
  rw [swap_zeros, swap_zeros] at hz
  have hmem : g ∈ insert h ((zeros x).erase i) := hz ▸ Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hmem with he | he
  · exact he
  · exact False.elim (hg (Finset.mem_of_mem_erase he))

lemma swap_diff (x : BitString n) (i g : Fin n) (hi : i ∈ zeros x) (hg : g ∉ zeros x) :
    Finset.univ.filter (fun j ↦ swapZero x i g j ≠ x j) = {i, g} := by
  have hgi : g ≠ i := fun hh ↦ hg (hh ▸ hi)
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  by_cases hji : j = i
  · subst j
    have hxi := (mem_zeros x i).mp hi
    simp [swapZero, fromZeros, hxi, Ne.symm hgi]
  · by_cases hjg : j = g
    · subst j
      have hxg : x g = 1 := by
        have hne : x g ≠ 0 := fun hh ↦ hg ((mem_zeros x g).mpr hh)
        have hb := (x g).isLt
        omega
      simp [swapZero, fromZeros, hxg]
    · have heq : swapZero x i g j = x j := by
        simp only [swapZero, fromZeros, Finset.mem_insert, hjg, false_or,
          Finset.mem_erase]
        by_cases hj : j ∈ zeros x
        · simp [hji, hj, (mem_zeros x j).mp hj]
        · have hxj : x j = 1 := by
            have hne : x j ≠ 0 := fun hh ↦ hj ((mem_zeros x j).mpr hh)
            have hb := (x j).isLt
            omega
          simp [hji, hj, hxj]
      simp only [heq, ne_eq, not_true_eq_false, hji, hjg, or_self]

lemma swap_probability (x : BitString n) (i g : Fin n) (hi : i ∈ zeros x) (hg : g ∉ zeros x)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (pairMutation x x p (swapZero x i g)).toReal = p ^ 2 * (1 - p) ^ (n - 2) := by
  rw [pairMutation_apply x x _ p hp, ENNReal.toReal_prod]
  have heq (j : Fin n) : (siteProbability (x j) (x j) (swapZero x i g j) p).toReal =
      if swapZero x i g j ≠ x j then p else 1 - p := by
    simp only [siteProbability, if_true]
    split_ifs <;> simp_all only [ENNReal.toReal_ofReal hp.1,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2), ne_eq, not_false_eq_true, not_true_eq_false]
  simp_rw [heq]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, swap_diff x i g hi hg]
  have hgi : i ≠ g := fun hh ↦ hg (hh ▸ hi)
  have hc : (Finset.univ.filter (fun j ↦ ¬swapZero x i g j ≠ x j)).card = n - 2 := by
    have hh := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun j ↦ swapZero x i g j ≠ x j)
    rw [swap_diff x i g hi hg, Finset.card_pair hgi, Finset.card_univ, Fintype.card_fin] at hh
    omega
  rw [Finset.card_pair hgi, hc]

end
end Lax343628Proofs.SwapMutation

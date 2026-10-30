import Lax343628Proofs.MutationLower
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Lax343628Proofs.OneBitMutation

open Lax343628.Algorithm Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.Sampling Lax343628Proofs.PhysicalOffspring
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def flip (x : BitString n) (j : Fin n) : BitString n := Function.update x j (1 - x j)

lemma flip_ne (b : Fin 2) : 1 - b ≠ b := by fin_cases b <;> norm_num

lemma injective (x : BitString n) : Function.Injective (flip x) := by
  intro i j hh
  by_contra hij
  have hp := congrFun hh i
  simp only [flip, Function.update_self, Function.update_of_ne hij] at hp
  exact flip_ne (x i) hp

lemma ones_up (x : BitString n) (j : Fin n) (hj : x j = 0) : ones (flip x j) = ones x + 1 := by
  have hcast : (fun v ↦ ((flip x j v).val : ℕ)) = Function.update (fun v ↦ (x v).val) j 1 := by
    funext v
    by_cases hv : v = j
    · subst v
      simp [flip, hj]
    · simp [flip, hv]
  unfold ones
  rw [hcast, Finset.sum_update_of_mem (Finset.mem_univ j)]
  simp only [Finset.sdiff_singleton_eq_erase]
  have hh := Finset.add_sum_erase (Finset.univ : Finset (Fin n)) (fun v ↦ (x v).val) (Finset.mem_univ j)
  simp only [hj, Fin.val_zero, zero_add] at hh
  omega

lemma probability (x : BitString n) (j : Fin n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (pairMutation x x p (flip x j)).toReal = p * (1 - p) ^ (n - 1) := by
  rw [pairMutation_apply x x _ p hp, ENNReal.toReal_prod]
  have hsite (v : Fin n) : (siteProbability (x v) (x v) (flip x j v) p).toReal =
      Function.update (fun _ : Fin n ↦ 1 - p) j p v := by
    by_cases hv : v = j
    · subst v
      simp only [siteProbability, if_true, flip, Function.update_self,
        if_neg (flip_ne (x j)), ENNReal.toReal_ofReal hp.1]
    · simp only [siteProbability, if_true, flip, Function.update_of_ne hv,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)]
  simp_rw [hsite]
  rw [Finset.prod_update_of_mem (Finset.mem_univ j), Finset.prod_const,
    Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]

lemma standard (hn : 2 ≤ n) (x : BitString n) (j : Fin n) :
    1 / (8 * (n : ℝ)) ≤ (pairMutation x x (1 / n) (flip x j)).toReal := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1 :=
    ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  rw [probability x j _ hp]
  have hpow := (ElementaryBounds.no_mutation_lower n hn).trans
    (pow_le_pow_of_le_one (sub_nonneg.mpr hp.2) (by linarith : (1 : ℝ) - 1 / n ≤ 1) (Nat.sub_le n 1))
  have hh := mul_le_mul_of_nonneg_left hpow hp.1
  have heq : 1 / (8 * (n : ℝ)) = (1 / (n : ℝ)) * (1 / 8) := by ring
  rw [heq]
  exact hh

lemma ordinary (hn : 2 ≤ n) (i b : ℕ) (hib : i < b) (x : BitString n) (hx : ones x = i) :
    ((n - i : ℕ) : ℝ) / (8 * n) ≤
      mean (pairMutation x x (1 / n)) (fun z ↦ if i < ones z ∧ ones z ≤ b then 1 else 0) := by
  let G := {j : Fin n // j ∈ zeros x}
  let e : G → BitString n := fun j ↦ flip x j
  have he : Function.Injective e := fun j k hh ↦ Subtype.ext (injective x hh)
  have hevent (j : G) : i < ones (e j) ∧ ones (e j) ≤ b := by
    have hh := ones_up x j ((mem_zeros x j).mp j.property)
    dsimp only [e]
    omega
  have hsum := injective_sum_le_indicator (pairMutation x x (1 / n)) e he
    (fun z ↦ i < ones z ∧ ones z ≤ b) hevent
  have hlower := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ standard hn x (j : G))
  have hcard : Fintype.card G = n - i := by
    rw [Fintype.card_coe, card_zeros, hx]
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] at hlower
  have hlo : ((n - i : ℕ) : ℝ) / (8 * n) ≤ ∑ j : G, (pairMutation x x (1 / n) (e j)).toReal := by
    simpa only [div_eq_mul_inv, mul_one, one_mul, e] using hlower
  exact hlo.trans hsum

lemma strict (hn : 2 ≤ n) (i : ℕ) (hin : i < n) (x : BitString n) (hx : ones x = i) :
    ((n - i : ℕ) : ℝ) / (8 * n) ≤ mean (pairMutation x x (1 / n)) (fun z ↦ if i < ones z then 1 else 0) := by
  apply (ordinary hn i n hin x hx).trans
  apply mean_mono
  intro z
  split_ifs <;> norm_num; omega

end
end Lax343628Proofs.OneBitMutation

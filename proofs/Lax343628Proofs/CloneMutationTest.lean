import Lax343628Proofs.AnchorMutation
import Lax343628Proofs.MutationCoupling
import Lax343628Proofs.NamedBirth

namespace Lax343628Proofs.CloneMutationTest

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.MutationCoupling Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.Genotypes
open Lax343628Proofs.AnchorMutation
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma unchanged_of_no_zero_hit {n k : ℕ} (x mask : BitString n)
    (hx : (zeros x).card = k) (hchild : (zeros (mutate x mask)).card = k)
    (hno : mask ∉ hits (zeros x)) : mutate x mask = x := by
  have hsub : zeros x ⊆ zeros (mutate x mask) := by
    intro j hj
    have hxj := (mem_zeros x j).mp hj
    have hm := no_hits (zeros x) mask hno j hj
    simp [mem_zeros, mutate, hm, hxj]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hx, hchild])
  have hh := congrArg NamedBirth.fromZeros heq.symm
  simpa only [NamedBirth.fromZeros_zeros] using hh

lemma changed_probability {n k : ℕ} (hn : 1 ≤ n) (x : BitString n) (hx : (zeros x).card = k) :
    mean (pairMutation x x (1 / n))
      (fun z ↦ if z ≠ x ∧ (zeros z).card = k then 1 else 0) ≤ (k : ℝ) / n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) ≤ 1 / n ∧ 1 / (n : ℝ) ≤ 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr hnR⟩
  rw [pairMutation_self, mean_map]
  have ht := mean_mono (independentBits n (1 / n)) (fun mask ↦
    show (if mutate x mask ≠ x ∧ (zeros (mutate x mask)).card = k then (1 : ℝ) else 0) ≤
      (if mask ∈ hits (zeros x) then 1 else 0) by
      by_cases hh : mutate x mask ≠ x ∧ (zeros (mutate x mask)).card = k
      · have hhit : mask ∈ hits (zeros x) := by
          by_contra hno
          exact hh.1 (unchanged_of_no_zero_hit x mask hx hh.2 hno)
        simp [hh, hhit]
      · rw [if_neg hh]
        split_ifs <;> norm_num)
  rw [mean_indicator] at ht
  have hb := hit_probability (zeros x) (1 / n) hp
  rw [hx] at hb
  exact ht.trans (by simpa only [div_eq_mul_inv, one_mul] using hb)

lemma copy_probability {n k : ℕ} (hn : 2 ≤ n) (x : BitString n) (hx : (zeros x).card = k) :
    (pairMutation x x (1 / n) x).toReal = (1 - 1 / (n : ℝ)) ^ n := by
  have hh := (cloneBirth_mass (ofString x hx) (ofString x hx) (ofString x hx)).symm.trans
    (cloneBirth_self hn (ofString x hx))
  simpa only [toString_ofString] using hh

lemma clone_error {n k : ℕ} (hn : 2 ≤ n) (x : BitString n) (hx : (zeros x).card = k)
    (ψ : BitString n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hh : ∀ z, 0 ≤ ψ z ∧ ψ z ≤ M)
    (hzero : ∀ z, (zeros z).card ≠ k → ψ z = 0) :
    0 ≤ mean (pairMutation x x (1 / n)) ψ - (1 - 1 / (n : ℝ)) ^ n * ψ x ∧
      mean (pairMutation x x (1 / n)) ψ - (1 - 1 / (n : ℝ)) ^ n * ψ x ≤ M * k / n := by
  have hlo := mean_single_lower (pairMutation x x (1 / n)) ψ (fun z ↦ (hh z).1) x
  rw [copy_probability hn x hx] at hlo
  have ht := mean_mono (pairMutation x x (1 / n)) (fun z ↦
    show ψ z ≤ (if z = x then ψ x else 0) +
      M * (if z ≠ x ∧ (zeros z).card = k then 1 else 0) by
      by_cases hzx : z = x
      · subst z; simp
      · by_cases hzc : (zeros z).card = k
        · simpa [hzx, hzc] using (hh z).2
        · rw [if_neg hzx, if_neg (by tauto : ¬(z ≠ x ∧ (zeros z).card = k)), hzero z hzc]
          norm_num)
  rw [mean_add, mean_pick, mean_mul, copy_probability hn x hx] at ht
  have hb := mul_le_mul_of_nonneg_left (changed_probability (by omega) x hx) hM
  constructor
  · linarith
  · have heq : M * ((k : ℝ) / n) = M * k / n := by ring
    rw [heq] at hb
    linarith

end
end Lax343628Proofs.CloneMutationTest

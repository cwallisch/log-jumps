import Lax343628Proofs.ClassBirth

namespace Lax343628Proofs.ClassBirthEstimates

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.ClassBirth Lax343628Proofs.ClassChannels
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.PhysicalOffspring Lax343628Proofs.TaggedDynamics
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def average (P : Population n μ) (ψ : BitString n → ℝ) : ℝ :=
  mean (PMF.uniformOfFintype (Fin (μ : ℕ))) (fun u ↦ ψ (P u))

lemma own_clone_error (hn : 2 ≤ n) (P : Population n μ) (hP : ∀ u, (zeros (P u)).card = k)
    (i : Fin n) (b : Fin 2) (ψ : BitString n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hh : ∀ z, 0 ≤ ψ z ∧ ψ z ≤ M) (hbit : ∀ z, z i ≠ b → ψ z = 0)
    (hzero : ∀ z, (zeros z).card ≠ k → ψ z = 0) :
    0 ≤ ownClone P i b ψ - (1 - 1 / (n : ℝ)) ^ n * average P ψ ∧
      ownClone P i b ψ - (1 - 1 / (n : ℝ)) ^ n * average P ψ ≤ M * k / n * fraction i b P := by
  have hpoint (u : Fin (μ : ℕ)) :
      0 ≤ (if P u i = b then pairTest ψ (P u) (P u) else 0) -
          (1 - 1 / (n : ℝ)) ^ n * ψ (P u) ∧
        (if P u i = b then pairTest ψ (P u) (P u) else 0) -
          (1 - 1 / (n : ℝ)) ^ n * ψ (P u) ≤ M * k / n * (if P u i = b then 1 else 0) := by
    by_cases hu : P u i = b
    · simpa only [if_pos hu, mul_one, pairTest] using
        CloneMutationTest.clone_error hn (P u) (hP u) ψ M hM hh hzero
    · simp only [if_neg hu, hbit _ hu, mul_zero, sub_zero, le_refl, and_self]
  have hlo := mean_nonneg (PMF.uniformOfFintype (Fin (μ : ℕ))) (fun u ↦ (hpoint u).1)
  have hhi := mean_mono (PMF.uniformOfFintype (Fin (μ : ℕ))) (fun u ↦ (hpoint u).2)
  rw [mean_sub, mean_mul] at hlo hhi
  rw [mean_mul] at hhi
  exact ⟨hlo, hhi⟩

lemma other_class_test (i : Fin n) (b : Fin 2) (x y : BitString n)
    (hx : x i ≠ b) (hy : y i ≠ b) (ψ : BitString n → ℝ) (M : ℝ) (_hM : 0 ≤ M)
    (hh : ∀ z, ψ z ≤ M) (hbit : ∀ z, z i ≠ b → ψ z = 0) :
    pairTest ψ x y ≤ M / n := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) ≤ 1 / n ∧ 1 / (n : ℝ) ≤ 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr hnR⟩
  have hxy : x i = y i := by
    have hxlt := (x i).isLt
    have hylt := (y i).isLt
    have hblt := b.isLt
    omega
  have ht := mean_mono (pairMutation x y (1 / n)) (fun z ↦
    show ψ z ≤ M * (if z i = b then 1 else 0) by
      by_cases hz : z i = b
      · simpa only [if_pos hz, mul_one] using hh z
      · simp only [if_neg hz, mul_zero, hbit z hz, le_refl])
  rw [mean_mul, ColumnKernels.pairMutation_class_mass _ _ _ hp,
    hxy, siteLaw_apply _ _ _ _ hp] at ht
  simp only [siteProbability, if_neg hy.symm, ite_true, ENNReal.toReal_ofReal hp.1] at ht
  exact ht.trans_eq (by ring)

lemma from_opposite_bound (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (P : Population n μ)
    (i : Fin n) (b : Fin 2) (ψ : BitString n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hh : ∀ z, 0 ≤ ψ z ∧ ψ z ≤ M) (hbit : ∀ z, z i ≠ b → ψ z = 0) :
    0 ≤ fromOpposite pc P i b ψ ∧ fromOpposite pc P i b ψ ≤ M / n * (1 - fraction i b P) := by
  constructor
  · apply mean_nonneg
    intro uv
    split_ifs
    · exact mean_nonneg _ (fun z ↦ (hh z).1)
    · rfl
  · have ht := mean_mono (parentLaw μ pc) (fun uv ↦
      show (if P uv.1 i ≠ b ∧ P uv.2 i ≠ b then pairTest ψ (P uv.1) (P uv.2) else 0) ≤
        (M / n) * (1 - if P uv.1 i = b then 1 else 0) by
        by_cases hu : P uv.1 i ≠ b ∧ P uv.2 i ≠ b
        · simpa only [if_pos hu, if_neg hu.1, sub_zero, mul_one] using
            other_class_test i b (P uv.1) (P uv.2) hu.1 hu.2 ψ M hM (fun z ↦ (hh z).2) hbit
        · rw [if_neg hu]
          split_ifs <;> simp only [sub_self, sub_zero, mul_zero, mul_one] <;> positivity)
    rw [mean_mul, mean_sub, mean_const, parent_first pc hpc (fun u ↦ if P u i = b then 1 else 0)] at ht
    exact ht

end
end Lax343628Proofs.ClassBirthEstimates

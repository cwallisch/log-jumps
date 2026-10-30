import Lax343628Proofs.Complement
import Lax343628Proofs.OneBitMutation
import Lax343628Proofs.OrdinaryBirth

namespace Lax343628Proofs.ValleyBirth

open Lax343628.Algorithm Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.Sampling Lax343628Proofs.PhysicalOffspring
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n j : ℕ} {mu : ℕ+}

def test (j : ℕ) (z : BitString n) : ℝ := if j < (zeros z).card then 1 else 0

lemma nonneg (j : ℕ) (z : BitString n) : 0 ≤ test j z := by unfold test; split_ifs <;> norm_num

lemma pair (hn : 2 ≤ n) (hj : 2 * j ≤ n) (x y : BitString n)
    (hx : j ≤ (zeros x).card) (hy : j ≤ (zeros y).card) :
    1 / 32 ≤ mean (pairMutation x y (1 / n)) (test j) := by
  by_cases hxy : x = y
  · subst y
    by_cases hhigh : j < (zeros x).card
    · have hh := MutationLower.standard hn x x (test j) (nonneg j)
      rw [pairMutation_self, CrossoverCount.zero_mutation, PMF.pure_map, mutate_zero, mean_pure] at hh
      simp only [test, if_pos hhigh] at hh
      linarith
    · have heq : (zeros x).card = j := by omega
      have hin : j < n := by omega
      have hh := OneBitMutation.strict hn j hin (Complement.bits x) (by rw [Complement.ones, heq])
      rw [Complement.mean x x (1 / n) (fun m ↦ if j < m then 1 else 0)] at hh
      have hhalf : (n : ℝ) / 2 ≤ (n - j : ℕ) := by
        rw [Nat.cast_sub (by omega : j ≤ n)]
        have hjR : 2 * (j : ℝ) ≤ n := by exact_mod_cast hj
        linarith
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hlo : (1 / 16 : ℝ) ≤ ((n - j : ℕ) : ℝ) / (8 * n) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * n)).mpr
        linarith
      exact (by norm_num : (1 / 32 : ℝ) ≤ 1 / 16).trans (hlo.trans hh)
  · have hneq : Complement.bits x ≠ Complement.bits y := fun hh ↦ hxy (Complement.injective hh)
    have hc := CrossoverCount.strict j (Complement.bits x) (Complement.bits y)
      (by rw [Complement.ones]; exact hx) (by rw [Complement.ones]; exact hy) hneq
    rw [Complement.mean x y 0 (fun m ↦ if j < m then 1 else 0)] at hc
    have hm := MutationLower.standard hn x y (test j) (nonneg j)
    change (1 / 4 : ℝ) ≤ mean (pairMutation x y 0) (test j) at hc
    linarith

lemma offspring (hn : 2 ≤ n) (hj : 2 * j ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (P : Population n mu) (hP : ∀ u, j ≤ (zeros (P u)).card) :
    pc / 32 ≤ mean (Sampling.offspring pc P) (test j) := by
  have hh := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ) × Fin (mu : ℕ)))
    (fun uv ↦ pair hn hj (P uv.1) (P uv.2) (hP uv.1) (hP uv.2))
  rw [mean_const] at hh
  rw [offspring_split, mean_bind, mean_coin pc hpc]
  simp only [if_true, Fin.zero_ne_one, if_false, mean_bind]
  have hclone : 0 ≤ mean (PMF.uniformOfFintype (Fin (mu : ℕ)))
      (fun u ↦ mean (pairMutation (P u) (P u) (1 / n)) (test j)) := mean_nonneg _ (fun u ↦ mean_nonneg _ (nonneg j))
  have hscale := mul_le_mul_of_nonneg_left hh hpc.1
  have hrest := mul_nonneg (sub_nonneg.mpr hpc.2) hclone
  linarith

end
end Lax343628Proofs.ValleyBirth

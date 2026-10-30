import Lax343628Proofs.EmpiricalSampling
import Lax343628Proofs.Genotypes
import Lax343628Proofs.ColumnKernels
import Mathlib.Data.Nat.Choose.Bounds

namespace Lax343628Proofs.SparseEnvironment

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.Genotypes Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Lists (n k J : ℕ) (rs : ℕ+) := Fin J → Fin (rs : ℕ) → Genotype n k

abbrev Net (n k R J : ℕ) (rs : ℕ+) := Fin (R + 1) × Lists n k J rs

lemma genotype_card (n k : ℕ) : Fintype.card (Genotype n k) = n.choose k := by
  rw [Fintype.card_finset_len, Fintype.card_fin]

lemma genotype_nonempty {n k : ℕ} (hk : k ≤ n) : Nonempty (Genotype n k) := by
  apply Fintype.card_pos_iff.mp
  rw [genotype_card]
  exact Nat.choose_pos hk

lemma net_card (n k R J : ℕ) (rs : ℕ+) :
    Fintype.card (Net n k R J rs) = (R + 1) * (n.choose k) ^ (J * (rs : ℕ)) := by
  simp only [Net, Lists, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, genotype_card]
  rw [← pow_mul, Nat.mul_comm (rs : ℕ) J]

lemma net_log_card {n k R J : ℕ} (hk : k ≤ n) (hn : 1 ≤ n) (rs : ℕ+) :
    Real.log (Fintype.card (Net n k R J rs) : ℝ) ≤
      Real.log ((R : ℝ) + 1) + (J : ℝ) * (rs : ℕ) * k * Real.log n := by
  rw [net_card, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hchoose : (n.choose k : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow n k
  have hl := Real.log_le_log hc hchoose
  rw [Real.log_pow] at hl
  have ht := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ J * (rs : ℕ))
  norm_num only [Nat.cast_mul] at ht ⊢
  nlinarith

def partnerLaw {n k : ℕ} {rs : ℕ+} (xs : Fin (rs : ℕ) → Genotype n k) : PMF (BitString n) :=
  (PMF.uniformOfFintype (Fin (rs : ℕ))).map (fun j ↦ toString (xs j))

lemma partner_support {n k : ℕ} {rs : ℕ+} (xs : Fin (rs : ℕ) → Genotype n k)
    (u : BitString n) (hu : u ∈ (partnerLaw xs).support) : (zeros u).card = k := by
  obtain ⟨j, _, rfl⟩ := (PMF.mem_support_map_iff _ _ u).mp hu
  rw [zeros_toString]
  exact (xs j).property

lemma partner_mean {n k : ℕ} {rs : ℕ+} (xs : Fin (rs : ℕ) → Genotype n k) (f : BitString n → ℝ) :
    mean (partnerLaw xs) f = (∑ j, f (toString (xs j))) / (rs : ℕ) := by
  rw [partnerLaw, mean_map, mean_uniform, Fintype.card_fin]
  ring

end
end Lax343628Proofs.SparseEnvironment

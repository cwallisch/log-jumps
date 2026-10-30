import Lax343628Proofs.CoreCounts
import Lax343628Proofs.ColumnBlock

namespace Lax343628Proofs.CoreSpecies

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.SeedGeometry
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison Lax343628Proofs.EmpiricalKernels
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

lemma frequency_mean (P : Population n mu) (z : BitString n) :
    frequency P z = mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun u ↦ if P u = z then 1 else 0) := by
  have hh := mean_map (PMF.uniformOfFintype (Fin (mu : ℕ))) P (fun x ↦ if x = z then 1 else 0)
  rw [mean_pick, mul_one] at hh
  exact hh

lemma exists_ordinary (C : Finset (Fin n)) (P : Population n mu) (hrho : rho C P < 1) :
    ∃ u, ordinary C (P u) := by
  by_contra hn
  push Not at hn
  have hh := ordinary_mean C P
  simp only [if_neg (hn _), mean_const] at hh
  linarith

lemma small_core (C : Finset (Fin n)) (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = k)
    (omega : ℝ) (hw : omega ≤ 1) (hcap : ColumnBlock.cap omega P) (hrho : rho C P < omega) :
    C.card < k := by
  obtain ⟨u, hu⟩ := exists_ordinary C P (hrho.trans_le hw)
  have hCk : C.card ≤ k := (Finset.card_le_card hu).trans_eq (hP u)
  by_contra hn
  have hC : C.card = k := by omega
  have heq (v : Fin (mu : ℕ)) (hv : ordinary C (P v)) : P v = NamedBirth.fromZeros C := by
    have hzero : C = zeros (P v) := Finset.eq_of_subset_of_card_le hv (by rw [hP v, hC])
    rw [hzero, NamedBirth.fromZeros_zeros]
  have hh := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun v ↦
    show (if ordinary C (P v) then (1 : ℝ) else 0) ≤ (if P v = NamedBirth.fromZeros C then 1 else 0) by
      by_cases hv : ordinary C (P v)
      · simp only [if_pos hv, if_pos (heq v hv), le_refl]
      · rw [if_neg hv]; split_ifs <;> norm_num)
  rw [ordinary_mean, ← frequency_mean] at hh
  have hc := hcap (NamedBirth.fromZeros C)
  linarith

end
end Lax343628Proofs.CoreSpecies

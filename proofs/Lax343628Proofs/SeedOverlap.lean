import Lax343628Proofs.SeedGeometry

namespace Lax343628Proofs.SeedOverlap

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.SeedGeometry
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison Lax343628Proofs.ClassChannels
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

lemma rho_le_missing (C : Finset (Fin n)) (P : Population n mu) : rho C P ≤ ∑ j ∈ C, fraction j 1 P := by
  have hp (u : Fin (mu : ℕ)) : (if ordinary C (P u) then (0 : ℝ) else 1) ≤
      ∑ j ∈ C, if P u j = 1 then 1 else 0 := by
    by_cases ho : ordinary C (P u)
    · rw [if_pos ho]
      exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> norm_num)
    · obtain ⟨j, hjC, hj⟩ : ∃ j ∈ C, P u j = 1 := by
        have hn : ∃ j ∈ C, j ∉ zeros (P u) := by
          by_contra hn
          apply ho
          intro j hj
          by_contra hjz
          exact hn ⟨j, hj, hjz⟩
        obtain ⟨j, hjC, hjnot⟩ := hn
        refine ⟨j, hjC, ?_⟩
        have hj0 : P u j ≠ 0 := by simpa only [mem_zeros] using hjnot
        have hlt := (P u j).isLt
        omega
      rw [if_neg ho]
      have hh := Finset.single_le_sum (s := C) (a := j) (f := fun j ↦ if P u j = 1 then (1 : ℝ) else 0)
        (fun _ _ ↦ by split_ifs <;> norm_num) hjC
      simpa only [if_pos hj] using hh
  have hh := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) hp
  rw [GroupKernelSampling.mean_finset_sum] at hh
  exact hh

lemma good_ordinary (C U : Finset (Fin n)) (P : Population n mu) (theta : ℝ)
    (hU : Disjoint U C) (hflat : ∀ j, j ∉ C → fraction j 0 P ≤ theta) :
    1 - rho C P - U.card * theta ≤ mean (PMF.uniformOfFintype (Fin (mu : ℕ)))
      (fun u ↦ if ordinary C (P u) ∧ Disjoint U (privateZeros C (P u)) then 1 else 0) := by
  have hb := fixed_overlap_flat C U P theta hU hflat
  have heq : (fun u : Fin (mu : ℕ) ↦ if ordinary C (P u) then (1 : ℝ) else 0) =
      (fun u ↦ (if ordinary C (P u) ∧ Disjoint U (privateZeros C (P u)) then 1 else 0) +
        (if ordinary C (P u) ∧ ¬Disjoint U (privateZeros C (P u)) then 1 else 0)) := by
    funext u
    by_cases ho : ordinary C (P u) <;> by_cases hd : Disjoint U (privateZeros C (P u)) <;> simp [ho, hd]
  have hh := ordinary_mean C P
  rw [heq, mean_add] at hh
  linarith

lemma family_good_ordinary (C : Finset (Fin n)) (i : Fin n) (hi : i ∈ C) (hC : C.card ≤ k)
    (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = k)
    (theta : ℝ) (hflat : ∀ j, j ∉ C → fraction j 0 P ≤ theta) :
    phi C i P * (1 - rho C P - ((k - C.card + 1 : ℕ) : ℝ) * theta) ≤
      mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun u ↦
        mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun v ↦
          if family C i (P u) ∧ ordinary C (P v) ∧ Disjoint (privateZeros C (P u)) (privateZeros C (P v)) then 1 else 0)) := by
  have hp (u : Fin (mu : ℕ)) :
      (1 - rho C P - ((k - C.card + 1 : ℕ) : ℝ) * theta) * (if family C i (P u) then 1 else 0) ≤
      mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun v ↦
        if family C i (P u) ∧ ordinary C (P v) ∧ Disjoint (privateZeros C (P u)) (privateZeros C (P v)) then 1 else 0) := by
    by_cases hf : family C i (P u)
    · simp only [hf, if_true, mul_one, true_and]
      have hh := good_ordinary C (privateZeros C (P u)) P theta (Finset.sdiff_disjoint) hflat
      rw [family_private_card C i hi hC (P u) (hP u) hf] at hh
      exact hh
    · simp only [hf, false_and, if_false, mean_const, mul_zero, le_refl]
  have hh := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) hp
  rw [mean_mul] at hh
  change _ * phi C i P ≤ _ at hh
  nlinarith

end
end Lax343628Proofs.SeedOverlap

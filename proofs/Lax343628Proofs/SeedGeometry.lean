import Lax343628Proofs.GroupKernelSampling
import Lax343628Proofs.ClassMeanDynamics

namespace Lax343628Proofs.SeedGeometry

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.ClassChannels
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

def ordinary (C : Finset (Fin n)) (x : BitString n) : Prop := C ⊆ zeros x

def family (C : Finset (Fin n)) (i : Fin n) (x : BitString n) : Prop := C.erase i ⊆ zeros x ∧ x i = 1

def privateZeros (C : Finset (Fin n)) (x : BitString n) : Finset (Fin n) := zeros x \ C

def rho (C : Finset (Fin n)) (P : Population n mu) : ℝ :=
  mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun u ↦ if ordinary C (P u) then 0 else 1)

def phi (C : Finset (Fin n)) (i : Fin n) (P : Population n mu) : ℝ :=
  mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun u ↦ if family C i (P u) then 1 else 0)

lemma ordinary_private_card (C : Finset (Fin n)) (x : BitString n)
    (hx : (zeros x).card = k) (hCx : ordinary C x) : (privateZeros C x).card = k - C.card := by
  unfold privateZeros
  rw [Finset.card_sdiff_of_subset hCx, hx]

lemma family_private_card (C : Finset (Fin n)) (i : Fin n) (hi : i ∈ C) (hC : C.card ≤ k)
    (x : BitString n) (hx : (zeros x).card = k) (hF : family C i x) :
    (privateZeros C x).card = k - C.card + 1 := by
  have hnot : i ∉ zeros x := by simp only [mem_zeros, hF.2]; decide
  have heq : zeros x ∩ C = C.erase i := by
    ext j
    constructor
    · intro hj
      have hh := Finset.mem_inter.mp hj
      exact Finset.mem_erase.mpr ⟨fun he ↦ hnot (he ▸ hh.1), hh.2⟩
    · intro hj
      exact Finset.mem_inter.mpr ⟨hF.1 hj, Finset.mem_of_mem_erase hj⟩
  unfold privateZeros
  rw [Finset.card_sdiff, hx, Finset.inter_comm C (zeros x), heq, Finset.card_erase_of_mem hi]
  have hcpos := Finset.card_pos.mpr ⟨i, hi⟩
  omega

lemma ordinary_mean (C : Finset (Fin n)) (P : Population n mu) :
    mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun u ↦ if ordinary C (P u) then 1 else 0) = 1 - rho C P := by
  have heq : (fun u ↦ if ordinary C (P u) then (1 : ℝ) else 0) =
      (fun u ↦ 1 - (if ordinary C (P u) then 0 else 1)) := by funext u; split_ifs <;> norm_num
  rw [heq, mean_sub, mean_const]
  rfl

lemma rho_bounds (C : Finset (Fin n)) (P : Population n mu) : 0 ≤ rho C P ∧ rho C P ≤ 1 := by
  constructor
  · exact mean_nonneg _ (fun _ ↦ by split_ifs <;> norm_num)
  · exact (mean_mono _ (fun _ ↦ show (if ordinary C (P _) then (0 : ℝ) else 1) ≤ 1 by split_ifs <;> norm_num)).trans_eq (mean_const _ 1)

lemma fixed_overlap (C U : Finset (Fin n)) (P : Population n mu) :
    mean (PMF.uniformOfFintype (Fin (mu : ℕ)))
      (fun u ↦ if ordinary C (P u) ∧ ¬ Disjoint U (privateZeros C (P u)) then 1 else 0) ≤
        ∑ j ∈ U, fraction j 0 P := by
  have hp (u : Fin (mu : ℕ)) :
      (if ordinary C (P u) ∧ ¬ Disjoint U (privateZeros C (P u)) then (1 : ℝ) else 0) ≤
        ∑ j ∈ U, if P u j = 0 then 1 else 0 := by
    by_cases hb : ordinary C (P u) ∧ ¬ Disjoint U (privateZeros C (P u))
    · obtain ⟨j, hjU, hjprivate⟩ : ∃ j ∈ U, j ∈ privateZeros C (P u) := by
        by_contra hn
        apply hb.2
        apply Finset.disjoint_left.mpr
        intro j hjU hjprivate
        exact hn ⟨j, hjU, hjprivate⟩
      have hj0 : P u j = 0 := by simpa only [mem_zeros] using (Finset.mem_sdiff.mp hjprivate).1
      have hh := Finset.single_le_sum (s := U) (a := j) (f := fun j ↦ if P u j = 0 then (1 : ℝ) else 0)
        (fun _ _ ↦ by split_ifs <;> norm_num) hjU
      simpa only [if_pos hb, if_pos hj0] using hh
    · rw [if_neg hb]
      exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> norm_num)
  have hh := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) hp
  rw [GroupKernelSampling.mean_finset_sum] at hh
  exact hh

lemma fixed_overlap_flat (C U : Finset (Fin n)) (P : Population n mu) (theta : ℝ)
    (hU : Disjoint U C) (hflat : ∀ j, j ∉ C → fraction j 0 P ≤ theta) :
    mean (PMF.uniformOfFintype (Fin (mu : ℕ)))
      (fun u ↦ if ordinary C (P u) ∧ ¬ Disjoint U (privateZeros C (P u)) then 1 else 0) ≤ U.card * theta := by
  apply (fixed_overlap C U P).trans
  have hh := Finset.sum_le_sum (s := U) (fun j hj ↦ hflat j (fun hjC ↦ Finset.disjoint_left.mp hU hj hjC))
  simpa only [Finset.sum_const, nsmul_eq_mul] using hh

end
end Lax343628Proofs.SeedGeometry

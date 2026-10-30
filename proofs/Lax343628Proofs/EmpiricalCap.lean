import Lax343628Proofs.PathCounts
import Lax343628Proofs.GroupKernelSampling

namespace Lax343628Proofs.EmpiricalCap

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.EmpiricalSampling Lax343628Proofs.ChannelNoise
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α]

def atomTest (u v : α) : ℝ := if v = u then 1 else 0

def frequency {r : ℕ} (xs : Fin r → α) (u : α) : ℝ := sampleMean (atomTest u) xs

def loss (p : PMF α) {r : ℕ} (xs : Fin r → α) : ℝ := ∑ u, (frequency xs u - (p u).toReal) ^ 2

lemma atom_mean (p : PMF α) (u : α) : mean p (atomTest u) = (p u).toReal := by
  change mean p (fun v ↦ if v = u then 1 else 0) = _
  simpa only [mul_one] using mean_pick p u 1

lemma expected_loss (p : PMF α) {r : ℕ} (hr : 1 ≤ r) : mean (samples p r) (loss p) ≤ 1 / r := by
  have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hpoint (u : α) : mean (samples p r) (fun xs ↦ (frequency xs u - (p u).toReal) ^ 2) ≤ (p u).toReal / r := by
    have hs := average_second p (atomTest u) hr
    rw [atom_mean] at hs
    have hv := (PathCounts.centered_unit p (atomTest u) (fun v ↦ by unfold atomTest; split_ifs <;> norm_num)).2
    rw [atom_mean] at hv
    change mean (samples p r) (fun xs ↦ (frequency xs u - (p u).toReal) ^ 2) ≤ _
    rw [show (fun xs ↦ (frequency xs u - (p u).toReal) ^ 2) = (fun xs ↦ (sampleMean (atomTest u) xs - (p u).toReal) ^ 2) by rfl, hs]
    exact div_le_div_of_nonneg_right hv hrR
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun u _ ↦ hpoint u)
  rw [← Finset.sum_div, sum_mass] at hh
  unfold loss
  rw [GroupKernelSampling.mean_finset_sum]
  exact hh

lemma large_atom_loss (p : PMF α) {r : ℕ} (xs : Fin r → α) (omega : ℝ) (homega : 0 ≤ omega)
    (hcap : ∀ u, (p u).toReal ≤ 1 - omega) (u : α) (hu : 1 - omega / 2 ≤ frequency xs u) :
    omega ^ 2 / 4 ≤ loss p xs := by
  have hgap : omega / 2 ≤ frequency xs u - (p u).toReal := by linarith [hcap u]
  have hsq : omega ^ 2 / 4 ≤ (frequency xs u - (p u).toReal) ^ 2 := by nlinarith
  exact hsq.trans (Finset.single_le_sum (fun v _ ↦ sq_nonneg (frequency xs v - (p v).toReal)) (Finset.mem_univ u))

lemma cap_tail (p : PMF α) {r : ℕ} (hr : 1 ≤ r) (omega : ℝ) (homega : 0 < omega)
    (hcap : ∀ u, (p u).toReal ≤ 1 - omega) :
    (samples p r).toOuterMeasure {xs | ∃ u, 1 - omega / 2 ≤ frequency xs u} ≤
      ENNReal.ofReal (4 / ((r : ℝ) * omega ^ 2)) := by
  have hmarkov := event_markov (samples p r) (loss p)
    (fun xs ↦ Finset.sum_nonneg (fun u _ ↦ sq_nonneg (frequency xs u - (p u).toReal)))
    {xs | ∃ u, 1 - omega / 2 ≤ frequency xs u} (omega ^ 2 / 4) (by positivity)
    (fun xs hx ↦ by obtain ⟨u, hu⟩ := hx; exact large_atom_loss p xs omega homega.le hcap u hu)
  apply hmarkov.trans
  apply ENNReal.ofReal_le_ofReal
  have hs := div_le_div_of_nonneg_right (expected_loss p hr) (show 0 ≤ omega ^ 2 / 4 by positivity)
  apply hs.trans_eq
  ring

lemma bad_mean (p : PMF α) {r : ℕ} (hr : 1 ≤ r) (omega : ℝ) (homega : 0 < omega)
    (hcap : ∀ u, (p u).toReal ≤ 1 - omega) :
    mean (samples p r) (fun xs ↦ if ∃ u, 1 - omega / 2 ≤ frequency xs u then 1 else 0) ≤
      4 / ((r : ℝ) * omega ^ 2) := by
  have hh := ENNReal.toReal_mono (by simp) (cap_tail p hr omega homega hcap)
  rw [← mean_indicator] at hh
  simp only [Set.mem_ofPred_eq, ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 / ((r : ℝ) * omega ^ 2))] at hh
  convert hh

lemma selected_lists_bad_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → PMF α) {r : ℕ} (hr : 1 ≤ r) (omega : ℝ) (homega : 0 < omega)
    (selected : ι → Prop) [DecidablePred selected]
    (hcap : ∀ j, selected j → ∀ u, (p j u).toReal ≤ 1 - omega) :
    mean (FiniteProduct.distribution (fun j ↦ samples (p j) r))
      (fun env ↦ if ∀ j, selected j → ∀ u, frequency (env j) u < 1 - omega / 2 then 0 else 1) ≤
        (Fintype.card ι : ℝ) * (4 / ((r : ℝ) * omega ^ 2)) := by
  have hpoint (env : ι → Fin r → α) :
      (if ∀ j, selected j → ∀ u, frequency (env j) u < 1 - omega / 2 then (0 : ℝ) else 1) ≤
        ∑ j : ι, if selected j ∧ ∃ u, 1 - omega / 2 ≤ frequency (env j) u then 1 else 0 := by
    by_cases hg : ∀ j, selected j → ∀ u, frequency (env j) u < 1 - omega / 2
    · rw [if_pos hg]
      exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> norm_num)
    · obtain ⟨j, hj, u, hu⟩ := show ∃ j, selected j ∧ ∃ u, 1 - omega / 2 ≤ frequency (env j) u by
        simpa only [not_forall, not_lt, Classical.not_imp, exists_prop] using hg
      rw [if_neg hg]
      have hh := Finset.single_le_sum (s := Finset.univ) (a := j)
        (f := fun j ↦ if selected j ∧ ∃ u, 1 - omega / 2 ≤ frequency (env j) u then (1 : ℝ) else 0)
        (fun _ _ ↦ by split_ifs <;> norm_num) (Finset.mem_univ j)
      simpa only [if_pos (show selected j ∧ ∃ u, 1 - omega / 2 ≤ frequency (env j) u from ⟨hj, u, hu⟩)] using hh
  have hcoord (j : ι) : mean (FiniteProduct.distribution (fun j ↦ samples (p j) r))
      (fun env ↦ if selected j ∧ ∃ u, 1 - omega / 2 ≤ frequency (env j) u then 1 else 0) ≤ 4 / ((r : ℝ) * omega ^ 2) := by
    apply FiniteConditioning.conditional_bound (j := j)
    intro rest
    by_cases hj : selected j
    · simpa only [FiniteConditioning.fill, dif_pos rfl, dite_true, hj, true_and] using bad_mean (p j) hr omega homega (hcap j hj)
    · simp only [hj, false_and, if_false, mean_const]
      positivity
  have hh := mean_mono (FiniteProduct.distribution (fun j ↦ samples (p j) r)) hpoint
  rw [GroupKernelSampling.mean_finset_sum] at hh
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcoord j)
  exact hh.trans (by simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hs)

end
end Lax343628Proofs.EmpiricalCap

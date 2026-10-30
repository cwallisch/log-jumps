import Lax343628Proofs.ClassIncrements
import Lax343628Proofs.ClassBirthEstimates

namespace Lax343628Proofs.ImmigrationMean

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.TaggedDynamics Lax343628Proofs.ClassChannels
open Lax343628Proofs.ClassIncrements Lax343628Proofs.ClassBirth
open Lax343628Proofs.PlateauDynamics Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

lemma mutant_point (i : Fin n) (ψ : BitString n → ℝ)
    (hbit : ∀ z, z i ≠ 1 → ψ z = 0) (haccept : ∀ z, ¬onPlateau k z → ψ z = 0)
    (P : Population n μ) (E : Event n μ) :
    (if immigration k i P E then change k ψ P E else 0) =
      (if ¬parentsHave i 1 P E.1 then ψ E.2.1 else 0) *
        (if deletedHave i 0 P E.2.2 then 1 else 0) := by
  obtain ⟨uv, z, d⟩ := E
  refine Fin.lastCases ?_ (fun u ↦ ?_) d
  · simp [immigration, deletedHave_last]
  · rw [change_old]
    simp only [immigration, deletedHave_cast]
    by_cases hpar : parentsHave i 1 P uv <;> by_cases hdel : P u i = 0 <;>
      by_cases hz : z i = 1 <;> by_cases hplat : onPlateau k z
    all_goals
      have hold : P u i = 0 → ψ (P u) = 0 := by
        intro hu
        apply hbit
        rw [hu]
        decide
      simp_all

lemma mutant_mean (pc : ℝ) (i : Fin n) (ψ : BitString n → ℝ)
    (hbit : ∀ z, z i ≠ 1 → ψ z = 0) (haccept : ∀ z, ¬onPlateau k z → ψ z = 0)
    (P : Population n μ) :
    mean (eventLaw pc P) (fun E ↦ if immigration k i P E then change k ψ P E else 0) =
      ((μ : ℕ) / ((μ : ℕ) + 1 : ℝ) * fraction i 0 P) * fromOpposite pc P i 1 ψ := by
  have hp : (fun E ↦ if immigration k i P E then change k ψ P E else 0) =
      (fun E ↦ (if ¬parentsHave i 1 P E.1 then ψ E.2.1 else 0) *
        (if deletedHave i 0 P E.2.2 then 1 else 0)) := funext (mutant_point i ψ hbit haccept P)
  rw [hp, mean_eventLaw]
  simp_rw [mean_mul, deleted_mean]
  have heq (uv : Fin (μ : ℕ) × Fin (μ : ℕ)) :
      mean (PhysicalOffspring.pairMutation (P uv.1) (P uv.2) (1 / n))
        (fun z ↦ (if ¬parentsHave i 1 P uv then ψ z else 0) *
          ((μ : ℕ) / ((μ : ℕ) + 1 : ℝ) * fraction i 0 P)) =
      ((μ : ℕ) / ((μ : ℕ) + 1 : ℝ) * fraction i 0 P) *
        (if P uv.1 i ≠ 1 ∧ P uv.2 i ≠ 1 then pairTest ψ (P uv.1) (P uv.2) else 0) := by
    by_cases hpar : parentsHave i 1 P uv
    · have hn : ¬(P uv.1 i ≠ 1 ∧ P uv.2 i ≠ 1) := by unfold parentsHave at hpar; tauto
      simp [hpar, hn, mean_const]
    · have hn : P uv.1 i ≠ 1 ∧ P uv.2 i ≠ 1 := by unfold parentsHave at hpar; tauto
      simp only [if_pos hpar, if_pos hn]
      have hfun : (fun z ↦ ψ z * ((μ : ℕ) / ((μ : ℕ) + 1 : ℝ) * fraction i 0 P)) =
          (fun z ↦ ((μ : ℕ) / ((μ : ℕ) + 1 : ℝ) * fraction i 0 P) * ψ z) := by
        funext z; ring
      rw [hfun, mean_mul]
      rfl
  simp_rw [heq]
  rw [mean_mul]
  rfl

def mutantAccept (k : ℕ) (i : Fin n) (z : BitString n) : ℝ :=
  if onPlateau k z ∧ z i = 1 then 1 else 0

def deletedWeight (ψ : BitString n → ℝ) (P : Population n μ) (d : Fin ((μ : ℕ) + 1)) : ℝ :=
  Fin.lastCases 0 (fun u ↦ ψ (P u)) d

lemma resident_point (i : Fin n) (ψ : BitString n → ℝ)
    (hbit : ∀ z, z i ≠ 0 → ψ z = 0) (P : Population n μ) (E : Event n μ) :
    (if immigration k i P E then change k ψ P E else 0) =
      -(if ¬parentsHave i 1 P E.1 then mutantAccept k i E.2.1 else 0) * deletedWeight ψ P E.2.2 := by
  obtain ⟨uv, z, d⟩ := E
  refine Fin.lastCases ?_ (fun u ↦ ?_) d
  · simp [immigration, deletedHave_last, deletedWeight]
  · rw [change_old]
    simp only [immigration, deletedHave_cast, deletedWeight, Fin.lastCases_castSucc]
    by_cases hpar : parentsHave i 1 P uv <;> by_cases hdel : P u i = 0 <;>
      by_cases hz : z i = 1 <;> by_cases hplat : onPlateau k z
    all_goals
      have hchild : z i = 1 → ψ z = 0 := by
        intro hzi
        apply hbit
        rw [hzi]
        decide
      simp_all [mutantAccept]

lemma deletedWeight_mean (ψ : BitString n → ℝ) (P : Population n μ) :
    mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))) (deletedWeight ψ P) =
      ((μ : ℕ) / ((μ : ℕ) + 1 : ℝ)) * ClassBirthEstimates.average P ψ := by
  rw [Deletion.uniform_mean, Fin.sum_univ_castSucc]
  simp only [deletedWeight, Fin.lastCases_castSucc, Fin.lastCases_last, add_zero, Fintype.card_fin]
  unfold ClassBirthEstimates.average
  rw [Deletion.uniform_mean, Fintype.card_fin]
  have hm : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have heq : (((μ : ℕ) + 1 : ℕ) : ℝ) = (μ : ℕ) + 1 := by norm_num
  rw [heq]
  field_simp

lemma resident_mean (pc : ℝ) (i : Fin n) (ψ : BitString n → ℝ)
    (hbit : ∀ z, z i ≠ 0 → ψ z = 0) (P : Population n μ) :
    mean (eventLaw pc P) (fun E ↦ if immigration k i P E then change k ψ P E else 0) =
      -((μ : ℕ) / ((μ : ℕ) + 1 : ℝ) * ClassBirthEstimates.average P ψ) *
        fromOpposite pc P i 1 (mutantAccept k i) := by
  have hp : (fun E ↦ if immigration k i P E then change k ψ P E else 0) =
      (fun E ↦ -(if ¬parentsHave i 1 P E.1 then mutantAccept k i E.2.1 else 0) *
        deletedWeight ψ P E.2.2) := funext (resident_point i ψ hbit P)
  rw [hp, mean_eventLaw]
  simp_rw [mean_mul, deletedWeight_mean]
  let C := (μ : ℕ) / ((μ : ℕ) + 1 : ℝ) * ClassBirthEstimates.average P ψ
  have heq (uv : Fin (μ : ℕ) × Fin (μ : ℕ)) :
      mean (PhysicalOffspring.pairMutation (P uv.1) (P uv.2) (1 / n))
        (fun z ↦ -(if ¬parentsHave i 1 P uv then mutantAccept k i z else 0) * C) =
      -C * (if P uv.1 i ≠ 1 ∧ P uv.2 i ≠ 1 then pairTest (mutantAccept k i) (P uv.1) (P uv.2) else 0) := by
    by_cases hpar : parentsHave i 1 P uv
    · have hn : ¬(P uv.1 i ≠ 1 ∧ P uv.2 i ≠ 1) := by unfold parentsHave at hpar; tauto
      simp [hpar, hn, mean_const]
    · have hn : P uv.1 i ≠ 1 ∧ P uv.2 i ≠ 1 := by unfold parentsHave at hpar; tauto
      simp only [if_pos hpar, if_pos hn]
      have hfun : (fun z ↦ -(mutantAccept k i z) * C) = (fun z ↦ -C * mutantAccept k i z) := by
        funext z; ring
      rw [hfun, mean_mul]
      rfl
  change mean (parentLaw μ pc) (fun uv ↦ mean (PhysicalOffspring.pairMutation (P uv.1) (P uv.2) (1 / n))
    (fun z ↦ -(if ¬parentsHave i 1 P uv then mutantAccept k i z else 0) * C)) = _
  simp_rw [heq]
  rw [mean_mul]
  rfl

lemma mutant_sign (i : Fin n) (ψ : BitString n → ℝ) (hn : ∀ z, 0 ≤ ψ z)
    (hbit : ∀ z, z i ≠ 1 → ψ z = 0) (haccept : ∀ z, ¬onPlateau k z → ψ z = 0)
    (P : Population n μ) (E : Event n μ) :
    0 ≤ change k ψ P E - nonImmChange k i ψ P E := by
  have heq : change k ψ P E - nonImmChange k i ψ P E =
      if immigration k i P E then change k ψ P E else 0 := by
    unfold nonImmChange
    split_ifs <;> ring
  rw [heq, mutant_point i ψ hbit haccept P E]
  apply mul_nonneg
  · split_ifs <;> first | exact hn _ | rfl
  · split_ifs <;> norm_num

lemma resident_sign (i : Fin n) (ψ : BitString n → ℝ) (hn : ∀ z, 0 ≤ ψ z)
    (hbit : ∀ z, z i ≠ 0 → ψ z = 0) (P : Population n μ) (E : Event n μ) :
    change k ψ P E - nonImmChange k i ψ P E ≤ 0 := by
  have heq : change k ψ P E - nonImmChange k i ψ P E =
      if immigration k i P E then change k ψ P E else 0 := by
    unfold nonImmChange
    split_ifs <;> ring
  rw [heq, resident_point i ψ hbit P E]
  have h1 : 0 ≤ (if ¬parentsHave i 1 P E.1 then mutantAccept k i E.2.1 else 0) := by
    unfold mutantAccept
    split_ifs <;> norm_num
  have h2 : 0 ≤ deletedWeight ψ P E.2.2 := by
    refine Fin.lastCases ?_ (fun u ↦ ?_) E.2.2
    · simp [deletedWeight]
    · simpa only [deletedWeight, Fin.lastCases_castSucc] using hn (P u)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h1) h2

end
end Lax343628Proofs.ImmigrationMean

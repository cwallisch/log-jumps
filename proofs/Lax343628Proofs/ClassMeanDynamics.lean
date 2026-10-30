import Lax343628Proofs.ImmigrationMean
import Lax343628Proofs.ClassAverages

namespace Lax343628Proofs.ClassMeanDynamics

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.TaggedDynamics Lax343628Proofs.ClassChannels
open Lax343628Proofs.ClassIncrements Lax343628Proofs.ClassBirth Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.PlateauDynamics Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.Deletion
open Lax343628Proofs.ImmigrationMean
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def viability (k : ℕ) (pc : ℝ) (P : Population n μ) : ℝ :=
  mean (offspring pc P) (fun z ↦ if onPlateau k z then 1 else 0)

def copyWeight (n : ℕ) (pc : ℝ) : ℝ := (1 - pc) * (1 - 1 / (n : ℝ)) ^ n

def cloneBias (pc : ℝ) (P : Population n μ) (i : Fin n) (b : Fin 2) (ψ : BitString n → ℝ) : ℝ :=
  (1 - pc) * (ownClone P i b ψ - (1 - 1 / (n : ℝ)) ^ n * average P ψ)

def mutantBias (pc : ℝ) (P : Population n μ) (i : Fin n) (ψ : BitString n → ℝ) : ℝ :=
  cloneBias pc P i 1 ψ + fraction i 1 P * fromOpposite pc P i 1 ψ

def residentBias (k : ℕ) (pc : ℝ) (P : Population n μ) (i : Fin n) (ψ : BitString n → ℝ) : ℝ :=
  cloneBias pc P i 0 ψ + fromOpposite pc P i 0 ψ +
    fromOpposite pc P i 1 (mutantAccept k i) * average P ψ

lemma average_total (P : Population n μ) (ψ : BitString n → ℝ) :
    (μ : ℕ) * average P ψ = total ψ P := by
  unfold average
  rw [uniform_mean, Fintype.card_fin]
  have hm : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  unfold total
  field_simp

lemma fraction_sum (i : Fin n) (P : Population n μ) : fraction i 0 P + fraction i 1 P = 1 := by
  unfold fraction
  rw [← mean_add]
  have heq : (fun u ↦ (if P u i = 0 then (1 : ℝ) else 0) + (if P u i = 1 then 1 else 0)) = fun _ ↦ 1 := by
    funext u
    have hh : P u i = 0 ∨ P u i = 1 := by have ht := (P u i).isLt; omega
    rcases hh with hh | hh <;> simp [hh]
  rw [heq, mean_const]

lemma full_mean (hkn : k ≤ n) (pc : ℝ) (P : Population n μ) (hP : plateauPopulation k P)
    (ψ : BitString n → ℝ) (haccept : ∀ z, ¬onPlateau k z → ψ z = 0) :
    ((μ : ℕ) + 1 : ℝ) * mean (eventLaw pc P) (change k ψ P) =
      (μ : ℕ) * (mean (offspring pc P) ψ - viability k pc P * average P ψ) := by
  have hm : mean (eventLaw pc P) (change k ψ P) =
      mean (auxiliaryStep k pc P) (fun Q ↦ total ψ Q - total ψ P) := by
    rw [← eventLaw_next hkn pc P hP, mean_map]
    rfl
  have haccepted : (fun z ↦ if onPlateau k z then ψ z else 0) = ψ := by
    funext z
    by_cases hz : onPlateau k z
    · simp only [if_pos hz]
    · simp only [if_neg hz, haccept z hz]
  rw [hm, auxiliary_statistic_drift hkn ψ pc P hP, haccepted, ← average_total P ψ]
  have hmpos : (0 : ℝ) < (μ : ℕ) + 1 := by positivity
  unfold viability
  field_simp

lemma mean_split (pc : ℝ) (i : Fin n) (ψ : BitString n → ℝ) (P : Population n μ) :
    mean (eventLaw pc P) (change k ψ P) = mean (eventLaw pc P) (nonImmChange k i ψ P) +
      mean (eventLaw pc P) (fun E ↦ if immigration k i P E then change k ψ P E else 0) := by
  rw [← mean_add]
  congr 1
  funext E
  unfold nonImmChange
  split_ifs <;> ring

lemma mutant_mean (hkn : k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (P : Population n μ) (hP : plateauPopulation k P) (i : Fin n) (ψ : BitString n → ℝ)
    (hbit : ∀ z, z i ≠ 1 → ψ z = 0) (haccept : ∀ z, ¬onPlateau k z → ψ z = 0) :
    ((μ : ℕ) + 1 : ℝ) * mean (eventLaw pc P) (nonImmChange k i ψ P) =
      (μ : ℕ) * (pc * ownCross P i 1 ψ + (copyWeight n pc - viability k pc P) * average P ψ +
        mutantBias pc P i ψ) := by
  have hf := full_mean hkn pc P hP ψ haccept
  rw [mean_split pc i ψ P, ImmigrationMean.mutant_mean pc i ψ hbit haccept P,
    offspring_decomposition pc hpc P i 1 ψ] at hf
  have hfrac := fraction_sum i P
  have hmpos : (0 : ℝ) < (μ : ℕ) + 1 := by positivity
  have hcancel : ((μ : ℕ) + 1 : ℝ) *
      (((μ : ℕ) / ((μ : ℕ) + 1 : ℝ) * fraction i 0 P) * fromOpposite pc P i 1 ψ) =
      (μ : ℕ) * fraction i 0 P * fromOpposite pc P i 1 ψ := by field_simp
  rw [mul_add, hcancel] at hf
  have hfrac0 : fraction i 0 P = 1 - fraction i 1 P := by linarith
  rw [hfrac0] at hf
  unfold copyWeight mutantBias cloneBias
  nlinarith

lemma resident_mean (hkn : k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (P : Population n μ) (hP : plateauPopulation k P) (i : Fin n) (ψ : BitString n → ℝ)
    (hbit : ∀ z, z i ≠ 0 → ψ z = 0) (haccept : ∀ z, ¬onPlateau k z → ψ z = 0) :
    ((μ : ℕ) + 1 : ℝ) * mean (eventLaw pc P) (nonImmChange k i ψ P) =
      (μ : ℕ) * (pc * ownCross P i 0 ψ + (copyWeight n pc - viability k pc P) * average P ψ +
        residentBias k pc P i ψ) := by
  have hf := full_mean hkn pc P hP ψ haccept
  rw [mean_split pc i ψ P, ImmigrationMean.resident_mean pc i ψ hbit P,
    offspring_decomposition pc hpc P i 0 ψ] at hf
  have hmpos : (0 : ℝ) < (μ : ℕ) + 1 := by positivity
  have hcancel : ((μ : ℕ) + 1 : ℝ) *
      (-((μ : ℕ) / ((μ : ℕ) + 1 : ℝ) * average P ψ) * fromOpposite pc P i 1 (mutantAccept k i)) =
      -(μ : ℕ) * average P ψ * fromOpposite pc P i 1 (mutantAccept k i) := by field_simp
  rw [mul_add, hcancel] at hf
  unfold copyWeight residentBias cloneBias
  nlinarith

end
end Lax343628Proofs.ClassMeanDynamics

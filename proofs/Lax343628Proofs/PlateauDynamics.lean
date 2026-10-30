import Lax343628Proofs.Plateau
import Lax343628Proofs.Deletion

namespace Lax343628Proofs.PlateauDynamics

open Lax343628.Algorithm Lax343628Proofs.Dynamics Lax343628Proofs.Sampling
open Lax343628Proofs.Deletion Lax343628Proofs.Plateau
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def onPlateau {n : ℕ} (k : ℕ) (x : BitString n) : Prop := ones x = n - k

def plateauPopulation {n : ℕ} {μ : ℕ+} (k : ℕ) (P : Population n μ) : Prop :=
  ∀ i, onPlateau k (P i)

lemma plateau_fitness {n k : ℕ} (hk : k ≤ n) (x : BitString n) (hx : onPlateau k x) :
    jump k x = (n : ℝ) := by
  have hx' : ones x = n - k := hx
  simp only [jump, hx', le_refl, true_or, if_true]
  congr 1
  omega

lemma off_plateau_fitness_lt {n k : ℕ} (hk : k ≤ n) (x : BitString n)
    (hx : ¬onPlateau k x) (hopt : x ≠ optimum n) : jump k x < (n : ℝ) := by
  have hxn := ones_le x
  have hxn' : ones x ≠ n := fun h ↦ hopt (eq_optimum_of_ones_eq x h)
  have hx' : ones x ≠ n - k := hx
  unfold jump
  split_ifs with h
  · have hval : k + ones x < n := by omega
    exact_mod_cast hval
  · have hval : n - ones x < n := by omega
    exact_mod_cast hval

lemma plateau_insert_rejected {n k : ℕ} {μ : ℕ+} (hk : k ≤ n)
    (P : Population n μ) (hP : plateauPopulation k P) (z : BitString n)
    (hz : ¬onPlateau k z) (hopt : z ≠ optimum n) :
    Lax343628Proofs.Sampling.insert (jump k) P z = PMF.pure P :=
  insert_rejected (jump k) P z n (fun i ↦ plateau_fitness hk (P i) (hP i))
    (off_plateau_fitness_lt hk z hz hopt)

lemma replace_onPlateau {n k : ℕ} {μ : ℕ+} (P : Population n μ)
    (hP : plateauPopulation k P) (z : BitString n) (hz : onPlateau k z)
    (d : Fin ((μ : ℕ) + 1)) : plateauPopulation k (replace P z d) := by
  intro i
  unfold replace
  split_ifs with h
  · by_cases hi : i = (⟨d.val, h⟩ : Fin (μ : ℕ))
    · subst i
      rw [Function.update_self]
      exact hz
    · rw [Function.update_of_ne hi]
      exact hP i
  · exact hP i

lemma plateau_step_invariant {n k : ℕ} {μ : ℕ+} (hk : 0 < k) (hkn : k ≤ n)
    (p_c : ℝ) (P : Population n μ) (hP : plateauPopulation k P) (Q : Population n μ)
    (hQ : Q ∈ (step (jump k) p_c P).support) (hmiss : Q ∈ missing) : plateauPopulation k Q := by
  rw [step_eq] at hQ
  obtain ⟨z, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
  by_cases hz : onPlateau k z
  · obtain ⟨d, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    have hQ := (PMF.mem_support_pure_iff _ Q).mp hQ
    subst Q
    exact replace_onPlateau P hP z hz d
  · by_cases hopt : z = optimum n
    · subst z
      exact False.elim (insert_optimum hk P Q hQ hmiss)
    · rw [plateau_insert_rejected hkn P hP z hz hopt] at hQ
      have hQ := (PMF.mem_support_pure_iff _ Q).mp hQ
      subst Q
      exact hP

lemma plateau_insertion_drift {n k : ℕ} {μ : ℕ+} (hkn : k ≤ n) (ψ : BitString n → ℝ)
    (P : Population n μ) (hP : plateauPopulation k P) (z : BitString n)
    (hz : onPlateau k z) :
    Lax343628Proofs.FiniteDrift.mean (Lax343628Proofs.Sampling.insert (jump k) P z)
      (fun Q ↦ total ψ Q - total ψ P) =
        ((μ : ℕ) * ψ z - total ψ P) / ((μ : ℕ) + 1) :=
  insert_drift_equal_fitness ψ (jump k) P z n (fun i ↦ plateau_fitness hkn (P i) (hP i))
    (plateau_fitness hkn z hz)

def auxiliaryInsert {n : ℕ} {μ : ℕ+} (k : ℕ) (P : Population n μ) (z : BitString n) :
    PMF (Population n μ) :=
  if onPlateau k z then Lax343628Proofs.Sampling.insert (jump k) P z else PMF.pure P

def auxiliaryStep {n : ℕ} {μ : ℕ+} (k : ℕ) (p_c : ℝ) (P : Population n μ) :
    PMF (Population n μ) := (offspring p_c P).bind (auxiliaryInsert k P)

lemma auxiliary_invariant {n k : ℕ} {μ : ℕ+} (p_c : ℝ) (P : Population n μ)
    (hP : plateauPopulation k P) (Q : Population n μ)
    (hQ : Q ∈ (auxiliaryStep k p_c P).support) : plateauPopulation k Q := by
  obtain ⟨z, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
  unfold auxiliaryInsert at hQ
  split_ifs at hQ with hz
  · obtain ⟨d, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    have hQ := (PMF.mem_support_pure_iff _ Q).mp hQ
    subst Q
    exact replace_onPlateau P hP z hz d
  · have hQ := (PMF.mem_support_pure_iff _ Q).mp hQ
    subst Q
    exact hP

lemma auxiliary_statistic_drift {n k : ℕ} {μ : ℕ+} (hkn : k ≤ n) (ψ : BitString n → ℝ)
    (p_c : ℝ) (P : Population n μ) (hP : plateauPopulation k P) :
    Lax343628Proofs.FiniteDrift.mean (auxiliaryStep k p_c P)
      (fun Q ↦ total ψ Q - total ψ P) =
        ((μ : ℕ) * Lax343628Proofs.FiniteDrift.mean (offspring p_c P)
          (fun z ↦ if onPlateau k z then ψ z else 0) -
          total ψ P * Lax343628Proofs.FiniteDrift.mean (offspring p_c P)
            (fun z ↦ if onPlateau k z then 1 else 0)) / ((μ : ℕ) + 1) := by
  open Lax343628Proofs.FiniteDrift in
  rw [auxiliaryStep, mean_bind]
  have heq : (fun z ↦ Lax343628Proofs.FiniteDrift.mean (auxiliaryInsert k P z)
      (fun Q ↦ total ψ Q - total ψ P)) = (fun z ↦
      (((μ : ℕ) + 1 : ℝ)⁻¹) *
        ((μ : ℕ) * (if onPlateau k z then ψ z else 0) -
          total ψ P * (if onPlateau k z then 1 else 0))) := by
    funext z
    unfold auxiliaryInsert
    split_ifs with hz
    · rw [plateau_insertion_drift hkn ψ P hP z hz]
      ring
    · rw [Lax343628Proofs.FiniteDrift.mean_pure]
      ring
  open Lax343628Proofs.FiniteDrift in
  rw [heq, mean_mul, mean_sub, mean_mul, mean_mul]
  ring

end
end Lax343628Proofs.PlateauDynamics

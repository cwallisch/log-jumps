import Lax343628Proofs.PhysicalOffspring
import Lax343628Proofs.PlateauDynamics
import Lax343628Proofs.ActualBirthKernels

namespace Lax343628Proofs.TaggedDynamics

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.PhysicalOffspring Lax343628Proofs.PlateauDynamics
open Lax343628Proofs.Deletion Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.EmpiricalKernels
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Event (n : ℕ) (μ : ℕ+) := (Fin (μ : ℕ) × Fin (μ : ℕ)) × BitString n × Fin ((μ : ℕ) + 1)

def parentLaw (μ : ℕ+) (pc : ℝ) : PMF (Fin (μ : ℕ) × Fin (μ : ℕ)) :=
  (coin pc).bind fun b ↦ if b = 1 then PMF.uniformOfFintype _ else
    (PMF.uniformOfFintype (Fin (μ : ℕ))).map (fun u ↦ (u, u))

def eventLaw {n : ℕ} {μ : ℕ+} (pc : ℝ) (P : Population n μ) : PMF (Event n μ) := do
  let uv ← parentLaw μ pc
  let z ← pairMutation (P uv.1) (P uv.2) (1 / n)
  let d ← PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))
  pure (uv, z, d)

def next {n : ℕ} {μ : ℕ+} (k : ℕ) (P : Population n μ) (E : Event n μ) : Population n μ :=
  if onPlateau k E.2.1 then replace P E.2.1 E.2.2 else P

lemma parentLaw_offspring {n : ℕ} {μ : ℕ+} (pc : ℝ) (P : Population n μ) :
    (parentLaw μ pc).bind (fun uv ↦ pairMutation (P uv.1) (P uv.2) (1 / n)) = offspring pc P := by
  rw [offspring_split]
  simp only [parentLaw, PMF.bind_bind]
  congr 1
  funext b
  split_ifs <;> simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_apply]

lemma eventLaw_child {n : ℕ} {μ : ℕ+} (pc : ℝ) (P : Population n μ) :
    (eventLaw pc P).map (fun E ↦ E.2.1) = offspring pc P := by
  rw [← parentLaw_offspring]
  simp only [eventLaw, Bind.bind, Pure.pure, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_apply, PMF.bind_const, PMF.bind_pure]

lemma auxiliaryInsert_uniform {n k : ℕ} {μ : ℕ+} (hk : k ≤ n)
    (P : Population n μ) (hP : plateauPopulation k P) (z : BitString n) :
    auxiliaryInsert k P z = (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))).map
      (fun d ↦ if onPlateau k z then replace P z d else P) := by
  by_cases hz : onPlateau k z
  · have hfit : ∀ d, jump k (Fin.lastCases z P d) = (n : ℝ) := by
      intro d
      refine Fin.lastCases ?_ (fun u ↦ ?_) d
      · simpa using plateau_fitness hk z hz
      · simpa using plateau_fitness hk (P u) (hP u)
    simp only [auxiliaryInsert, if_pos hz, Sampling.insert, Bind.bind, Pure.pure,
      deletion_uniform (jump k) (Fin.lastCases z P) n hfit]
    rfl
  · simp [auxiliaryInsert, hz, PMF.map, Function.comp_def, PMF.bind_const]

lemma eventLaw_next {n k : ℕ} {μ : ℕ+} (hk : k ≤ n) (pc : ℝ)
    (P : Population n μ) (hP : plateauPopulation k P) :
    (eventLaw pc P).map (next k P) = auxiliaryStep k pc P := by
  rw [auxiliaryStep, ← parentLaw_offspring]
  simp only [eventLaw, Bind.bind, Pure.pure, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_apply]
  congr 1
  funext uv
  congr 1
  funext z
  rw [auxiliaryInsert_uniform hk P hP z]
  rfl

lemma mean_parentLaw {μ : ℕ+} (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (f : Fin (μ : ℕ) × Fin (μ : ℕ) → ℝ) :
    mean (parentLaw μ pc) f = pc * mean (PMF.uniformOfFintype _) f +
      (1 - pc) * mean (PMF.uniformOfFintype (Fin (μ : ℕ))) (fun u ↦ f (u, u)) := by
  rw [parentLaw, mean_bind, mean_coin pc hpc]
  simp only [if_neg (show (0 : Fin 2) ≠ 1 by decide), ite_true, mean_map]

end
end Lax343628Proofs.TaggedDynamics

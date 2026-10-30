import Lax343628Proofs.DrivenNoise
import Lax343628Proofs.KernelProjection

namespace Lax343628Proofs.KilledSampling

open Lax343628.Algorithm Lax343628Proofs.DrivenNoise Lax343628Proofs.TaggedDynamics
open Lax343628Proofs.Sampling Lax343628Proofs.PlateauDynamics Lax343628Proofs.Dynamics
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} {n k : ℕ} {mu : ℕ+}

lemma map_on_support (p : PMF α) (f g : α → β) (hf : ∀ x ∈ p.support, f x = g x) :
    p.map f = p.map g := by
  apply PMF.ext
  intro y
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : p x = 0
  · simp only [hx, ite_self]
  · rw [hf x hx]

lemma map_pure_on_support (p : PMF α) (f : α → β) (b : β) (hf : ∀ x ∈ p.support, f x = b) :
    p.map f = PMF.pure b := by
  rw [map_on_support p f (fun _ ↦ b) hf]
  exact PMF.map_const p b

def collapse (P : Population n mu) : Option (Population n mu) := if P ∈ missing then some P else none

def kernel (k : ℕ) (pc : ℝ) : Option (Population n mu) → PMF (Option (Population n mu))
  | none => PMF.pure none
  | some P => (step (jump k) pc P).map collapse

lemma physical_map (hk : 0 < k) (pc : ℝ) (P : Population n mu) :
    (step (jump k) pc P).map collapse = kernel k pc (collapse P) := by
  by_cases hp : P ∈ missing
  · simp only [collapse, if_pos hp, kernel]
  · simp only [collapse, if_neg hp, kernel]
    apply map_pure_on_support
    intro Q hQ
    exact if_neg (step_retains_optimum hk pc P hp Q hQ)

lemma plateau_missing (hk : 0 < k) (hkn : k ≤ n) (P : Population n mu) (hP : plateauPopulation k P) :
    P ∈ missing := by
  intro u heq
  have hh := hP u
  change ones (P u) = n - k at hh
  rw [heq, ones_optimum] at hh
  omega

lemma insert_nonopt (hkn : k ≤ n) (P : Population n mu) (hP : plateauPopulation k P)
    (z : BitString n) (hz : z ≠ optimum n) : Sampling.insert (jump k) P z = auxiliaryInsert k P z := by
  unfold auxiliaryInsert
  split_ifs with hplat
  · rfl
  · exact plateau_insert_rejected hkn P hP z hplat hz

lemma auxiliary_missing (hk : 0 < k) (hkn : k ≤ n) (P : Population n mu) (hP : plateauPopulation k P)
    (z : BitString n) (Q : Population n mu) (hQ : Q ∈ (auxiliaryInsert k P z).support) : Q ∈ missing := by
  apply plateau_missing hk hkn
  unfold auxiliaryInsert at hQ
  split_ifs at hQ with hz
  · obtain ⟨d, _, hd⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    have he := (PMF.mem_support_pure_iff _ _).mp hd
    subst Q
    exact replace_onPlateau P hP z hz d
  · have he := (PMF.mem_support_pure_iff _ _).mp hQ
    subst Q
    exact hP

lemma physical_killed (hk : 0 < k) (hkn : k ≤ n) (pc : ℝ) (P : Population n mu)
    (hP : plateauPopulation k P) :
    (step (jump k) pc P).map collapse =
      (offspring pc P).bind (fun z ↦ if z = optimum n then PMF.pure none else
        (auxiliaryInsert k P z).map some) := by
  rw [step_eq, PMF.map_bind]
  congr 1
  funext z
  by_cases hz : z = optimum n
  · subst z
    rw [if_pos rfl]
    apply map_pure_on_support
    intro Q hQ
    exact if_neg (Plateau.insert_optimum hk P Q hQ)
  · rw [if_neg hz, insert_nonopt hkn P hP z hz]
    apply map_on_support
    intro Q hQ
    exact if_pos (auxiliary_missing hk hkn P hP z Q hQ)

end
end Lax343628Proofs.KilledSampling

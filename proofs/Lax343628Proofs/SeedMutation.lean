import Lax343628Proofs.SeedSurplus
import Lax343628Proofs.ClassMeanDynamics

namespace Lax343628Proofs.SeedMutation

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.SeedGeometry
open Lax343628Proofs.ColumnKernels Lax343628Proofs.SeedIdeal Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.PhysicalOffspring Lax343628Proofs.EmpiricalKernels
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+} {i : Fin n}

lemma family_bounds (C : Finset (Fin n)) (z : BitString n) :
    0 ≤ liftClass (familyClass (r := r) (i := i) C) z ∧ liftClass (familyClass (r := r) (i := i) C) z ≤ 1 := by
  unfold liftClass familyClass
  split_ifs <;> norm_num

lemma family_average (C : Finset (Fin n)) (P : Population n mu)
    (hP : ∀ u, (zeros (P u)).card = r + 1) :
    ClassBirthEstimates.average P (liftClass (familyClass (r := r) (i := i) C)) = phi C i P := by
  apply congrArg (mean (PMF.uniformOfFintype (Fin (mu : ℕ))))
  funext u
  unfold liftClass familyClass family
  by_cases hb : P u i = 1
  · simp only [hb, and_true, hP u, dite_true]
  · simp only [hb, and_false, if_false, dite_false]

lemma clone_mean (P : Population n mu) (f : BitString n → ℝ) :
    mean (offspring 0 P) f = mean (PMF.uniformOfFintype (Fin (mu : ℕ)))
      (fun u ↦ mean (pairMutation (P u) (P u) (1 / n)) f) := by
  rw [offspring_split, SuppressedRegions.coin_zero_rate, PMF.pure_bind,
    if_neg (by decide : (0 : Fin 2) ≠ 1), mean_bind]

lemma offspring_affine (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (P : Population n mu) (f : BitString n → ℝ) :
    mean (offspring pc P) f = pc * mean (offspring 1 P) f + (1 - pc) * mean (offspring 0 P) f := by
  rw [offspring_split, mean_bind, mean_coin pc hpc]
  norm_num only [if_true, if_neg (by decide : (0 : Fin 2) ≠ 1), mean_bind]
  rw [clone_mean, SeedViability.crossover_mean]
  congr 1
  congr 1
  exact mean_uniform_pair (fun u v ↦ mean (pairMutation (P u) (P v) (1 / n)) f)

lemma clone_family_lower (hn : 2 ≤ n) (C : Finset (Fin n)) (P : Population n mu)
    (hP : ∀ u, (zeros (P u)).card = r + 1) :
    -phi C i P * ((r + 1 : ℝ) / n) ≤
      mean (offspring 0 P) (liftClass (familyClass (r := r) (i := i) C)) -
        phi C i P * mean (offspring 0 P) (BirthMass.plateauTest (r + 1)) := by
  let c := (1 - 1 / (n : ℝ)) ^ n
  have hb (u : Fin (mu : ℕ)) : c * liftClass (familyClass (r := r) (i := i) C) (P u) ≤
      mean (pairMutation (P u) (P u) (1 / n)) (liftClass (familyClass (r := r) (i := i) C)) := by
    have hh := (CloneMutationTest.clone_error hn (P u) (hP u) (liftClass (familyClass (r := r) (i := i) C)) 1 (by norm_num)
      (family_bounds C) (NormalizedPrivate.liftClass_exact_support _)).1
    change 0 ≤ _ - c * _ at hh
    linarith
  have hv (u : Fin (mu : ℕ)) : mean (pairMutation (P u) (P u) (1 / n)) (BirthMass.plateauTest (r + 1)) ≤
      c + ((r + 1 : ℝ) / n) := by
    have hh := (CloneMutationTest.clone_error hn (P u) (hP u) (BirthMass.plateauTest (r + 1)) 1 (by norm_num)
      (fun z ↦ by unfold BirthMass.plateauTest; split_ifs <;> norm_num) (fun z hz ↦ if_neg hz)).2
    have hself : BirthMass.plateauTest (r + 1) (P u) = 1 := if_pos (hP u)
    rw [hself, mul_one, one_mul] at hh
    norm_num only [Nat.cast_add, Nat.cast_one] at hh
    linarith
  have hbirth := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) hb
  rw [mean_mul, ← clone_mean] at hbirth
  change c * ClassBirthEstimates.average P _ ≤ _ at hbirth
  rw [family_average C P hP] at hbirth
  have hviable := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) hv
  rw [mean_const, ← clone_mean] at hviable
  have hphi : 0 ≤ phi C i P := mean_nonneg _ (fun _ ↦ by split_ifs <;> norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hviable hphi
  nlinarith

end
end Lax343628Proofs.SeedMutation

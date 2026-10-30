import Lax343628Proofs.SeedMutation
import Lax343628Proofs.SparseDynamics

namespace Lax343628Proofs.SeedDrift

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.SeedGeometry
open Lax343628Proofs.ColumnKernels Lax343628Proofs.SeedIdeal Lax343628Proofs.SeedMutation
open Lax343628Proofs.FiniteDrift Lax343628Proofs.ClassMeanDynamics Lax343628Proofs.ClassIncrements
open Lax343628Proofs.TaggedDynamics
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+} {i : Fin n}

lemma plateau_test_eq {k : ℕ} (hkn : k ≤ n) : BirthMass.plateauTest (n := n) k =
    (fun z ↦ if PlateauDynamics.onPlateau k z then 1 else 0) := by
  funext z
  have hh : (zeros z).card = k ↔ PlateauDynamics.onPlateau k z := by
    rw [card_zeros]
    have hz := Dynamics.ones_le z
    unfold PlateauDynamics.onPlateau
    omega
  simp only [BirthMass.plateauTest, hh]

lemma offspring_surplus (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r)
    (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = r + 1)
    (theta : ℝ) (htheta : 0 ≤ theta) (hflat : ∀ j, j ∉ C → ClassChannels.fraction j 0 P ≤ theta)
    (hrho : rho C P ≤ 1 / 4)
    (hcost : 2 * (r + 1 : ℝ) * theta + 2 * rho C P + 256 * (r + 1 : ℝ) ^ 2 / n + 1 / n ≤
      Real.exp (-1) / (64 * (r + 1 : ℝ) ^ 2))
    (hmutation : (r + 1 : ℝ) / n ≤ pc * Real.exp (-1) / (128 * (r + 1 : ℝ) ^ 2)) :
    phi C i P * (pc * Real.exp (-1) / (128 * (r + 1 : ℝ) ^ 2)) ≤
      mean (offspring pc P) (liftClass (familyClass (r := r) (i := i) C)) -
        phi C i P * mean (offspring pc P) (BirthMass.plateauTest (r + 1)) := by
  have hc := SeedSurplus.crossover_positive hr hn C hi hC P hP theta htheta hflat hrho hcost
  have hm := clone_family_lower (i := i) (by omega : 2 ≤ n) C P hP
  have hphi : 0 ≤ phi C i P := mean_nonneg _ (fun _ ↦ by split_ifs <;> norm_num)
  have hcross := mul_le_mul_of_nonneg_left hc hpc.1
  have hclone := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hpc.2)
  have hmut := mul_le_mul_of_nonneg_left hmutation hphi
  have hloss : -phi C i P * ((r + 1 : ℝ) / n) ≤
      (1 - pc) * (-phi C i P * ((r + 1 : ℝ) / n)) := by
    nlinarith [mul_nonneg hpc.1 (mul_nonneg hphi (show (0 : ℝ) ≤ (r + 1 : ℝ) / n by positivity))]
  have hclone' := hloss.trans hclone
  have heq : pc * (phi C i P * (Real.exp (-1) / (64 * (r + 1 : ℝ) ^ 2))) =
      2 * (phi C i P * (pc * Real.exp (-1) / (128 * (r + 1 : ℝ) ^ 2))) := by field_simp; ring
  rw [heq] at hcross
  rw [offspring_affine pc hpc P (liftClass (familyClass (r := r) (i := i) C)),
    offspring_affine pc hpc P (BirthMass.plateauTest (r + 1))]
  nlinarith only [hcross, hclone', hmut]

lemma family_drift (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r)
    (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = r + 1)
    (theta : ℝ) (htheta : 0 ≤ theta) (hflat : ∀ j, j ∉ C → ClassChannels.fraction j 0 P ≤ theta)
    (hrho : rho C P ≤ 1 / 4)
    (hcost : 2 * (r + 1 : ℝ) * theta + 2 * rho C P + 256 * (r + 1 : ℝ) ^ 2 / n + 1 / n ≤
      Real.exp (-1) / (64 * (r + 1 : ℝ) ^ 2))
    (hmutation : (r + 1 : ℝ) / n ≤ pc * Real.exp (-1) / (128 * (r + 1 : ℝ) ^ 2)) :
    phi C i P * (pc * Real.exp (-1) / (256 * (r + 1 : ℝ) ^ 2)) ≤
      mean (eventLaw pc P) (change (r + 1) (liftClass (familyClass (r := r) (i := i) C)) P) := by
  have hkn : r + 1 ≤ n := by omega
  have hp : PlateauDynamics.plateauPopulation (r + 1) P := fun u ↦
    PlateauKernelApproximation.plateau_of_zero_card hkn _ (hP u)
  have hmean := full_mean hkn pc P hp (liftClass (familyClass (r := r) (i := i) C))
    (SparseDynamics.lift_off_plateau hkn _)
  unfold viability at hmean
  rw [← plateau_test_eq hkn, family_average C P hP] at hmean
  have hgap := offspring_surplus hr hn pc hpc C hi hC P hP theta htheta hflat hrho hcost hmutation
  have heq : phi C i P * (pc * Real.exp (-1) / (128 * (r + 1 : ℝ) ^ 2)) =
      2 * (phi C i P * (pc * Real.exp (-1) / (256 * (r + 1 : ℝ) ^ 2))) := by field_simp; ring
  rw [heq] at hgap
  have hmR : (1 : ℝ) ≤ (mu : ℕ) := by exact_mod_cast mu.pos
  have hscale := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (mu : ℕ))
  have hnon : 0 ≤ phi C i P * (pc * Real.exp (-1) / (256 * (r + 1 : ℝ) ^ 2)) :=
    mul_nonneg (mean_nonneg _ (fun _ ↦ by split_ifs <;> norm_num))
      (div_nonneg (mul_nonneg hpc.1 (Real.exp_pos _).le) (by positivity))
  apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (mu : ℕ) + 1)).mp
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ ((mu : ℕ) : ℝ) - 1 by linarith) hnon]

end
end Lax343628Proofs.SeedDrift

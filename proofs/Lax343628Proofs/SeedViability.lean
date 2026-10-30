import Lax343628Proofs.SeedPairs
import Lax343628Proofs.SeedOverlap

namespace Lax343628Proofs.SeedViability

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.SeedGeometry
open Lax343628Proofs.SeedPairs Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.EmpiricalKernels Lax343628Proofs.PhysicalOffspring Lax343628Proofs.CurveBounds
open Lax343628Proofs.ClassChannels
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+} {i : Fin n}

lemma crossover_mean (P : Population n mu) (f : BitString n → ℝ) :
    mean (offspring 1 P) f = pairMean (PMF.uniformOfFintype (Fin (mu : ℕ)))
      (fun u v ↦ mean (pairMutation (P u) (P v) (1 / n)) f) := by
  rw [offspring_split, SuppressedRegions.coin_one_rate, PMF.pure_bind, if_pos rfl, mean_bind]
  exact mean_uniform_pair (fun u v ↦ mean (pairMutation (P u) (P v) (1 / n)) f)

lemma ordinary_pair_mass (C : Finset (Fin n)) (P : Population n mu) :
    pairMean (PMF.uniformOfFintype (Fin (mu : ℕ)))
      (fun u v ↦ if ordinary C (P u) ∧ ordinary C (P v) then 1 else 0) = (1 - rho C P) ^ 2 := by
  have heq (u v : Fin (mu : ℕ)) : (if ordinary C (P u) ∧ ordinary C (P v) then (1 : ℝ) else 0) =
      (if ordinary C (P u) then 1 else 0) * (if ordinary C (P v) then 1 else 0) := by
    by_cases hu : ordinary C (P u) <;> by_cases hv : ordinary C (P v) <;> simp [hu, hv]
  unfold pairMean
  simp_rw [heq, mean_mul, ordinary_mean]
  rw [EmpiricalSampling.mean_mul_right, ordinary_mean]
  ring

lemma bad_pair_overlap (C : Finset (Fin n)) (P : Population n mu)
    (hP : ∀ u, (zeros (P u)).card = r + 1) (theta : ℝ) (htheta : 0 ≤ theta)
    (hflat : ∀ j, j ∉ C → fraction j 0 P ≤ theta) :
    pairMean (PMF.uniformOfFintype (Fin (mu : ℕ)))
      (fun u v ↦ if ordinary C (P u) ∧ ordinary C (P v) ∧ ¬Disjoint (privateZeros C (P u)) (privateZeros C (P v)) then 1 else 0) ≤
        (r + 1 : ℝ) * theta := by
  have hp (u : Fin (mu : ℕ)) :
      mean (PMF.uniformOfFintype (Fin (mu : ℕ)))
        (fun v ↦ if ordinary C (P u) ∧ ordinary C (P v) ∧ ¬Disjoint (privateZeros C (P u)) (privateZeros C (P v)) then 1 else 0) ≤
      ((r + 1 : ℝ) * theta) * (if ordinary C (P u) then 1 else 0) := by
    by_cases hu : ordinary C (P u)
    · simp only [hu, true_and, if_true, mul_one]
      have hh := fixed_overlap_flat C (privateZeros C (P u)) P theta Finset.sdiff_disjoint hflat
      rw [ordinary_private_card C (P u) (hP u) hu] at hh
      have hcard : ((r + 1 - C.card : ℕ) : ℝ) ≤ (r + 1 : ℝ) := by exact_mod_cast Nat.sub_le (r + 1) C.card
      exact hh.trans (mul_le_mul_of_nonneg_right hcard htheta)
    · simp only [hu, false_and, if_false, mean_const, mul_zero, le_refl]
  have hh := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) hp
  rw [mean_mul, ordinary_mean] at hh
  have hprod := mul_le_mul_of_nonneg_left (show 1 - rho C P ≤ 1 by linarith [(rho_bounds C P).1])
    (show 0 ≤ (r + 1 : ℝ) * theta by positivity)
  change pairMean _ _ ≤ _ at hh
  exact hh.trans (by simpa only [mul_one] using hprod)

lemma crossover_upper (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r + 1)
    (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = r + 1)
    (theta : ℝ) (htheta : 0 ≤ theta) (hflat : ∀ j, j ∉ C → fraction j 0 P ≤ theta) :
    mean (offspring 1 P) (BirthMass.plateauTest (r + 1)) ≤
      Real.exp (-1) * q (r + 1 - C.card) * (1 - rho C P) ^ 2 +
      (r + 1 : ℝ) * theta + 2 * rho C P + (128 * (r + 1 : ℝ) ^ 2 / n + 1 / n) := by
  let p := PMF.uniformOfFintype (Fin (mu : ℕ))
  let A := Real.exp (-1) * q (r + 1 - C.card)
  let err := 128 * (r + 1 : ℝ) ^ 2 / n + 1 / n
  let O := fun u v : Fin (mu : ℕ) ↦ if ordinary C (P u) ∧ ordinary C (P v) then (1 : ℝ) else 0
  let bad := fun u v : Fin (mu : ℕ) ↦ if ordinary C (P u) ∧ ordinary C (P v) ∧
    ¬Disjoint (privateZeros C (P u)) (privateZeros C (P v)) then (1 : ℝ) else 0
  have hA : 0 ≤ A := by dsimp [A, q]; exact mul_nonneg (Real.exp_pos _).le (profile_pos _ _).le
  have herr : 0 ≤ err := by dsimp [err]; positivity
  have hv (u v : Fin (mu : ℕ)) : mean (pairMutation (P u) (P v) (1 / n)) (BirthMass.plateauTest (r + 1)) ≤ 1 :=
    (mean_mono _ (fun z ↦ show BirthMass.plateauTest (r + 1) z ≤ 1 by unfold BirthMass.plateauTest; split_ifs <;> norm_num)).trans_eq (mean_const _ 1)
  have hp (u v : Fin (mu : ℕ)) : mean (pairMutation (P u) (P v) (1 / n)) (BirthMass.plateauTest (r + 1)) ≤
      ((A * O u v + bad u v) + (1 - O u v)) + err * O u v := by
    by_cases ho : ordinary C (P u) ∧ ordinary C (P v)
    · by_cases hd : Disjoint (privateZeros C (P u)) (privateZeros C (P v))
      · have hb := ordinary_upper hr hn C hi hC (P u) (P v) (hP u) (hP v) ho.1 ho.2 hd
        have hbad : ¬(ordinary C (P u) ∧ ordinary C (P v) ∧ ¬Disjoint (privateZeros C (P u)) (privateZeros C (P v))) := by tauto
        simp only [O, bad, if_pos ho, if_neg hbad, mul_one, add_zero, sub_self]
        dsimp [A, err]
        linarith
      · have hbad : ordinary C (P u) ∧ ordinary C (P v) ∧ ¬Disjoint (privateZeros C (P u)) (privateZeros C (P v)) := ⟨ho.1, ho.2, hd⟩
        simp only [O, bad, if_pos ho, if_pos hbad, mul_one, sub_self, add_zero]
        linarith [hv u v]
    · have hbad : ¬(ordinary C (P u) ∧ ordinary C (P v) ∧ ¬Disjoint (privateZeros C (P u)) (privateZeros C (P v))) := by tauto
      simp only [O, bad, if_neg ho, if_neg hbad, mul_zero, add_zero, sub_zero, zero_add]
      exact hv u v
  have hh := pairMean_mono p hp
  simp only [pairMean_add, pairMean_sub, pairMean_mul, pairMean_const] at hh
  have hO : pairMean p O = (1 - rho C P) ^ 2 := ordinary_pair_mass C P
  have hbad : pairMean p bad ≤ (r + 1 : ℝ) * theta := bad_pair_overlap C P hP theta htheta hflat
  rw [hO] at hh
  have hrho := rho_bounds C P
  have hsquare : (1 - rho C P) ^ 2 ≤ 1 := by nlinarith
  have heprod := mul_le_mul_of_nonneg_left hsquare herr
  rw [mul_one] at heprod
  rw [crossover_mean]
  change pairMean p _ ≤ _
  dsimp [A, err] at hh heprod
  nlinarith [sq_nonneg (rho C P)]

end
end Lax343628Proofs.SeedViability

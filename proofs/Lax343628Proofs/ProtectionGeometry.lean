import Lax343628Proofs.Odds
import Lax343628Proofs.ColumnEndpoint
import Lax343628Proofs.FirstExit

namespace Lax343628Proofs.ProtectionGeometry

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.ClassMeanDynamics
open Lax343628Proofs.DrivenNoise Lax343628Proofs.ColumnBlock Lax343628Proofs.ColumnEndpoint
open Lax343628Proofs.Trajectories
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R : ℕ} {mu : ℕ+}

lemma odds_lt_inv (i : Fin n) (P : Population n mu) (u : ℝ) (hu : 0 < u)
    (ha : u ≤ fraction i 0 P) : Odds.value i P < 1 / u := by
  have ha0 : 0 < fraction i 0 P := hu.trans_le ha
  have hf := fraction_bounds i 1 P
  have hs := fraction_sum i P
  unfold Odds.value
  apply (div_lt_div_iff₀ ha0 hu).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ 1 - fraction i 1 P by linarith)]

lemma initial_odds_lower (i : Fin n) (P : Population n mu) (u : ℝ)
    (hu : 0 < u) (huquarter : u ≤ 1 / 4)
    (ha : u ≤ fraction i 0 P ∧ fraction i 0 P ≤ 2 * u) :
    1 / (4 * u) ≤ Odds.value i P := by
  have ha0 : 0 < fraction i 0 P := hu.trans_le ha.1
  have hs := fraction_sum i P
  unfold Odds.value
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * u) ha0).mpr
  nlinarith [mul_nonneg hu.le (show 0 ≤ 1 / 2 - fraction i 0 P by linarith)]

lemma protection_thresholds (i : Fin n) (P : Population n mu) (u theta D : ℝ)
    (hu : 0 < u) (huquarter : u ≤ 1 / 4) (hD : 0 < D) (htheta : theta = 16 * D * u)
    (ha : u ≤ fraction i 0 P ∧ fraction i 0 P ≤ 2 * u) :
    1 / theta ≤ Odds.value i P / (4 * D) ∧ 1 / u < 8 * Odds.value i P := by
  have hlo := initial_odds_lower i P u hu huquarter ha
  constructor
  · have hh := div_le_div_of_nonneg_right hlo (show 0 ≤ 4 * D by positivity)
    have heq : 1 / (4 * u) / (4 * D) = 1 / theta := by rw [htheta]; field_simp; ring
    rwa [heq] at hh
  · have hh := mul_le_mul_of_nonneg_left hlo (show (0 : ℝ) ≤ 8 by norm_num)
    have hstrict : 1 / u < 8 * (1 / (4 * u)) := by
      have hpos : 0 < 1 / u := by positivity
      have heq : 8 * (1 / (4 * u)) = 2 * (1 / u) := by ring
      rw [heq]
      linarith
    exact hstrict.trans_le hh

lemma stay_above_failure (i : Fin n) (u theta D omega : ℝ) (hu : 0 < u)
    (huquarter : u ≤ 1 / 4) (hD : 0 < D) (htheta : theta = 16 * D * u)
    (h : Fin (R + 1) → State n mu)
    (hstart : fraction i 0 (h 0).1 ≤ 2 * u)
    (hband : ∀ j, u ≤ fraction i 0 (h j).1)
    (hcap : ∀ j, cap omega (h j).1) :
    ¬good i (Odds.value i (h 0).1 / (4 * D)) (8 * Odds.value i (h 0).1) omega
      (frozen {S | active k i (Odds.value i (h 0).1 / (4 * D))
        (8 * Odds.value i (h 0).1) omega S.1} h) := by
  have hthreshold := protection_thresholds i (h 0).1 u theta D hu huquarter hD htheta
    ⟨hband 0, hstart⟩
  obtain ⟨j, hj⟩ := frozen_mem_range
    {S : State n mu | active k i (Odds.value i (h 0).1 / (4 * D))
      (8 * Odds.value i (h 0).1) omega S.1} h
  intro hg
  rw [hj] at hg
  rcases hg.2 with hup | hnot
  · exact (not_le_of_gt ((odds_lt_inv i (h j).1 u hu (hband j)).trans hthreshold.2)) hup
  · exact hnot (hcap j)

lemma crossing_failure (i : Fin n) (u theta D omega : ℝ) (hu : 0 < u)
    (huquarter : u ≤ 1 / 4) (hD : D = (3 : ℝ) ^ k) (htheta : theta = 16 * D * u)
    (h : Fin (R + 1) → State n mu) (t : Fin (R + 1))
    (hstart : fraction i 0 (h 0).1 ≤ 2 * u)
    (hband : ∀ j, j ≤ t → u ≤ fraction i 0 (h j).1)
    (hplateau : ∀ j, j ≤ t → ∀ v, (Sampling.zeros ((h j).1 v)).card = k)
    (hcap : ∀ j, j ≤ t → cap omega (h j).1)
    (hbad : theta ≤ fraction i 0 (h t).1) :
    ¬good i (Odds.value i (h 0).1 / (4 * D)) (8 * Odds.value i (h 0).1) omega
      (frozen {S | active k i (Odds.value i (h 0).1 / (4 * D))
        (8 * Odds.value i (h 0).1) omega S.1} h) := by
  have hDpos : 0 < D := by rw [hD]; positivity
  have hthreshold := protection_thresholds i (h 0).1 u theta D hu huquarter hDpos htheta
    ⟨hband 0 (Fin.zero_le _), hstart⟩
  let lo := Odds.value i (h 0).1 / (4 * D)
  let hi := 8 * Odds.value i (h 0).1
  let A : Set (State n mu) := {S | active k i lo hi omega S.1}
  have htheta0 : 0 < theta := by rw [htheta]; positivity
  have htlo : Odds.value i (h t).1 ≤ lo := by
    exact (odds_lt_inv i (h t).1 theta htheta0 hbad).le.trans hthreshold.1
  have htA : h t ∉ A := by
    intro hh
    exact (not_lt_of_ge htlo) hh.2.1
  have hlow := FirstExit.frozen_in_of_exit_before A {S | Odds.value i S.1 ≤ lo} h t htA
    (by
      intro j hj hnot
      have hhi : Odds.value i (h j).1 < hi :=
        (odds_lt_inv i (h j).1 u hu (hband j hj)).trans hthreshold.2
      by_contra hh
      apply hnot
      exact ⟨hplateau j hj, lt_of_not_ge hh, hhi, hcap j hj⟩)
  intro hg
  exact (not_lt_of_ge hlow) hg.1

end
end Lax343628Proofs.ProtectionGeometry

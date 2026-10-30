import Lax343628Proofs.SeedBirthLower
import Lax343628Proofs.SeedViability

namespace Lax343628Proofs.SeedSurplus

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.SeedGeometry
open Lax343628Proofs.SeedIdeal Lax343628Proofs.FiniteDrift Lax343628Proofs.CurveBounds
open Lax343628Proofs.ClassChannels
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+} {i : Fin n}

lemma catalyst_uniform {k d : ℕ} (hd : 1 ≤ d) (hdk : d ≤ k) :
    1 / (16 * (k : ℝ) ^ 2) ≤ t d - q d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hd.trans hdk
  have hdkR : (d : ℝ) ≤ k := by exact_mod_cast hdk
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  have hspos := Real.sqrt_nonneg (d : ℝ)
  have hroot : Real.sqrt (d : ℝ) ≤ k := by nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by positivity) (show 0 ≤ (k : ℝ) - 1 by linarith)]
  have hprod := mul_le_mul hdkR hroot hspos (show (0 : ℝ) ≤ k by positivity)
  have hdpos : (0 : ℝ) < d := by linarith
  have hden : 0 < 16 * (d : ℝ) * Real.sqrt d := mul_pos (mul_pos (by norm_num) hdpos) (Real.sqrt_pos.mpr hdpos)
  exact (div_le_div_of_nonneg_left (by norm_num) hden (by nlinarith [hprod])).trans (CatalystBounds.catalyst_polynomial hd)

lemma bracket {Q T rho theta j k E F : ℝ} (hQ : 0 ≤ Q) (hT : T ≤ 1)
    (hrho : 0 ≤ rho ∧ rho ≤ 1) (htheta : 0 ≤ theta) (hj : 0 ≤ j) (hjk : j ≤ k) :
    (1 - rho) * (T - Q) - (2 * k * theta + 2 * rho + 2 * E + F) ≤
      T * (1 - rho - j * theta) - E - (Q * (1 - rho) ^ 2 + k * theta + 2 * rho + E + F) := by
  have hnon := mul_nonneg hQ (mul_nonneg hrho.1 (show 0 ≤ 1 - rho by linarith))
  have ht := mul_le_mul_of_nonneg_right hT (mul_nonneg hj htheta)
  have hj' := mul_le_mul_of_nonneg_right hjk htheta
  nlinarith

lemma crossover_lower (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r + 1)
    (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = r + 1)
    (theta : ℝ) (htheta : 0 ≤ theta) (hflat : ∀ j, j ∉ C → fraction j 0 P ≤ theta) :
    phi C i P * ((1 - rho C P) * (Real.exp (-1) * (t (r + 1 - C.card) - q (r + 1 - C.card))) -
      (2 * (r + 1 : ℝ) * theta + 2 * rho C P + 256 * (r + 1 : ℝ) ^ 2 / n + 1 / n)) ≤
      mean (offspring 1 P) (ColumnKernels.liftClass (familyClass (r := r) (i := i) C)) -
        phi C i P * mean (offspring 1 P) (BirthMass.plateauTest (r + 1)) := by
  have hb := SeedBirthLower.crossover_family_lower hr hn C hi hC P hP theta hflat
  have hv := SeedViability.crossover_upper hr hn C hi hC P hP theta htheta hflat
  have hphi : 0 ≤ phi C i P := mean_nonneg _ (fun _ ↦ by split_ifs <;> norm_num)
  have hv' := mul_le_mul_of_nonneg_left hv hphi
  have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hT : Real.exp (-1) * t (r + 1 - C.card) ≤ 1 := by
    have ht : 0 ≤ t (r + 1 - C.card) ∧ t (r + 1 - C.card) ≤ 1 := ⟨(profile_pos _ _).le, profile_le_one _ _⟩
    have hh := mul_le_mul he ht.2 ht.1 (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hcpos := Finset.card_pos.mpr ⟨i, hi⟩
  have hjk : ((r + 1 - C.card + 1 : ℕ) : ℝ) ≤ (r + 1 : ℝ) := by exact_mod_cast (show r + 1 - C.card + 1 ≤ r + 1 by omega)
  have hbr := bracket (Q := Real.exp (-1) * q (r + 1 - C.card)) (T := Real.exp (-1) * t (r + 1 - C.card))
    (rho := rho C P) (theta := theta) (j := ((r + 1 - C.card + 1 : ℕ) : ℝ)) (k := (r + 1 : ℝ))
    (E := 128 * (r + 1 : ℝ) ^ 2 / n) (F := 1 / (n : ℝ))
    (mul_nonneg (Real.exp_pos _).le (profile_pos _ _).le) hT (rho_bounds C P) htheta (Nat.cast_nonneg _) hjk
  have hscale := mul_le_mul_of_nonneg_left hbr hphi
  apply le_trans _ (sub_le_sub hb hv')
  convert hscale using 1 <;> ring

lemma crossover_positive (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r)
    (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = r + 1)
    (theta : ℝ) (htheta : 0 ≤ theta) (hflat : ∀ j, j ∉ C → fraction j 0 P ≤ theta)
    (hrho : rho C P ≤ 1 / 4)
    (hcost : 2 * (r + 1 : ℝ) * theta + 2 * rho C P + 256 * (r + 1 : ℝ) ^ 2 / n + 1 / n ≤
      Real.exp (-1) / (64 * (r + 1 : ℝ) ^ 2)) :
    phi C i P * (Real.exp (-1) / (64 * (r + 1 : ℝ) ^ 2)) ≤
      mean (offspring 1 P) (ColumnKernels.liftClass (familyClass (r := r) (i := i) C)) -
        phi C i P * mean (offspring 1 P) (BirthMass.plateauTest (r + 1)) := by
  have hc := crossover_lower hr hn C hi (hC.trans (Nat.le_succ r)) P hP theta htheta hflat
  have hg := catalyst_uniform (show 1 ≤ r + 1 - C.card by omega) (Nat.sub_le (r + 1) C.card)
  norm_num only [Nat.cast_add, Nat.cast_one] at hg
  have he : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hrhon : 0 ≤ 1 - rho C P := by linarith
  have hgain := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg he) hrhon
  have hhalf := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 - rho C P by linarith)
    (show 0 ≤ Real.exp (-1) * (1 / (16 * (r + 1 : ℝ) ^ 2)) by positivity)
  have heq : (1 / 2 : ℝ) * (Real.exp (-1) * (1 / (16 * (r + 1 : ℝ) ^ 2))) =
      Real.exp (-1) / (32 * (r + 1 : ℝ) ^ 2) := by field_simp; ring
  rw [heq] at hhalf
  have heq' : Real.exp (-1) / (32 * (r + 1 : ℝ) ^ 2) - Real.exp (-1) / (64 * (r + 1 : ℝ) ^ 2) =
      Real.exp (-1) / (64 * (r + 1 : ℝ) ^ 2) := by field_simp; ring
  have hcoeff : Real.exp (-1) / (64 * (r + 1 : ℝ) ^ 2) ≤
      (1 - rho C P) * (Real.exp (-1) * (t (r + 1 - C.card) - q (r + 1 - C.card))) -
      (2 * (r + 1 : ℝ) * theta + 2 * rho C P + 256 * (r + 1 : ℝ) ^ 2 / n + 1 / n) := by
    linarith
  exact (mul_le_mul_of_nonneg_left hcoeff (mean_nonneg _ (fun _ ↦ by split_ifs <;> norm_num))).trans hc

end
end Lax343628Proofs.SeedSurplus

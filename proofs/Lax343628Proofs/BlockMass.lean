import Lax343628Proofs.ServiceGeometry
import Lax343628Proofs.ProtectionGeometry

namespace Lax343628Proofs.BlockMass

open Lax343628.Algorithm Lax343628Proofs.ClassChannels
open Lax343628Proofs.ServiceGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {mu : ℕ+}

lemma ratio (lo hi Q : ℝ) (hlo : 0 ≤ lo) (hhi : lo ≤ hi) (hQ : 1 ≤ Q) (hbound : hi ≤ Q * lo) :
    Odds.lowerMass hi ≤ Q * Odds.lowerMass lo := by
  have hhi0 : 0 ≤ hi := hlo.trans hhi
  have hQ0 : 0 ≤ Q := by linarith
  apply (Odds.lowerMass_mono hhi0 hbound).trans
  unfold Odds.lowerMass
  have heq : Q * (lo / (1 + lo)) = Q * lo / (1 + lo) := by ring
  rw [heq]
  apply div_le_div_of_nonneg_left (mul_nonneg hQ0 hlo) (by linarith : 0 < 1 + lo)
  nlinarith [mul_nonneg (sub_nonneg.mpr hQ) hlo]

lemma block_ratio (O hi D : ℝ) (hO : 0 < O) (hD : 1 ≤ D)
    (hhi : O < hi) (hupper : hi ≤ 8 * O) :
    Odds.lowerMass hi ≤ (32 * D) * Odds.lowerMass (O / (4 * D)) := by
  have hD0 : 0 < D := by linarith
  have hlo : 0 < O / (4 * D) := by positivity
  refine ratio _ _ _ hlo.le ?_ (by linarith) ?_
  · have hh : O / (4 * D) ≤ O := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * D)).mpr
      nlinarith
    exact hh.trans hhi.le
  · have heq : 32 * D * (O / (4 * D)) = 8 * O := by field_simp; ring
    rwa [heq]

lemma service_mutant (i : Fin n) (P : Population n mu) (D : ℝ) (hD : 1 ≤ D)
    (ha : 0 < fraction i 0 P) :
    fraction i 1 P / (4 * D) ≤ Odds.lowerMass (Odds.value i P / (4 * D)) := by
  have hh := Odds.lowerMass_scaled
    (div_nonneg (fraction_bounds i 1 P).1 ha.le : 0 ≤ Odds.value i P) (show 1 ≤ 4 * D by linarith)
  change Odds.lowerMass (Odds.value i P) / (4 * D) ≤ Odds.lowerMass (Odds.value i P / (4 * D)) at hh
  rwa [(Odds.exact_fractions i P ha).1] at hh

lemma service_resident (a O : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hO : 0 ≤ O) :
    a ≤ Odds.upperMass (target a O) := by
  have hf : 0 ≤ finalOdds a := div_nonneg (sub_nonneg.mpr ha1) ha.le
  have ht := min_le_right (8 * O) (finalOdds a)
  have ht0 : 0 ≤ target a O := le_min (by positivity) hf
  have hh := Odds.upperMass_antitone ht0 ht
  have heq : Odds.upperMass (finalOdds a) = a := by
    unfold Odds.upperMass finalOdds
    field_simp; ring
  rwa [heq] at hh

lemma protection_mutant (lo : ℝ) (hlo : 1 ≤ lo) : (1 / 2 : ℝ) ≤ Odds.lowerMass lo := by
  unfold Odds.lowerMass
  apply (le_div_iff₀ (by linarith : 0 < 1 + lo)).mpr
  linarith

lemma protection_resident (i : Fin n) (P : Population n mu) (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1)
    (ha : u ≤ fraction i 0 P) : u / 9 ≤ Odds.upperMass (8 * Odds.value i P) := by
  have hO0 : 0 ≤ Odds.value i P := div_nonneg (fraction_bounds i 1 P).1 (hu.le.trans ha)
  have hO := (ProtectionGeometry.odds_lt_inv i P u hu ha).le
  have hh := Odds.upperMass_antitone (show 0 ≤ 8 * Odds.value i P by positivity)
    (mul_le_mul_of_nonneg_left hO (show (0 : ℝ) ≤ 8 by norm_num))
  apply le_trans _ hh
  unfold Odds.upperMass
  have heq : 1 / (1 + 8 * (1 / u)) = u / (u + 8) := by field_simp
  rw [heq]
  apply div_le_div_of_nonneg_left hu.le (by positivity : 0 < u + 8)
  linarith

end
end Lax343628Proofs.BlockMass

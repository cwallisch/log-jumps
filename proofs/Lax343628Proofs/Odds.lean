import Lax343628Proofs.ClassMeanDynamics

namespace Lax343628Proofs.Odds

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.ClassMeanDynamics
noncomputable section

variable {n : ℕ} {mu : ℕ+}

def value (i : Fin n) (P : Population n mu) : ℝ := fraction i 1 P / fraction i 0 P

def lowerMass (O : ℝ) : ℝ := O / (1 + O)

def upperMass (O : ℝ) : ℝ := 1 / (1 + O)

lemma positive_fractions (i : Fin n) (P : Population n mu) (hO : 0 < value i P) :
    0 < fraction i 1 P ∧ 0 < fraction i 0 P := by
  have hf := fraction_bounds i 1 P
  exact (div_pos_iff.mp hO).resolve_right (by rintro ⟨hfneg, _⟩; linarith)

lemma band_frequencies (i : Fin n) (P : Population n mu) {L U : ℝ} (hL : 0 < L)
    (hlower : L < value i P) (hupper : value i P < U) :
    lowerMass L < fraction i 1 P ∧ upperMass U < fraction i 0 P := by
  have hpos := positive_fractions i P (hL.trans hlower)
  have hU : 0 < U := (hL.trans hlower).trans hupper
  have hlo := (lt_div_iff₀ hpos.2).mp hlower
  have hhi := (div_lt_iff₀ hpos.2).mp hupper
  have hsum := fraction_sum i P
  constructor
  · apply (div_lt_iff₀ (show 0 < 1 + L by linarith)).mpr
    nlinarith
  · apply (div_lt_iff₀ (show 0 < 1 + U by linarith)).mpr
    nlinarith

lemma exact_fractions (i : Fin n) (P : Population n mu) (ha : 0 < fraction i 0 P) :
    lowerMass (value i P) = fraction i 1 P ∧ upperMass (value i P) = fraction i 0 P := by
  have hs := fraction_sum i P
  unfold lowerMass upperMass value
  constructor <;> field_simp <;> nlinarith

lemma lowerMass_pos {O : ℝ} (hO : 0 < O) : 0 < lowerMass O := div_pos hO (by linarith)

lemma lowerMass_mono {O V : ℝ} (hO : 0 ≤ O) (hOV : O ≤ V) : lowerMass O ≤ lowerMass V := by
  unfold lowerMass
  apply (div_le_div_iff₀ (by linarith : 0 < 1 + O) (by linarith : 0 < 1 + V)).mpr
  nlinarith

lemma upperMass_antitone {O V : ℝ} (hO : 0 ≤ O) (hOV : O ≤ V) : upperMass V ≤ upperMass O :=
  div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

lemma lowerMass_scaled {O C : ℝ} (hO : 0 ≤ O) (hC : 1 ≤ C) : lowerMass O / C ≤ lowerMass (O / C) := by
  have hCp : 0 < C := by linarith
  unfold lowerMass
  have heq : O / C / (1 + O / C) = O / (C + O) := by field_simp
  rw [heq]
  have heq' : O / (1 + O) / C = O / (C * (1 + O)) := by rw [div_div, mul_comm]
  rw [heq']
  apply div_le_div_of_nonneg_left hO (by positivity : 0 < C + O)
  nlinarith [mul_nonneg (show 0 ≤ C - 1 by linarith) hO]

end
end Lax343628Proofs.Odds

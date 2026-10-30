import Lax343628Proofs.SpeciesScale

namespace Lax343628Proofs.SpeciesExponents

open Lax343628Proofs.SpeciesParameters Lax343628Proofs.SpeciesProtection
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma count (s m pc p root : ℝ) (hs : 16777216 ≤ s) (hm : 1 ≤ m)
    (hpc : 1 / s ≤ pc) (hp : 1 / s ^ 2 ≤ p) (hr : 0 < root ∧ root ≤ s)
    (hmp : 300 ≤ m * p) :
    m / s ^ 12 ≤ (pc * Real.exp (-1) * p * (1 / (2 * root)) / 16) * (m * p - 1) := by
  have hsp : 0 < s := by linarith
  have hrootp := hr.1
  have hs1 : 1 ≤ s := by linarith
  have hpc0 : 0 ≤ pc := (by positivity : (0 : ℝ) ≤ 1 / s).trans hpc
  have hp0 : 0 ≤ p := (by positivity : (0 : ℝ) ≤ 1 / s ^ 2).trans hp
  have he : 1 / s ≤ Real.exp (-1) := by
    have hh : 1 / s ≤ (1 / 8 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith [Real.exp_neg_one_gt_d9]
  have hprod : 1 / s ^ 4 ≤ pc * Real.exp (-1) * p := by
    have h1 := mul_le_mul hpc he (by positivity : (0 : ℝ) ≤ 1 / s) hpc0
    have h2 := mul_le_mul h1 hp (by positivity : (0 : ℝ) ≤ 1 / s ^ 2) (mul_nonneg hpc0 (Real.exp_nonneg (-1)))
    have heq : 1 / s * (1 / s) * (1 / s ^ 2) = 1 / s ^ 4 := by field_simp
    rwa [heq] at h2
  have hroot : 1 / s ^ 2 ≤ 1 / (32 * root) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have hdrift : 1 / s ^ 6 ≤ pc * Real.exp (-1) * p * (1 / (2 * root)) / 16 := by
    have h1 := mul_le_mul hprod hroot (by positivity : (0 : ℝ) ≤ 1 / s ^ 2)
      (by positivity : 0 ≤ pc * Real.exp (-1) * p)
    have heq : 1 / s ^ 4 * (1 / s ^ 2) = 1 / s ^ 6 := by field_simp
    rw [heq] at h1
    have heqR : pc * Real.exp (-1) * p * (1 / (32 * root)) =
        pc * Real.exp (-1) * p * (1 / (2 * root)) / 16 := by ring
    rwa [heqR] at h1
  have hmpp := mul_le_mul_of_nonneg_left hp (show 0 ≤ m by linarith)
  have hhalf : m / (2 * s ^ 2) ≤ m * p / 2 := by linear_combination hmpp / 2
  have h3 : m / s ^ 3 ≤ m / (2 * s ^ 2) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith)
  have hmass : m / s ^ 3 ≤ m * p - 1 := by linarith
  have hh := mul_le_mul hdrift hmass (by positivity : 0 ≤ m / s ^ 3)
    (by positivity : 0 ≤ pc * Real.exp (-1) * p * (1 / (2 * root)) / 16)
  have heq : 1 / s ^ 6 * (m / s ^ 3) = m / s ^ 9 := by field_simp
  rw [heq] at hh
  exact (div_le_div_of_nonneg_left (by linarith) (by positivity)
    (pow_le_pow_right₀ hs1 (by norm_num : 9 ≤ 12))).trans hh

lemma ratio (s m pc p : ℝ) (hs : 16777216 ≤ s) (hm : 1 ≤ m)
    (hpc : 1 / s ≤ pc) (hp : 1 / s ^ 2 ≤ p) (hmp : 300 ≤ m * p) :
    m / s ^ 12 ≤ (pc * strictConstant * p ^ 2 / (m + 1) / (3 / (m * p)) ^ 2) *
      (1 / 25 - 3 / (m * p) - 1 / 50) := by
  have hsp : 0 < s := by linarith
  have hmp0 : 0 < m * p := by linarith
  have hm0 : 0 < m := by linarith
  have hp0 : 0 < p := (by positivity : (0 : ℝ) < 1 / s ^ 2).trans_le hp
  have hpc0 : 0 ≤ pc := (by positivity : (0 : ℝ) ≤ 1 / s).trans hpc
  have hcpos := strictConstant_pos
  have hc : 1 / s ≤ strictConstant := by
    unfold strictConstant
    apply (div_le_iff₀ hsp).mpr
    linarith
  have hp4 : 1 / s ^ 8 ≤ p ^ 4 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / s ^ 2) hp 4
    have heq : (1 / s ^ 2) ^ 4 = 1 / s ^ 8 := by field_simp
    rwa [heq] at hh
  have hprod : 1 / s ^ 10 ≤ pc * strictConstant * p ^ 4 := by
    have h1 := mul_le_mul hpc hc (by positivity : (0 : ℝ) ≤ 1 / s) hpc0
    have h2 := mul_le_mul h1 hp4 (by positivity : (0 : ℝ) ≤ 1 / s ^ 8) (mul_nonneg hpc0 strictConstant_pos.le)
    have heq : 1 / s * (1 / s) * (1 / s ^ 8) = 1 / s ^ 10 := by field_simp
    rwa [heq] at h2
  have hscale : m / s ≤ m ^ 2 / (9 * (m + 1)) := by
    apply (div_le_div_iff₀ hsp (by positivity : (0 : ℝ) < 9 * (m + 1))).mpr
    have hh := mul_le_mul_of_nonneg_right (show (18 : ℝ) ≤ s by linarith) (sq_nonneg m)
    nlinarith
  have hstep : 3 / (m * p) ≤ (1 / 100 : ℝ) := (div_le_iff₀ hmp0).mpr (by linarith)
  have hgap : 1 / s ≤ 1 / 25 - 3 / (m * p) - 1 / 50 := by
    have hh : 1 / s ≤ (1 / 100 : ℝ) := (div_le_iff₀ hsp).mpr (by linarith)
    linarith
  have h1 := mul_le_mul hprod hscale (by positivity : 0 ≤ m / s)
    (by positivity : 0 ≤ pc * strictConstant * p ^ 4)
  have h2 := mul_le_mul h1 hgap (by positivity : (0 : ℝ) ≤ 1 / s)
    (by positivity : 0 ≤ pc * strictConstant * p ^ 4 * (m ^ 2 / (9 * (m + 1))))
  have heq : 1 / s ^ 10 * (m / s) * (1 / s) = m / s ^ 12 := by field_simp
  rw [heq] at h2
  have heqR : (pc * strictConstant * p ^ 2 / (m + 1) / (3 / (m * p)) ^ 2) *
      (1 / 25 - 3 / (m * p) - 1 / 50) =
      pc * strictConstant * p ^ 4 * (m ^ 2 / (9 * (m + 1))) * (1 / 25 - 3 / (m * p) - 1 / 50) := by
    field_simp
    ring
  rw [heqR]
  exact h2

lemma threshold_mass (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (k n : ℕ) (mu : ℕ+) (delta : ℝ)
    (hk : 1 ≤ k) (hks : k ≤ (S : ℕ)) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * EntropyLedger.logarithms n mu delta ≤ (mu : ℕ)) :
    300 ≤ (mu : ℕ) * threshold k := by
  let s : ℝ := (S : ℕ)
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hW := (EntropyLedger.logarithms_bounds n mu delta hd).1
  have hlarge : s ^ 300 ≤ (mu : ℕ) := by
    have hh := mul_le_mul_of_nonneg_left hW (show 0 ≤ s ^ 300 by positivity)
    linarith
  have h300 : 300 * s ^ 2 ≤ (mu : ℕ) := (SpeciesScale.constant_power s 300 (by linarith)
    (by nlinarith) 2 300 (by norm_num)).trans hlarge
  have hp := SpeciesScale.threshold_lower s hs k hk (by dsimp [s]; exact_mod_cast hks)
  have hh := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ (mu : ℕ) by positivity)
  have hdiv : (300 : ℝ) ≤ (mu : ℕ) / s ^ 2 := (le_div_iff₀ (by positivity)).mpr h300
  rw [mul_one_div] at hh
  exact hdiv.trans hh

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (k n : ℕ) (mu : ℕ+) (pc delta : ℝ)
    (hk : 1 ≤ k) (hks : k ≤ (S : ℕ)) (hpc : 1 / (S : ℕ) ≤ pc) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * EntropyLedger.logarithms n mu delta ≤ (mu : ℕ)) :
    SpeciesReentry.countFailure k mu pc (threshold k) + SpeciesReentry.ratioFailure mu pc (threshold k) ≤
      2 * Real.exp (-((mu : ℕ) : ℝ) / ((S : ℕ) : ℝ) ^ 12) := by
  let s : ℝ := (S : ℕ)
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hksR : (k : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hks
  have hr : 0 < Real.sqrt k ∧ Real.sqrt k ≤ s :=
    ⟨Real.sqrt_pos.mpr (by linarith), (Real.sqrt_le_self_iff.mpr (Or.inr hkR)).trans hksR⟩
  have hm : (1 : ℝ) ≤ (mu : ℕ) := by exact_mod_cast mu.pos
  have hp := SpeciesScale.threshold_lower s hs k hk hksR
  have hmp := threshold_mass S hS k n mu delta hk hks hd hmu
  have hc := count s (mu : ℕ) pc (threshold k) (Real.sqrt k) hs hm hpc hp hr hmp
  have hq := ratio s (mu : ℕ) pc (threshold k) hs hm hpc hp hmp
  have hc' : SpeciesReentry.countFailure k mu pc (threshold k) ≤ Real.exp (-((mu : ℕ) : ℝ) / s ^ 12) := by
    unfold SpeciesReentry.countFailure CloneProtection.countDrift
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul, neg_div] using neg_le_neg hc
  have hq' : SpeciesReentry.ratioFailure mu pc (threshold k) ≤ Real.exp (-((mu : ℕ) : ℝ) / s ^ 12) := by
    unfold SpeciesReentry.ratioFailure ratioDrift ratioStep
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul, neg_div] using neg_le_neg hq
  linarith

end
end Lax343628Proofs.SpeciesExponents

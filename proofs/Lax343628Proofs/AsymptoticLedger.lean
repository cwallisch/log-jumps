import Lax343628Proofs.CommonRuntime
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Lax343628Proofs.AsymptoticLedger

open Filter Lax343628Proofs.EntropyLedger
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma logarithms_upper (n : ℕ) (mu : ℕ+) (a : ℝ) (ha : 0 < a)
    (hn : 1 ≤ (n : ℝ)) (hl : 1 ≤ Real.log (n : ℝ))
    (hmu : ((mu : ℕ) : ℝ) ≤ (n : ℝ) ^ a) :
    logarithms n mu (AttemptError.delta n mu) ≤ 100 * (a + 1) * Real.log (n : ℝ) := by
  let q := (n : ℝ) ^ (a + 1)
  have hnp : (0 : ℝ) < n := by linarith
  have hq : 1 ≤ q := Real.one_le_rpow hn (by linarith)
  have hnq : (n : ℝ) ≤ q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn (show 1 ≤ a + 1 by linarith)
  have hmq : ((mu : ℕ) : ℝ) ≤ q := hmu.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
  have hqp : 0 < q := by linarith
  have hlog : Real.log (3 * q) = Real.log 3 + (a + 1) * Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num) hqp.ne', Real.log_rpow hnp]
  have h1 := Real.log_le_log (by positivity : (0 : ℝ) < n + 1)
    (show (n : ℝ) + 1 ≤ 3 * q by linarith)
  have h2 := Real.log_le_log (by positivity : (0 : ℝ) < (mu : ℕ) + 1)
    (show ((mu : ℕ) : ℝ) + 1 ≤ 3 * q by linarith)
  have h3 := Real.log_le_log (by positivity : (0 : ℝ) < n + (mu : ℕ) + 1)
    (show (n : ℝ) + (mu : ℕ) + 1 ≤ 3 * q by linarith)
  have hd : Real.log (1 / AttemptError.delta n mu) =
      8 * Real.log ((n : ℝ) + (mu : ℕ) + 1) := by
    simp only [AttemptError.delta, one_div_one_div, Real.log_pow, Nat.cast_ofNat]
  have hlog3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  unfold logarithms
  rw [hd, hlog] at *
  nlinarith [mul_nonneg ha.le (show 0 ≤ Real.log (n : ℝ) by linarith)]

lemma eventually_log_absorb (D r : ℝ) (hD : 0 < D) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, D * Real.log (n : ℝ) ≤ (n : ℝ) ^ r := by
  have hh := (isLittleO_log_rpow_atTop hr).def (show 0 < 1 / D by positivity)
  have hh' := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually hh
  filter_upwards [hh', (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually_ge_atTop 1] with n hn hn1
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)] at hn
  simpa only [mul_comm] using (le_div_iff₀ hD).mp (by simpa only [one_div_mul_eq_div] using hn)

lemma eventually_log_square (D : ℝ) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, D * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1 by norm_num)).def
    (show 0 < 1 / D by positivity)
  have hh' := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually hh
  filter_upwards [hh'] with n hn
  simp only [Real.rpow_two, Real.rpow_one, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (Real.log (n : ℝ))), abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), one_div_mul_eq_div] at hn
  simpa only [mul_comm] using (le_div_iff₀ hD).mp hn

/-- A fixed integer scale absorbs the fixed crossover probability. -/
lemma choose_scale (pc : ℝ) (hp : 0 < pc) :
    ∃ A : ℕ+, 16777216 ≤ (A : ℕ) ∧ 1 / ((A : ℕ) : ℝ) ≤ pc := by
  let A : ℕ+ := ⟨Nat.ceil (1 / pc) + 16777216, by omega⟩
  refine ⟨A, by dsimp [A]; omega, ?_⟩
  have hA : (0 : ℝ) < (A : ℕ) := by exact_mod_cast A.pos
  apply (div_le_iff₀ hA).mpr
  have hc := Nat.le_ceil (1 / pc)
  have hh : 1 / pc ≤ ((A : ℕ) : ℝ) := by
    dsimp [A]
    rw [Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hh' := (div_le_iff₀ hp).mp hh
  linarith

def scale (A : ℕ+) (k : ℕ) : ℕ+ := ⟨(A : ℕ) * 3 ^ k, by positivity⟩

lemma scale_facts (A : ℕ+) (hA : 16777216 ≤ (A : ℕ)) (k : ℕ) (pc : ℝ)
    (hp : 1 / ((A : ℕ) : ℝ) ≤ pc) :
    16777216 ≤ (scale A k : ℕ) ∧ k ≤ (scale A k : ℕ) ∧
      (3 : ℝ) ^ k ≤ (scale A k : ℕ) ∧ 1 / ((scale A k : ℕ) : ℝ) ≤ pc := by
  have hpow : 1 ≤ (3 : ℕ) ^ k := Nat.one_le_pow k 3 (by norm_num)
  have ha1 : 1 ≤ (A : ℕ) := A.pos
  have hle : (A : ℕ) ≤ (scale A k : ℕ) := by dsimp [scale]; nlinarith
  have hpw : (3 : ℕ) ^ k ≤ (scale A k : ℕ) := by dsimp [scale]; nlinarith
  have hk : k ≤ (3 : ℕ) ^ k := (Nat.lt_pow_self (by norm_num : 1 < (3 : ℕ))).le
  refine ⟨hA.trans hle, hk.trans hpw, ?_, ?_⟩
  · exact_mod_cast hpw
  · apply le_trans _ hp
    exact one_div_le_one_div_of_le (by exact_mod_cast A.pos) (by exact_mod_cast hle)

lemma scale_bound (A : ℕ+) (k : ℕ) (x t : ℝ) (hx : 0 < x)
    (hk : (k : ℝ) ≤ (t / (300 * Real.log 3)) * Real.log x) :
    ((scale A k : ℕ) : ℝ) ^ 300 ≤ ((A : ℕ) : ℝ) ^ 300 * x ^ t := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpow : ((3 : ℝ) ^ k) ^ 300 ≤ x ^ t := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), Real.log_pow,
      Real.rpow_def_of_pos hx]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ 300 * Real.log 3 by positivity)
    field_simp at hh
    norm_num only [Nat.cast_ofNat] at *
    nlinarith
  simp only [scale, PNat.mk_coe, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow]
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

end
end Lax343628Proofs.AsymptoticLedger

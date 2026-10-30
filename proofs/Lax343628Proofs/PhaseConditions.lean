import Lax343628Proofs.ScaleProducts

namespace Lax343628Proofs.PhaseConditions

open Lax343628Proofs.PhaseParameters Lax343628Proofs.EntropyLedger
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure Conditions (S : ℕ+) (n k : ℕ) (mu : ℕ+) (delta : ℝ) : Prop where
  dimension : 4 * k ≤ n
  twice : 2 * mass S n mu delta ≤ (mu : ℕ)
  serviceMass : mass S n mu delta ≤ (mu : ℕ) * processed S k
  serviceDimension : ((S : ℕ) : ℝ) ^ 40 ≤ (n : ℝ) * processed S k
  protectionMass : mass S n mu delta ≤ (mu : ℕ) * (lowerZero S k / 9)
  protectionDimension : ((S : ℕ) : ℝ) ^ 40 ≤ (n : ℝ) * (lowerZero S k / 9)
  processedLower : 1 / (mu : ℕ) ≤ processed S k
  services : services S k ≤ (S : ℕ) ^ 12
  coreSmall : (k : ℝ) * seedSize S n k mu delta / (mu : ℕ) < 1 / 125
  flat : theta S ≤ 1 / (2 * (k : ℝ))

lemma of_size (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n k : ℕ) (mu : ℕ+) (delta : ℝ)
    (hk : 1 ≤ k) (hkS : k ≤ (S : ℕ)) (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n) : Conditions S n k mu delta := by
  let s : ℝ := (S : ℕ)
  let W := logarithms n mu delta
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hs1 : 1 ≤ s := by linarith
  have hsp : 0 < s := by linarith
  have hWp : 1 ≤ W := (logarithms_bounds n mu delta hd).1
  have hmup : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkSR : (k : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hkS
  have hap := (processed_bounds S k).1
  have ha := processed_scale S hS k hD
  have hu := ScaleProducts.divide_nine s (lowerZero S k) hs (lower_scale S hS k hD)
  have hservice := ScaleProducts.mass s W (mu : ℕ) (processed S k) hs1 hWp hmu ha
  have hserviceDim := ScaleProducts.dimension s W n (processed S k) hs1 hWp hn ha
  have hprotect := ScaleProducts.mass s W (mu : ℕ) (lowerZero S k / 9) hs1 hWp hmu hu
  have hprotectDim := ScaleProducts.dimension s W n (lowerZero S k / 9) hs1 hWp hn hu
  have hmassEq : mass S n mu delta = s ^ 248 * W := mass_eq S n mu delta
  have hm : 1 ≤ mass S n mu delta := mass_one S n mu delta hd
  have hn300 := PhaseScale.dimension S n mu delta hd hn
  have hs300 : s ^ 2 ≤ s ^ 300 := pow_le_pow_right₀ hs1 (by norm_num)
  have hdim : 4 * k ≤ n := by
    have hs4 : 4 * s ≤ s ^ 2 := by nlinarith
    have hh : 4 * (k : ℝ) ≤ n := by linarith
    exact_mod_cast hh
  have hcore := PhaseScale.core_fraction S hS n k mu delta hkS hD hd hmu
  have hS49 : s ≤ s ^ 49 := by
    have hh : s ^ 1 ≤ s ^ 49 := pow_le_pow_right₀ hs1 (by norm_num)
    simpa only [pow_one] using hh
  have hcore' : (k : ℝ) * seedSize S n k mu delta / (mu : ℕ) < 1 / 125 := by
    have hh := hcore.trans (div_le_div_of_nonneg_left (by norm_num) hsp hS49)
    apply hh.trans_lt
    apply (div_lt_div_iff₀ hsp (by norm_num : (0 : ℝ) < 125)).mpr
    linarith
  have hflat : theta S ≤ 1 / (2 * (k : ℝ)) := by
    have hs8 : s ^ 2 ≤ s ^ 8 := pow_le_pow_right₀ hs1 (by norm_num)
    have hh : 2 * (k : ℝ) ≤ s ^ 8 := by nlinarith
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hh
  refine ⟨hdim, ?_, ?_, hserviceDim, ?_, hprotectDim, ?_, services_bound S hS k hkS hD, hcore', hflat⟩
  · rw [hmassEq]
    exact ScaleProducts.twice_mass s W (mu : ℕ) hs hWp hmu
  · rw [hmassEq]
    exact hservice
  · rw [hmassEq]
    exact hprotect
  · apply (div_le_iff₀ hmup).mpr
    rw [hmassEq] at hm
    nlinarith

end
end Lax343628Proofs.PhaseConditions

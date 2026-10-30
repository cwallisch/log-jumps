import Lax343628Proofs.SpeciesCap

namespace Lax343628Proofs.SpeciesParameters

open Lax343628Proofs.SpeciesEntry
noncomputable section
set_option backward.isDefEq.respectTransparency false

def threshold (k : ℕ) : ℝ := 1 / (64 * Real.sqrt k)

def entry (n : ℕ) (mu : ℕ+) : ℕ := 16777216 * n * ((mu : ℕ) + 1)

lemma threshold_bounds (k : ℕ) (hk : 1 ≤ k) :
    0 < threshold k ∧ threshold k ≤ 1 / 64 ∧ threshold k ≤ 1 / (16 * Real.sqrt k) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsqrt : (1 : ℝ) ≤ Real.sqrt k := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hkR
  unfold threshold
  refine ⟨by positivity, ?_, ?_⟩
  · exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  · exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)

lemma threshold_square (k : ℕ) (hk : 1 ≤ k) : (threshold k) ^ 2 * k = 1 / 4096 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs : (Real.sqrt k) ^ 2 = (k : ℝ) := Real.sq_sqrt hkR.le
  unfold threshold
  field_simp
  nlinarith

lemma entry_bound (n k : ℕ) (mu : ℕ+) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (1 / 20 : ℝ) / (threshold k * entryDrift n k mu (threshold k) * ((entry n mu : ℝ) + 1)) ≤ 1 / 128 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmp : (0 : ℝ) < (mu : ℕ) + 1 := by positivity
  have hp := (threshold_bounds k hk).1
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs := threshold_square k hk
  have he : (entry n mu : ℝ) = 16777216 * n * ((mu : ℕ) + 1 : ℝ) := by
    simp only [entry, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have hd : threshold k * entryDrift n k mu (threshold k) * ((entry n mu : ℝ) + 1) ≥ 64 := by
    unfold entryDrift
    have heq : threshold k * (threshold k * (k : ℝ) / (64 * n * ((mu : ℕ) + 1))) * ((entry n mu : ℝ) + 1) =
        (threshold k ^ 2 * k) * ((entry n mu : ℝ) + 1) / (64 * n * ((mu : ℕ) + 1)) := by ring
    rw [heq, hs]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * n * ((mu : ℕ) + 1))).mpr
    rw [he]
    nlinarith [mul_pos hnp hmp]
  apply (div_le_iff₀ (show 0 < threshold k * entryDrift n k mu (threshold k) * ((entry n mu : ℝ) + 1) by linarith)).mpr
  linarith

lemma entry_time (n : ℕ) (mu : ℕ+) : (entry n mu : ℝ) ≤ 33554432 * (mu : ℕ) * (n : ℝ) := by
  have hm : (1 : ℝ) ≤ (mu : ℕ) := by exact_mod_cast mu.pos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  simp only [entry, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  nlinarith [mul_nonneg hn (show 0 ≤ (mu : ℕ) - (1 : ℝ) by linarith)]

end
end Lax343628Proofs.SpeciesParameters

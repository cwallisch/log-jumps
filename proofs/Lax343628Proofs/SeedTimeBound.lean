import Lax343628Proofs.SeedEstimate

namespace Lax343628Proofs.SeedTimeBound

open Lax343628Proofs.PhaseParameters Lax343628Proofs.EntropyLedger
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma scale_product (p : ℕ) (c x m q b s W : ℝ) (_hc : 0 ≤ c) (hx : 0 ≤ x) (hm : 0 ≤ m)
    (hq : 0 ≤ q) (hb : 0 ≤ b) (hs : 0 ≤ s) (hW : 0 ≤ W)
    (hcS : c ≤ s) (hmS : m ≤ s ^ p * W) (hqS : q ≤ s ^ 2) (hbS : b ≤ s) :
    c * x * m * q * b ≤ x * s ^ (p + 4) * W := by
  calc
    _ ≤ s * x * (s ^ p * W) * s ^ 2 * s := by gcongr
    _ = (x * W) * (s ^ p * s ^ 2 * (s * s)) := by ac_rfl
    _ = (x * W) * (s ^ p * s ^ 2 * s ^ 2) := by rw [← pow_two]
    _ = _ := by rw [← pow_add, ← pow_add]; ac_rfl

lemma fourth_power (S : ℝ) (k : ℕ) (hS : 0 ≤ S) (hD : (3 : ℝ) ^ k ≤ S) : (4 : ℝ) ^ k ≤ S ^ 2 := by
  have h1 := pow_le_pow_left₀ (show (0 : ℝ) ≤ 4 by norm_num) (show (4 : ℝ) ≤ 3 ^ 2 by norm_num) k
  have heq : ((3 : ℝ) ^ 2) ^ k = ((3 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]
  rw [heq] at h1
  exact h1.trans ((sq_le_sq₀ (by positivity) hS).mpr hD)

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n k : ℕ) (mu : ℕ+) (delta pc : ℝ)
    (hn : 1 ≤ n) (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (hkS : k ≤ (S : ℕ))
    (hd : 0 < delta ∧ delta ≤ 1) (hpc : 1 / (S : ℕ) ≤ pc) :
    (seedSize S n k mu delta : ℝ) / (pc * (1 / 4 : ℝ) ^ k / (64 * n)) +
      (mu : ℕ) * seedSize S n k mu delta / (pc * Real.exp (-1) / (256 * (k : ℝ) ^ 2)) ≤
        ((n : ℝ) + (mu : ℕ)) * ((S : ℕ) : ℝ) ^ 254 * logarithms n mu delta := by
  let s : ℝ := (S : ℕ)
  let W := logarithms n mu delta
  let M : ℝ := seedSize S n k mu delta
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hsp : 0 < s := by linarith
  have hW : 0 ≤ W := by have hh := (logarithms_bounds n mu delta hd).1; linarith
  have hMp : 0 ≤ M := by positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpcp : 0 < pc := (div_pos (by norm_num) hsp).trans_le hpc
  have hInv : 1 / pc ≤ s := by
    apply (div_le_iff₀ hpcp).mpr
    have hh := (div_le_iff₀ hsp).mp hpc
    nlinarith
  have h4 := fourth_power s k hsp.le hD
  have hK : (k : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hkS
  have hK2 := (sq_le_sq₀ (Nat.cast_nonneg k) hsp.le).mpr hK
  have hM := seed_upper S hS n k mu delta hD hd
  have hroot := scale_product 250 64 n M ((4 : ℝ) ^ k) (1 / pc) s W (by norm_num) hnR.le hMp
    (by positivity) (by positivity) hsp.le hW (by linarith) hM h4 hInv
  have hroot' : M / (pc * (1 / 4 : ℝ) ^ k / (64 * n)) ≤ (n : ℝ) * s ^ 254 * W := by
    have heq : M / (pc * (1 / 4 : ℝ) ^ k / (64 * n)) = 64 * n * M * (4 : ℝ) ^ k * (1 / pc) := by
      rw [one_div, inv_pow]
      field_simp
    rw [heq]
    exact hroot
  have hexpInv : 1 / Real.exp (-1) ≤ 4 := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith [GrowthParameters.exp_lower]
  have hpositive := scale_product 250 1024 (mu : ℕ) M ((k : ℝ) ^ 2) (1 / pc) s W (by norm_num)
    (by positivity) hMp (sq_nonneg _) (by positivity) hsp.le hW (by linarith) hM hK2 hInv
  have hpos' : (mu : ℕ) * M / (pc * Real.exp (-1) / (256 * (k : ℝ) ^ 2)) ≤
      (mu : ℕ) * s ^ 254 * W := by
    have heq : (mu : ℕ) * M / (pc * Real.exp (-1) / (256 * (k : ℝ) ^ 2)) =
        256 * (mu : ℕ) * M * (k : ℝ) ^ 2 * (1 / pc) * (1 / Real.exp (-1)) := by field_simp
    have hh := mul_le_mul_of_nonneg_left hexpInv
      (show 0 ≤ 256 * (mu : ℕ) * M * (k : ℝ) ^ 2 * (1 / pc) by positivity)
    have hh' : (mu : ℕ) * M / (pc * Real.exp (-1) / (256 * (k : ℝ) ^ 2)) ≤
        1024 * (mu : ℕ) * M * (k : ℝ) ^ 2 * (1 / pc) := by
      rw [heq]
      convert hh using 1 <;> first | rfl | ring
    exact hh'.trans hpositive
  have hh := add_le_add hroot' hpos'
  change M / (pc * (1 / 4 : ℝ) ^ k / (64 * n)) +
    (mu : ℕ) * M / (pc * Real.exp (-1) / (256 * (k : ℝ) ^ 2)) ≤ _
  calc
    _ ≤ (n : ℝ) * s ^ 254 * W + (mu : ℕ) * s ^ 254 * W := hh
    _ = _ := by rw [add_mul, add_mul]

end
end Lax343628Proofs.SeedTimeBound

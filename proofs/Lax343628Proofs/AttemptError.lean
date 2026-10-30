import Lax343628Proofs.AttemptLengths

namespace Lax343628Proofs.AttemptError

noncomputable section
set_option backward.isDefEq.respectTransparency false

def delta (n : ℕ) (mu : ℕ+) : ℝ := 1 / ((n : ℝ) + (mu : ℕ) + 1) ^ 8

lemma delta_bounds (n : ℕ) (mu : ℕ+) : 0 < delta n mu ∧ delta n mu ≤ 1 := by
  have hm : (1 : ℝ) ≤ (mu : ℕ) := by exact_mod_cast mu.pos
  have hn : (0 : ℝ) ≤ n := by positivity
  have hq : (1 : ℝ) ≤ n + (mu : ℕ) + 1 := by linarith
  unfold delta
  exact ⟨by positivity, (div_le_one (by positivity)).mpr (one_le_pow₀ hq)⟩

lemma bound (n L R : ℕ) (mu : ℕ+) (hn : 4 ≤ n) (hL : (L : ℝ) ≤ (mu : ℕ) * (n : ℝ))
    (hR : R ≤ L) :
    (n : ℝ) * (((L : ℝ) + 1) * delta n mu) +
      (n : ℝ) * (((L : ℝ) + 1) * (((R : ℝ) + 1) * delta n mu)) ≤ 1 / 64 := by
  let q : ℝ := (n : ℝ) + (mu : ℕ) + 1
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (1 : ℝ) ≤ (mu : ℕ) := by exact_mod_cast mu.pos
  have hq4 : 4 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 ≤ q := by linarith
  have hnq : (n : ℝ) ≤ q := by dsimp [q]; linarith
  have hR' : (R : ℝ) ≤ L := by exact_mod_cast hR
  have hmul : (mu : ℕ) * (n : ℝ) + 2 ≤ q ^ 2 := by dsimp [q]; nlinarith
  have hLq : (L : ℝ) + 1 ≤ q ^ 2 := by linarith
  have hRq : (R : ℝ) + 2 ≤ q ^ 2 := by linarith
  have hcoef : (n : ℝ) * ((L : ℝ) + 1) * ((R : ℝ) + 2) ≤ q ^ 5 := by
    calc
      _ ≤ q * q ^ 2 * q ^ 2 := by gcongr
      _ = _ := by ring
  have hdelta := (delta_bounds n mu).1
  have hh := mul_le_mul_of_nonneg_right hcoef hdelta.le
  have heq : q ^ 5 * delta n mu = 1 / q ^ 3 := by
    unfold delta
    change q ^ 5 * (1 / q ^ 8) = _
    field_simp
  rw [heq] at hh
  have hpow : (64 : ℝ) ≤ q ^ 3 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hq4 3
    norm_num at hp ⊢
    exact hp
  have hfinal := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) < 64 by norm_num) hpow
  apply le_trans _ (hh.trans hfinal)
  ring_nf
  exact le_rfl

lemma service_le (S : ℕ+) (n : ℕ) (mu : ℕ+) (d : ℝ) :
    AttemptLengths.service S mu ≤ AttemptLengths.decision S n mu d + AttemptLengths.terminal S := by
  unfold AttemptLengths.decision
  have hh : AttemptLengths.wait S n mu d + AttemptLengths.service S mu ≤
      (2 * (S : ℕ) ^ 12 + 2) * (AttemptLengths.wait S n mu d + AttemptLengths.service S mu) :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

end
end Lax343628Proofs.AttemptError

import Lax343628Proofs.BudgetReduction

namespace Lax343628Proofs.BlockParameters

noncomputable section
set_option backward.isDefEq.respectTransparency false

def horizon (S : ℕ) (mu : ℕ+) : ℕ := ((mu : ℕ) + 1) * S ^ 10

def groupSize (S : ℕ) (mu : ℕ+) : ℕ := (mu : ℕ) / S ^ 40

def samples (S : ℕ+) : ℕ+ := ⟨(S : ℕ) ^ 120, pow_pos S.pos _⟩

lemma horizon_bound (S : ℕ) (hS : 2 ≤ S) (mu : ℕ+) : horizon S mu ≤ (mu : ℕ) * S ^ 12 := by
  have hmu : (mu : ℕ) + 1 ≤ 2 * (mu : ℕ) := by have := mu.pos; omega
  have hS2 : 2 ≤ S ^ 2 := by nlinarith
  have hh := Nat.mul_le_mul_left (S ^ 10) hS2
  have heq : S ^ 12 = S ^ 10 * S ^ 2 := by rw [← pow_add]
  unfold horizon
  calc
    _ ≤ 2 * (mu : ℕ) * S ^ 10 := Nat.mul_le_mul_right _ hmu
    _ = (mu : ℕ) * (S ^ 10 * 2) := by ring
    _ ≤ (mu : ℕ) * S ^ 12 := by rw [heq]; exact Nat.mul_le_mul_left _ hh

lemma group_positive (S : ℕ) (hS : 1 ≤ S) (mu : ℕ+) (hmu : S ^ 40 ≤ (mu : ℕ)) :
    1 ≤ groupSize S mu := by
  exact (Nat.one_le_div_iff (by positivity : 0 < S ^ 40)).mpr hmu

lemma group_upper (S : ℕ) (hS : 1 ≤ S) (mu : ℕ+) :
    (groupSize S mu : ℝ) / (mu : ℕ) ≤ 1 / (S : ℝ) ^ 40 := by
  have hpos : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hSp : (0 : ℝ) < (S : ℝ) ^ 40 := by exact_mod_cast (show 0 < S ^ 40 by positivity)
  apply (div_le_div_iff₀ hpos hSp).mpr
  rw [one_mul]
  have hh : groupSize S mu * S ^ 40 ≤ (mu : ℕ) := Nat.div_mul_le_self _ _
  exact_mod_cast hh

lemma sqrt_samples (S : ℕ+) : Real.sqrt ((samples S : ℕ) : ℝ) = ((S : ℕ) : ℝ) ^ 60 := by
  change Real.sqrt (((S : ℕ) ^ 120 : ℕ) : ℝ) = _
  rw [Nat.cast_pow]
  have heq : (((S : ℕ) : ℝ) ^ 120) = ((((S : ℕ) : ℝ) ^ 60) ^ 2) := by rw [← pow_mul]
  rw [heq, Real.sqrt_sq (by positivity)]

lemma group_lower (S : ℕ) (hS : 1 ≤ S) (mu : ℕ+) (hmu : S ^ 40 ≤ (mu : ℕ)) :
    (mu : ℕ) ≤ 2 * groupSize S mu * S ^ 40 := by
  have hp : 0 < S ^ 40 := by positivity
  have he := Nat.mod_add_div (mu : ℕ) (S ^ 40)
  have hr := Nat.mod_lt (mu : ℕ) hp
  have hg := group_positive S hS mu hmu
  unfold groupSize at *
  nlinarith

lemma group_count (S : ℕ) (hS : 2 ≤ S) (mu : ℕ+) (hmu : S ^ 40 ≤ (mu : ℕ)) :
    SparseGroups.count (horizon S mu) (groupSize S mu) ≤ S ^ 54 := by
  have hS1 : 1 ≤ S := by omega
  have hR := horizon_bound S hS mu
  have hg := group_lower S hS1 mu hmu
  have hmul := Nat.mul_le_mul_right (S ^ 12) hg
  have heq : S ^ 40 * S ^ 12 = S ^ 52 := by rw [← pow_add]
  have hR' : horizon S mu ≤ groupSize S mu * (2 * S ^ 52) := by
    calc
      _ ≤ (mu : ℕ) * S ^ 12 := hR
      _ ≤ (2 * groupSize S mu * S ^ 40) * S ^ 12 := hmul
      _ = _ := by rw [mul_assoc (2 * groupSize S mu), heq]; ring
  have hd := Nat.div_le_of_le_mul hR'
  have hS52 : 1 ≤ S ^ 52 := one_le_pow₀ hS1
  have hS2 : 4 ≤ S ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_left (S ^ 52) hS2
  have h54 : S ^ 54 = S ^ 52 * S ^ 2 := by rw [← pow_add]
  unfold SparseGroups.count
  rw [h54]
  nlinarith

end
end Lax343628Proofs.BlockParameters

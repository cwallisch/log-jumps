import Lax343628Proofs.GrowthParameters

namespace Lax343628Proofs.UniformBlockBudget

open Lax343628Proofs.BlockParameters Lax343628Proofs.ColumnBudget Lax343628Proofs.SparseGroups
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

lemma budget (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hk : 2 ≤ k) (hn : 4 * k ≤ n)
    (hkS : k ≤ (S : ℕ)) (hDS : (3 : ℝ) ^ k ≤ (S : ℕ))
    (pc omega L f A F : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1)
    (hw : 1 / (S : ℕ) ≤ omega ∧ omega ≤ 1) (hL : 1 ≤ L)
    (hmu : ((S : ℕ) : ℝ) ^ 64 * L ≤ (mu : ℕ))
    (hf : ((S : ℕ) : ℝ) ^ 64 * L ≤ (mu : ℕ) * f)
    (hA : ((S : ℕ) : ℝ) ^ 64 * L ≤ (mu : ℕ) * A) (hA1 : A ≤ 1)
    (hF : 0 ≤ F) (hFQ : F ≤ (32 * (3 : ℝ) ^ k) * f)
    (hsize : ((S : ℕ) : ℝ) ^ 40 ≤ (n : ℝ) * A) :
    Budget n k (horizon (S : ℕ) mu) (groupSize (S : ℕ) mu) mu (samples S)
      pc (pc / ((mu : ℕ) + 1 : ℝ)) f A F omega L 8 := by
  let s : ℝ := (S : ℕ)
  let D : ℝ := (3 : ℝ) ^ k
  let a : ℝ := pc / ((mu : ℕ) + 1 : ℝ)
  let M : ℝ := s ^ 64 * L
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hkSR : (k : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hkS
  have hs1 : 1 ≤ s := by linarith
  have hsp : 0 < s := by linarith
  have hmp : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hS2 : 2 ≤ (S : ℕ) := by omega
  have hHp : 1 ≤ s ^ 12 := one_le_pow₀ hs1
  have hD : 1 ≤ D := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hDp : 0 ≤ D := by linarith
  have hQ : 1 ≤ 32 * D := by linarith
  have hQS : 32 * D ≤ s ^ 2 := by
    have hh := mul_le_mul (show (32 : ℝ) ≤ s by linarith) hDS hDp hsp.le
    change 32 * D ≤ s ^ 2
    nlinarith
  have hM1 : 2 ≤ M := by
    have hp : s ^ 1 ≤ s ^ 64 := pow_le_pow_right₀ hs1 (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hL (show 0 ≤ s ^ 64 by positivity)
    dsimp [M]
    norm_num only [pow_one, mul_one] at hp hm
    linarith
  have hmu40 : (S : ℕ) ^ 40 ≤ (mu : ℕ) := by
    have hp : s ^ 40 ≤ s ^ 64 := pow_le_pow_right₀ hs1 (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hL (show 0 ≤ s ^ 64 by positivity)
    have hh : s ^ 40 ≤ (mu : ℕ) := by linarith
    dsimp [s] at hh
    exact_mod_cast hh
  have hu40 : s ^ 40 ≤ (mu : ℕ) := by dsimp [s]; exact_mod_cast hmu40
  have hR : ((horizon (S : ℕ) mu : ℕ) : ℝ) ≤ (mu : ℕ) * s ^ 12 := by
    dsimp [s]
    exact_mod_cast horizon_bound (S : ℕ) hS2 mu
  have hAp : 0 < A := ((mul_pos_iff.mp ((show (0 : ℝ) < M by linarith).trans_le hA)).resolve_right
    (by rintro ⟨hh, _⟩; linarith)).2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn40 := DimensionBounds.dimension s n A hs1 hnR hA1 hsize
  have hpcp : 0 < pc := (div_pos (by norm_num) hsp).trans_le hpc.1
  have hwp : 0 < omega := (div_pos (by norm_num) hsp).trans_le hw.1
  have hap : 0 ≤ a := by dsimp [a]; positivity
  have haMu : a ≤ 1 / ((mu : ℕ) : ℝ) := by
    apply (div_le_div_of_nonneg_right hpc.2 (by positivity : (0 : ℝ) ≤ (mu : ℕ) + 1)).trans
    exact div_le_div_of_nonneg_left (by norm_num) hmp (by linarith)
  have ha1 : a ≤ 1 := haMu.trans ((div_le_one hmp).mpr (by exact_mod_cast mu.pos))
  have hRa : (horizon (S : ℕ) mu : ℝ) * a = pc * s ^ 10 := by
    dsimp [horizon, a, s]
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
    field_simp
  have hRt : (horizon (S : ℕ) mu : ℝ) * a ≤ s ^ 12 := by
    have hh := mul_le_mul hR haMu hap (show (0 : ℝ) ≤ (mu : ℕ) * s ^ 12 by positivity)
    have heq : ((mu : ℕ) : ℝ) * s ^ 12 * (1 / (mu : ℕ)) = s ^ 12 := by field_simp
    rwa [heq] at hh
  have hbig := BlockParameterBounds.mass s D (32 * D) L hs hDp hDS (by positivity) hQS (by linarith)
  have hsampling := BlockParameterBounds.sampling s D hs hDp hDS
  have hsampling' : 10 * s ^ 12 * (1 / s ^ 40) * D ^ 2 + s ^ 12 * D / Real.sqrt (samples S : ℕ) ≤ 1 / 32 := by
    rwa [sqrt_samples]
  have hlists := BlockParameterBounds.lists s (count (horizon (S : ℕ) mu) (groupSize (S : ℕ) mu)) omega hs
    (by positivity) (by dsimp [s]; exact_mod_cast group_count (S : ℕ) hS2 mu hmu40) hw.1
  have hlists' : (count (horizon (S : ℕ) mu) (groupSize (S : ℕ) mu) : ℝ) *
      (4 / ((samples S : ℕ) * omega ^ 2)) ≤ 1 / 8 := by
    change (count (horizon (S : ℕ) mu) (groupSize (S : ℕ) mu) : ℝ) *
      (4 / ((((S : ℕ) ^ 120 : ℕ) : ℝ) * omega ^ 2)) ≤ 1 / 8
    simpa only [Nat.cast_pow] using hlists
  have hz1 : 1 / s ^ 40 ≤ 1 := by
    apply (div_le_one (by positivity : 0 < s ^ 40)).mpr
    exact one_le_pow₀ hs1
  have herror : (horizon (S : ℕ) mu : ℝ) * a * ReproductiveAdmissibility.error n k ≤ 1 := by
    have hh := DimensionBounds.horizon_error s n D k ((horizon (S : ℕ) mu : ℝ) * a)
      hs hn40 hDp hDS (by positivity) hkSR (by positivity) hRt
    exact hh
  have hgrowth := GrowthParameters.growth s (horizon (S : ℕ) mu) a pc omega k hs
    (by omega) hkSR hDS (by positivity) hap ha1 hpc.1 hw.1 hw.2 hRa
  exact BudgetReduction.of_mass pc a f A F omega L 8 (s ^ 12) (32 * D) M (1 / s ^ 40)
    hk hn (group_positive (S : ℕ) (by omega) mu hmu40) ⟨hpcp.le, hpc.2⟩ rfl
    hHp hQ hL hM1 hmu hf hA hA1 hF hFQ hwp hR hbig
    (group_upper (S : ℕ) (by omega) mu) hz1 hsampling'
    (DimensionBounds.drift s n A (mu : ℕ) D k hs hnR hAp hu40 hsize hDp hDS (by positivity) hkSR)
    hlists' (DimensionBounds.immigration s n A hs1 hnR hsize)
    (DimensionBounds.bias s n D k hs hn40 hDp hDS (by positivity) hkSR)
    herror (DimensionBounds.shadow_error s n D k a hs hn40 hDp hDS (by positivity) hkSR hap ha1)
    (DimensionBounds.shadow_dimension s n D k (ShadowGaps.delta k) omega hs hn40 hDp hDS
      (by positivity) hkSR (GrowthParameters.delta_lower s hs k (by omega) hkSR) hw.1)
    hgrowth

end
end Lax343628Proofs.UniformBlockBudget

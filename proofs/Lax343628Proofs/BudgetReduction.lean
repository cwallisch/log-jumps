import Lax343628Proofs.TrackingMass

namespace Lax343628Proofs.BudgetReduction

open Lax343628Proofs.ColumnBudget Lax343628Proofs.SparseGroups
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu rs : ℕ+}

lemma of_mass (pc a f A F omega L B H Q M zeta : ℝ)
    (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hell : 1 ≤ ell)
    (hpc : 0 ≤ pc ∧ pc ≤ 1) (halpha : a = pc / ((mu : ℕ) + 1 : ℝ))
    (hH : 1 ≤ H) (hQ : 1 ≤ Q) (hL : 1 ≤ L) (hM : 2 ≤ M)
    (hmu : M ≤ (mu : ℕ)) (hmf : M ≤ (mu : ℕ) * f) (hma : M ≤ (mu : ℕ) * A)
    (hA1 : A ≤ 1) (hF : 0 ≤ F) (hFQ : F ≤ Q * f) (homega : 0 < omega)
    (hR : (R : ℝ) ≤ (mu : ℕ) * H)
    (hbig : H * ((3 : ℝ) ^ k) ^ 4 * Q * L / M ≤ 1 / 16777216)
    (hzeta : (ell : ℝ) / (mu : ℕ) ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hsampling : 10 * H * zeta * ((3 : ℝ) ^ k) ^ 2 + H * (3 : ℝ) ^ k / Real.sqrt (rs : ℕ) ≤ 1 / 32)
    (hdrift : H * (3 : ℝ) ^ k / (mu : ℕ) +
      H * (3 : ℝ) ^ k * ((k : ℝ) + 2) / (n * A) ≤ 1 / 32)
    (hlists : (count R ell : ℝ) * (4 / ((rs : ℕ) * omega ^ 2)) ≤ 1 / 8)
    (himm : 1 / (n : ℝ) ≤ A)
    (hbias : (3 : ℝ) ^ k * ((k : ℝ) + 1) / n ≤ 1)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (hshadow : a * (128 * (k : ℝ) ^ 2 / n) * (3 : ℝ) ^ k ≤ 1)
    (hdimension : (128 * (k : ℝ) ^ 2 / n) * (3 : ℝ) ^ k * (1 + (3 : ℝ) ^ k) ≤
      ShadowGaps.delta k * (omega / 2) / 2)
    (hgrowth : Real.log (B * (3 : ℝ) ^ k) + 1 ≤ R * Real.log (SparseGrowth.base k a omega)) :
    Budget n k R ell mu rs pc a f A F omega L B := by
  have hup : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hHp : 0 ≤ H := by linarith
  have hMp : 0 < M := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : 0 < A := ((mul_pos_iff.mp (hMp.trans_le hma)).resolve_right
    (by rintro ⟨hh, _⟩; linarith)).2
  have ha : 0 ≤ a := by rw [halpha]; exact div_nonneg hpc.1 (by positivity)
  have ha1 : a ≤ 1 / ((mu : ℕ) : ℝ) := by
    rw [halpha]
    apply (div_le_div_of_nonneg_right hpc.2 (by positivity : (0 : ℝ) ≤ (mu : ℕ) + 1)).trans
    exact div_le_div_of_nonneg_left (by norm_num) hup (by linarith)
  have hD : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hmasses := TrackingMass.of_mass R (mu : ℕ) a ((3 : ℝ) ^ k) f A F L H Q M
    (by linarith) hmu hmf hma hR (Nat.cast_nonneg _) hH hD hQ hL ha ha1 hF hFQ hbig
  have hcell : (ell : ℝ) * a ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left ha1 (show (0 : ℝ) ≤ ell by positivity)
    have hh' : (ell : ℝ) * a ≤ (ell : ℝ) / (mu : ℕ) := by convert hh using 1 <;> first | rfl | ring
    exact hh'.trans (hzeta.trans hzeta1)
  refine ⟨hk, hn, hell, hpc, ha, halpha, hcell, horizon, ?_, ?_, hF, homega,
    by linarith, himm, hbias, hmasses.small, ?_, ?_, ?_, hlists,
    hmasses.stepM, hmasses.varM, hmasses.stepR, hmasses.varR, hshadow, hdimension, hgrowth⟩
  · apply (div_lt_iff₀ hup).mpr
    nlinarith
  · apply (div_lt_iff₀ hup).mpr
    nlinarith
  · intro T
    have ht : (T.val : ℝ) ≤ R := by exact_mod_cast (Nat.le_of_lt_succ T.isLt)
    have htime : (T.val : ℝ) ≤ (mu : ℕ) * H := ht.trans hR
    apply (BudgetEstimates.drift T.val (mu : ℕ) H a ((3 : ℝ) ^ k) ((k : ℝ) + 1) n A
      (Nat.cast_nonneg _) htime hup hHp ha ha1 (by positivity) (by positivity) hnR hA hA1).trans
    convert hdrift using 1 <;> first | rfl | ring
  · intro T
    exact hmasses.square T.val (Nat.cast_nonneg _) (by exact_mod_cast (Nat.le_of_lt_succ T.isLt))
  · intro T
    have ht : (T.val : ℝ) ≤ (mu : ℕ) * H :=
      (show (T.val : ℝ) ≤ R by exact_mod_cast (Nat.le_of_lt_succ T.isLt)).trans hR
    have hat : a * T.val ≤ H := by
      have hh := mul_le_mul ha1 ht (Nat.cast_nonneg T.val) (by positivity : (0 : ℝ) ≤ 1 / (mu : ℕ))
      have heq : 1 / ((mu : ℕ) : ℝ) * ((mu : ℕ) * H) = H := by field_simp
      rwa [heq] at hh
    have hc := BudgetEstimates.mismatch (mu : ℕ) ell a ((3 : ℝ) ^ k) zeta hup ha1 hD hzeta
    have hc0 : 0 ≤ MismatchTotals.cost (mu : ℕ) ell a ((3 : ℝ) ^ k) := by
      unfold MismatchTotals.cost
      positivity
    have h1 := mul_le_mul hat hc hc0 hHp
    have h2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hat (show (0 : ℝ) ≤ (3 : ℝ) ^ k by positivity))
      (show 0 ≤ 2 * Real.sqrt (rs : ℕ) by positivity)
    have hh : 2 * (a * T.val * MismatchTotals.cost (mu : ℕ) ell a ((3 : ℝ) ^ k) +
        a * T.val * (3 : ℝ) ^ k / (2 * Real.sqrt (rs : ℕ))) ≤
        10 * H * zeta * ((3 : ℝ) ^ k) ^ 2 + H * (3 : ℝ) ^ k / Real.sqrt (rs : ℕ) := by
      linear_combination 2 * h1 + 2 * h2
    exact hh.trans hsampling

end
end Lax343628Proofs.BudgetReduction

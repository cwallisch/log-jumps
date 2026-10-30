import Lax343628Proofs.Dynamics
import Lax343628Proofs.Flatness
import Lax343628Proofs.FiniteChain
import Lax343628Proofs.ElementaryBounds

namespace Lax343628Proofs.Plateau

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.Dynamics
open Lax343628Proofs.Flatness Lax343628Proofs.FiniteChain Lax343628Proofs.ElementaryBounds
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma insert_optimum {n k : ℕ} {μ : ℕ+} (hk : 0 < k) (P : Population n μ)
    (Q : Population n μ) (hQ : Q ∈ (insert (jump k) P (optimum n)).support) :
    Q ∉ missing := by
  obtain ⟨d, hd, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
  have hQ := (PMF.mem_support_pure_iff _ Q).mp hQ
  subst Q
  have hmin : ∀ j, jump k (Fin.lastCases (optimum n) P d) ≤
      jump k (Fin.lastCases (optimum n) P j) := by
    simpa [deletionIndex] using hd
  split_ifs with h
  · intro hmiss
    exact hmiss ⟨d.val, h⟩ (Function.update_self _ _ _)
  · have hdlast : d = Fin.last (μ : ℕ) := Fin.ext (by have h' := d.isLt; simp; omega)
    let i : Fin (μ : ℕ) := ⟨0, μ.pos⟩
    have hPi : P i = optimum n := by
      by_contra hPi
      have hm := hmin i.castSucc
      rw [hdlast, Fin.lastCases_last, Fin.lastCases_castSucc] at hm
      exact not_lt_of_ge hm (jump_lt_optimum hk (P i) hPi)
    exact fun hmiss ↦ hmiss i hPi

lemma insert_optimum_success {n k : ℕ} {μ : ℕ+} (hk : 0 < k) (P : Population n μ) :
    (insert (jump k) P (optimum n)).toOuterMeasure missingᶜ = 1 := by
  rw [PMF.toOuterMeasure_apply_eq_one_iff]
  intro Q hQ
  exact insert_optimum hk P Q hQ

lemma offspring_le_success {n k : ℕ} {μ : ℕ+} (hk : 0 < k) (p_c : ℝ)
    (P : Population n μ) :
    offspring p_c P (optimum n) ≤ (step (jump k) p_c P).toOuterMeasure missingᶜ := by
  rw [step_eq, PMF.toOuterMeasure_bind_apply]
  have h := ENNReal.le_tsum (f := fun z ↦ offspring p_c P z *
    (insert (jump k) P z).toOuterMeasure missingᶜ) (optimum n)
  simpa only [insert_optimum_success hk P, mul_one] using h

lemma crossover_parent_mass {n k : ℕ} {μ : ℕ+} (p_c : ℝ)
    (hp : 0 ≤ p_c ∧ p_c ≤ 1) (P : Population n μ)
    (hP : ∀ i, (zeros (P i)).card = k) :
    ENNReal.ofReal p_c *
      (PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ))).toOuterMeasure (complementary P) *
      (2 : ℝ≥0∞)⁻¹ ^ (2 * k) ≤ parents p_c P (optimum n) := by
  have hbranch := bind_apply_lower (coin p_c) (fun b ↦ if b = 1 then
      (PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ))).bind (fun uv ↦
        (PMF.uniformOfFintype (BitString n)).bind fun mask ↦
          PMF.pure (crossover (P uv.1) (P uv.2) mask))
      else (PMF.uniformOfFintype (Fin (μ : ℕ))).bind fun u ↦ PMF.pure (P u)) 1 (optimum n)
  simp only [ite_true, coin_one p_c hp] at hbranch
  have hpairs :
      (PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ))).toOuterMeasure (complementary P) *
        (2 : ℝ≥0∞)⁻¹ ^ (2 * k) ≤
      ((PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ))).bind fun uv ↦
        (PMF.uniformOfFintype (BitString n)).bind fun mask ↦
          PMF.pure (crossover (P uv.1) (P uv.2) mask)) (optimum n) := by
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right, PMF.bind_apply]
    apply ENNReal.tsum_le_tsum
    intro uv
    by_cases huv : uv ∈ complementary P
    · have hc := crossover_optimum (P uv.1) (P uv.2) huv
      rw [hP uv.1, hP uv.2, ← two_mul k] at hc
      simp only [Set.indicator_of_mem huv, hc]
      exact le_rfl
    · simp only [Set.indicator_of_notMem huv, zero_mul, zero_le]
  rw [mul_assoc]
  have h := (mul_le_mul_right hpairs (ENNReal.ofReal p_c)).trans hbranch
  simpa only [parents, Bind.bind, Pure.pure] using h

lemma flat_offspring_success {n k : ℕ} {μ : ℕ+} (hn : 2 ≤ n) (p_c : ℝ)
    (hp : 0 ≤ p_c ∧ p_c ≤ 1) (P : Population n μ)
    (hP : ∀ i, (zeros (P i)).card = k)
    (hflat : ∀ j, 2 * k * columnCount P j ≤ (μ : ℕ)) :
    ENNReal.ofReal (p_c / 16) * (4 : ℝ≥0∞)⁻¹ ^ k ≤ offspring p_c P (optimum n) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp_mut : 0 ≤ 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1 := by
    constructor
    · positivity
    · have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hnR
      linarith
  have hnomut : ENNReal.ofReal (1 / 8) ≤ ENNReal.ofReal (1 - 1 / (n : ℝ)) ^ n := by
    rw [← ENNReal.ofReal_pow (sub_nonneg.mpr hp_mut.2)]
    exact ENNReal.ofReal_le_ofReal (no_mutation_lower n hn)
  have hparent : ENNReal.ofReal p_c * (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ^ (2 * k) ≤
      parents p_c P (optimum n) :=
    (mul_le_mul' (mul_le_mul' le_rfl (complementary_probability P hP hflat)) le_rfl).trans
      (crossover_parent_mass p_c hp P hP)
  have hmut := mutation_preserves_mass (1 / (n : ℝ)) hp_mut (parents p_c P) (optimum n)
  have h := (mul_le_mul' hparent hnomut).trans hmut
  have hfour : (2 : ℝ≥0∞)⁻¹ ^ (2 * k) = (4 : ℝ≥0∞)⁻¹ ^ k := by
    rw [pow_mul, ← ENNReal.inv_pow]
    norm_num
  rw [hfour] at h
  have heq : ENNReal.ofReal p_c * (2 : ℝ≥0∞)⁻¹ * (4 : ℝ≥0∞)⁻¹ ^ k *
      ENNReal.ofReal (1 / 8) = ENNReal.ofReal (p_c / 16) * (4 : ℝ≥0∞)⁻¹ ^ k := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8), ENNReal.ofReal_one,
      one_div, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16)]
    norm_num only [ENNReal.ofReal_ofNat]
    rw [mul_right_comm _ _ ((8 : ℝ≥0∞)⁻¹), mul_assoc (ENNReal.ofReal p_c),
      ← ENNReal.mul_inv (by norm_num) (by norm_num)]
    norm_num [div_eq_mul_inv]
  rw [heq] at h
  simpa only [offspring, Bind.bind, Pure.pure, PMF.bind_bind, PMF.pure_bind] using h

end
end Lax343628Proofs.Plateau

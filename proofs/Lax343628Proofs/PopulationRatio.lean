import Lax343628Proofs.MutationDrift
import Lax343628Proofs.RatioBounds

namespace Lax343628Proofs.PopulationRatio

open Lax343628.Algorithm Lax343628Proofs.Deletion Lax343628Proofs.FiniteDrift
open Lax343628Proofs.RatioBounds
open Lax343628Proofs.PlateauDynamics Lax343628Proofs.Sampling
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def indicator {n : ℕ} (B x : BitString n) : ℝ := if x = B then 1 else 0

def count {n : ℕ} {μ : ℕ+} (B : BitString n) (P : Population n μ) : ℝ := total (indicator B) P

def ratio {n : ℕ} {μ : ℕ+} (w : BitString n → ℝ) (B : BitString n) (P : Population n μ) : ℝ :=
  total w P / count B P

lemma count_nonneg {n : ℕ} {μ : ℕ+} (B : BitString n) (P : Population n μ) : 0 ≤ count B P := by
  unfold count total
  apply Finset.sum_nonneg
  intro i _
  unfold indicator
  split_ifs <;> norm_num

lemma count_le_size {n : ℕ} {μ : ℕ+} (B : BitString n) (P : Population n μ) :
    count B P ≤ (μ : ℕ) := by
  have h : count B P ≤ ∑ _i : Fin (μ : ℕ), (1 : ℝ) := by
    unfold count total
    apply Finset.sum_le_sum
    intro i _
    unfold indicator
    split_ifs <;> norm_num
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using h

lemma update_count_abs {n : ℕ} {μ : ℕ+} (B : BitString n) (P : Population n μ)
    (i : Fin (μ : ℕ)) (z : BitString n) :
    |count B (Function.update P i z) - count B P| ≤ 1 := by
  change |total (indicator B) (Function.update P i z) - total (indicator B) P| ≤ _
  rw [total_update]
  unfold indicator
  split_ifs <;> norm_num

lemma ratio_nonneg {n : ℕ} {μ : ℕ+} (w : BitString n → ℝ) (B : BitString n)
    (hw : ∀ x, 0 ≤ w x) (P : Population n μ) : 0 ≤ ratio w B P :=
  div_nonneg (Finset.sum_nonneg (fun i _ ↦ hw (P i))) (count_nonneg B P)

lemma replacement_data {n : ℕ} (w : BitString n → ℝ) (B old child : BitString n)
    (hwB : w B = 0) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 5 / 4) :
    let a := w child - w old
    let b := indicator B child - indicator B old
    (b = -1 ∨ b = 0 ∨ b = 1) ∧ |a| ≤ 5 / 4 ∧ |b| ≤ 1 ∧
      (b = 1 → a ≤ 0) ∧ (b = -1 → 0 ≤ a) := by
  dsimp only
  have ha : |w child - w old| ≤ 5 / 4 := by
    apply abs_le.mpr
    constructor <;> linarith [(hw child).1, (hw child).2, (hw old).1, (hw old).2]
  by_cases hc : child = B <;> by_cases ho : old = B <;>
    norm_num [indicator, hc, ho, hwB, ha, (hw child).1, (hw old).1,
      (hw child).2, (hw old).2, abs_of_nonneg (hw child).1, abs_of_nonneg (hw old).1]

lemma update_ratio_identity {n : ℕ} {μ : ℕ+} (w : BitString n → ℝ) (B : BitString n)
    (P : Population n μ) (i : Fin (μ : ℕ)) (z : BitString n)
    (hN : 1 < count B P) :
    ratio w B (Function.update P i z) - ratio w B P =
      ((w z - w (P i)) - ratio w B P * (indicator B z - indicator B (P i))) /
        (count B P + (indicator B z - indicator B (P i))) := by
  have hcount : count B (Function.update P i z) =
      count B P + (indicator B z - indicator B (P i)) := by
    have h := total_update (indicator B) P i z
    change count B (Function.update P i z) - count B P = _ at h
    linarith
  have htotal : total w (Function.update P i z) = total w P + (w z - w (P i)) := by
    linarith [total_update w P i z]
  have hb : -1 ≤ indicator B z - indicator B (P i) := by
    unfold indicator
    split_ifs <;> norm_num
  have hN0 : count B P ≠ 0 := by linarith
  have hnext : count B P + (indicator B z - indicator B (P i)) ≠ 0 := by linarith
  unfold ratio
  rw [hcount, htotal]
  field_simp
  ring

lemma update_ratio_lower {n : ℕ} {μ : ℕ+} (w : BitString n → ℝ) (B : BitString n)
    (hwB : w B = 0) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 5 / 4)
    (P : Population n μ) (i : Fin (μ : ℕ)) (z : BitString n) (hN : 1 < count B P) :
    ((w z - w (P i)) - ratio w B P * (indicator B z - indicator B (P i))) / count B P ≤
      ratio w B (Function.update P i z) - ratio w B P := by
  rw [update_ratio_identity w B P i z hN]
  have hdata := replacement_data w B (P i) z hwB hw
  exact ratio_increment_lower _ _ _ _ hN (ratio_nonneg w B (fun x ↦ (hw x).1) P)
    hdata.1 hdata.2.2.2.1 hdata.2.2.2.2

lemma update_ratio_abs {n : ℕ} {μ : ℕ+} (w : BitString n → ℝ) (B : BitString n)
    (hwB : w B = 0) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 5 / 4)
    (P : Population n μ) (i : Fin (μ : ℕ)) (z : BitString n) (hN : 1 < count B P) :
    |ratio w B (Function.update P i z) - ratio w B P| ≤
      (5 / 4 + ratio w B P) / (count B P - 1) := by
  rw [update_ratio_identity w B P i z hN]
  have hdata := replacement_data w B (P i) z hwB hw
  exact ratio_increment_abs _ _ _ _ hN (ratio_nonneg w B (fun x ↦ (hw x).1) P)
    hdata.2.1 hdata.2.2.1

lemma replace_ratio_lower {n : ℕ} {μ : ℕ+} (w : BitString n → ℝ) (B : BitString n)
    (hwB : w B = 0) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 5 / 4)
    (P : Population n μ) (z : BitString n) (hN : 1 < count B P)
    (d : Fin ((μ : ℕ) + 1)) :
    ((total w (replace P z d) - total w P) -
      ratio w B P * (count B (replace P z d) - count B P)) / count B P ≤
        ratio w B (replace P z d) - ratio w B P := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) d
  · simp [replace]
  · rw [total_replace_castSucc]
    have hc := total_replace_castSucc (indicator B) P z i
    change count B (replace P z i.castSucc) - count B P = _ at hc
    rw [hc]
    have hrepl : replace P z i.castSucc = Function.update P i z := by simp [replace, i.isLt]
    rw [hrepl]
    exact update_ratio_lower w B hwB hw P i z hN

lemma replace_ratio_abs {n : ℕ} {μ : ℕ+} (w : BitString n → ℝ) (B : BitString n)
    (hwB : w B = 0) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 5 / 4)
    (P : Population n μ) (z : BitString n) (hN : 1 < count B P)
    (d : Fin ((μ : ℕ) + 1)) :
    |ratio w B (replace P z d) - ratio w B P| ≤
      (5 / 4 + ratio w B P) / (count B P - 1) := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) d
  · have hQ := ratio_nonneg w B (fun x ↦ (hw x).1) P
    have hbound : 0 ≤ (5 / 4 + ratio w B P) / (count B P - 1) := by positivity
    simpa [replace] using hbound
  · have hrepl : replace P z i.castSucc = Function.update P i z := by simp [replace, i.isLt]
    rw [hrepl]
    exact update_ratio_abs w B hwB hw P i z hN

lemma auxiliary_ratio_pointwise {n k : ℕ} {μ : ℕ+} (w : BitString n → ℝ) (B : BitString n)
    (hwB : w B = 0) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 5 / 4) (p_c : ℝ)
    (P : Population n μ) (hN : 1 < count B P) (Q : Population n μ)
    (hQ : Q ∈ (auxiliaryStep k p_c P).support) :
    ((total w Q - total w P) - ratio w B P * (count B Q - count B P)) / count B P ≤
      ratio w B Q - ratio w B P := by
  obtain ⟨z, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
  unfold auxiliaryInsert at hQ
  split_ifs at hQ with hz
  · obtain ⟨d, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    have hQ := (PMF.mem_support_pure_iff _ Q).mp hQ
    subst Q
    exact replace_ratio_lower w B hwB hw P z hN d
  · have hQ := (PMF.mem_support_pure_iff _ Q).mp hQ
    subst Q
    simp

lemma auxiliary_ratio_abs {n k : ℕ} {μ : ℕ+} (w : BitString n → ℝ) (B : BitString n)
    (hwB : w B = 0) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 5 / 4) (p_c : ℝ)
    (P : Population n μ) (hN : 1 < count B P) (Q : Population n μ)
    (hQ : Q ∈ (auxiliaryStep k p_c P).support) :
    |ratio w B Q - ratio w B P| ≤ (5 / 4 + ratio w B P) / (count B P - 1) := by
  obtain ⟨z, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
  unfold auxiliaryInsert at hQ
  split_ifs at hQ with hz
  · obtain ⟨d, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    have hQ := (PMF.mem_support_pure_iff _ Q).mp hQ
    subst Q
    exact replace_ratio_abs w B hwB hw P z hN d
  · have hQ := (PMF.mem_support_pure_iff _ Q).mp hQ
    subst Q
    have hpos := ratio_nonneg w B (fun x ↦ (hw x).1) P
    simp only [sub_self, abs_zero]
    positivity

lemma auxiliary_linear_drift {n k : ℕ} {μ : ℕ+} (hkn : k ≤ n)
    (w : BitString n → ℝ) (B : BitString n) (p_c : ℝ)
    (P : Population n μ) (hP : plateauPopulation k P) (hN : 0 < count B P) :
    mean (auxiliaryStep k p_c P) (fun Q ↦
      (total w Q - total w P) - ratio w B P * (count B Q - count B P)) =
      ((μ : ℕ) / ((μ : ℕ) + 1 : ℝ)) *
        (mean (offspring p_c P) (fun z ↦ if onPlateau k z then w z else 0) -
          ratio w B P * mean (offspring p_c P)
            (fun z ↦ if onPlateau k z then indicator B z else 0)) := by
  rw [mean_sub, mean_mul]
  change mean (auxiliaryStep k p_c P) (fun Q ↦ total w Q - total w P) -
    ratio w B P * mean (auxiliaryStep k p_c P)
      (fun Q ↦ total (indicator B) Q - total (indicator B) P) = _
  rw [auxiliary_statistic_drift hkn w p_c P hP,
    auxiliary_statistic_drift hkn (indicator B) p_c P hP]
  have hcancel : ratio w B P * total (indicator B) P = total w P := by
    exact div_mul_cancel₀ _ hN.ne'
  have hcancelV := congrArg (fun x ↦ x * mean (offspring p_c P)
    (fun z ↦ if onPlateau k z then 1 else 0)) hcancel
  field_simp
  nlinarith

lemma auxiliary_ratio_drift_lower {n k : ℕ} {μ : ℕ+} (hkn : k ≤ n)
    (w : BitString n → ℝ) (B : BitString n)
    (hwB : w B = 0) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 5 / 4) (p_c : ℝ)
    (P : Population n μ) (hP : plateauPopulation k P) (hN : 1 < count B P) :
    (((μ : ℕ) / ((μ : ℕ) + 1 : ℝ)) / count B P) *
      (mean (offspring p_c P) (fun z ↦ if onPlateau k z then w z else 0) -
        ratio w B P * mean (offspring p_c P)
          (fun z ↦ if onPlateau k z then indicator B z else 0)) ≤
      mean (auxiliaryStep k p_c P) (fun Q ↦ ratio w B Q - ratio w B P) := by
  have h := mean_mono_on_support (auxiliaryStep k p_c P)
    (auxiliary_ratio_pointwise w B hwB hw p_c P hN)
  have hfun : (fun Q : Population n μ ↦ ((total w Q - total w P) -
      ratio w B P * (count B Q - count B P)) / count B P) =
      (fun Q : Population n μ ↦ (count B P)⁻¹ * ((total w Q - total w P) -
        ratio w B P * (count B Q - count B P))) := by funext Q; ring
  rw [hfun, mean_mul, auxiliary_linear_drift hkn w B p_c P hP (by linarith)] at h
  convert h using 1
  ring

lemma auxiliary_count_abs {n k : ℕ} {μ : ℕ+} (B : BitString n) (p_c : ℝ)
    (P Q : Population n μ) (hQ : Q ∈ (auxiliaryStep k p_c P).support) :
    |count B Q - count B P| ≤ 1 := by
  obtain ⟨z, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
  unfold auxiliaryInsert at hQ
  split_ifs at hQ with hz
  · obtain ⟨d, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    have hQ := (PMF.mem_support_pure_iff _ Q).mp hQ
    subst Q
    change |count B (replace P z d) - count B P| ≤ 1
    refine Fin.lastCases ?_ (fun i ↦ ?_) d
    · simp [replace]
    · have hrepl : replace P z i.castSucc = Function.update P i z := by simp [replace, i.isLt]
      rw [hrepl]
      exact update_count_abs B P i z
  · have hQ := (PMF.mem_support_pure_iff _ Q).mp hQ
    subst Q
    norm_num

end
end Lax343628Proofs.PopulationRatio

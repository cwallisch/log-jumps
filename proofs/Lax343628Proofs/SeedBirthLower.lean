import Lax343628Proofs.SeedPairs
import Lax343628Proofs.SeedOverlap
import Lax343628Proofs.ClassAverages

namespace Lax343628Proofs.SeedBirthLower

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.SeedGeometry
open Lax343628Proofs.ColumnKernels Lax343628Proofs.SeedIdeal Lax343628Proofs.SeedPairs
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison Lax343628Proofs.ClassBirth
open Lax343628Proofs.EmpiricalKernels Lax343628Proofs.CurveBounds
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+} {i : Fin n}

lemma ownCross_lower (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r + 1)
    (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = r + 1) :
    Real.exp (-1) * t (r + 1 - C.card) *
      mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun u ↦ mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun v ↦
        if family C i (P u) ∧ ordinary C (P v) ∧ Disjoint (privateZeros C (P u)) (privateZeros C (P v)) then 1 else 0)) -
      (128 * (r + 1 : ℝ) ^ 2 / n) * phi C i P ≤
        ownCross P i 1 (liftClass (familyClass (r := r) (i := i) C)) := by
  let h := familyClass (r := r) (i := i) C
  let A := fun (u v : Fin (mu : ℕ)) ↦ if hb : P u i = 1 then action (P v) h ⟨P u, hP u, hb⟩ else 0
  have hnon (u v : Fin (mu : ℕ)) : 0 ≤ A u v := by
    dsimp [A]
    split_ifs
    · exact action_nonneg _ h (fun z ↦ by dsimp [h, familyClass]; split_ifs <;> norm_num) _
    · rfl
  have hpoint (u v : Fin (mu : ℕ)) :
      Real.exp (-1) * t (r + 1 - C.card) *
        (if family C i (P u) ∧ ordinary C (P v) ∧ Disjoint (privateZeros C (P u)) (privateZeros C (P v)) then 1 else 0) -
        (128 * (r + 1 : ℝ) ^ 2 / n) * (if family C i (P u) then 1 else 0) ≤ A u v := by
    by_cases hf : family C i (P u)
    · by_cases hg : ordinary C (P v) ∧ Disjoint (privateZeros C (P u)) (privateZeros C (P v))
      · have hh := family_lower hr hn C hi hC (⟨P u, hP u, hf.2⟩ : ColumnClass n (r + 1) i 1) (P v) (hP v) hf hg.1 hg.2
        simpa only [A, h, dif_pos hf.2, hf, hg, true_and, if_true, mul_one] using hh
      · have hbad : ¬(family C i (P u) ∧ ordinary C (P v) ∧ Disjoint (privateZeros C (P u)) (privateZeros C (P v))) := by tauto
        simp only [if_neg hbad, if_pos hf, mul_zero, mul_one, zero_sub]
        exact (neg_nonpos.mpr (by positivity)).trans (hnon u v)
    · have hbad : ¬(family C i (P u) ∧ ordinary C (P v) ∧ Disjoint (privateZeros C (P u)) (privateZeros C (P v))) := by tauto
      simp only [if_neg hbad, if_neg hf, mul_zero, sub_self]
      exact hnon u v
  have hmean := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun u ↦
    mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) (hpoint u))
  simp_rw [mean_sub, mean_mul, mean_const] at hmean
  have hrepr : ownCross P i 1 (liftClass h) =
      mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun u ↦ mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (A u)) := by
    rw [ClassAverages.ownCross_operator P hP]
    unfold ClassAverages.operatorAverage
    apply congrArg (mean (PMF.uniformOfFintype (Fin (mu : ℕ))))
    funext u
    by_cases hb : P u i = 1
    · simp only [dif_pos hb, A]
      rw [mixed_action, empirical, mean_map]
    · simp only [dif_neg hb, A, mean_const]
  rw [hrepr]
  exact hmean

lemma crossover_family_lower (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r + 1)
    (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = r + 1)
    (theta : ℝ) (hflat : ∀ j, j ∉ C → ClassChannels.fraction j 0 P ≤ theta) :
    phi C i P * (Real.exp (-1) * t (r + 1 - C.card) *
      (1 - rho C P - ((r + 1 - C.card + 1 : ℕ) : ℝ) * theta) - 128 * (r + 1 : ℝ) ^ 2 / n) ≤
      mean (offspring 1 P) (liftClass (familyClass (r := r) (i := i) C)) := by
  have hcross := ownCross_lower hr hn C hi hC P hP
  have hgood := SeedOverlap.family_good_ordinary C i hi hC P hP theta hflat
  have hscale := mul_le_mul_of_nonneg_left hgood
    (show 0 ≤ Real.exp (-1) * t (r + 1 - C.card) by
      unfold t
      exact mul_nonneg (Real.exp_pos _).le (profile_pos _ _).le)
  have hdecomp := offspring_decomposition 1 (by norm_num : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) P i 1
    (liftClass (familyClass (r := r) (i := i) C))
  have hother : 0 ≤ fromOpposite 1 P i 1 (liftClass (familyClass (r := r) (i := i) C)) := by
    apply mean_nonneg
    intro uv
    split_ifs
    · exact mean_nonneg _ (fun z ↦ by
        unfold liftClass familyClass
        split_ifs <;> norm_num)
    · rfl
  norm_num only [one_mul, sub_self, zero_mul, add_zero] at hdecomp
  nlinarith

end
end Lax343628Proofs.SeedBirthLower

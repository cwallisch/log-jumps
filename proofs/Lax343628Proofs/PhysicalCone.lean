import Lax343628Proofs.ClassTest

namespace Lax343628Proofs.PhysicalCone

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.ColumnKernels Lax343628Proofs.PrivateColumns
open Lax343628Proofs.GeneralBirthApproximation Lax343628Proofs.ColumnApproximation
open Lax343628Proofs.ClassTest Lax343628Proofs.FiniteDrift
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {i : Fin n} {b : Fin 2}

lemma private_disjoint (S : Finset (Fin n)) (x : BitString n) (hx : zeros x ⊆ S) :
    Disjoint ((zeros x).erase i) (freshSet S) := by
  apply Finset.disjoint_left.mpr
  intro j hj hjR
  exact (Finset.mem_sdiff.mp hjR).2 (hx (Finset.mem_of_mem_erase hj))

lemma size_adjacent (hk : 1 ≤ k) (b c : Fin 2) :
    size k c = size k b ∨ size k c = size k b + 1 ∨ size k c + 1 = size k b := by
  fin_cases b <;> fin_cases c <;> simp [size] <;> omega

lemma ideal_comparison (hk : 1 ≤ k) (S : Finset (Fin n)) (hR : k ≤ (freshSet S).card)
    (hi : i ∈ S) (x y : ColumnClass n k i b) (partner : BitString n)
    (hpartner : (zeros partner).card = k) (hx : zeros x.val ⊆ S) (hy : zeros y.val ⊆ S)
    (hu : zeros partner ⊆ S) (hstep : classDistance x y = 1)
    (rho : ℝ) (hrho : 2 ≤ rho) (h : ColumnClass n k i b → ℝ) (hn : ∀ z, 0 ≤ h z)
    (hc : ∀ z w, classDistance z w = 1 → h w ≤ rho * h z) :
    idealAction S partner h y ≤ rho * idealAction S partner h x ∧
      idealAction S partner h x ≤ rho * idealAction S partner h y := by
  rw [PrivateKernelFormula.column_ideal_private S hR hi y partner hy hu h,
    PrivateKernelFormula.column_ideal_private S hR hi x partner hx hu h,
    SetBirth.private_formula, SetBirth.private_formula]
  apply ParentCone.adjacent _ _ _ _ (private_card hk x) (private_card hk y)
    (by rw [private_distance]; exact hstep)
  · rw [private_card hk (⟨partner, hpartner, rfl⟩ : ColumnClass n k i (partner i))]
    exact size_adjacent hk b (partner i)
  · exact private_disjoint S x.val hx
  · exact private_disjoint S y.val hy
  · exact private_disjoint S partner hu
  · exact Finset.notMem_erase _ _
  · exact Finset.notMem_erase _ _
  · exact Finset.notMem_erase _ _
  · simpa [freshSet] using hi
  · unfold size; split_ifs <;> omega
  · exact hR
  · exact hrho
  · exact test_nonneg h hn
  · exact test_support hk h
  · exact test_cone hk rho (by linarith) h hn hc

lemma action_comparison (hk : 1 ≤ k) (hn : 4 * k ≤ n) (S : Finset (Fin n))
    (hS : S.card ≤ 3 * k) (hi : i ∈ S) (x y : ColumnClass n k i b) (partner : BitString n)
    (hpartner : (zeros partner).card = k) (hx : zeros x.val ⊆ S) (hy : zeros y.val ⊆ S)
    (hu : zeros partner ⊆ S) (hstep : classDistance x y = 1)
    (rho : ℝ) (hrho : 2 ≤ rho) (h : ColumnClass n k i b → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hh : ∀ z, 0 ≤ h z ∧ h z ≤ M)
    (hc : ∀ z w, classDistance z w = 1 → h w ≤ rho * h z) :
    action partner h y ≤ rho * action partner h x + 128 * (1 + rho) * M * (k : ℝ) ^ 2 / n := by
  have hR : k ≤ (freshSet S).card := by rw [freshSet_card]; omega
  have hcone := (ideal_comparison hk S hR hi x y partner hpartner hx hy hu hstep rho hrho h
    (fun z ↦ (hh z).1) hc).1
  have ex := (abs_le.mp (action_ideal_error hk hn S hS x partner hx hu h M hM hh)).1
  have ey := (abs_le.mp (action_ideal_error hk hn S hS y partner hy hu h M hM hh)).2
  have hp : 0 ≤ rho := by linarith
  have ht := mul_le_mul_of_nonneg_left ex hp
  calc
    action partner h y ≤ idealAction S partner h y + 128 * M * (k : ℝ) ^ 2 / n := by linarith
    _ ≤ rho * action partner h x + 128 * (1 + rho) * M * (k : ℝ) ^ 2 / n := by
      have hid : 128 * (1 + rho) * M * (k : ℝ) ^ 2 / n =
          128 * M * (k : ℝ) ^ 2 / n + rho * (128 * M * (k : ℝ) ^ 2 / n) := by ring
      rw [hid]
      linarith

lemma named_set_bound (hk : 2 ≤ k) (x y : ColumnClass n k i b) (partner : BitString n)
    (hp : (zeros partner).card = k) (hstep : classDistance x y = 1) :
    (insert i (zeros x.val ∪ zeros y.val ∪ zeros partner)).card ≤ 3 * k := by
  have hsd : (zeros x.val \ zeros y.val).card = 1 := hstep
  have hcard := Finset.card_inter_add_card_sdiff (zeros x.val) (zeros y.val)
  have hunion := Finset.card_union_add_card_inter (zeros x.val) (zeros y.val)
  have hlast := Finset.card_union_le (zeros x.val ∪ zeros y.val) (zeros partner)
  have hinsert := Finset.card_insert_le i (zeros x.val ∪ zeros y.val ∪ zeros partner)
  rw [x.property.1] at hcard
  rw [x.property.1, y.property.1] at hunion
  rw [hp] at hlast
  omega

lemma action_adjacent (hk : 2 ≤ k) (hn : 4 * k ≤ n) (x y : ColumnClass n k i b)
    (partner : BitString n) (hp : (zeros partner).card = k) (hstep : classDistance x y = 1)
    (rho : ℝ) (hrho : 2 ≤ rho) (h : ColumnClass n k i b → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hh : ∀ z, 0 ≤ h z ∧ h z ≤ M)
    (hc : ∀ z w, classDistance z w = 1 → h w ≤ rho * h z) :
    action partner h y ≤ rho * action partner h x + 128 * (1 + rho) * M * (k : ℝ) ^ 2 / n := by
  let S := insert i (zeros x.val ∪ zeros y.val ∪ zeros partner)
  apply action_comparison (by omega) hn S (named_set_bound hk x y partner hp hstep)
    (Finset.mem_insert_self _ _) x y partner hp _ _ _ hstep rho hrho h M hM hh hc
  all_goals
    intro j hj
    simp only [S, Finset.mem_insert, Finset.mem_union]
    tauto

lemma global_ratio (hk : 1 ≤ k) (rho : ℝ) (hrho : 1 ≤ rho)
    (h : ColumnClass n k i b → ℝ) (hh : ∀ z, 0 ≤ h z)
    (hc : ∀ z w, classDistance z w = 1 → h w ≤ rho * h z)
    (x y : ColumnClass n k i b) : h y ≤ rho ^ k * h x := by
  cases k with
  | zero => omega
  | succ r =>
    fin_cases b
    · exact (resident_ratio hrho h hh hc x y).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hrho (by omega : r ≤ r + 1)) (hh x))
    · exact mutant_ratio hrho h hh hc x y

lemma action_relative (hk : 2 ≤ k) (hn : 4 * k ≤ n) (x y : ColumnClass n k i b)
    (partner : BitString n) (hp : (zeros partner).card = k) (hstep : classDistance x y = 1)
    (rho : ℝ) (hrho : 2 ≤ rho) (hrho' : rho ≤ 3) (h : ColumnClass n k i b → ℝ)
    (hh : ∀ z, 0 ≤ h z) (hc : ∀ z w, classDistance z w = 1 → h w ≤ rho * h z) :
    action partner h y ≤ rho * action partner h x +
      (512 * (3 : ℝ) ^ k * (k : ℝ) ^ 2 / n) * h x := by
  have hD : ∀ z, h z ≤ (3 : ℝ) ^ k * h x := by
    intro z
    exact (global_ratio (by omega) rho (by linarith) h hh hc x z).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hrho' k) (hh x))
  have hhM : 0 ≤ (3 : ℝ) ^ k * h x := mul_nonneg (by positivity) (hh x)
  have ha := action_adjacent hk hn x y partner hp hstep rho hrho h _ hhM
    (fun z ↦ ⟨hh z, hD z⟩) hc
  have hbound : 128 * (1 + rho) * ((3 : ℝ) ^ k * h x) * (k : ℝ) ^ 2 / n ≤
      (512 * (3 : ℝ) ^ k * (k : ℝ) ^ 2 / n) * h x := by
    have ht : 128 * (1 + rho) ≤ (512 : ℝ) := by linarith
    have hp' := mul_nonneg hhM (sq_nonneg (k : ℝ))
    have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht hp')
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    convert hb using 1 <;> first | rfl | ring
  linarith [hbound]

end
end Lax343628Proofs.PhysicalCone

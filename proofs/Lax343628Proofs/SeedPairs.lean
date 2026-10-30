import Lax343628Proofs.SeedIdeal
import Lax343628Proofs.BirthMass

namespace Lax343628Proofs.SeedPairs

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.SeedGeometry
open Lax343628Proofs.ColumnKernels Lax343628Proofs.SeedIdeal Lax343628Proofs.ColumnApproximation
open Lax343628Proofs.GeneralBirthApproximation Lax343628Proofs.PrivatePool
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.CurveBounds
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {i : Fin n}

lemma ordinary_inter (C : Finset (Fin n)) (x y : BitString n)
    (hx : ordinary C x) (hy : ordinary C y) (hd : Disjoint (privateZeros C x) (privateZeros C y)) :
    zeros x ∩ zeros y = C := by
  apply Finset.Subset.antisymm
  · intro j hj
    by_contra hjC
    exact Finset.disjoint_left.mp hd (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hj).1, hjC⟩)
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hj).2, hjC⟩)
  · exact fun j hj ↦ Finset.mem_inter.mpr ⟨hx hj, hy hj⟩

lemma family_inter (C : Finset (Fin n)) (x y : BitString n)
    (hx : family C i x) (hy : ordinary C y) (hd : Disjoint (privateZeros C x) (privateZeros C y)) :
    zeros x ∩ zeros y = C.erase i := by
  apply Finset.Subset.antisymm
  · intro j hj
    have hjC : j ∈ C := by
      by_contra hjC
      exact Finset.disjoint_left.mp hd (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hj).1, hjC⟩)
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hj).2, hjC⟩)
    have hji : j ≠ i := by
      intro he
      have hz : x j = 0 := by simpa only [mem_zeros] using (Finset.mem_inter.mp hj).1
      rw [he, hx.2] at hz
      exact (by decide : (1 : Fin 2) ≠ 0) hz
    exact Finset.mem_erase.mpr ⟨hji, hjC⟩
  · exact fun j hj ↦ Finset.mem_inter.mpr ⟨hx.1 hj, hy (Finset.mem_of_mem_erase hj)⟩

lemma pair_plateau_le_resident (hn : 2 ≤ n) (x : ColumnClass n (r + 1) i 0)
    (y : BitString n) (hyi : y i = 0) :
    mean (pairMutation x.val y (1 / n)) (BirthMass.plateauTest (r + 1)) ≤
      action y (fun _ ↦ 1) x + 1 / (n : ℝ) := by
  have hp (z : BitString n) : BirthMass.plateauTest (r + 1) z ≤
      liftClass (fun _ : ColumnClass n (r + 1) i 0 ↦ (1 : ℝ)) z + (if z i = 1 then 1 else 0) := by
    unfold BirthMass.plateauTest liftClass
    by_cases hcard : (zeros z).card = r + 1
    · by_cases hz : z i = 0
      · simp only [if_pos hcard, dif_pos (And.intro hcard hz)]
        split_ifs <;> norm_num
      · have hz1 : z i = 1 := by have hh := (z i).isLt; omega
        simp only [if_pos hcard, dif_neg (by tauto : ¬((zeros z).card = r + 1 ∧ z i = 0)), if_pos hz1, zero_add, le_refl]
    · simp only [if_neg hcard, dif_neg (by tauto : ¬((zeros z).card = r + 1 ∧ z i = 0)), zero_add]
      split_ifs <;> norm_num
  have hh := mean_mono (pairMutation x.val y (1 / n)) hp
  rw [mean_add] at hh
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hprob : (0 : ℝ) ≤ 1 / n ∧ 1 / (n : ℝ) ≤ 1 := ⟨by positivity,
    (div_le_one (by positivity : (0 : ℝ) < n)).mpr (by linarith)⟩
  rw [pairMutation_class_mass x.val y (1 / n) hprob i 1,
    x.property.2, hyi, siteLaw_apply 0 0 1 _ hprob] at hh
  norm_num only [siteProbability, if_true, Fin.zero_ne_one, if_neg (by decide : (1 : Fin 2) ≠ 0), if_false,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / n)] at hh
  rw [action_eq_mean, classFactor, if_pos hyi.symm, one_mul]
  exact hh

lemma ordinary_upper (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r + 1)
    (x y : BitString n) (hx : (zeros x).card = r + 1) (hy : (zeros y).card = r + 1)
    (hox : ordinary C x) (hoy : ordinary C y) (hd : Disjoint (privateZeros C x) (privateZeros C y)) :
    mean (pairMutation x y (1 / n)) (BirthMass.plateauTest (r + 1)) ≤
      Real.exp (-1) * q (r + 1 - C.card) + 128 * (r + 1 : ℝ) ^ 2 / n + 1 / n := by
  let S := zeros x ∪ zeros y
  have hxi : x i = 0 := by simpa only [mem_zeros] using hox hi
  have hyi : y i = 0 := by simpa only [mem_zeros] using hoy hi
  let xx : ColumnClass n (r + 1) i 0 := ⟨x, hx, hxi⟩
  have hS : S.card ≤ 3 * (r + 1) := by have hh := Finset.card_union_le (zeros x) (zeros y); rw [hx, hy] at hh; dsimp [S]; omega
  have hxS : zeros x ⊆ S := Finset.subset_union_left
  have hyS : zeros y ⊆ S := Finset.subset_union_right
  have hR : r + 1 ≤ (freshSet S).card := by rw [freshSet_card]; omega
  have hiS : i ∈ S := hxS (hox hi)
  have hc : common i x y = C.erase i := by unfold common; rw [ordinary_inter C x y hox hoy hd]
  have he := action_ideal_error (by omega : 1 ≤ r + 1) hn S hS xx y hxS hyS (fun _ ↦ 1) 1 (by norm_num)
    (fun _ ↦ ⟨by norm_num, le_rfl⟩)
  rw [resident_value C S hi hC hR hiS xx y hy hyi hxS hyS hc] at he
  have hb := pair_plateau_le_resident (by omega : 2 ≤ n) xx y hyi
  have he' := (abs_le.mp he).2
  norm_num only [mul_one, one_mul, Nat.cast_add, Nat.cast_one] at he'
  exact hb.trans (by nlinarith)

lemma family_lower (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r + 1)
    (x : ColumnClass n (r + 1) i 1) (y : BitString n) (hy : (zeros y).card = r + 1)
    (hfx : family C i x.val) (hoy : ordinary C y) (hd : Disjoint (privateZeros C x.val) (privateZeros C y)) :
    Real.exp (-1) * t (r + 1 - C.card) - 128 * (r + 1 : ℝ) ^ 2 / n ≤
      action y (familyClass (r := r) (i := i) C) x := by
  let S := zeros x.val ∪ zeros y
  have hyi : y i = 0 := by simpa only [mem_zeros] using hoy hi
  have hS : S.card ≤ 3 * (r + 1) := by
    have hh := Finset.card_union_le (zeros x.val) (zeros y)
    rw [x.property.1, hy] at hh
    dsimp [S]
    omega
  have hxS : zeros x.val ⊆ S := Finset.subset_union_left
  have hyS : zeros y ⊆ S := Finset.subset_union_right
  have hR : r + 1 ≤ (freshSet S).card := by rw [freshSet_card]; omega
  have hiS : i ∈ S := hyS (hoy hi)
  have hc : common i x.val y = C.erase i := by unfold common; rw [family_inter C x.val y hfx hoy hd, Finset.erase_idem]
  have he := action_ideal_error (by omega : 1 ≤ r + 1) hn S hS x y hxS hyS (familyClass (r := r) (i := i) C) 1 (by norm_num)
    (fun z ↦ by unfold familyClass; split_ifs <;> norm_num)
  rw [mutant_value C S hi hC hR hiS x y hy hyi hxS hyS hc] at he
  have he' := (abs_le.mp he).1
  norm_num only [mul_one, one_mul, Nat.cast_add, Nat.cast_one] at he'
  linarith

end
end Lax343628Proofs.SeedPairs

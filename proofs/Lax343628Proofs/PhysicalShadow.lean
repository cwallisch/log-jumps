import Lax343628Proofs.PhysicalCone
import Lax343628Proofs.ShadowParent

namespace Lax343628Proofs.PhysicalShadow

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.ColumnKernels Lax343628Proofs.ColumnApproximation
open Lax343628Proofs.GeneralBirthApproximation Lax343628Proofs.ClassTest
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {i : Fin n}

def Related (x : ColumnClass n (r + 1) i 1) (y : ColumnClass n (r + 1) i 0) : Prop :=
  (zeros y.val).erase i ⊆ (zeros x.val).erase i

def bonus (y : ColumnClass n (r + 1) i 0) (partner : BitString n) : ℝ :=
  if (zeros y.val).erase i = (zeros partner).erase i then 0 else ShadowGaps.delta (r + 1)

lemma exists_extra (x : ColumnClass n (r + 1) i 1) (y : ColumnClass n (r + 1) i 0)
    (hxy : Related x y) : ∃ e, e ∉ (zeros y.val).erase i ∧
      (zeros x.val).erase i = insert e ((zeros y.val).erase i) := by
  have hcM := NormalizedPrivate.mutant_private_size x
  have hcR := NormalizedPrivate.resident_private_size y
  have hc : (((zeros x.val).erase i) \ ((zeros y.val).erase i)).card = 1 := by
    rw [Finset.card_sdiff_of_subset hxy, hcM, hcR]
    omega
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hc
  have hm := Finset.mem_sdiff.mp (show e ∈ ((zeros x.val).erase i) \ ((zeros y.val).erase i) by rw [he]; simp)
  refine ⟨e, hm.2, ?_⟩
  ext a
  constructor
  · intro ha
    by_cases haR : a ∈ (zeros y.val).erase i
    · exact Finset.mem_insert_of_mem haR
    · have hh : a ∈ ((zeros x.val).erase i) \ ((zeros y.val).erase i) := Finset.mem_sdiff.mpr ⟨ha, haR⟩
      rw [he, Finset.mem_singleton] at hh
      exact Finset.mem_insert.mpr (Or.inl hh)
  · intro ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hm.1
    · exact hxy ha

lemma ideal_comparison (S : Finset (Fin n)) (hR : r + 1 ≤ (freshSet S).card) (hi : i ∈ S)
    (x : ColumnClass n (r + 1) i 1) (y : ColumnClass n (r + 1) i 0)
    (partner : BitString n) (hp : (zeros partner).card = r + 1)
    (hx : zeros x.val ⊆ S) (hy : zeros y.val ⊆ S) (hu : zeros partner ⊆ S) (hxy : Related x y)
    (m : ColumnClass n (r + 1) i 1 → ℝ) (g : ColumnClass n (r + 1) i 0 → ℝ)
    (c L : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L) (hmin : ∀ z, L ≤ g z)
    (hdom : ∀ z w, Related z w → c * g w ≤ m z) :
    c * (idealAction S partner g y + bonus y partner * L) ≤ idealAction S partner m x := by
  obtain ⟨e, heA, heq⟩ := exists_extra x y hxy
  have heM : e ∈ (zeros x.val).erase i := by rw [heq]; simp
  have heS := hx (Finset.mem_of_mem_erase heM)
  have heR : e ∉ freshSet S := by simpa [freshSet] using heS
  have hie : i ≠ e := (Finset.ne_of_mem_erase heM).symm
  have hpSize : ((zeros partner).erase i).card = r ∨ ((zeros partner).erase i).card = r + 1 := by
    by_cases hbit : partner i = 0
    · left
      exact NormalizedPrivate.resident_private_size (⟨partner, hp, hbit⟩ : ColumnClass n (r + 1) i 0)
    · right
      have hbit' : partner i = 1 := by have hlt := (partner i).isLt; omega
      exact NormalizedPrivate.mutant_private_size (⟨partner, hp, hbit'⟩ : ColumnClass n (r + 1) i 1)
  rw [PrivateKernelFormula.column_ideal_private S hR hi y partner hy hu g,
    PrivateKernelFormula.column_ideal_private S hR hi x partner hx hu m,
    SetBirth.private_formula, SetBirth.private_formula, heq]
  apply ShadowParent.comparison _ _ _ (NormalizedPrivate.resident_private_size y) hpSize
    (Nat.le_succ r) (by omega) heA heR (PhysicalCone.private_disjoint S y.val hy)
    (PhysicalCone.private_disjoint S partner hu) (Finset.notMem_erase _ _) (Finset.notMem_erase _ _)
    (by simpa [freshSet] using hi) hie (by rfl) hR (test m) (test g)
    _ _ c L hc hL _ _
  · simpa [size] using test_support (by omega : 1 ≤ r + 1) m
  · simpa [size] using test_support (by omega : 1 ≤ r + 1) g
  · intro Z hZ hiZ
    rw [test_encode (by omega) g Z (by simpa [size] using hZ) hiZ]
    exact hmin _
  · intro Z W hZW hZ hW hiW
    have hiZ : i ∉ Z := fun hh ↦ hiW (hZW hh)
    rw [test_encode (by omega) g Z (by simpa [size] using hZ) hiZ,
      test_encode (by omega) m W (by simpa [size] using hW) hiW]
    apply hdom
    unfold Related
    rw [encode_private, encode_private]
    exact hZW

lemma action_comparison (hn : 4 * (r + 1) ≤ n) (S : Finset (Fin n))
    (hS : S.card ≤ 3 * (r + 1)) (hi : i ∈ S)
    (x : ColumnClass n (r + 1) i 1) (y : ColumnClass n (r + 1) i 0)
    (partner : BitString n) (hp : (zeros partner).card = r + 1)
    (hx : zeros x.val ⊆ S) (hy : zeros y.val ⊆ S) (hu : zeros partner ⊆ S) (hxy : Related x y)
    (m : ColumnClass n (r + 1) i 1 → ℝ) (g : ColumnClass n (r + 1) i 0 → ℝ)
    (c L U V : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L) (hmin : ∀ z, L ≤ g z)
    (hm : ∀ z, 0 ≤ m z ∧ m z ≤ U) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ V)
    (hdom : ∀ z w, Related z w → c * g w ≤ m z) :
    c * (action partner g y + bonus y partner * L - 128 * (r + 1 : ℝ) ^ 2 / n * V) -
      128 * (r + 1 : ℝ) ^ 2 / n * U ≤ action partner m x := by
  have hR : r + 1 ≤ (freshSet S).card := by rw [freshSet_card]; omega
  have hcomp := ideal_comparison S hR hi x y partner hp hx hy hu hxy m g c L hc hL hmin hdom
  have hU : 0 ≤ U := (hm x).1.trans (hm x).2
  have hV : 0 ≤ V := (hg y).1.trans (hg y).2
  have em := (abs_le.mp (action_ideal_error (by omega) hn S hS x partner hx hu m U hU hm)).1
  have eg := (abs_le.mp (action_ideal_error (by omega) hn S hS y partner hy hu g V hV hg)).2
  have hcast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by norm_num
  rw [hcast] at em eg
  have hM : 128 * U * (r + 1 : ℝ) ^ 2 / n = 128 * (r + 1 : ℝ) ^ 2 / n * U := by ring
  have hG : 128 * V * (r + 1 : ℝ) ^ 2 / n = 128 * (r + 1 : ℝ) ^ 2 / n * V := by ring
  rw [hM] at em
  rw [hG] at eg
  have ht := mul_le_mul_of_nonneg_left eg hc
  linarith

lemma named_set_bound (x : ColumnClass n (r + 1) i 1) (y : ColumnClass n (r + 1) i 0)
    (partner : BitString n) (hp : (zeros partner).card = r + 1) (hxy : Related x y) :
    (zeros x.val ∪ zeros y.val ∪ zeros partner).card ≤ 3 * (r + 1) := by
  have hsub : (zeros y.val).erase i ⊆ zeros x.val ∩ zeros y.val := by
    intro j hj
    exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (hxy hj), Finset.mem_of_mem_erase hj⟩
  have hci := Finset.card_le_card hsub
  rw [NormalizedPrivate.resident_private_size y] at hci
  have hcu := Finset.card_union_add_card_inter (zeros x.val) (zeros y.val)
  rw [x.property.1, y.property.1] at hcu
  have hcl := Finset.card_union_le (zeros x.val ∪ zeros y.val) (zeros partner)
  rw [hp] at hcl
  omega

lemma action_unconditional (hn : 4 * (r + 1) ≤ n)
    (x : ColumnClass n (r + 1) i 1) (y : ColumnClass n (r + 1) i 0)
    (partner : BitString n) (hp : (zeros partner).card = r + 1) (hxy : Related x y)
    (m : ColumnClass n (r + 1) i 1 → ℝ) (g : ColumnClass n (r + 1) i 0 → ℝ)
    (c L U V : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L) (hmin : ∀ z, L ≤ g z)
    (hm : ∀ z, 0 ≤ m z ∧ m z ≤ U) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ V)
    (hdom : ∀ z w, Related z w → c * g w ≤ m z) :
    c * (action partner g y + bonus y partner * L - 128 * (r + 1 : ℝ) ^ 2 / n * V) -
      128 * (r + 1 : ℝ) ^ 2 / n * U ≤ action partner m x := by
  let S := zeros x.val ∪ zeros y.val ∪ zeros partner
  have hi : i ∈ S := by
    apply Finset.mem_union.mpr; left
    apply Finset.mem_union.mpr; right
    rw [mem_zeros]; exact y.property.2
  apply action_comparison hn S (named_set_bound x y partner hp hxy) hi x y partner hp
    _ _ _ hxy m g c L U V hc hL hmin hm hg hdom
  all_goals intro j hj; simp only [S, Finset.mem_union]; tauto

lemma private_equal_iff (y : ColumnClass n (r + 1) i 0) (partner : BitString n)
    (hp : (zeros partner).card = r + 1) :
    (zeros y.val).erase i = (zeros partner).erase i ↔ partner = y.val := by
  constructor
  · intro heq
    have hiP : partner i = 0 := by
      by_contra hbit
      have hbit' : partner i = 1 := by have hlt := (partner i).isLt; omega
      have hcM := NormalizedPrivate.mutant_private_size
        (⟨partner, hp, hbit'⟩ : ColumnClass n (r + 1) i 1)
      have hcR := NormalizedPrivate.resident_private_size y
      rw [heq, hcM] at hcR
      omega
    have hzy : zeros y.val = insert i ((zeros y.val).erase i) :=
      (Finset.insert_erase (by rw [mem_zeros]; exact y.property.2)).symm
    have hzp : zeros partner = insert i ((zeros partner).erase i) :=
      (Finset.insert_erase (by rw [mem_zeros]; exact hiP)).symm
    have hz : zeros partner = zeros y.val := by rw [hzp, hzy, heq]
    have hh := congrArg NamedBirth.fromZeros hz
    simpa only [NamedBirth.fromZeros_zeros] using hh
  · rintro rfl; rfl

lemma bonus_eq (y : ColumnClass n (r + 1) i 0) (partner : BitString n)
    (hp : (zeros partner).card = r + 1) :
    bonus y partner = if partner = y.val then 0 else ShadowGaps.delta (r + 1) := by
  unfold bonus
  simp only [private_equal_iff y partner hp]

end
end Lax343628Proofs.PhysicalShadow

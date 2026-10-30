import Lax343628Proofs.ConeExpansion
import Lax343628Proofs.CatalystBounds

namespace Lax343628Proofs.ShadowBirth

open Lax343628Proofs.ConeExpansion Lax343628Proofs.BirthGeometry
open Lax343628Proofs.BirthCouplings Lax343628Proofs.ShadowMeans
open Lax343628Proofs.FiniteDrift
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

lemma split_one (K : ℕ) (C : Finset (Fin n)) (label : α ⊕ Unit ↪ Fin n)
    (R : Finset (Fin n)) (h : Finset (Fin n) → ℝ) :
    setValue K C label R h = (1 / 2 : ℝ) *
      (setValue K C (Function.Embedding.inl.trans label) R h +
        setValue K (insert (label (Sum.inr ())) C) (Function.Embedding.inl.trans label) R h) := by
  unfold setValue
  rw [BirthOn.split_sum, BirthSplit.sum_unit_sets]
  simp only [Fintype.card_unique, pow_one, Finset.map_empty, Finset.union_empty,
    Finset.map_singleton, Finset.union_singleton]
  rfl

omit [Fintype α] [DecidableEq α] in
lemma left_admissible (C : Finset (Fin n)) (label : α ⊕ Unit ↪ Fin n)
    (R : Finset (Fin n)) (hA : Admissible C label R) :
    Admissible C (Function.Embedding.inl.trans label) R :=
  ⟨fun a ↦ hA.named_fresh (Sum.inl a), fun a ↦ hA.named_common (Sum.inl a), hA.common_fresh⟩

omit [Fintype α] [DecidableEq α] in
lemma extra_point (C : Finset (Fin n)) (label : α ⊕ Unit ↪ Fin n)
    (R : Finset (Fin n)) (hA : Admissible C label R) :
    Extra C (Function.Embedding.inl.trans label) R (label (Sum.inr ())) := by
  refine ⟨hA.named_common _, hA.named_fresh _, ?_⟩
  intro a ha
  have hh : (Sum.inl a : α ⊕ Unit) = Sum.inr () := label.injective ha
  cases hh

omit [DecidableEq α] in
lemma insert_mass (r : ℕ) (C : Finset (Fin n)) (label : α ↪ Fin n) (e : Fin n)
    (he : e ∉ C) (_hC : C.card ≤ r) :
    mass (r + 1) (insert e C) label = mass r C label := by
  unfold mass
  rw [Finset.card_insert_of_notMem he, Nat.add_sub_add_right]

lemma outside {K j : ℕ} (C : Finset (Fin n)) (label : α ⊕ Unit ↪ Fin n)
    (R : Finset (Fin n)) (hAll : Admissible C label R) {i : Fin n} (hi : Extra C label R i)
    (hK : K ≤ R.card) (hrK : C.card + j + 1 ≤ K)
    (m g : Finset (Fin n) → ℝ) (hmzero : ∀ Z, Z.card ≠ C.card + j + 1 → m Z = 0)
    (hgzero : ∀ Z, Z.card ≠ C.card + j → g Z = 0)
    (c L eps : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L) (heps : 0 ≤ eps)
    (hmin : ∀ U, U.card = C.card + j → i ∉ U → L ≤ g U)
    (hdom : ∀ U V, U ⊆ V → U.card = C.card + j → V.card = C.card + j + 1 →
      i ∉ V → c * g U ≤ m V)
    (hrise : mass (C.card + j) C (Function.Embedding.inl.trans label) ≤
      mass (C.card + j + 1) C (Function.Embedding.inl.trans label))
    (hsurplus : eps ≤ (mass (C.card + j + 1) C (Function.Embedding.inl.trans label) -
      mass (C.card + j) C (Function.Embedding.inl.trans label)) / 2) :
    c * (setValue K C (Function.Embedding.inl.trans label) R g + eps * L) ≤
      setValue K C label R m := by
  let l := Function.Embedding.inl.trans label
  let e := label (Sum.inr ())
  let r := C.card + j
  have hA := left_admissible C label R hAll
  have he : Extra C l R e := extra_point C label R hAll
  have hiL : Extra C l R i := ⟨hi.1, hi.2.1, fun a ↦ hi.2.2 (Sum.inl a)⟩
  have hie : i ≠ e := (hi.2.2 (Sum.inr ())).symm
  have hCe := admissible_insert C l R hA he
  have hcc : (insert e C).card = C.card + 1 := Finset.card_insert_of_notMem he.1
  have hG : setValue K C l R g = mass r C l * expect C l R hA.named_fresh j g := by
    have hh := normalized (r := r) (by omega) C l R hA (by omega) hK g hgzero
    simpa only [r, Nat.add_sub_cancel_left] using hh
  have hM0 : setValue K C l R m = mass (r + 1) C l *
      expect C l R hA.named_fresh (j + 1) m := by
    have hh := normalized (r := r + 1) hrK C l R hA (by omega) hK m hmzero
    simpa only [r, show C.card + j + 1 - C.card = j + 1 by omega] using hh
  have hMe : setValue K (insert e C) l R m = mass r C l *
      expect C l R hA.named_fresh j (fun U ↦ m (insert e U)) := by
    have hh := normalized (r := r + 1) hrK (insert e C) l R hCe (by rw [hcc]; omega) hK m hmzero
    rw [insert_mass r C l e he.1 (by omega)] at hh
    simpa only [r, show C.card + j + 1 - (insert e C).card = j by rw [hcc]; omega,
      expect_insert] using hh
  rw [split_one, hG, hM0, hMe]
  have hX := inserted_lower C l R hA hiL he hie (by omega : j ≤ R.card) m g c hdom
  have hY := nested_lower C l R hA hiL (by omega : j + 1 ≤ R.card) m g c hdom
  have hmin' := expect_lower C l R hA hiL (by omega : j ≤ R.card) g L hmin
  have hh := outside_surplus (mass_pos r C l).le hrise hc heps hL hmin' hX hY hsurplus
  nlinarith

lemma inside_positive {K j : ℕ} (C : Finset (Fin n)) (label : α ⊕ Unit ↪ Fin n)
    (R : Finset (Fin n)) (hAll : Admissible C label R) {i : Fin n} (hi : Extra C label R i)
    (hj : 1 ≤ j) (hK : K ≤ R.card) (hrK : C.card + j + 1 ≤ K)
    (m g : Finset (Fin n) → ℝ) (hmzero : ∀ Z, Z.card ≠ C.card + j + 1 → m Z = 0)
    (hgzero : ∀ Z, Z.card ≠ C.card + j → g Z = 0)
    (c L eps : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L) (heps : 0 ≤ eps)
    (hmin : ∀ U, U.card = C.card + j → i ∉ U → L ≤ g U)
    (hdom : ∀ U V, U ⊆ V → U.card = C.card + j → V.card = C.card + j + 1 →
      i ∉ V → c * g U ≤ m V)
    (hrise : mass (C.card + j) (insert (label (Sum.inr ())) C)
        (Function.Embedding.inl.trans label) ≤ mass (C.card + j) C (Function.Embedding.inl.trans label))
    (hsurplus : eps ≤ (mass (C.card + j) C (Function.Embedding.inl.trans label) -
      mass (C.card + j) (insert (label (Sum.inr ())) C) (Function.Embedding.inl.trans label)) / 2) :
    c * (setValue K C label R g + eps * L) ≤
      setValue K (insert (label (Sum.inr ())) C) (Function.Embedding.inl.trans label) R m := by
  let l := Function.Embedding.inl.trans label
  let e := label (Sum.inr ())
  let r := C.card + j
  have hA := left_admissible C label R hAll
  have he : Extra C l R e := extra_point C label R hAll
  have hiL : Extra C l R i := ⟨hi.1, hi.2.1, fun a ↦ hi.2.2 (Sum.inl a)⟩
  have hie : i ≠ e := (hi.2.2 (Sum.inr ())).symm
  have hCe := admissible_insert C l R hA he
  have hiCe := extra_insert C l R hiL hie
  have hcc : (insert e C).card = C.card + 1 := Finset.card_insert_of_notMem he.1
  have hG0 : setValue K C l R g = mass r C l * expect C l R hA.named_fresh j g := by
    have hh := normalized (r := r) (by omega) C l R hA (by omega) hK g hgzero
    simpa only [r, Nat.add_sub_cancel_left] using hh
  have hGe : setValue K (insert e C) l R g = mass r (insert e C) l *
      expect (insert e C) l R hCe.named_fresh (j - 1) g := by
    have hh := normalized (r := r) (by omega) (insert e C) l R hCe (by rw [hcc]; omega) hK g hgzero
    simpa only [r, show C.card + j - (insert e C).card = j - 1 by rw [hcc]; omega] using hh
  have hM : setValue K (insert e C) l R m = mass r C l *
      expect (insert e C) l R hCe.named_fresh j m := by
    have hh := normalized (r := r + 1) hrK (insert e C) l R hCe (by rw [hcc]; omega) hK m hmzero
    rw [insert_mass r C l e he.1 (by omega)] at hh
    simpa only [r, show C.card + j + 1 - (insert e C).card = j by rw [hcc]; omega] using hh
  rw [split_one, hG0, hGe, hM]
  have hX := inserted_lower C l R hA hiL he hie (by omega : j ≤ R.card) m g c hdom
  rw [← expect_insert] at hX
  have hdom' : ∀ U V, U ⊆ V → U.card = (insert e C).card + (j - 1) →
      V.card = (insert e C).card + (j - 1) + 1 → i ∉ V → c * g U ≤ m V := by
    intro U V hUV hUc hVc hiV
    apply hdom U V hUV _ _ hiV <;> rw [hcc] at * <;> omega
  have hY := nested_lower (insert e C) l R hCe hiCe (j := j - 1) (by omega) m g c hdom'
  rw [show j - 1 + 1 = j by omega] at hY
  have hmin' := expect_lower (insert e C) l R hCe hiCe (j := j - 1) (by omega) g L
    (fun U hUc hiU ↦ hmin U (by rw [hcc] at hUc; omega) hiU)
  have hh := inside_surplus (mass_pos r (insert e C) l).le hrise hc heps hL hmin' hX hY hsurplus
  nlinarith

lemma inside_zero {K : ℕ} (C : Finset (Fin n)) (label : α ⊕ Unit ↪ Fin n)
    (R : Finset (Fin n)) (hAll : Admissible C label R) {i : Fin n} (hi : Extra C label R i)
    (hK : K ≤ R.card) (hrK : C.card + 1 ≤ K)
    (m g : Finset (Fin n) → ℝ) (hmzero : ∀ Z, Z.card ≠ C.card + 1 → m Z = 0)
    (hgzero : ∀ Z, Z.card ≠ C.card → g Z = 0)
    (c L eps : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L) (_heps : 0 ≤ eps)
    (hmin : ∀ U, U.card = C.card → i ∉ U → L ≤ g U)
    (hdom : ∀ U V, U ⊆ V → U.card = C.card → V.card = C.card + 1 →
      i ∉ V → c * g U ≤ m V)
    (hsurplus : eps ≤ mass C.card C (Function.Embedding.inl.trans label) / 2) :
    c * (setValue K C label R g + eps * L) ≤
      setValue K (insert (label (Sum.inr ())) C) (Function.Embedding.inl.trans label) R m := by
  let l := Function.Embedding.inl.trans label
  let e := label (Sum.inr ())
  have hA := left_admissible C label R hAll
  have he : Extra C l R e := extra_point C label R hAll
  have hiL : Extra C l R i := ⟨hi.1, hi.2.1, fun a ↦ hi.2.2 (Sum.inl a)⟩
  have hie : i ≠ e := (hi.2.2 (Sum.inr ())).symm
  have hCe := admissible_insert C l R hA he
  have hcc : (insert e C).card = C.card + 1 := Finset.card_insert_of_notMem he.1
  have hG0 : setValue K C l R g = mass C.card C l * expect C l R hA.named_fresh 0 g := by
    have hh := normalized (r := C.card) (by omega) C l R hA (by rfl) hK g hgzero
    simpa only [Nat.sub_self] using hh
  have hGe : setValue K (insert e C) l R g = 0 :=
    zero_large_common _ _ _ (by rw [hcc]; omega) g hgzero
  have hM : setValue K (insert e C) l R m = mass C.card C l *
      expect C l R hA.named_fresh 0 (fun U ↦ m (insert e U)) := by
    have hh := normalized hrK (insert e C) l R hCe (by rw [hcc]) hK m hmzero
    rw [insert_mass C.card C l e he.1 (by rfl)] at hh
    simpa only [hcc, Nat.sub_self, expect_insert] using hh
  rw [split_one, hG0, hGe, hM, add_zero]
  have hX := inserted_lower C l R hA hiL he hie (j := 0) (by omega) m g c (by
    simpa only [Nat.add_zero] using hdom)
  have hmin' := expect_lower C l R hA hiL (j := 0) (by omega) g L (by
    simpa only [Nat.add_zero] using hmin)
  have hB := (mass_pos C.card C l).le
  have hAn : 0 ≤ expect C l R hA.named_fresh 0 g := hL.trans hmin'
  have hca : c * expect C l R hA.named_fresh 0 g * mass C.card C l ≤
      expect C l R hA.named_fresh 0 (fun U ↦ m (insert e U)) * mass C.card C l :=
    mul_le_mul_of_nonneg_right hX hB
  have hs : eps * L ≤ mass C.card C l / 2 * expect C l R hA.named_fresh 0 g :=
    (mul_le_mul_of_nonneg_right hsurplus hL).trans
      (mul_le_mul_of_nonneg_left hmin' (by positivity))
  nlinarith [mul_le_mul_of_nonneg_left hs hc]

end
end Lax343628Proofs.ShadowBirth

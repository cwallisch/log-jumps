import Lax343628Proofs.BirthCouplings

namespace Lax343628Proofs.ShadowMeans

open Lax343628Proofs.BirthGeometry Lax343628Proofs.BirthCouplings
open Lax343628Proofs.FiniteCoupling Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.PlacedBase
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

def expect (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hR : ∀ a, label a ∉ R) (j : ℕ) (f : Finset (Fin n) → ℝ) : ℝ :=
  mean (placedLaw (α := α) (β := Fin R.card) j) (fun S ↦ f (realize C label R hR S))

omit [DecidableEq α] in
lemma expect_insert (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hR : ∀ a, label a ∉ R) (e : Fin n) (j : ℕ) (f : Finset (Fin n) → ℝ) :
    expect (insert e C) label R hR j f = expect C label R hR j (fun U ↦ f (insert e U)) := by
  unfold expect
  simp_rw [realize_insert]

lemma expect_lower (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) {i : Fin n} (hi : Extra C label R i) {j : ℕ} (hj : j ≤ R.card)
    (g : Finset (Fin n) → ℝ) (L : ℝ)
    (hmin : ∀ U, U.card = C.card + j → i ∉ U → L ≤ g U) :
    L ≤ expect C label R hA.named_fresh j g := by
  calc
    L = mean (placedLaw (α := α) (β := Fin R.card) j) (fun _ ↦ L) := (mean_const _ _).symm
    _ ≤ _ := mean_mono_on_support _ (fun S hS ↦ hmin _
      (by rw [realize_card C label R hA, SlotBirth.placedLaw_card (by simpa using hj) S hS])
      (extra_not_realize C label R hA.named_fresh hi S))

lemma nested_lower (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) {i : Fin n} (hi : Extra C label R i) {j : ℕ} (hj : j + 1 ≤ R.card)
    (m g : Finset (Fin n) → ℝ) (c : ℝ)
    (hdom : ∀ U V, U ⊆ V → U.card = C.card + j → V.card = C.card + j + 1 →
      i ∉ V → c * g U ≤ m V) :
    c * expect C label R hA.named_fresh j g ≤ expect C label R hA.named_fresh (j + 1) m := by
  let K := nestedCoupling C label R hA.named_fresh j
  have ht := test_le (reverse K) m (fun U ↦ c * g U) (fun V U hpos ↦ by
    change 0 < K.mass U V at hpos
    have hs := nestedCoupling_support C label R hA hj U V hpos
    have hiV := (nestedCoupling_avoids C label R hA.named_fresh hi j U V hpos).2
    exact hdom U V hs.1 hs.2.1 hs.2.2 hiV)
  simp only [mean_map] at ht
  rw [mean_mul] at ht
  exact ht

lemma inserted_lower (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) {i e : Fin n} (hi : Extra C label R i) (he : Extra C label R e)
    (hie : i ≠ e) {j : ℕ} (hj : j ≤ R.card) (m g : Finset (Fin n) → ℝ) (c : ℝ)
    (hdom : ∀ U V, U ⊆ V → U.card = C.card + j → V.card = C.card + j + 1 →
      i ∉ V → c * g U ≤ m V) :
    c * expect C label R hA.named_fresh j g ≤
      expect C label R hA.named_fresh j (fun U ↦ m (insert e U)) := by
  unfold expect
  rw [← mean_mul]
  apply mean_mono_on_support
  intro S hS
  let U := realize C label R hA.named_fresh S
  have hUc : U.card = C.card + j := by
    rw [realize_card C label R hA, SlotBirth.placedLaw_card (by simpa using hj) S hS]
  have heU : e ∉ U := extra_not_realize C label R hA.named_fresh he S
  have hiU : i ∉ U := extra_not_realize C label R hA.named_fresh hi S
  exact hdom U (insert e U) (Finset.subset_insert _ _) hUc
    (by rw [Finset.card_insert_of_notMem heU, hUc]) (by simp [hie, hiU])

lemma outside_surplus {B Bplus X Y A L c eps : ℝ} (hB : 0 ≤ B) (hplus : B ≤ Bplus)
    (hc : 0 ≤ c) (heps : 0 ≤ eps) (hL : 0 ≤ L) (hA : L ≤ A)
    (hX : c * A ≤ X) (hY : c * A ≤ Y) (hsurplus : eps ≤ (Bplus - B) / 2) :
    c * (B * A + eps * L) ≤ (B / 2) * X + (Bplus / 2) * Y := by
  have hBa := mul_le_mul_of_nonneg_left hX (show 0 ≤ B / 2 by positivity)
  have hBy := mul_le_mul_of_nonneg_left hY (show 0 ≤ Bplus / 2 by linarith)
  have hs : eps * L ≤ ((Bplus - B) / 2) * A := by
    exact (mul_le_mul_of_nonneg_left hA heps).trans
      (mul_le_mul_of_nonneg_right hsurplus (hL.trans hA))
  have hsc := mul_le_mul_of_nonneg_left hs hc
  nlinarith

lemma inside_surplus {B Bprev X A G L c eps : ℝ} (hprev : 0 ≤ Bprev) (hB : Bprev ≤ B)
    (hc : 0 ≤ c) (heps : 0 ≤ eps) (hL : 0 ≤ L) (hG : L ≤ G)
    (hX : c * A ≤ X) (hY : c * G ≤ X) (hsurplus : eps ≤ (B - Bprev) / 2) :
    c * ((B / 2) * A + (Bprev / 2) * G + eps * L) ≤ B * X := by
  have h1 := mul_le_mul_of_nonneg_left hX (show 0 ≤ B / 2 by linarith)
  have h2 := mul_le_mul_of_nonneg_left hY (show 0 ≤ B / 2 by linarith)
  have hs : eps * L ≤ ((B - Bprev) / 2) * G :=
    (mul_le_mul_of_nonneg_left hG heps).trans
      (mul_le_mul_of_nonneg_right hsurplus (hL.trans hG))
  have hsc := mul_le_mul_of_nonneg_left hs hc
  nlinarith

end
end Lax343628Proofs.ShadowMeans

import Lax343628Proofs.ShadowMeans
import Lax343628Proofs.CouplingTests

namespace Lax343628Proofs.MeanCone

open Lax343628Proofs.BirthGeometry Lax343628Proofs.BirthCouplings
open Lax343628Proofs.FiniteExchange Lax343628Proofs.FiniteCoupling
open Lax343628Proofs.FiniteDrift Lax343628Proofs.CouplingTests
open Lax343628Proofs.ShadowMeans Lax343628Proofs.PlacedBase
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def Cone {n : ℕ} (i : Fin n) (r : ℕ) (rho : ℝ) (h : Finset (Fin n) → ℝ) : Prop :=
  ∀ U V, U.card = r → i ∉ U → i ∉ V → Near U V → h V ≤ rho * h U

lemma cone_pair {n r : ℕ} {i : Fin n} {rho : ℝ} {h : Finset (Fin n) → ℝ} (hc : Cone i r rho h)
    (U V : Finset (Fin n)) (hUc : U.card = r) (hiU : i ∉ U) (hiV : i ∉ V) (hUV : Near U V) :
    h V ≤ rho * h U ∧ h U ≤ rho * h V :=
  ⟨hc U V hUc hiU hiV hUV, hc V U (hUV.1.symm.trans hUc) hiV hiU (near_symm hUV)⟩

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

lemma exchange_means (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) {i e : Fin n} (hi : Extra C label R i) (he : Extra C label R e)
    (hie : i ≠ e) {j : ℕ} (hj : j + 1 ≤ R.card)
    (rho : ℝ) (h : Finset (Fin n) → ℝ) (hc : Cone i (C.card + j + 1) rho h) :
    expect C label R hA.named_fresh (j + 1) h ≤
        rho * expect C label R hA.named_fresh j (fun U ↦ h (insert e U)) ∧
      expect C label R hA.named_fresh j (fun U ↦ h (insert e U)) ≤
        rho * expect C label R hA.named_fresh (j + 1) h := by
  apply comparable_means (placedCoupling (α := α) (β := Fin R.card) j)
  intro S T hpos
  have hp := map_positive (placedCoupling (α := α) (β := Fin R.card) j)
    (fun Z ↦ insert e (realize C label R hA.named_fresh Z)) (realize C label R hA.named_fresh) S T hpos
  have hs := exchangeCoupling_support C label R hA he hj _ _ hp
  have hiS := extra_not_realize C label R hA.named_fresh hi S
  have hiT := extra_not_realize C label R hA.named_fresh hi T
  exact cone_pair hc _ _ hs.2.1 (by simp [hie, hiS]) hiT hs.1

lemma swap_means (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) {i e g : Fin n} (hi : Extra C label R i)
    (he : Extra C label R e) (hg : Extra C label R g) (hie : i ≠ e) (hig : i ≠ g)
    {j : ℕ} (hj : j ≤ R.card) (rho : ℝ) (h : Finset (Fin n) → ℝ)
    (hc : Cone i (C.card + j + 1) rho h) :
    expect C label R hA.named_fresh j (fun U ↦ h (insert g U)) ≤
        rho * expect C label R hA.named_fresh j (fun U ↦ h (insert e U)) ∧
      expect C label R hA.named_fresh j (fun U ↦ h (insert e U)) ≤
        rho * expect C label R hA.named_fresh j (fun U ↦ h (insert g U)) := by
  have hpoint (S : Finset (α ⊕ Fin R.card)) (hS : S ∈ (placedLaw j).support) :
      h (insert g (realize C label R hA.named_fresh S)) ≤
          rho * h (insert e (realize C label R hA.named_fresh S)) ∧
        h (insert e (realize C label R hA.named_fresh S)) ≤
          rho * h (insert g (realize C label R hA.named_fresh S)) := by
    have heS := extra_not_realize C label R hA.named_fresh he S
    have hgS := extra_not_realize C label R hA.named_fresh hg S
    have hiS := extra_not_realize C label R hA.named_fresh hi S
    have hsize : (insert e (realize C label R hA.named_fresh S)).card = C.card + j + 1 := by
      rw [Finset.card_insert_of_notMem heS, realize_card C label R hA,
        SlotBirth.placedLaw_card (by simpa using hj) S hS]
    exact cone_pair hc _ _ hsize (by simp [hie, hiS]) (by simp [hig, hiS])
      (near_swap _ e g heS hgS)
  constructor
  · have ht := mean_mono_on_support (placedLaw (α := α) (β := Fin R.card) j)
      (fun S hS ↦ (hpoint S hS).1)
    rw [mean_mul] at ht
    exact ht
  · have ht := mean_mono_on_support (placedLaw (α := α) (β := Fin R.card) j)
      (fun S hS ↦ (hpoint S hS).2)
    rw [mean_mul] at ht
    exact ht

lemma double_means (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) {i e g : Fin n} (hi : Extra C label R i)
    (he : Extra C label R e) (hg : Extra C label R g)
    (hie : i ≠ e) (hig : i ≠ g) (heg : e ≠ g) {j : ℕ} (hj : j + 1 ≤ R.card)
    (rho : ℝ) (h : Finset (Fin n) → ℝ) (hc : Cone i (C.card + j + 2) rho h) :
    expect C label R hA.named_fresh j (fun U ↦ h (insert e (insert g U))) ≤
        rho * expect C label R hA.named_fresh (j + 1) (fun U ↦ h (insert e U)) ∧
      expect C label R hA.named_fresh (j + 1) (fun U ↦ h (insert e U)) ≤
        rho * expect C label R hA.named_fresh j (fun U ↦ h (insert e (insert g U))) := by
  apply comparable_means (reverse (placedCoupling (α := α) (β := Fin R.card) j))
  intro T S hpos
  have hp := map_positive (reverse (placedCoupling (α := α) (β := Fin R.card) j))
    (fun Z ↦ insert e (realize C label R hA.named_fresh Z))
    (fun Z ↦ insert e (insert g (realize C label R hA.named_fresh Z))) T S hpos
  have hs := doubleCoupling_support C label R hA he hg heg hj _ _ hp
  have hnest := placedCoupling_support (by simpa using hj) S T hpos
  have heT := extra_not_realize C label R hA.named_fresh he T
  have hiT := extra_not_realize C label R hA.named_fresh hi T
  have hiS := extra_not_realize C label R hA.named_fresh hi S
  have hsize : (insert e (realize C label R hA.named_fresh T)).card = C.card + j + 2 := by
    rw [Finset.card_insert_of_notMem heT, realize_card C label R hA, hnest.2.2.1]
    omega
  exact cone_pair hc _ _ hsize (by simp [hie, hiT]) (by simp [hie, hig, hiS]) hs

end
end Lax343628Proofs.MeanCone

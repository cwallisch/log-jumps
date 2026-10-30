import Lax343628Proofs.ConeExpansion

namespace Lax343628Proofs.AsymmetricCone

open Lax343628Proofs.BirthGeometry Lax343628Proofs.BirthCouplings
open Lax343628Proofs.ConeExpansion Lax343628Proofs.ShadowMeans
open Lax343628Proofs.MeanCone Lax343628Proofs.FiniteDrift
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

lemma expansion {K j : ℕ} (C : Finset (Fin n)) (label : α ⊕ Fin 2 ↪ Fin n)
    (R : Finset (Fin n)) (hAll : Admissible C label R)
    (hrK : C.card + j + 1 ≤ K) (hK : K ≤ R.card)
    (h : Finset (Fin n) → ℝ) (hzero : ∀ Z, Z.card ≠ C.card + j + 1 → h Z = 0) :
    let l := Function.Embedding.inl.trans label
    let e := label (Sum.inr 0)
    let g := label (Sum.inr 1)
    let hA := left_admissible C label R hAll
    let r := C.card + j + 1
    setValue K C label R h = (1 / 4 : ℝ) *
      (mass r C l * expect C l R hA.named_fresh (j + 1) h +
        mass r (insert e C) l * expect C l R hA.named_fresh j (fun U ↦ h (insert e U)) +
        mass r (insert g C) l * expect C l R hA.named_fresh j (fun U ↦ h (insert g U)) +
        (if j = 0 then 0 else mass r (insert e (insert g C)) l *
          expect C l R hA.named_fresh (j - 1) (fun U ↦ h (insert e (insert g U))))) := by
  dsimp only
  let l := Function.Embedding.inl.trans label
  let e := label (Sum.inr 0)
  let g := label (Sum.inr 1)
  let r := C.card + j + 1
  have hA := left_admissible C label R hAll
  have hx := two_extras C label R hAll
  have he : Extra C l R e := hx.1
  have hg : Extra C l R g := hx.2.1
  have heg : e ≠ g := hx.2.2
  have hCe := admissible_insert C l R hA he
  have hCg := admissible_insert C l R hA hg
  have hCeg := admissible_insert (insert g C) l R hCg (extra_insert C l R he heg)
  have hce : (insert e C).card = C.card + 1 := Finset.card_insert_of_notMem he.1
  have hcg : (insert g C).card = C.card + 1 := Finset.card_insert_of_notMem hg.1
  have hceg : (insert e (insert g C)).card = C.card + 2 := by
    rw [Finset.card_insert_of_notMem (by simp [heg, he.1]), hcg]
  have h0 : setValue K C l R h =
      mass r C l * expect C l R hA.named_fresh (j + 1) h := by
    have hn := normalized hrK C l R hA (by omega) hK h hzero
    simpa only [r, show C.card + j + 1 - C.card = j + 1 by omega] using hn
  have heq : setValue K (insert e C) l R h = mass r (insert e C) l *
      expect C l R hA.named_fresh j (fun U ↦ h (insert e U)) := by
    have hn := normalized hrK (insert e C) l R hCe (by rw [hce]; omega) hK h hzero
    simpa only [r, show C.card + j + 1 - (insert e C).card = j by rw [hce]; omega, expect_insert] using hn
  have hgq : setValue K (insert g C) l R h = mass r (insert g C) l *
      expect C l R hA.named_fresh j (fun U ↦ h (insert g U)) := by
    have hn := normalized hrK (insert g C) l R hCg (by rw [hcg]; omega) hK h hzero
    simpa only [r, show C.card + j + 1 - (insert g C).card = j by rw [hcg]; omega, expect_insert] using hn
  have hegq : setValue K (insert e (insert g C)) l R h =
      if j = 0 then 0 else mass r (insert e (insert g C)) l *
        expect C l R hA.named_fresh (j - 1) (fun U ↦ h (insert e (insert g U))) := by
    by_cases hj : j = 0
    · rw [if_pos hj]
      exact zero_large_common _ _ _ (by rw [hceg]; omega) h hzero
    · rw [if_neg hj]
      have hn := normalized hrK (insert e (insert g C)) l R hCeg
        (by rw [hceg]; omega) hK h hzero
      simpa only [r, show C.card + j + 1 - (insert e (insert g C)).card = j - 1 by rw [hceg]; omega,
        expect_insert] using hn
  change setValue K C label R h = _
  have hs := BirthSplit.split_two K C label R (fun x ↦ h (Lax343628Proofs.Sampling.zeros x))
  change setValue K C label R h = (1 / 4 : ℝ) *
    (setValue K C l R h + setValue K (insert e C) l R h +
      setValue K (insert g C) l R h + setValue K (insert e (insert g C)) l R h) at hs
  rw [hs, h0, heq, hgq, hegq]

lemma comparison {K j : ℕ} (C : Finset (Fin n)) (label : α ⊕ Fin 2 ↪ Fin n)
    (R : Finset (Fin n)) (hAll : Admissible C label R)
    {i : Fin n} (hi : Extra C label R i) (hrK : C.card + j + 1 ≤ K) (hK : K ≤ R.card)
    (hv : Fintype.card α = 2 * j ∨ Fintype.card α = 2 * j + 1 ∨ Fintype.card α + 1 = 2 * j)
    (rho : ℝ) (hrho : 2 ≤ rho) (h : Finset (Fin n) → ℝ) (hnonneg : ∀ U, 0 ≤ h U)
    (hzero : ∀ Z, Z.card ≠ C.card + j + 1 → h Z = 0)
    (hc : Cone i (C.card + j + 1) rho h) :
    setValue K C label R h ≤ rho *
        setValue K (insert (label (Sum.inr 0)) C) (Function.Embedding.inl.trans label) R h ∧
      setValue K (insert (label (Sum.inr 0)) C) (Function.Embedding.inl.trans label) R h ≤
        rho * setValue K C label R h := by
  let l := Function.Embedding.inl.trans label
  let e := label (Sum.inr 0)
  let g := label (Sum.inr 1)
  let r := C.card + j + 1
  have hA := left_admissible C label R hAll
  have hx := two_extras C label R hAll
  have he : Extra C l R e := hx.1
  have hg : Extra C l R g := hx.2.1
  have heg : e ≠ g := hx.2.2
  have hiL : Extra C l R i := ⟨hi.1, hi.2.1, fun a ↦ hi.2.2 (Sum.inl a)⟩
  have hie : i ≠ e := (hi.2.2 (Sum.inr 0)).symm
  have hig : i ≠ g := (hi.2.2 (Sum.inr 1)).symm
  have hjR : j + 1 ≤ R.card := by omega
  let A := expect C l R hA.named_fresh j (fun U ↦ h (insert e U))
  let A0 := expect C l R hA.named_fresh (j + 1) h
  let Ag := expect C l R hA.named_fresh j (fun U ↦ h (insert g U))
  let A2 := expect C l R hA.named_fresh (j - 1) (fun U ↦ h (insert e (insert g U)))
  let B := mass r (insert e C) l
  let B0 := mass r C l
  let B2 := if j = 0 then 0 else mass r (insert e (insert g C)) l
  let b := (B0 + B + B2) / 4
  let W := (B0 * A0 + B * Ag + B2 * A2) / 4
  have hB : 0 ≤ B := (mass_pos r _ l).le
  have hB0 : 0 ≤ B0 := (mass_pos r C l).le
  have hB2 : 0 ≤ B2 := by dsimp [B2]; split_ifs; rfl; exact (mass_pos r _ l).le
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hAn : 0 ≤ A := mean_nonneg _ (fun S ↦ hnonneg _)
  have hm0 : A0 ≤ rho * A ∧ A ≤ rho * A0 :=
    exchange_means C l R hA hiL he hie hjR rho h hc
  have hmg : Ag ≤ rho * A ∧ A ≤ rho * Ag :=
    swap_means C l R hA hiL he hg hie hig (by omega) rho h hc
  have hm2 : B2 * A2 ≤ rho * B2 * A ∧ B2 * A ≤ rho * B2 * A2 := by
    by_cases hj : j = 0
    · simp [B2, hj]
    · have hc' : Cone i (C.card + (j - 1) + 2) rho h := by
        convert hc using 1; omega
      have hh := double_means C l R hA hiL he hg hie hig heg (j := j - 1) (by omega) rho h hc'
      have hpair : A2 ≤ rho * A ∧ A ≤ rho * A2 := by
        simpa only [show j - 1 + 1 = j by omega] using hh
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hpair.1 hB2]
      · nlinarith [mul_le_mul_of_nonneg_left hpair.2 hB2]
  have hWup : W ≤ rho * b * A := by
    dsimp [W, b]
    nlinarith [mul_le_mul_of_nonneg_left hm0.1 hB0, mul_le_mul_of_nonneg_left hmg.1 hB, hm2.1]
  have hWlow : b * A ≤ rho * W := by
    dsimp [W, b]
    nlinarith [mul_le_mul_of_nonneg_left hm0.2 hB0, mul_le_mul_of_nonneg_left hmg.2 hB, hm2.2]
  have hmass : mass r C label = B / 4 + b := by
    have hh := four_masses C label e g he.1 hg.1 heg j
    change mass r C label = (1 / 4 : ℝ) * (B0 + 2 * B + B2) at hh
    dsimp [b]
    linarith
  have hbounds := QuarterCone.asymmetric_masses C label e he.1 hv
  change (3 / 4 : ℝ) * B ≤ mass r C label ∧ mass r C label ≤ (9 / 8 : ℝ) * B at hbounds
  rw [hmass] at hbounds
  have hscalar := QuarterCone.comparison hB hb hAn hrho hbounds.1 hbounds.2 hWup hWlow
  have hOld : setValue K (insert e C) l R h = B * A := by
    have hCe := admissible_insert C l R hA he
    have hce : (insert e C).card = C.card + 1 := Finset.card_insert_of_notMem he.1
    have hh := normalized hrK (insert e C) l R hCe (by rw [hce]; omega) hK h hzero
    simpa only [show C.card + j + 1 - (insert e C).card = j by rw [hce]; omega, expect_insert] using hh
  have hNew : setValue K C label R h = B / 4 * A + W := by
    have hh := expansion C label R hAll hrK hK h hzero
    have hmg_eq : mass r (insert g C) l = B := same_card_mass r _ _
      (by rw [Finset.card_insert_of_notMem hg.1, Finset.card_insert_of_notMem he.1]) l
    have hterm : (if j = 0 then 0 else mass r (insert e (insert g C)) l * A2) = B2 * A2 := by
      by_cases hj : j = 0 <;> simp [B2, hj]
    change setValue K C label R h = (1 / 4 : ℝ) *
      (B0 * A0 + B * A + mass r (insert g C) l * Ag +
        (if j = 0 then 0 else mass r (insert e (insert g C)) l * A2)) at hh
    rw [hmg_eq, hterm] at hh
    dsimp [W]
    linarith
  change setValue K C label R h ≤ rho * setValue K (insert e C) l R h ∧
    setValue K (insert e C) l R h ≤ rho * setValue K C label R h
  rw [hOld, hNew]
  exact hscalar

end
end Lax343628Proofs.AsymmetricCone

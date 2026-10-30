import Lax343628Proofs.Concentration
import Lax343628Proofs.Trajectories
import Lax343628Proofs.FiniteEvents

namespace Lax343628Proofs.PathNoise

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.FiniteChain Lax343628Proofs.Trajectories
open Lax343628Proofs.Concentration Lax343628Proofs.FiniteEvents
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α]

def accumulate (d : ℕ → α → α → ℝ) : (t : ℕ) → (Fin (t + 1) → α) → ℝ
  | 0, _ => 0
  | t + 1, h => accumulate d t (Fin.init h) +
      d t (h (Fin.last t).castSucc) (h (Fin.last (t + 1)))

omit [Fintype α] in
lemma accumulate_snoc (d : ℕ → α → α → ℝ) (t : ℕ) (h : Fin (t + 1) → α) (x : α) :
    accumulate d (t + 1) (Fin.snoc h x) = accumulate d t h + d t (h (Fin.last t)) x := by
  simp only [accumulate, Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last]

lemma exp_moment (K : α → PMF α) (p : PMF α) (d : ℕ → α → α → ℝ) (lam v : ℝ)
    (hsmall : ∀ t x y, y ∈ (K x).support → |lam * d t x y| ≤ 1)
    (hmean : ∀ t x, mean (K x) (d t x) = 0)
    (hvar : ∀ t x, mean (K x) (fun y ↦ d t x y ^ 2) ≤ v) (t : ℕ) :
    mean (pathLaw K p t) (fun h ↦ Real.exp (lam * accumulate d t h)) ≤
      Real.exp (t * lam ^ 2 * v) := by
  induction t with
  | zero => simp only [accumulate, mul_zero, zero_mul, Real.exp_zero, mean_const, Nat.cast_zero, le_refl]
  | succ t ih =>
    rw [pathLaw, mean_bind]
    have ht : mean (pathLaw K p t) (fun h ↦
        mean ((K (h (Fin.last t))).map (Fin.snoc h))
          (fun h' ↦ Real.exp (lam * accumulate d (t + 1) h'))) ≤
        mean (pathLaw K p t) (fun h ↦ Real.exp (lam * accumulate d t h) * Real.exp (lam ^ 2 * v)) := by
      apply mean_mono
      intro h
      rw [mean_map]
      have hfun : (fun x ↦ Real.exp (lam * accumulate d (t + 1) (Fin.snoc h x))) =
          (fun x ↦ Real.exp (lam * accumulate d t h) * Real.exp (lam * d t (h (Fin.last t)) x)) := by
        funext x
        rw [accumulate_snoc, mul_add, Real.exp_add]
      rw [hfun, mean_mul]
      exact mul_le_mul_of_nonneg_left
        (centered_exp_bound _ _ lam v (hsmall t _) (hmean t _) (hvar t _)) (Real.exp_pos _).le
    have hright : mean (pathLaw K p t) (fun h ↦ Real.exp (lam * accumulate d t h) * Real.exp (lam ^ 2 * v)) =
        Real.exp (lam ^ 2 * v) * mean (pathLaw K p t) (fun h ↦ Real.exp (lam * accumulate d t h)) := by
      have heq : (fun h ↦ Real.exp (lam * accumulate d t h) * Real.exp (lam ^ 2 * v)) =
          (fun h ↦ Real.exp (lam ^ 2 * v) * Real.exp (lam * accumulate d t h)) := by funext h; ring
      rw [heq, mean_mul]
    rw [hright] at ht
    calc
      _ ≤ _ := ht
      _ ≤ Real.exp (lam ^ 2 * v) * Real.exp (t * lam ^ 2 * v) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

lemma upper_tail (K : α → PMF α) (p : PMF α) (d : ℕ → α → α → ℝ) (lam v : ℝ)
    (hlam : 0 ≤ lam) (hsmall : ∀ t x y, y ∈ (K x).support → |lam * d t x y| ≤ 1)
    (hmean : ∀ t x, mean (K x) (d t x) = 0)
    (hvar : ∀ t x, mean (K x) (fun y ↦ d t x y ^ 2) ≤ v) (t : ℕ) (b : ℝ) :
    (pathLaw K p t).toOuterMeasure {h | b ≤ accumulate d t h} ≤
      ENNReal.ofReal (Real.exp (-lam * b + t * lam ^ 2 * v)) := by
  have hm := exp_moment K p d lam v hsmall hmean hvar t
  have ht := event_markov (pathLaw K p t) (fun h ↦ Real.exp (lam * accumulate d t h))
    (fun h ↦ (Real.exp_pos _).le) {h | b ≤ accumulate d t h} (Real.exp (lam * b)) (Real.exp_pos _)
    (fun h hh ↦ Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hh hlam))
  apply ht.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.exp (t * lam ^ 2 * v) / Real.exp (lam * b) :=
      div_le_div_of_nonneg_right hm (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

omit [Fintype α] in
lemma accumulate_neg (d : ℕ → α → α → ℝ) (t : ℕ) (h : Fin (t + 1) → α) :
    accumulate (fun s x y ↦ -d s x y) t h = -accumulate d t h := by
  induction t with
  | zero => simp [accumulate]
  | succ t ih => simp only [accumulate, ih]; ring

lemma absolute_tail (K : α → PMF α) (p : PMF α) (d : ℕ → α → α → ℝ) (lam v : ℝ)
    (hlam : 0 ≤ lam) (hsmall : ∀ t x y, y ∈ (K x).support → |lam * d t x y| ≤ 1)
    (hmean : ∀ t x, mean (K x) (d t x) = 0)
    (hvar : ∀ t x, mean (K x) (fun y ↦ d t x y ^ 2) ≤ v) (t : ℕ) (b : ℝ) :
    (pathLaw K p t).toOuterMeasure {h | b ≤ |accumulate d t h|} ≤
      ENNReal.ofReal (2 * Real.exp (-lam * b + t * lam ^ 2 * v)) := by
  let events : Fin 2 → Set (Fin (t + 1) → α) := fun j ↦
    if j = 0 then {h | b ≤ accumulate d t h} else {h | b ≤ -accumulate d t h}
  have hneg : (pathLaw K p t).toOuterMeasure {h | b ≤ -accumulate d t h} ≤
      ENNReal.ofReal (Real.exp (-lam * b + t * lam ^ 2 * v)) := by
    have ht := upper_tail K p (fun s x y ↦ -d s x y) lam v hlam
      (fun s x y hy ↦ by simpa only [mul_neg, abs_neg] using hsmall s x y hy)
      (fun s x ↦ by
        have heq : (fun y ↦ -d s x y) = (fun y ↦ (-1 : ℝ) * d s x y) := by funext y; ring
        rw [heq, mean_mul, hmean, mul_zero])
      (fun s x ↦ by simpa only [neg_sq] using hvar s x) t b
    simpa only [accumulate_neg] using ht
  have hu := finite_union_bound (pathLaw K p t) (Finset.univ : Finset (Fin 2)) events
    (Real.exp (-lam * b + t * lam ^ 2 * v)) (Real.exp_pos _).le (fun j _ ↦ by
      fin_cases j
      · exact upper_tail K p d lam v hlam hsmall hmean hvar t b
      · exact hneg)
  have hsub : {h | b ≤ |accumulate d t h|} ⊆ {h | ∃ j ∈ (Finset.univ : Finset (Fin 2)), h ∈ events j} := by
    intro h hh
    by_cases hsign : 0 ≤ accumulate d t h
    · exact ⟨0, Finset.mem_univ _, by simpa [events, abs_of_nonneg hsign] using hh⟩
    · exact ⟨1, Finset.mem_univ _, by simpa [events, abs_of_neg (lt_of_not_ge hsign)] using hh⟩
  apply (MeasureTheory.measure_mono hsub).trans
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] using hu

lemma prefix_tail (K : α → PMF α) (p : PMF α) (d : ℕ → α → α → ℝ) (lam v : ℝ)
    (hlam : 0 ≤ lam) (hv : 0 ≤ v)
    (hsmall : ∀ t x y, y ∈ (K x).support → |lam * d t x y| ≤ 1)
    (hmean : ∀ t x, mean (K x) (d t x) = 0)
    (hvar : ∀ t x, mean (K x) (fun y ↦ d t x y ^ 2) ≤ v) (H : ℕ) (b : ℝ) :
    (pathLaw K p H).toOuterMeasure {h | ∃ T : Fin (H + 1),
      b ≤ |accumulate d T.val (before H T.val (by have := T.isLt; omega) h)|} ≤
      ENNReal.ofReal (((H : ℝ) + 1) * (2 * Real.exp (-lam * b + H * lam ^ 2 * v))) := by
  let events : Fin (H + 1) → Set (Fin (H + 1) → α) := fun T ↦
    {h | b ≤ |accumulate d T.val (before H T.val (by have := T.isLt; omega) h)|}
  have hbound (T : Fin (H + 1)) : (pathLaw K p H).toOuterMeasure (events T) ≤
      ENNReal.ofReal (2 * Real.exp (-lam * b + H * lam ^ 2 * v)) := by
    have hT : T.val ≤ H := by have := T.isLt; omega
    have ht := absolute_tail K p d lam v hlam hsmall hmean hvar T.val b
    rw [← pathLaw_before K p H T.val hT, PMF.toOuterMeasure_map_apply] at ht
    apply ht.trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    have hTr : (T.val : ℝ) ≤ H := by exact_mod_cast hT
    have hscale := mul_le_mul_of_nonneg_right hTr (mul_nonneg (sq_nonneg lam) hv)
    nlinarith
  have ht := finite_union_bound (pathLaw K p H) (Finset.univ : Finset (Fin (H + 1))) events
    (2 * Real.exp (-lam * b + H * lam ^ 2 * v)) (by positivity) (fun T _ ↦ hbound T)
  simpa only [events, Set.mem_ofPred_eq, Finset.mem_univ, true_and, Finset.card_univ, Fintype.card_fin, Nat.cast_add,
    Nat.cast_one] using ht

end
end Lax343628Proofs.PathNoise

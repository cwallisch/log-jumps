import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace Lax343628Proofs.FiniteChain

open scoped ENNReal BigOperators

noncomputable section

variable {α : Type*}

def law (K : α → PMF α) (p : PMF α) : ℕ → PMF α
  | 0 => p
  | t + 1 => (law K p t).bind K

@[simp] lemma law_zero (K : α → PMF α) (p : PMF α) : law K p 0 = p := rfl

@[simp] lemma law_succ (K : α → PMF α) (p : PMF α) (t : ℕ) :
    law K p (t + 1) = (law K p t).bind K := rfl

lemma law_bind (K : α → PMF α) (p : PMF α) (f : α → PMF α) (t : ℕ) :
    law K (p.bind f) t = p.bind (fun x ↦ law K (f x) t) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [law_succ, ih, PMF.bind_bind]

lemma law_add (K : α → PMF α) (p : PMF α) (s t : ℕ) :
    law K p (s + t) = (law K p s).bind (fun x ↦ law K (PMF.pure x) t) := by
  induction t with
  | zero => simp
  | succ t ih => simp only [Nat.add_succ, law_succ, ih, PMF.bind_bind]

lemma event_le_one (p : PMF α) (A : Set α) : p.toOuterMeasure A ≤ 1 := by
  calc
    p.toOuterMeasure A ≤ p.toOuterMeasure Set.univ := p.toOuterMeasure.mono (Set.subset_univ A)
    _ = 1 := by simp [PMF.toOuterMeasure_apply]

lemma event_add_compl (p : PMF α) (A : Set α) :
    p.toOuterMeasure A + p.toOuterMeasure Aᶜ = 1 := by
  classical
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  calc
    (∑' x, (A.indicator p x + Aᶜ.indicator p x)) = ∑' x, p x := by
      apply tsum_congr
      intro x
      by_cases hx : x ∈ A <;> simp [hx]
    _ = 1 := p.tsum_coe

lemma event_bind_le_mul (p : PMF α) (f : α → PMF α) (A : Set α) (r : ℝ≥0∞)
    (h : ∀ x ∈ A, (f x).toOuterMeasure A ≤ r)
    (habs : ∀ x ∉ A, (f x).toOuterMeasure A = 0) :
    (p.bind f).toOuterMeasure A ≤ p.toOuterMeasure A * r := by
  classical
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ A
  · simpa [Set.indicator_of_mem hx] using mul_le_mul' (le_refl (p x)) (h x hx)
  · simp [habs x hx, Set.indicator_of_notMem hx]

lemma event_law_le (K : α → PMF α) (p : PMF α) (A : Set α)
    (habs : ∀ x ∉ A, (K x).toOuterMeasure A = 0) (t : ℕ) :
    (law K p t).toOuterMeasure A ≤ p.toOuterMeasure A := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    have h := event_bind_le_mul (law K p t) K A 1
      (fun x _ ↦ event_le_one (K x) A) habs
    simpa only [law_succ, mul_one] using h.trans (by simpa using ih)

lemma event_law_eq_zero (K : α → PMF α) (A : Set α)
    (habs : ∀ x ∉ A, (K x).toOuterMeasure A = 0) (t : ℕ) (x : α) (hx : x ∉ A) :
    (law K (PMF.pure x) t).toOuterMeasure A = 0 := by
  apply le_antisymm _ zero_le
  simpa [PMF.toOuterMeasure_pure_apply, hx] using event_law_le K (PMF.pure x) A habs t

lemma event_law_block (K : α → PMF α) (p : PMF α) (A : Set α)
    (habs : ∀ x ∉ A, (K x).toOuterMeasure A = 0)
    (L : ℕ) (r : ℝ≥0∞)
    (hblock : ∀ x ∈ A, (law K (PMF.pure x) L).toOuterMeasure A ≤ r) (j : ℕ) :
    (law K p (j * L)).toOuterMeasure A ≤ r ^ j := by
  induction j with
  | zero => simpa using event_le_one p A
  | succ j ih =>
    rw [Nat.succ_mul, law_add]
    exact (event_bind_le_mul _ _ A r hblock
      (fun x hx ↦ event_law_eq_zero K A habs L x hx)).trans
      (by simpa only [pow_succ] using mul_le_mul' ih (le_refl r))

lemma event_law_antitone (K : α → PMF α) (p : PMF α) (A : Set α)
    (habs : ∀ x ∉ A, (K x).toOuterMeasure A = 0) :
    Antitone (fun t ↦ (law K p t).toOuterMeasure A) := by
  intro s t hst
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hst
  have heq : law K p (s + u) = law K (law K p s) u := by
    rw [law_add, ← law_bind, PMF.bind_pure]
  change (law K p (s + u)).toOuterMeasure A ≤ (law K p s).toOuterMeasure A
  rw [heq]
  exact event_law_le K (law K p s) A habs u

lemma tsum_le_of_blocks (f : ℕ → ℝ≥0∞) (L : ℕ) (hL : 0 < L) (r : ℝ≥0∞)
    (hanti : Antitone f) (hblock : ∀ j, f (j * L) ≤ r ^ j) :
    ∑' t, f t ≤ (L : ℝ≥0∞) * (1 - r)⁻¹ := by
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  calc
    ∑' t, f t = ∑' p : ℕ × Fin L, f (p.1 * L + p.2) := by
      exact ((Nat.divModEquiv L).symm.tsum_eq f).symm
    _ ≤ ∑' p : ℕ × Fin L, r ^ p.1 := ENNReal.tsum_le_tsum fun p ↦
      (hanti (Nat.le_add_right _ _)).trans (hblock p.1)
    _ = (L : ℝ≥0∞) * (1 - r)⁻¹ := by
      rw [ENNReal.tsum_prod (f := fun j (_ : Fin L) ↦ r ^ j)]
      simp [tsum_fintype, nsmul_eq_mul, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

lemma runtime_le_of_block (K : α → PMF α) (p : PMF α) (A : Set α)
    (habs : ∀ x ∉ A, (K x).toOuterMeasure A = 0)
    (L : ℕ) (hL : 0 < L) (r : ℝ≥0∞)
    (hblock : ∀ x ∈ A, (law K (PMF.pure x) L).toOuterMeasure A ≤ r) :
    ∑' t, (law K p t).toOuterMeasure A ≤ (L : ℝ≥0∞) * (1 - r)⁻¹ :=
  tsum_le_of_blocks _ L hL r (event_law_antitone K p A habs)
    (event_law_block K p A habs L r hblock)

end
end Lax343628Proofs.FiniteChain

import Lax343628Proofs.FiniteComparison

namespace Lax343628Proofs.FiniteEvents

open Lax343628Proofs.FiniteDrift
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma large_atoms_card {α : Type*} [Fintype α] (p : PMF α) (S : Finset α)
    (p0 : ℝ) (hp0 : 0 < p0) (hS : ∀ x ∈ S, p0 ≤ (p x).toReal) :
    (S.card : ℝ) ≤ 1 / p0 := by
  have hsum : (S.card : ℝ) * p0 ≤ ∑ x ∈ S, (p x).toReal := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hS
  have hle : (∑ x ∈ S, (p x).toReal) ≤ 1 := by
    rw [← sum_mass p]
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ ENNReal.toReal_nonneg)
  exact (le_div_iff₀ hp0).mpr (hsum.trans hle)

lemma finite_union_bound {α ι : Type*} (p : PMF α) (S : Finset ι) (events : ι → Set α)
    (bound : ℝ) (_hbound : 0 ≤ bound)
    (h : ∀ i ∈ S, p.toOuterMeasure (events i) ≤ ENNReal.ofReal bound) :
    p.toOuterMeasure {x | ∃ i ∈ S, x ∈ events i} ≤ ENNReal.ofReal ((S.card : ℝ) * bound) := by
  have heq : {x | ∃ i ∈ S, x ∈ events i} = ⋃ i ∈ S, events i := by ext x; simp
  rw [heq]
  calc
    _ ≤ ∑ i ∈ S, p.toOuterMeasure (events i) := MeasureTheory.measure_biUnion_finset_le S events
    _ ≤ ∑ _i ∈ S, ENNReal.ofReal bound := Finset.sum_le_sum h
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ S.card)]
      simp

lemma event_zero_of_support {α : Type*} (p : PMF α) (A : Set α)
    (h : ∀ x ∈ p.support, x ∉ A) : p.toOuterMeasure A = 0 := by
  rw [PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  by_cases hx : x ∈ A
  · have hpx : p x = 0 := by
      by_contra hn
      exact h x hn hx
    simp [hx, hpx]
  · simp [hx]

lemma event_bind_bound {α β : Type*} (p : PMF α) (K : α → PMF β) (A : Set β) (r : ℝ≥0∞)
    (h : ∀ x, (K x).toOuterMeasure A ≤ r) : (p.bind K).toOuterMeasure A ≤ r := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' x, p x * r := ENNReal.tsum_le_tsum (fun x ↦ mul_le_mul' le_rfl (h x))
    _ = r := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

lemma event_mono_on_support {α : Type*} (p : PMF α) (A B : Set α)
    (h : ∀ x ∈ p.support, x ∈ A → x ∈ B) : p.toOuterMeasure A ≤ p.toOuterMeasure B := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hA : x ∈ A
  · by_cases hB : x ∈ B
    · simp [hA, hB]
    · have hzero : p x = 0 := by
        by_contra hn
        exact hB (h x hn hA)
      simp [hA, hB, hzero]
  · simp [hA]

end
end Lax343628Proofs.FiniteEvents

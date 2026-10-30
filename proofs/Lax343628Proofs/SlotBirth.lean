import Lax343628Proofs.PlacedBase
import Lax343628Proofs.SlotProfiles
import Lax343628Proofs.MaskSets

namespace Lax343628Proofs.SlotBirth

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.BaseSubsets Lax343628Proofs.PlacedBase
open Lax343628Proofs.SlotProfiles Lax343628Proofs.CountStatistics
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def freshLaw (β : Type*) [Fintype β] [DecidableEq β] (w : ℕ) : PMF (Finset β) :=
  subsetLaw ⟨min w (Fintype.card β), by omega⟩

def freshMean (h : Finset (α ⊕ β) → ℝ) (J : Finset α) (w : ℕ) : ℝ :=
  mean (freshLaw β w) (fun F ↦ h (J.disjSum F))

omit [Fintype α] [DecidableEq α] in
lemma freshMean_zero {j w : ℕ} (hw : w ≤ Fintype.card β)
    (h : Finset (α ⊕ β) → ℝ) (hsupport : ∀ S, S.card ≠ j → h S = 0)
    (J : Finset α) (hsize : J.card + w ≠ j) : freshMean h J w = 0 := by
  unfold freshMean mean
  apply Finset.sum_eq_zero
  intro F _
  change (freshLaw β w F).toReal * h (J.disjSum F) = 0
  by_cases hF : F.card = w
  · rw [hsupport _ (by rwa [Finset.card_disjSum, hF]), mul_zero]
  · have hz : (freshLaw β w F).toReal = 0 := by
      simp only [freshLaw, subsetLaw_mass, Nat.min_eq_left hw, if_neg hF]
    rw [hz, zero_mul]

omit [Fintype α] [DecidableEq α] in
lemma poisson_freshMean {j k : ℕ} (hj : j ≤ k) (hk : k ≤ Fintype.card β)
    (h : Finset (α ⊕ β) → ℝ) (hsupport : ∀ S, S.card ≠ j → h S = 0) (J : Finset α) :
    poissonMean k (freshMean h J) =
      Real.exp (-1) * baseWeight j J * freshMean h J (j - J.card) := by
  unfold poissonMean baseWeight
  by_cases hJ : J.card ≤ j
  · rw [if_pos hJ, Finset.sum_eq_single (j - J.card)]
    · ring
    · intro w hw hne
      have hwk : w ≤ k := by have := Finset.mem_range.mp hw; omega
      rw [freshMean_zero (hwk.trans hk) h hsupport J (by omega), mul_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hJ, mul_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro w hw
    have hwk : w ≤ k := by have := Finset.mem_range.mp hw; omega
    rw [freshMean_zero (hwk.trans hk) h hsupport J (by omega), mul_zero]

omit [DecidableEq α] in
lemma fillLaw_mean (j : ℕ) (J : Finset α) (h : Finset (α ⊕ β) → ℝ) :
    mean (fillLaw j J) h = freshMean h J (j - J.card) := by
  rw [fillLaw, mean_map]
  rfl

lemma mass_times_mean (j : ℕ) (h : Finset (α ⊕ β) → ℝ) :
    beta (Fintype.card α) j * mean (placedLaw j) h =
      ∑ J : Finset α, baseWeight j J * freshMean h J (j - J.card) := by
  rw [beta_eq_rankMass, placedLaw, mean_bind]
  simp_rw [fillLaw_mean]
  unfold mean
  simp_rw [baseLaw_mass]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  have hp := BaseRanks.rankMass_pos (Fintype.card α) j
  field_simp

def birthMean (k : ℕ) (h : Finset (α ⊕ β) → ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ Fintype.card α * ∑ J : Finset α, poissonMean k (freshMean h J)

lemma birthMean_fixed_size {j k : ℕ} (hj : j ≤ k) (hk : k ≤ Fintype.card β)
    (h : Finset (α ⊕ β) → ℝ) (hsupport : ∀ S, S.card ≠ j → h S = 0) :
    birthMean k h = Real.exp (-1) * (1 / 2 : ℝ) ^ Fintype.card α *
      beta (Fintype.card α) j * mean (placedLaw j) h := by
  unfold birthMean
  simp_rw [poisson_freshMean hj hk h hsupport]
  rw [show (∑ J : Finset α, Real.exp (-1) * baseWeight j J * freshMean h J (j - J.card)) =
      Real.exp (-1) * ∑ J : Finset α, baseWeight j J * freshMean h J (j - J.card) by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro J _; ring,
    ← mass_times_mean j h]
  ring

lemma placedLaw_card {j : ℕ} (hj : j ≤ Fintype.card β) (S : Finset (α ⊕ β))
    (hS : S ∈ (placedLaw j).support) : S.card = j := by
  change S ∈ ((baseLaw (α := α) j).bind (fillLaw j)).support at hS
  obtain ⟨J, hJ, hJS⟩ := (PMF.mem_support_bind_iff _ _ S).mp hS
  have hJsize := baseLaw_support j J (ENNReal.toReal_pos hJ ((baseLaw j).apply_ne_top J))
  change S ∈ ((subsetLaw (freshRank (β := β) j J)).map (fun F ↦ J.disjSum F)).support at hJS
  obtain ⟨F, hF, rfl⟩ := (PMF.mem_support_map_iff _ _ S).mp hJS
  have hFsize := subsetLaw_support _ F (ENNReal.toReal_pos hF ((subsetLaw _).apply_ne_top F))
  rw [freshRank_val hj] at hFsize
  rw [Finset.card_disjSum, hFsize]
  omega

end
end Lax343628Proofs.SlotBirth

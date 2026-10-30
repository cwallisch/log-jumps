import Lax343628Proofs.WeightedLaw
import Lax343628Proofs.UniformSubsets

namespace Lax343628Proofs.BaseRanks

open Lax343628Proofs.WeightedLaw Lax343628Proofs.FiniteOrder
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def rankWeight (v j s : ℕ) : ℝ := if s ≤ j then (v.choose s : ℝ) / ((j - s).factorial : ℝ) else 0

lemma rankWeight_nonneg (v j s : ℕ) : 0 ≤ rankWeight v j s := by
  unfold rankWeight
  split_ifs <;> positivity

lemma rankWeight_zero (v j : ℕ) : rankWeight v j 0 = 1 / (j.factorial : ℝ) := by
  simp [rankWeight]

lemma rankWeight_outside {v j s : ℕ} (hs : v < s) : rankWeight v j s = 0 := by
  unfold rankWeight
  rw [Nat.choose_eq_zero_of_lt hs, Nat.cast_zero, zero_div]
  split_ifs <;> rfl

def rankMass (v j : ℕ) : ℝ := ∑ s : Fin (v + 1), rankWeight v j s.val

lemma rankMass_pos (v j : ℕ) : 0 < rankMass v j := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (v + 1))))
    (f := fun s ↦ rankWeight v j s.val) (fun s _ ↦ rankWeight_nonneg v j s.val)
    (Finset.mem_univ (0 : Fin (v + 1)))
  have hzero : 0 < rankWeight v j 0 := by rw [rankWeight_zero]; positivity
  exact hzero.trans_le h

def rankLaw (v j : ℕ) : PMF (Fin (v + 1)) :=
  normalized (fun s ↦ rankWeight v j s.val) (fun s ↦ rankWeight_nonneg v j s.val) (rankMass_pos v j)

lemma rankLaw_mass (v j : ℕ) (s : Fin (v + 1)) :
    (rankLaw v j s).toReal = rankWeight v j s.val / rankMass v j :=
  normalized_mass _ _ _ s

lemma rankLaw_cumulative (v j r : ℕ) : cumulative (rankLaw v j) r =
    lowerSum (fun s : Fin (v + 1) ↦ rankWeight v j s.val) r / rankMass v j :=
  normalized_cumulative _ _ _ r

lemma rankWeight_next {v j s : ℕ} (hs : s ≤ j) :
    rankWeight v (j + 1) s = rankWeight v j s / ((j + 1 - s : ℕ) : ℝ) := by
  have hdiff : j + 1 - s = (j - s) + 1 := by omega
  simp only [rankWeight, if_pos hs, if_pos (show s ≤ j + 1 by omega), hdiff, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

lemma rank_likelihood {v j : ℕ} {s t : ℕ} (hst : s < t) :
    rankWeight v (j + 1) s * rankWeight v j t ≤
      rankWeight v j s * rankWeight v (j + 1) t := by
  by_cases ht : t ≤ j
  · have hs : s ≤ j := by omega
    have htpos : (0 : ℝ) < (j + 1 - t : ℕ) := by exact_mod_cast (show 0 < j + 1 - t by omega)
    have hden : ((j + 1 - t : ℕ) : ℝ) ≤ ((j + 1 - s : ℕ) : ℝ) := by
      exact_mod_cast (show j + 1 - t ≤ j + 1 - s by omega)
    calc
      _ = (rankWeight v j s * rankWeight v j t) / ((j + 1 - s : ℕ) : ℝ) := by
        rw [rankWeight_next hs]
        ring
      _ ≤ (rankWeight v j s * rankWeight v j t) / ((j + 1 - t : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (mul_nonneg (rankWeight_nonneg _ _ _) (rankWeight_nonneg _ _ _))
          htpos hden
      _ = _ := by rw [rankWeight_next ht]; ring
  · have hzero : rankWeight v j t = 0 := by simp only [rankWeight, if_neg ht]
    rw [hzero, mul_zero]
    exact mul_nonneg (rankWeight_nonneg _ _ _) (rankWeight_nonneg _ _ _)

lemma rank_stochastic_order (v j r : ℕ) :
    cumulative (rankLaw v (j + 1)) r ≤ cumulative (rankLaw v j) r := by
  apply likelihood_order
  intro s t hst
  exact rank_likelihood hst

lemma choose_shift_cross {v s t : ℕ} (hs : 0 < s) (hst : s < t) :
    (v.choose (s - 1) : ℝ) * (v.choose t : ℝ) ≤
      (v.choose s : ℝ) * (v.choose (t - 1) : ℝ) := by
  by_cases ht : v < t
  · rw [Nat.choose_eq_zero_of_lt ht, Nat.cast_zero, mul_zero]
    positivity
  have htv : t ≤ v := by omega
  have hs1 : s - 1 + 1 = s := by omega
  have ht1 : t - 1 + 1 = t := by omega
  have hsrec := congrArg (fun a : ℕ ↦ (a : ℝ)) (Nat.choose_succ_right_eq v (s - 1))
  have htrec := congrArg (fun a : ℕ ↦ (a : ℝ)) (Nat.choose_succ_right_eq v (t - 1))
  have hsd : v - (s - 1) = v + 1 - s := by omega
  have htd : v - (t - 1) = v + 1 - t := by omega
  simp only [hs1, ht1, hsd, htd, Nat.cast_mul] at hsrec htrec
  have hdpos : (0 : ℝ) < (v + 1 - s : ℕ) := by exact_mod_cast (show 0 < v + 1 - s by omega)
  have hds : ((v + 1 - t : ℕ) : ℝ) ≤ ((v + 1 - s : ℕ) : ℝ) := by
    exact_mod_cast (show v + 1 - t ≤ v + 1 - s by omega)
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst.le
  have h1 := mul_le_mul_of_nonneg_left hst'
    (show 0 ≤ (v.choose s : ℝ) * (v.choose t : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hds
    (show 0 ≤ (v.choose s : ℝ) * (v.choose (t - 1) : ℝ) by positivity)
  have heq1 := congrArg (fun z : ℝ ↦ z * (v.choose t : ℝ)) hsrec
  have heq2 := congrArg (fun z : ℝ ↦ z * (v.choose s : ℝ)) htrec
  exact (mul_le_mul_iff_left₀ hdpos).mp (by nlinarith)

def shiftedWeight (v j s : ℕ) : ℝ := if s = 0 then 0 else rankWeight v j (s - 1)

lemma shiftedWeight_nonneg (v j s : ℕ) : 0 ≤ shiftedWeight v j s := by
  unfold shiftedWeight
  split_ifs
  · exact le_rfl
  · exact rankWeight_nonneg _ _ _

lemma shifted_likelihood {v j s t : ℕ} (hst : s < t) :
    shiftedWeight v j s * rankWeight v (j + 1) t ≤
      rankWeight v (j + 1) s * shiftedWeight v j t := by
  by_cases hs : s = 0
  · simp only [shiftedWeight, if_pos hs, zero_mul]
    exact mul_nonneg (rankWeight_nonneg _ _ _) (shiftedWeight_nonneg _ _ _)
  have ht : t ≠ 0 := by omega
  simp only [shiftedWeight, if_neg hs, if_neg ht]
  by_cases hsize : t ≤ j + 1
  · have hs0 : 0 < s := by omega
    have hsj : s - 1 ≤ j := by omega
    have htj : t - 1 ≤ j := by omega
    have hsj1 : s ≤ j + 1 := by omega
    have hsd : j - (s - 1) = j + 1 - s := by omega
    have htd : j - (t - 1) = j + 1 - t := by omega
    simp only [rankWeight, if_pos hsj, if_pos htj, if_pos hsj1, if_pos hsize, hsd, htd]
    rw [div_mul_div_comm, div_mul_div_comm]
    exact div_le_div_of_nonneg_right (choose_shift_cross hs0 hst) (by positivity)
  · rw [show rankWeight v (j + 1) t = 0 by simp [rankWeight, hsize], mul_zero]
    exact mul_nonneg (rankWeight_nonneg _ _ _) (rankWeight_nonneg _ _ _)

lemma extended_mass (v j : ℕ) :
    (∑ s : Fin (v + 2), rankWeight v j s.val) = rankMass v j := by
  rw [show v + 2 = (v + 1) + 1 by omega, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, rankWeight_outside (show v < v + 1 by omega), add_zero]
  rfl

lemma shifted_mass (v j : ℕ) :
    (∑ s : Fin (v + 2), shiftedWeight v j s.val) = rankMass v j := by
  rw [show v + 2 = (v + 1) + 1 by omega, Fin.sum_univ_succ]
  simp [shiftedWeight, rankMass]

lemma extended_lowerSum (v j r : ℕ) :
    lowerSum (fun s : Fin (v + 2) ↦ rankWeight v j s.val) r =
      lowerSum (fun s : Fin (v + 1) ↦ rankWeight v j s.val) r := by
  unfold lowerSum
  rw [show v + 2 = (v + 1) + 1 by omega, Fin.sum_univ_castSucc]
  simp [rankWeight_outside (show v < v + 1 by omega)]

lemma shifted_lowerSum (v j r : ℕ) :
    lowerSum (fun s : Fin (v + 2) ↦ shiftedWeight v j s.val) (r + 1) =
      lowerSum (fun s : Fin (v + 1) ↦ rankWeight v j s.val) r := by
  unfold lowerSum
  rw [show v + 2 = (v + 1) + 1 by omega, Fin.sum_univ_succ]
  simp [shiftedWeight]

lemma rank_interleaving (v j r : ℕ) :
    cumulative (rankLaw v j) r ≤ cumulative (rankLaw v (j + 1)) (r + 1) := by
  have h := likelihood_cumulative
    (fun s : Fin (v + 2) ↦ rankWeight v (j + 1) s.val)
    (fun s : Fin (v + 2) ↦ shiftedWeight v j s.val)
    (by rw [extended_mass]; exact rankMass_pos _ _)
    (by rw [shifted_mass]; exact rankMass_pos _ _)
    (fun s t hst ↦ shifted_likelihood hst) (r + 1)
  rw [extended_mass, shifted_mass, extended_lowerSum, shifted_lowerSum] at h
  simpa only [rankLaw_cumulative] using h

def adjacentCoupling (v j : ℕ) :
    FiniteCoupling.Coupling (rankLaw v j) (rankLaw v (j + 1)) :=
  FiniteCoupling.ofCumulative _ _ (rank_stochastic_order v j) (rank_interleaving v j)

lemma adjacentCoupling_support (v j : ℕ) (s t : Fin (v + 1))
    (h : 0 < (adjacentCoupling v j).mass s t) :
    s.val ≤ t.val ∧ t.val ≤ s.val + 1 :=
  FiniteCoupling.ofCumulative_support _ _ _ _ s t h

lemma rankLaw_support (v j : ℕ) (s : Fin (v + 1))
    (h : 0 < (rankLaw v j s).toReal) : s.val ≤ j := by
  rw [rankLaw_mass] at h
  by_contra hn
  simp [rankWeight, hn] at h

end
end Lax343628Proofs.BaseRanks

import Lax343628Proofs.ElitistCounts
import Lax343628Proofs.ValleyBirth
import Lax343628Proofs.PlateauDynamics

namespace Lax343628Proofs.ArrivalFitness

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.Dynamics
open Lax343628Proofs.PlateauDynamics
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

def score (k : ℕ) (x : BitString n) : ℕ := if ones x ≤ n - k ∨ ones x = n then k + ones x else n - ones x

lemma score_cast (k : ℕ) (x : BitString n) : (score k x : ℝ) = jump k x := by
  unfold score jump
  split_ifs <;> rfl

lemma bounds (hk : 1 ≤ k) (hkn : k ≤ n) (x : BitString n) (hx : x ≠ optimum n) :
    1 ≤ score k x ∧ score k x ≤ n := by
  have hxn : ones x ≠ n := fun hh ↦ hx (eq_optimum_of_ones_eq x hh)
  have hle := ones_le x
  unfold score
  split_ifs <;> omega

lemma full_fitness (_hk : 1 ≤ k) (hkn : k ≤ n) (x : BitString n) (hx : x ≠ optimum n)
    (hs : n ≤ score k x) : onPlateau k x := by
  have hxn : ones x ≠ n := fun hh ↦ hx (eq_optimum_of_ones_eq x hh)
  have hle := ones_le x
  unfold score at hs
  unfold onPlateau
  split_ifs at hs <;> omega

lemma ordinary_floor (hk : k ≤ n) (i : ℕ) (x : BitString n) (hx : x ≠ optimum n)
    (hs : k + i ≤ score k x) : i ≤ ones x ∧ ones x ≤ n - k := by
  have hxn : ones x ≠ n := fun hh ↦ hx (eq_optimum_of_ones_eq x hh)
  have hle := ones_le x
  unfold score at hs
  split_ifs at hs <;> omega

lemma ordinary_score (x : BitString n) (hx : ones x ≤ n - k) : score k x = k + ones x := by
  exact if_pos (Or.inl hx)

lemma ordinary_elite (i : ℕ) (x : BitString n) (hx : ones x ≤ n - k) :
    (k + i + 1 : ℝ) ≤ jump k x ↔ i < ones x := by
  rw [← score_cast, ordinary_score x hx]
  exact_mod_cast (show k + i + 1 ≤ k + ones x ↔ i < ones x by omega)

lemma ordinary_event (i : ℕ) (x : BitString n) (hx : i < ones x ∧ ones x ≤ n - k) :
    (k + i + 1 : ℝ) ≤ jump k x := (ordinary_elite i x hx.2).mpr hx.1

lemma valley_floor (hkn : k ≤ n) (j : ℕ) (hj : j < k) (x : BitString n) (hx : x ≠ optimum n) (hs : j ≤ score k x) :
    j ≤ (zeros x).card := by
  have hle := ones_le x
  have hxn : ones x ≠ n := fun hh ↦ hx (eq_optimum_of_ones_eq x hh)
  rw [card_zeros]
  unfold score at hs
  split_ifs at hs <;> omega

lemma valley_event (j : ℕ) (hj : j < k) (x : BitString n) (hx : j < (zeros x).card) :
    (j + 1 : ℝ) ≤ jump k x := by
  rw [← score_cast]
  have hle := ones_le x
  rw [card_zeros] at hx
  unfold score
  split_ifs <;> exact_mod_cast (show j + 1 ≤ _ by omega)

def active (k : ℕ) : Set (Population n mu) := {P | P ∈ missing ∧ ¬plateauPopulation k P}

lemma minimum (hk : 1 ≤ k) (hkn : k ≤ n) (P : Population n mu) (hP : P ∈ active k) :
    ∃ v : Fin n, 1 ≤ v.val ∧ (∀ u, v.val ≤ score k (P u)) ∧ ∃ u, score k (P u) = v.val := by
  obtain ⟨u, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (mu : ℕ)))
    (fun u ↦ score k (P u)) Finset.univ_nonempty
  have hmin' : ∀ w, score k (P u) ≤ score k (P w) := fun w ↦ hmin w (Finset.mem_univ _)
  have hb := bounds hk hkn (P u) (hP.1 u)
  have hv : score k (P u) < n := by
    by_contra hn
    have hn' : ∀ w, n ≤ score k (P w) := fun w ↦ (by omega : n ≤ score k (P u)).trans (hmin' w)
    exact hP.2 (fun w ↦ full_fitness hk hkn (P w) (hP.1 w) (hn' w))
  exact ⟨⟨score k (P u), hv⟩, hb.1, hmin', u, rfl⟩

end
end Lax343628Proofs.ArrivalFitness

import Lax343628Proofs.DrivenPaths
import Lax343628Proofs.PlateauKernelApproximation
import Lax343628Proofs.EmpiricalStability

namespace Lax343628Proofs.RunBoundary

open Lax343628.Algorithm Lax343628Proofs.TaggedDynamics Lax343628Proofs.ClassChannels
open Lax343628Proofs.PlateauDynamics Lax343628Proofs.Sampling
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

lemma next_zero_card (hkn : k ≤ n) (P : Population n mu)
    (hP : ∀ u, (zeros (P u)).card = k) (E : Event n mu) : ∀ u, (zeros (next k P E u)).card = k := by
  have hp : plateauPopulation k P := fun u ↦ PlateauKernelApproximation.plateau_of_zero_card hkn _ (hP u)
  have hq : plateauPopulation k (next k P E) := by
    unfold next
    split_ifs with hz
    · exact replace_onPlateau P hp _ hz _
    · exact hp
  intro u
  rw [card_zeros]
  have hh := hq u
  change ones (next k P E u) = n - k at hh
  omega

lemma plateau_until (hkn : k ≤ n) (P : ℕ → Population n mu) (E : ℕ → Event n mu) (H : ℕ)
    (hnext : ∀ t, t < H → P (t + 1) = next k (P t) (E t))
    (hP0 : ∀ u, (zeros (P 0 u)).card = k) :
    ∀ t, t ≤ H → ∀ u, (zeros (P t u)).card = k := by
  intro t ht
  induction t with
  | zero => exact hP0
  | succ t ih =>
    rw [hnext t (by omega)]
    exact next_zero_card hkn (P t) (ih (by omega)) (E t)

lemma fraction_step (P : Population n mu) (E : Event n mu) (i : Fin n) (b : Fin 2) :
    |fraction i b (next k P E) - fraction i b P| ≤ 1 / (mu : ℕ) := by
  exact EmpiricalStability.average_step_abs P E (fun z ↦ if z i = b then 1 else 0) 1 (by norm_num)
    (fun z ↦ by split_ifs <;> norm_num)

lemma fraction_positive_until (P : ℕ → Population n mu) (E : ℕ → Event n mu) (H : ℕ)
    (hnext : ∀ t, t < H → P (t + 1) = next k (P t) (E t))
    (i : Fin n) (b : Fin 2) (q : ℝ) (hq : 1 / (mu : ℕ) < q)
    (hP0 : 0 < fraction i b (P 0)) (hband : ∀ t, t < H → q ≤ fraction i b (P t)) :
    ∀ t, t ≤ H → 0 < fraction i b (P t) := by
  have hqpos : 0 < q := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 1 / (mu : ℕ)) hq
  intro t ht
  by_cases hbefore : t < H
  · exact hqpos.trans_le (hband t hbefore)
  · have htH : t = H := by omega
    subst t
    cases H with
    | zero => exact hP0
    | succ H =>
      have hs := fraction_step (k := k) (P H) (E H) i b
      rw [← hnext H (by omega)] at hs
      have hlo := (abs_le.mp hs).1
      have hband' := hband H (by omega)
      linarith

lemma exists_class (P : Population n mu) (hP : ∀ u, (zeros (P u)).card = k)
    (i : Fin n) (b : Fin 2) (hf : 0 < fraction i b P) : Nonempty (ColumnKernels.ColumnClass n k i b) := by
  obtain ⟨u, hu⟩ : ∃ u, P u i = b := by
    by_contra hn
    push Not at hn
    have hz : fraction i b P = 0 := by
      unfold fraction
      simp only [if_neg (hn _), FiniteDrift.mean_const]
    linarith
  exact ⟨⟨P u, hP u, hu⟩⟩

end
end Lax343628Proofs.RunBoundary

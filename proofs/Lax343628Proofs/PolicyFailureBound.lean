import Lax343628Proofs.PolicyFailure

namespace Lax343628Proofs.PolicyFailureBound

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PhaseParameters Lax343628Proofs.EntropyLedger
open Lax343628Proofs.PolicyPaths Lax343628Proofs.BlockParameters Lax343628Proofs.Trajectories
open Lax343628Proofs.FiniteEvents
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r H : ℕ} {mu : ℕ+}

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (Rw : ℕ) (hRw : 0 < Rw) (p : PMF (State n mu))
    (hp : ∀ T ∈ p.support, ∀ u, (Sampling.zeros (T.1 u)).card = r + 1)
    (qcap : ℝ≥0∞)
    (hcap : (pathLaw (driver (r + 1) pc) p H).toOuterMeasure
      {h | ∃ t, ¬ColumnBlock.cap (1 / 125) (h t).1} ≤ qcap) :
    (pathLaw (driver (r + 1) pc) p H).toOuterMeasure
      {h | (configuration (processed S (r + 1)) (theta S) (1 / 125)
        (seedSize S n (r + 1) mu delta) Rw (rounds mu * horizon (S : ℕ) mu) h (Fin.last H)).stage = Stage.failure} ≤
      qcap + ENNReal.ofReal ((n : ℝ) * (((H : ℝ) + 1) * delta)) +
        ENNReal.ofReal (((2 * (S : ℕ) ^ 12 + 2 : ℕ) : ℝ) *
          ((((n : ℝ) + (mu : ℕ)) * ((S : ℕ) : ℝ) ^ 254 * logarithms n mu delta) / ((Rw : ℝ) + 1))) +
        ENNReal.ofReal ((n : ℝ) * (((H : ℝ) + 1) *
          ((((rounds mu * horizon (S : ℕ) mu : ℕ) : ℝ) + 1) * delta))) := by
  let Rs := rounds mu * horizon (S : ℕ) mu
  let M := seedSize S n (r + 1) mu delta
  let a := processed S (r + 1)
  let process := pathLaw (driver (r + 1) pc) p H
  let A : Set (Fin (H + 1) → State n mu) := {h | ∃ t, ¬ColumnBlock.cap (1 / 125) (h t).1}
  let B := GlobalProtection.failure (n := n) (mu := mu) S H (r + 1) (1 / 125)
  let C : Set (Fin (H + 1) → State n mu) := {h | ∃ e : Fin (2 * (S : ℕ) ^ 12 + 2),
    h ∈ GlobalWait.failure H (r + 1) a (theta S) (1 / 125) M Rw Rs e.val}
  let D : Set (Fin (H + 1) → State n mu) := {h | ∃ i : Fin n, ∃ s : Fin (H + 1),
    h ∈ GlobalService.failure H Rs (r + 1) M a (1 / 125) i s}
  have hc := PhaseConditions.of_size S hS n (r + 1) mu delta (by omega) hrS hD hd hmu hn
  have hw : 1 / ((S : ℕ) : ℝ) ≤ 1 / 125 ∧ (1 / 125 : ℝ) ≤ 1 := by
    constructor
    · apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      exact_mod_cast (show 125 ≤ (S : ℕ) by omega)
    · norm_num
  have hRs : 0 < Rs := by unfold Rs rounds horizon; positivity
  have hmono : process.toOuterMeasure
      {h | (configuration a (theta S) (1 / 125) M Rw Rs h (Fin.last H)).stage = Stage.failure} ≤
      process.toOuterMeasure ((A ∪ B) ∪ C ∪ D) := by
    apply event_mono_on_support
    intro h hh hfail
    have hplat := path_invariant (driver (r + 1) pc) p
      {T | ∀ u, (Sampling.zeros (T.1 u)).card = r + 1} hp (by
        intro T hT U hU
        obtain ⟨E, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hU
        exact RunBoundary.next_zero_card (by have := hc.dimension; omega) T.1 hT E) h hh
    have hK : (ColumnMarks.refresh Finset.univ a (h 0).1).card ≤ (S : ℕ) ^ 12 :=
      (ColumnMarks.refresh_size (h 0).1 (hplat 0) Finset.univ a (processed_bounds S (r + 1)).1).trans hc.services
    have hbad := PolicyFailure.contains S delta Rw ((S : ℕ) ^ 12) hRw hRs h hplat hK hfail
    rcases hbad with ha | hb | hc | hd
    · exact Or.inl (Or.inl (Or.inl ha))
    · exact Or.inl (Or.inl (Or.inr hb))
    · exact Or.inl (Or.inr hc)
    · exact Or.inr hd
  have hB := GlobalProtection.bound (J := H) S hS hr hrS hD pc (1 / 125) delta hpc hw hd hmu hn p
  have hC := GlobalWait.bound (H := H) S hS hr hrS hD pc delta hpc hd hmu hn Rw Rs
    (2 * (S : ℕ) ^ 12 + 2) hRw hRs p
  have hD' := GlobalService.bound (H := H) S hS hr hrS hD pc (1 / 125) delta hpc hw hd hmu hn p
  exact hmono.trans ((MeasureTheory.measure_union_le _ _).trans
    (add_le_add ((MeasureTheory.measure_union_le _ _).trans
      (add_le_add ((MeasureTheory.measure_union_le _ _).trans (add_le_add hcap hB)) hC)) hD'))

end
end Lax343628Proofs.PolicyFailureBound

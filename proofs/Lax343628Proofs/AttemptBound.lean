import Lax343628Proofs.PolicyFailureBound
import Lax343628Proofs.PolicyTerminal
import Lax343628Proofs.FlatSampling
import Lax343628Proofs.TimeAbsorption

namespace Lax343628Proofs.AttemptBound

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PhaseParameters Lax343628Proofs.EntropyLedger Lax343628Proofs.AttemptLengths
open Lax343628Proofs.PolicyPaths Lax343628Proofs.Trajectories Lax343628Proofs.FiniteEvents
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r H : ℕ} {mu : ℕ+}

def noOptimum (H : ℕ) : Set (Fin (H + 1) → State n mu) :=
  {h | ∀ j : Fin H, (h j.succ).2.2.1 ≠ optimum n}

lemma no_child_at (h : Fin (H + 1) → State n mu) (hh : h ∈ noOptimum H)
    (t : Fin (H + 1)) (ht : 0 < t.val) : (h t).2.2.1 ≠ optimum n := by
  let j : Fin H := ⟨t.val - 1, by have := t.isLt; omega⟩
  have heq : j.succ = t := Fin.ext (by simp only [Fin.val_succ]; dsimp [j]; omega)
  rw [← heq]
  exact hh j

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (p : PMF (State n mu)) (hp : ∀ T ∈ p.support, ∀ u, (Sampling.zeros (T.1 u)).card = r + 1)
    (qcap : ℝ≥0∞)
    (hcap : (pathLaw (driver (r + 1) pc) p (decision S n mu delta + terminal S)).toOuterMeasure
      {h | ∃ t, ¬ColumnBlock.cap (1 / 125) (h t).1} ≤ qcap) :
    (pathLaw (driver (r + 1) pc) p (decision S n mu delta + terminal S)).toOuterMeasure
      (noOptimum (decision S n mu delta + terminal S)) ≤
      qcap + (qcap + ENNReal.ofReal ((n : ℝ) * (((decision S n mu delta + terminal S : ℕ) : ℝ) + 1) * delta) +
        ENNReal.ofReal (1 / 16) + ENNReal.ofReal ((n : ℝ) *
          ((((decision S n mu delta + terminal S : ℕ) : ℝ) + 1) * (((service S mu : ℝ) + 1) * delta)))) +
        ENNReal.ofReal (1 / 64) := by
  let D := decision S n mu delta
  let R := terminal S
  let L := D + R
  let Rw := wait S n mu delta
  let Rs := service S mu
  let M := seedSize S n (r + 1) mu delta
  let a := processed S (r + 1)
  let process := pathLaw (driver (r + 1) pc) p L
  let A : Set (Fin (L + 1) → State n mu) := {h | ∃ t, ¬ColumnBlock.cap (1 / 125) (h t).1}
  let B : Set (Fin (L + 1) → State n mu) :=
    {h | (configuration a (theta S) (1 / 125) M Rw Rs h (Fin.last L)).stage = Stage.failure}
  let C : Set (Fin (L + 1) → State n mu) :=
    {h | ∀ j, PathWindows.window L R D (by omega) h j ∈ FlatSampling.safe (r + 1) (theta S)}
  have hc := PhaseConditions.of_size S hS n (r + 1) mu delta (by omega) hrS hD hd hmu hn
  have hRw := wait_pos S n mu delta hd
  have hRs := service_pos S mu
  have hDpos : 0 < D := by dsimp [D, decision]; positivity
  have hmono : process.toOuterMeasure (noOptimum L) ≤ process.toOuterMeasure ((A ∪ B) ∪ C) := by
    apply event_mono_on_support
    intro h hh hno
    by_cases hA : h ∈ A
    · exact Or.inl (Or.inl hA)
    by_cases hB : h ∈ B
    · exact Or.inl (Or.inr hB)
    right
    have hcap0 : ColumnBlock.cap (1 / 125) (h 0).1 := by
      by_contra hn
      exact hA ⟨0, hn⟩
    have hplat := path_invariant (driver (r + 1) pc) p
      {T | ∀ u, (Sampling.zeros (T.1 u)).card = r + 1} hp (by
        intro T hT U hU
        obtain ⟨E, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hU
        exact RunBoundary.next_zero_card (by have := hc.dimension; omega) T.1 hT E) h hh
    have hK := (ColumnMarks.refresh_size (h 0).1 (hplat 0) Finset.univ a (processed_bounds S (r + 1)).1).trans hc.services
    intro j
    let t : Fin (L + 1) := ⟨D + j.val, by have := j.isLt; omega⟩
    refine ⟨hplat t, ?_, no_child_at h hno t (by dsimp [t]; omega)⟩
    exact PolicyTerminal.flat_after a (theta S) (1 / 125) M Rw Rs ((S : ℕ) ^ 12)
      (PolicyWaitBound.processed_lt_theta S (r + 1)) hRw hRs h hcap0 hK hno hB t (by
        change (2 * (S : ℕ) ^ 12 + 2) * (Rw + Rs) ≤ D + j.val
        change D ≤ D + j.val
        omega)
  have hB := PolicyFailureBound.bound (H := L) S hS hr hrS hD pc delta hpc hd hmu hn Rw hRw p hp qcap hcap
  have hwait := wait_error S n mu delta hd
  have hB' : process.toOuterMeasure B ≤ qcap + ENNReal.ofReal ((n : ℝ) * (((L : ℝ) + 1) * delta)) +
      ENNReal.ofReal (1 / 16) + ENNReal.ofReal ((n : ℝ) * (((L : ℝ) + 1) * (((Rs : ℝ) + 1) * delta))) := by
    apply hB.trans
    exact add_le_add (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hwait)) le_rfl
  have hC : process.toOuterMeasure C ≤ ENNReal.ofReal (1 / 64) := by
    have hh := event_bind_bound (FiniteChain.law (driver (r + 1) pc) p D)
      (fun x ↦ pathLaw (driver (r + 1) pc) (PMF.pure x) R)
      {h | ∀ j, h j ∈ FlatSampling.safe (r + 1) (theta S)} (ENNReal.ofReal (1 / 64))
      (fun x ↦ FlatSampling.bound S hS (by omega) (by have := hc.dimension; omega) hD pc hpc hc.flat (PMF.pure x))
    rw [← PathWindows.window_law (driver (r + 1) pc) p L R D (by omega), PMF.toOuterMeasure_map_apply] at hh
    exact hh
  have hh := hmono.trans ((MeasureTheory.measure_union_le _ _).trans
    (add_le_add ((MeasureTheory.measure_union_le _ _).trans (add_le_add hcap hB')) hC))
  simpa only [mul_assoc] using hh

end
end Lax343628Proofs.AttemptBound

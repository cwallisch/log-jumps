import Lax343628Proofs.SpeciesReentry

namespace Lax343628Proofs.SpeciesCap

open Lax343628.Algorithm Lax343628Proofs.Genotypes Lax343628Proofs.SpeciesState
open Lax343628Proofs.PopulationRatio Lax343628Proofs.PlateauDynamics Lax343628Proofs.Deletion
open Lax343628Proofs.SpeciesEntry Lax343628Proofs.SpeciesProtection
open Lax343628Proofs.SpeciesReentry Lax343628Proofs.Trajectories
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteEvents Lax343628Proofs.FiniteChain
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma total_weight_upper {n k : ℕ} {μ : ℕ+} (B : Genotype n k) (P : Population n μ) :
    total (weightFunction B) P ≤ (5 / 4 : ℝ) * ((μ : ℕ) - count (toString B) P) := by
  have hpoint : ∀ x, weightFunction B x ≤ (5 / 4 : ℝ) * (1 - indicator (toString B) x) := by
    intro x
    by_cases hx : x = toString B
    · subst x
      simp [indicator, weightFunction_anchor]
    · simpa only [indicator, if_neg hx, sub_zero, mul_one] using (weightFunction_bounds B x).2
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (μ : ℕ)))) ↦ hpoint (P i))
  change total (weightFunction B) P ≤ _ at h
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact h

lemma cap_violation {n k : ℕ} {μ : ℕ+} (B : Genotype n k) (P : Population n μ)
    (hcap : (124 / 125 : ℝ) * (μ : ℕ) < count (toString B) P) :
    (μ : ℕ) / (2 : ℝ) ≤ count (toString B) P ∧
      ratio (weightFunction B) (toString B) P < 1 / 50 := by
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have hN : 0 < count (toString B) P := by linarith
  constructor
  · linarith
  · by_contra hn
    have hQ : 1 / 50 ≤ ratio (weightFunction B) (toString B) P := le_of_not_gt hn
    have hW := (le_div_iff₀ hN).mp hQ
    have hupper := total_weight_upper B P
    nlinarith

def capFailure {n k : ℕ} {μ : ℕ+} (t0 H : ℕ) : Set (Fin (H + 1) → Population n μ) :=
  {h | ∃ t : Fin (H + 1), t0 ≤ t.val ∧ ∃ B : Genotype n k,
    (124 / 125 : ℝ) * (μ : ℕ) < count (toString B) (h t)}

lemma horizon_cap_bound {n k : ℕ} {μ : ℕ+} {p0 p_c : ℝ}
    (hcond : CloneProtection.Conditions n k p_c p0)
    (herror : (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤
      strictConstant * p0 ^ 2) (hμ : 200 ≤ (μ : ℕ) * p0) (hp0 : p0 ≤ 1 / 8)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) (P : Population n μ) (hP : plateauPopulation k P)
    (t0 H : ℕ) (hH : t0 ≤ H) :
    (pathLaw (auxiliaryStep k p_c) (PMF.pure P) H).toOuterMeasure (capFailure (k := k) t0 H) ≤
      ENNReal.ofReal ((1 / 20 : ℝ) / (p0 * entryDrift n k μ p0 * ((t0 : ℝ) + 1)) +
        (Fintype.card (Genotype n k) : ℝ) * ((H : ℝ) + 1) ^ 2 *
          (countFailure k μ p_c p0 + ratioFailure μ p_c p0)) := by
  let K : Population n μ → PMF (Population n μ) := auxiliaryStep k p_c
  let process := pathLaw K (PMF.pure P) H
  let entryEvent : Set (Fin (H + 1) → Population n μ) :=
    {h | ∃ B ∈ initiallyBad (k := k) P p0, ∀ i, before H t0 hH h i ∈ badSet B p0}
  let returning (t : Fin (H + 1)) : Set (Fin (H + 1) → Population n μ) :=
    {h | before H t.val (Nat.le_of_lt_succ t.isLt) h ∈ reentryEvent (k := k) p0 t.val}
  let F : ℝ := countFailure k μ p_c p0 + ratioFailure μ p_c p0
  have hF : 0 ≤ F := by dsimp [F, countFailure, ratioFailure]; positivity
  have hEntry : process.toOuterMeasure entryEvent ≤
      ENNReal.ofReal ((1 / 20 : ℝ) / (p0 * entryDrift n k μ p0 * ((t0 : ℝ) + 1))) := by
    have h := initial_species_entry hcond.entry hμ p_c hp_c P hP t0
    rw [← pathLaw_before K (PMF.pure P) H t0 hH, PMF.toOuterMeasure_map_apply] at h
    exact h
  have hReturn (t : Fin (H + 1)) : process.toOuterMeasure (returning t) ≤
      ENNReal.ofReal ((Fintype.card (Genotype n k) : ℝ) * ((H : ℝ) + 1) * F) := by
    have h := reentry_probability hcond herror hμ hp0 hp_c (PMF.pure P)
      (fun Q hQ ↦ by have heq := (PMF.mem_support_pure_iff P Q).mp hQ; simpa only [heq] using hP) t.val
    rw [← pathLaw_before K (PMF.pure P) H t.val (Nat.le_of_lt_succ t.isLt),
      PMF.toOuterMeasure_map_apply] at h
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    have ht : (t.val : ℝ) + 1 ≤ (H : ℝ) + 1 := by exact_mod_cast t.isLt
    have hc : (0 : ℝ) ≤ Fintype.card (Genotype n k) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hc) hF
  have hUnion := finite_union_bound process (Finset.univ : Finset (Fin (H + 1))) returning
    ((Fintype.card (Genotype n k) : ℝ) * ((H : ℝ) + 1) * F) (by positivity) (fun t _ ↦ hReturn t)
  have hmono : process.toOuterMeasure (capFailure (k := k) t0 H) ≤
      process.toOuterMeasure (entryEvent ∪ {h | ∃ t ∈ (Finset.univ : Finset (Fin (H + 1))), h ∈ returning t}) := by
    apply event_mono_on_support
    intro h hh hcap
    obtain ⟨t, ht0, B, hB⟩ := hcap
    have hbad := cap_violation B (h t) hB
    let g := before H t.val (Nat.le_of_lt_succ t.isLt) h
    by_cases hprev : ∃ i, g i ∉ badSet B p0
    · right
      exact ⟨t, Finset.mem_univ _, B, by simpa only [g, before_last] using hbad.1,
        by simpa only [g, before_last] using hbad.2, hprev⟩
    · left
      have hall : ∀ i, g i ∈ badSet B p0 := by simpa only [not_exists, not_not] using hprev
      have hinit := hall 0
      change h 0 ∈ badSet B p0 at hinit
      rw [path_pure_start K P h hh] at hinit
      refine ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinit⟩, ?_⟩
      intro i
      exact hall ⟨i.val, by have hi := i.isLt; omega⟩
  have hprob := hmono.trans (MeasureTheory.measure_union_le _ _)
  apply (hprob.trans (add_le_add hEntry hUnion)).trans_eq
  rw [← ENNReal.ofReal_add (by
    have hp := hcond.entry.threshold_pos
    have hd := SpeciesEntry.entryDrift_pos (μ := μ) hcond.entry
    positivity) (by positivity)]
  congr 1
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  dsimp [F]
  ring

end
end Lax343628Proofs.SpeciesCap

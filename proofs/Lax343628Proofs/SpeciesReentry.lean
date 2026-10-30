import Lax343628Proofs.BandPaths

namespace Lax343628Proofs.SpeciesReentry

open Lax343628.Algorithm Lax343628Proofs.Genotypes Lax343628Proofs.SpeciesState
open Lax343628Proofs.PopulationRatio Lax343628Proofs.PlateauDynamics
open Lax343628Proofs.SpeciesEntry Lax343628Proofs.SpeciesProtection
open Lax343628Proofs.Trajectories Lax343628Proofs.LastExit Lax343628Proofs.BandPaths
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain Lax343628Proofs.PathBarriers
open Lax343628Proofs.FiniteEvents
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def entryTail {α : Type*} (T : ℕ) (s : Fin (T + 1)) (h : Fin (T + 1) → α) :
    Fin (T - s.val + 1) → α :=
  suffix T s.val (T - s.val) (by have h := s.isLt; omega) h

lemma entryTail_first {α : Type*} (T : ℕ) (s : Fin (T + 1)) (h : Fin (T + 1) → α) :
    entryTail T s h 0 = h s := rfl

lemma entryTail_last {α : Type*} (T : ℕ) (s : Fin (T + 1)) (h : Fin (T + 1) → α) :
    entryTail T s h (Fin.last (T - s.val)) = h (Fin.last T) := by
  unfold entryTail suffix
  congr 1
  apply Fin.ext
  have hs := s.isLt
  simp only [Fin.val_last]
  omega

def countEvent {n k : ℕ} {μ : ℕ+} (B : Genotype n k) (p0 : ℝ) (T : ℕ)
    (s : Fin (T + 1)) : Set (Fin (T + 1) → Population n μ) :=
  {h | count (toString B) (h s) ≤ (μ : ℕ) * p0 + 1 ∧
    2 * (μ : ℕ) * p0 < count (toString B) (frozen (CloneProtection.countBand B p0) (entryTail T s h))}

def ratioEvent {n k : ℕ} {μ : ℕ+} (B : Genotype n k) (p0 : ℝ) (T : ℕ)
    (s : Fin (T + 1)) : Set (Fin (T + 1) → Population n μ) :=
  {h | 1 / 25 - ratioStep μ p0 ≤ ratio (weightFunction B) (toString B) (h s) ∧
    ratio (weightFunction B) (toString B) (frozen (ratioBand B p0) (entryTail T s h)) < 1 / 50}

lemma reentry_alternative {n k T : ℕ} {μ : ℕ+} {p0 p_c : ℝ}
    (hμ : 200 ≤ (μ : ℕ) * p0) (hp0 : p0 ≤ 1 / 8) (B : Genotype n k)
    (initial : PMF (Population n μ)) (h : Fin (T + 1) → Population n μ)
    (hh : h ∈ (pathLaw (auxiliaryStep k p_c) initial T).support)
    (hplateau : ∀ i, plateauPopulation k (h i))
    (hcount : (μ : ℕ) / (2 : ℝ) ≤ count (toString B) (h (Fin.last T)))
    (hratio : ratio (weightFunction B) (toString B) (h (Fin.last T)) < 1 / 50)
    (hprev : ∃ i, h i ∉ badSet B p0) :
    ∃ s, h ∈ countEvent B p0 T s ∨ h ∈ ratioEvent B p0 T s := by
  have hμpos : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have hscaled := mul_le_mul_of_nonneg_left hp0 hμpos.le
  have hlastN : 2 * (μ : ℕ) * p0 < count (toString B) (h (Fin.last T)) := by nlinarith
  have hlastbad : h (Fin.last T) ∈ badSet B p0 :=
    ⟨hplateau _, by nlinarith, by linarith⟩
  have hprevious : ∃ i ≤ Fin.last T, h i ∉ badSet B p0 := by
    obtain ⟨i, hi⟩ := hprev
    exact ⟨i, Fin.le_last i, hi⟩
  obtain ⟨old, holdT, holdbad, hafter⟩ := last_outside h (badSet B p0) (Fin.last T) hlastbad hprevious
  have holdval : old.val < T := holdT
  let s : Fin (T + 1) := ⟨old.val + 1, by omega⟩
  have hbad : ∀ j, entryTail T s h j ∈ badSet B p0 := by
    intro j
    apply hafter ⟨s.val + j.val, by have hj := j.isLt; have hs := s.isLt; omega⟩
    · change old.val < s.val + j.val
      dsimp [s]
      omega
    · exact Fin.le_last _
  let i : Fin T := ⟨old.val, holdval⟩
  have hstep : h s ∈ (auxiliaryStep k p_c (h old)).support := by
    have hi : i.castSucc = old := by apply Fin.ext; rfl
    have his : i.succ = s := by apply Fin.ext; rfl
    have hstep := path_step_support (auxiliaryStep k p_c) initial h hh i
    rw [hi, his] at hstep
    exact hstep
  refine ⟨s, ?_⟩
  by_cases holdN : count (toString B) (h old) ≤ (μ : ℕ) * p0
  · left
    constructor
    · have hs := (abs_le.mp (auxiliary_count_abs (toString B) p_c (h old) (h s) hstep)).2
      linarith
    · apply count_frozen_exit B _ hbad
      rwa [entryTail_last]
  · right
    have holdQ : 1 / 25 ≤ ratio (weightFunction B) (toString B) (h old) := by
      by_contra hn
      apply holdbad
      exact ⟨hplateau _, lt_of_not_ge holdN, lt_of_not_ge hn⟩
    constructor
    · exact ratio_entry_overshoot hμ B p_c (h old) (h s) (lt_of_not_ge holdN) holdQ hstep
    · apply ratio_frozen_exit B _ hbad
      rwa [entryTail_last]

def countFailure (k : ℕ) (μ : ℕ+) (p_c p0 : ℝ) : ℝ :=
  Real.exp (-CloneProtection.countDrift k p_c p0 * ((μ : ℕ) * p0 - 1))

def ratioFailure (μ : ℕ+) (p_c p0 : ℝ) : ℝ :=
  Real.exp (-(ratioDrift μ p_c p0 / ratioStep μ p0 ^ 2) *
    (1 / 25 - ratioStep μ p0 - 1 / 50))

lemma countEvent_probability {n k : ℕ} {μ : ℕ+} {p0 p_c : ℝ}
    (hcond : CloneProtection.Conditions n k p_c p0) (hp_c : 0 ≤ p_c ∧ p_c ≤ 1)
    (B : Genotype n k) (initial : PMF (Population n μ)) (T : ℕ) (s : Fin (T + 1)) :
    (pathLaw (auxiliaryStep k p_c) initial T).toOuterMeasure (countEvent B p0 T s) ≤
      ENNReal.ofReal (countFailure k μ p_c p0) := by
  let K : Population n μ → PMF (Population n μ) := auxiliaryStep k p_c
  let E : Set (Fin (T - s.val + 1) → Population n μ) :=
    {h | 2 * (μ : ℕ) * p0 < count (toString B) (frozen (CloneProtection.countBand B p0) h)}
  let S : Set (Population n μ) := {P | count (toString B) P ≤ (μ : ℕ) * p0 + 1}
  have hδ := (CloneProtection.countDrift_bounds hcond hp_c).1
  have hbound : ∀ P ∈ S, (pathLaw K (PMF.pure P) (T - s.val)).toOuterMeasure E ≤
      ENNReal.ofReal (countFailure k μ p_c p0) := by
    intro P hP
    apply (CloneProtection.count_path_barrier hcond hp_c B P (T - s.val)).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hδ)
    dsimp [S] at hP
    linarith
  have h := conditional_path_bound K (law K initial s.val) S (T - s.val) E _ hbound
  have hmap := pathLaw_suffix K initial T s.val (T - s.val) (by have h := s.isLt; omega)
  change (pathLaw K initial T).map (entryTail T s) = _ at hmap
  rw [← hmap, PMF.toOuterMeasure_map_apply] at h
  have heq : countEvent B p0 T s = (entryTail T s) ⁻¹' {h | h ∈ E ∧ h 0 ∈ S} := by
    ext h
    simp only [countEvent, E, S, Set.mem_preimage, Set.mem_ofPred_eq, entryTail_first, and_comm]
  rw [heq]
  exact h

lemma ratioEvent_probability {n k : ℕ} {μ : ℕ+} {p0 p_c : ℝ}
    (hcond : EntryBounds.Conditions n k p0)
    (herror : (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤
      strictConstant * p0 ^ 2) (hμ : 200 ≤ (μ : ℕ) * p0)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) (B : Genotype n k)
    (initial : PMF (Population n μ)) (T : ℕ) (s : Fin (T + 1)) :
    (pathLaw (auxiliaryStep k p_c) initial T).toOuterMeasure (ratioEvent B p0 T s) ≤
      ENNReal.ofReal (ratioFailure μ p_c p0) := by
  let K : Population n μ → PMF (Population n μ) := auxiliaryStep k p_c
  let E : Set (Fin (T - s.val + 1) → Population n μ) :=
    {h | ratio (weightFunction B) (toString B) (frozen (ratioBand B p0) h) < 1 / 50}
  let S : Set (Population n μ) :=
    {P | 1 / 25 - ratioStep μ p0 ≤ ratio (weightFunction B) (toString B) P}
  have hpar := ratio_parameters (μ := μ) hcond.threshold_pos hcond.threshold_le_one hp_c
  have hδ : 0 ≤ ratioDrift μ p_c p0 / ratioStep μ p0 ^ 2 :=
    div_nonneg hpar.2.1 (sq_nonneg _)
  have hbound : ∀ P ∈ S, (pathLaw K (PMF.pure P) (T - s.val)).toOuterMeasure E ≤
      ENNReal.ofReal (ratioFailure μ p_c p0) := by
    intro P hP
    apply (ratio_path_barrier hcond herror hμ B p_c hp_c P (T - s.val)).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (sub_le_sub_right hP (1 / 50)) (neg_nonpos.mpr hδ)
  have h := conditional_path_bound K (law K initial s.val) S (T - s.val) E _ hbound
  have hmap := pathLaw_suffix K initial T s.val (T - s.val) (by have h := s.isLt; omega)
  change (pathLaw K initial T).map (entryTail T s) = _ at hmap
  rw [← hmap, PMF.toOuterMeasure_map_apply] at h
  have heq : ratioEvent B p0 T s = (entryTail T s) ⁻¹' {h | h ∈ E ∧ h 0 ∈ S} := by
    ext h
    simp only [ratioEvent, E, S, Set.mem_preimage, Set.mem_ofPred_eq, entryTail_first, and_comm]
  rw [heq]
  exact h

def reentryEvent {n k : ℕ} {μ : ℕ+} (p0 : ℝ) (T : ℕ) :
    Set (Fin (T + 1) → Population n μ) :=
  {h | ∃ B : Genotype n k, (μ : ℕ) / (2 : ℝ) ≤ count (toString B) (h (Fin.last T)) ∧
    ratio (weightFunction B) (toString B) (h (Fin.last T)) < 1 / 50 ∧
      ∃ i, h i ∉ badSet B p0}

lemma reentry_probability {n k : ℕ} {μ : ℕ+} {p0 p_c : ℝ}
    (hcond : CloneProtection.Conditions n k p_c p0)
    (herror : (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤
      strictConstant * p0 ^ 2) (hμ : 200 ≤ (μ : ℕ) * p0) (hp0 : p0 ≤ 1 / 8)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) (initial : PMF (Population n μ))
    (hinitial : ∀ P ∈ initial.support, plateauPopulation k P) (T : ℕ) :
    (pathLaw (auxiliaryStep k p_c) initial T).toOuterMeasure (reentryEvent (k := k) p0 T) ≤
      ENNReal.ofReal ((Fintype.card (Genotype n k) : ℝ) * (T + 1) *
        (countFailure k μ p_c p0 + ratioFailure μ p_c p0)) := by
  let process := pathLaw (auxiliaryStep k p_c) initial T
  let events : (Genotype n k × Fin (T + 1)) → Set (Fin (T + 1) → Population n μ) :=
    fun Bs ↦ countEvent Bs.1 p0 T Bs.2 ∪ ratioEvent Bs.1 p0 T Bs.2
  have hbound : ∀ Bs, process.toOuterMeasure (events Bs) ≤
      ENNReal.ofReal (countFailure k μ p_c p0 + ratioFailure μ p_c p0) := by
    intro Bs
    have hcount := countEvent_probability hcond hp_c Bs.1 initial T Bs.2
    have hratio := ratioEvent_probability hcond.entry herror hμ hp_c Bs.1 initial T Bs.2
    have hunion := MeasureTheory.measure_union_le (μ := process.toOuterMeasure)
      (countEvent Bs.1 p0 T Bs.2) (ratioEvent Bs.1 p0 T Bs.2)
    have h := hunion.trans (add_le_add hcount hratio)
    rw [← ENNReal.ofReal_add
      (show 0 ≤ countFailure k μ p_c p0 by unfold countFailure; positivity)
      (show 0 ≤ ratioFailure μ p_c p0 by unfold ratioFailure; positivity)] at h
    exact h
  have hunion := finite_union_bound process (Finset.univ : Finset (Genotype n k × Fin (T + 1)))
    events (countFailure k μ p_c p0 + ratioFailure μ p_c p0)
    (by unfold countFailure ratioFailure; positivity) (fun Bs _ ↦ hbound Bs)
  have hmono : process.toOuterMeasure (reentryEvent (k := k) p0 T) ≤
      process.toOuterMeasure {h | ∃ Bs ∈ (Finset.univ : Finset (Genotype n k × Fin (T + 1))),
        h ∈ events Bs} := by
    apply event_mono_on_support
    intro h hh hevent
    obtain ⟨B, hc, hq, hprev⟩ := hevent
    have hplat : ∀ i, plateauPopulation k (h i) := path_invariant (auxiliaryStep k p_c) initial
      {P | plateauPopulation k P} hinitial (fun P hP Q hQ ↦ auxiliary_invariant p_c P hP Q hQ) h hh
    obtain ⟨s, hs⟩ := reentry_alternative hμ hp0 B initial h hh hplat hc hq hprev
    exact ⟨(B, s), Finset.mem_univ _, hs⟩
  apply hmono.trans
  simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one] using hunion

end
end Lax343628Proofs.SpeciesReentry

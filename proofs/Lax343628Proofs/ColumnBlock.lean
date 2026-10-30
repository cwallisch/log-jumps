import Lax343628Proofs.ColumnBudget
import Lax343628Proofs.DrivenStop
import Lax343628Proofs.Odds

namespace Lax343628Proofs.ColumnBlock

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels Lax343628Proofs.ColumnBudget
open Lax343628Proofs.DrivenNoise Lax343628Proofs.DrivenPaths Lax343628Proofs.DrivenStop
open Lax343628Proofs.FiniteDrift Lax343628Proofs.Trajectories Lax343628Proofs.ClassChannels
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r R ell : ℕ} {mu rs : ℕ+}

def cap (omega : ℝ) (P : Population n mu) : Prop := ∀ z : BitString n, EmpiricalKernels.frequency P z ≤ 1 - omega

def active (k : ℕ) (i : Fin n) (lo hi omega : ℝ) (P : Population n mu) : Prop :=
  (∀ u, (Sampling.zeros (P u)).card = k) ∧ lo < Odds.value i P ∧ Odds.value i P < hi ∧ cap omega P

lemma active_bands {k : ℕ} (i : Fin n) (lo hi omega : ℝ) (hlo : 0 < lo)
    (P : Population n mu) (hP : active k i lo hi omega P) :
    Odds.lowerMass lo ≤ fraction i 1 P ∧ Odds.upperMass hi ≤ fraction i 0 P ∧
      fraction i 1 P ≤ Odds.lowerMass hi := by
  have hp := Odds.positive_fractions i P (hlo.trans hP.2.1)
  have hb := Odds.band_frequencies i P hlo hP.2.1 hP.2.2.1
  refine ⟨hb.1.le, hb.2.le, ?_⟩
  have he := (Odds.exact_fractions i P hp.2).1
  rw [← he]
  exact Odds.lowerMass_mono (hlo.trans hP.2.1).le hP.2.2.1.le

lemma pointwise_exit (hr : 1 ≤ r) (pc a omega L B hi : ℝ) (i : Fin n)
    (S0 : State n mu) (hP0 : ∀ u, (Sampling.zeros (S0.1 u)).card = r + 1)
    (hf0 : ∀ b : Fin 2, 0 < fraction i b S0.1) (hB : 0 < B)
    (_hhi : Odds.value i S0.1 < hi) (hupper : hi ≤ B * Odds.value i S0.1)
    (hb : Budget n (r + 1) R ell mu rs pc a
      (Odds.lowerMass (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))))
      (Odds.upperMass hi) (Odds.lowerMass hi) omega L B)
    (h : Fin (R + 1) → State n mu)
    (hh : h ∈ (pathLaw (stopped (driver (r + 1) pc)
      {S | active (r + 1) i (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))) hi omega S.1}) (PMF.pure S0) R).support)
    (hnoiseM : h ∉ UniformTrackingNoise.noiseBad (k := r + 1) (ell := ell) (rs := rs) pc i 1 a (1 / 64)
      (active (r + 1) i (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))) hi omega))
    (hnoiseR : h ∉ UniformTrackingNoise.noiseBad (k := r + 1) (ell := ell) (rs := rs) pc i 0 a (1 / 64)
      (active (r + 1) i (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))) hi omega))
    (hcount : h ∉ UniformTrackingNoise.countBad i (Odds.lowerMass hi) L
      (active (r + 1) i (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))) hi omega)) :
    let H := time (active (r + 1) i (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))) hi omega) h
    Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1)) < Odds.value i (population h H.val) ∧
      (hi ≤ Odds.value i (population h H.val) ∨ ¬cap omega (population h H.val)) := by
  let lo := Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))
  let A : Population n mu → Prop := active (r + 1) i lo hi omega
  let H := time A h
  let P := population h
  let E := event h
  have hO0 : 0 < Odds.value i S0.1 := div_pos (hf0 1) (hf0 0)
  have hlo : 0 < lo := by dsimp [lo]; positivity
  have hstart : P 0 = S0.1 := by
    have hs := path_pure_start (stopped (driver (r + 1) pc) {S | A S.1}) S0 h hh
    change (extend h 0).1 = _
    rw [extend_at h 0 (Nat.zero_le R)]
    exact congrArg Prod.fst hs
  have hact (t : ℕ) (ht : t < H.val) : A (P t) := before_active A h t ht
  have hnext (t : ℕ) (ht : t < H.val) : P (t + 1) = TaggedDynamics.next (r + 1) (P t) (E t) :=
    next_of_active pc A (PMF.pure S0) h hh t (by have := H.isLt; omega) (hact t ht)
  have hp0 : ∀ u, (Sampling.zeros (P 0 u)).card = r + 1 := by rw [hstart]; exact hP0
  have hplateau := RunBoundary.plateau_until (by have := hb.hn; omega : r + 1 ≤ n) P E H.val hnext hp0
  have hmut (t : ℕ) (ht : t < H.val) : Odds.lowerMass lo ≤ fraction i 1 (P t) :=
    (active_bands i lo hi omega hlo (P t) (hact t ht)).1
  have hres (t : ℕ) (ht : t < H.val) : Odds.upperMass hi ≤ fraction i 0 (P t) :=
    (active_bands i lo hi omega hlo (P t) (hact t ht)).2.1
  have hmutpos := RunBoundary.fraction_positive_until P E H.val hnext i 1 (Odds.lowerMass lo) hb.hfmin
    (by rw [hstart]; exact hf0 1) hmut
  have hrespos := RunBoundary.fraction_positive_until P E H.val hnext i 0 (Odds.upperMass hi) hb.hamin
    (by rw [hstart]; exact hf0 0) hres
  have hfractions (t : ℕ) (ht : t ≤ H.val) (b : Fin 2) : 0 < fraction i b (P t) := by
    fin_cases b
    · exact hrespos t ht
    · exact hmutpos t ht
  let : Nonempty (Genotypes.Genotype n (r + 1)) := ⟨Genotypes.ofString (S0.1 0) (hP0 0)⟩
  obtain ⟨env, hgood, ht⟩ := DrivenTracking.track hb.hk hb.hn hb.hell pc hb.hpc i hb.ha hb.halpha hb.hcell hb.horizon
    A (PMF.pure S0) h hh H hact hplateau hfractions (Odds.lowerMass lo) (Odds.upperMass hi) (Odds.lowerMass hi) L omega
    hb.fmin_pos hb.amin_pos hb.homega hmut hres (fun t ht ↦ (hact t ht).2.2.2) hb.hbias hb.hsmall
    (hb.driftBudget H) (hb.squareBudget H) (hb.samplingBudget H) hb.listsBudget hnoiseM hnoiseR hcount
  have hH : (H.val : ℝ) ≤ R := by exact_mod_cast (Nat.le_of_lt_succ H.isLt)
  have hHscaled := mul_le_mul_of_nonneg_right hH
    (mul_nonneg hb.ha (ReproductiveAdmissibility.error_nonneg n (r + 1)))
  have hhorizon : H.val * a * ReproductiveAdmissibility.error n (r + 1) ≤ 1 := by nlinarith [hb.horizon]
  have hinit := SparseGrowth.initial_log_bound hr hb.hn H env i omega hb.homega.le hgood hb.ha hhorizon
    (by simpa only [Nat.cast_add, Nat.cast_one] using hb.shadowSmall)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hb.shadowDimension) P hp0 (hfractions 0 (Nat.zero_le H.val))
  rw [hstart] at hinit
  have hgrowth : Real.log (Odds.value i S0.1) + H.val * Real.log (SparseGrowth.base (r + 1) a omega) -
      Real.log ((3 : ℝ) ^ (r + 1)) - 1 / 4 ≤ Real.log (Odds.value i (P H.val)) := by
    change Real.log (Odds.value i (P H.val)) ≥ _ at ht
    change Real.log (Odds.value i S0.1) + _ - _ ≤ _ at hinit
    linarith
  have hOend : 0 < Odds.value i (P H.val) := div_pos (hfractions H.val le_rfl 1) (hfractions H.val le_rfl 0)
  have hnotlower : lo < Odds.value i (P H.val) := ColumnExit.prevents_lower hO0 hOend
    (by positivity) (SparseGrowth.base_one_le (by omega) hb.ha hb.homega.le) H.val hgrowth
  change lo < Odds.value i (P H.val) ∧ _
  refine ⟨hnotlower, ?_⟩
  by_cases hHR : H.val = R
  · have ht := hb.growthTime
    rw [← hHR] at ht
    have hu := ColumnExit.upper_at_horizon hO0 hOend (by positivity) hB H.val ht hgrowth
    exact Or.inl (hupper.trans hu.le)
  · have hstop : ¬ A (P H.val) := (time_spec A h).resolve_left hHR
    by_cases hc : cap omega (P H.val)
    · left
      by_contra hupper'
      exact hstop ⟨hplateau H.val le_rfl, hnotlower, lt_of_not_ge hupper', hc⟩
    · exact Or.inr hc

def outcome (k : ℕ) (i : Fin n) (lo hi omega : ℝ) (h : Fin (R + 1) → State n mu) : Prop :=
  let H := time (active k i lo hi omega) h
  lo < Odds.value i (population h H.val) ∧ (hi ≤ Odds.value i (population h H.val) ∨ ¬cap omega (population h H.val))

lemma failure_bound (hr : 1 ≤ r) (pc a omega L B hi : ℝ) (i : Fin n)
    (S0 : State n mu) (hP0 : ∀ u, (Sampling.zeros (S0.1 u)).card = r + 1)
    (hf0 : ∀ b : Fin 2, 0 < fraction i b S0.1) (hB : 0 < B)
    (hhi : Odds.value i S0.1 < hi) (hupper : hi ≤ B * Odds.value i S0.1)
    (hb : Budget n (r + 1) R ell mu rs pc a
      (Odds.lowerMass (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))))
      (Odds.upperMass hi) (Odds.lowerMass hi) omega L B) :
    (pathLaw (stopped (driver (r + 1) pc)
      {S | active (r + 1) i (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))) hi omega S.1}) (PMF.pure S0) R).toOuterMeasure
      {h | ¬outcome (r + 1) i (Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))) hi omega h} ≤
      ENNReal.ofReal ((4 * (Fintype.card (Net n (r + 1) R (count R ell) rs) : ℝ) * ((R : ℝ) + 1) + 1) * Real.exp (-L)) := by
  let lo := Odds.value i S0.1 / (4 * (3 : ℝ) ^ (r + 1))
  let A : Population n mu → Prop := active (r + 1) i lo hi omega
  have hO0 : 0 < Odds.value i S0.1 := div_pos (hf0 1) (hf0 0)
  have hlo : 0 < lo := by dsimp [lo]; positivity
  let refM := Classical.choice (RunBoundary.exists_class S0.1 hP0 i 1 (hf0 1))
  let refR := Classical.choice (RunBoundary.exists_class S0.1 hP0 i 0 (hf0 0))
  have hbands (P : Population n mu) (hP : A P) := active_bands i lo hi omega hlo P hP
  have himm (P : Population n mu) (hP : A P) : fraction i 1 P / n ≤ fraction i 0 P := by
    have hh := div_le_div_of_nonneg_right (fraction_bounds i 1 P).2 (Nat.cast_nonneg n)
    exact hh.trans (hb.himm.trans (hbands P hP).2.1)
  have hjoint := UniformTrackingNoise.joint_bound (ell := ell) (rs := rs) hb.hk hb.hn pc hb.hpc i a hb.ha hb.horizon
    refM refR (Odds.lowerMass lo) (Odds.upperMass hi) (Odds.lowerMass hi) hb.fmin_pos hb.amin_pos hb.hfmax
    A (fun P hP ↦ hP.1) (fun P hP ↦ (hbands P hP).1) (fun P hP ↦ (hbands P hP).2.1)
    (fun P hP ↦ (hbands P hP).2.2) himm (PMF.pure S0) (1 / 64) L (by norm_num) hb.hL
    hb.noiseStepM hb.noiseVarM hb.noiseStepR hb.noiseVarR
  apply le_trans _ hjoint
  apply FiniteEvents.event_mono_on_support
  intro h hh hfailure
  by_contra hnot
  have hnM : h ∉ UniformTrackingNoise.noiseBad (k := r + 1) (ell := ell) (rs := rs) pc i 1 a (1 / 64) A :=
    fun hm ↦ hnot (Or.inl (Or.inl hm))
  have hnR : h ∉ UniformTrackingNoise.noiseBad (k := r + 1) (ell := ell) (rs := rs) pc i 0 a (1 / 64) A :=
    fun hm ↦ hnot (Or.inl (Or.inr hm))
  have hnC : h ∉ UniformTrackingNoise.countBad i (Odds.lowerMass hi) L A := fun hc ↦ hnot (Or.inr hc)
  exact hfailure (pointwise_exit hr pc a omega L B hi i S0 hP0 hf0 hB hhi hupper hb h hh hnM hnR hnC)

end
end Lax343628Proofs.ColumnBlock

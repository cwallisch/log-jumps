import Lax343628Proofs.TaggedDynamics
import Lax343628Proofs.PathNoise

namespace Lax343628Proofs.DrivenNoise

open Lax343628.Algorithm Lax343628Proofs.TaggedDynamics
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.FiniteChain Lax343628Proofs.PathNoise
open Lax343628Proofs.Trajectories
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev State (n : ℕ) (mu : ℕ+) := Population n mu × Event n mu

def driver {n : ℕ} {mu : ℕ+} (k : ℕ) (pc : ℝ) (S : State n mu) : PMF (State n mu) :=
  (eventLaw pc S.1).map (fun E ↦ (next k S.1 E, E))

lemma driver_population {n k : ℕ} {mu : ℕ+} (hk : k ≤ n) (pc : ℝ) (S : State n mu)
    (hS : PlateauDynamics.plateauPopulation k S.1) :
    (driver k pc S).map Prod.fst = PlateauDynamics.auxiliaryStep k pc S.1 := by
  rw [driver, PMF.map_comp]
  exact eventLaw_next hk pc S.1 hS

variable {n : ℕ} {mu : ℕ+}

def increment (N : ℕ → Population n mu → Event n mu → ℝ)
    (active : Population n mu → Prop) [DecidablePred active] (H t : ℕ) (S T : State n mu) : ℝ :=
  if t < H ∧ active S.1 then N t S.1 T.2 else 0

lemma mean_increment (k : ℕ) (pc : ℝ) (N : ℕ → Population n mu → Event n mu → ℝ)
    (active : Population n mu → Prop) [DecidablePred active] (H t : ℕ)
    (hmean : ∀ t P, t < H → active P → mean (eventLaw pc P) (N t P) = 0) (S : State n mu) :
    mean (stopped (driver k pc) {S | active S.1} S) (increment N active H t S) = 0 := by
  by_cases hguard : t < H ∧ active S.1
  · rw [stopped]
    simp only [Set.mem_ofPred_eq, if_pos hguard.2]
    rw [driver, mean_map]
    simp only [increment, if_pos hguard]
    exact hmean t S.1 hguard.1 hguard.2
  · change mean _ (fun T : State n mu ↦ if t < H ∧ active S.1 then N t S.1 T.2 else 0) = 0
    simp only [if_neg hguard, mean_const]

lemma variance_increment (k : ℕ) (pc : ℝ) (N : ℕ → Population n mu → Event n mu → ℝ)
    (active : Population n mu → Prop) [DecidablePred active] (H t : ℕ) (v : ℝ) (hv : 0 ≤ v)
    (hvar : ∀ t P, t < H → active P → mean (eventLaw pc P) (fun E ↦ N t P E ^ 2) ≤ v) (S : State n mu) :
    mean (stopped (driver k pc) {S | active S.1} S) (fun T ↦ increment N active H t S T ^ 2) ≤ v := by
  by_cases hguard : t < H ∧ active S.1
  · rw [stopped]
    simp only [Set.mem_ofPred_eq, if_pos hguard.2]
    rw [driver, mean_map]
    simp only [increment, if_pos hguard]
    exact hvar t S.1 hguard.1 hguard.2
  · simpa only [increment, if_neg hguard, zero_pow (by decide : (2 : ℕ) ≠ 0), mean_const] using hv

lemma small_increment (N : ℕ → Population n mu → Event n mu → ℝ)
    (active : Population n mu → Prop) [DecidablePred active] (H : ℕ) (lam c : ℝ)
    (hlam : 0 ≤ lam) (hsmall : lam * c ≤ 1)
    (hbound : ∀ t P E, t < H → active P → |N t P E| ≤ c) (t : ℕ) (S T : State n mu) :
    |lam * increment N active H t S T| ≤ 1 := by
  by_cases hguard : t < H ∧ active S.1
  · simp only [increment, if_pos hguard, abs_mul, abs_of_nonneg hlam]
    exact (mul_le_mul_of_nonneg_left (hbound t S.1 T.2 hguard.1 hguard.2) hlam).trans hsmall
  · simp only [increment, if_neg hguard, mul_zero, abs_zero]
    norm_num

lemma prefix_noise_bound (k : ℕ) (pc : ℝ) (p : PMF (State n mu))
    (N : ℕ → Population n mu → Event n mu → ℝ) (active : Population n mu → Prop) [DecidablePred active]
    (H : ℕ) (lam c v bound : ℝ) (hlam : 0 ≤ lam) (hv : 0 ≤ v) (hsmall : lam * c ≤ 1)
    (hmean : ∀ t P, t < H → active P → mean (eventLaw pc P) (N t P) = 0)
    (hbound : ∀ t P E, t < H → active P → |N t P E| ≤ c)
    (hvar : ∀ t P, t < H → active P → mean (eventLaw pc P) (fun E ↦ N t P E ^ 2) ≤ v) :
    (pathLaw (stopped (driver k pc) {S | active S.1}) p H).toOuterMeasure {h | ∃ T : Fin (H + 1),
      bound ≤ |accumulate (increment N active H) T.val (before H T.val (by have := T.isLt; omega) h)|} ≤
      ENNReal.ofReal (((H : ℝ) + 1) * (2 * Real.exp (-lam * bound + H * lam ^ 2 * v))) := by
  apply prefix_tail _ _ _ lam v hlam hv
  · intro t S T _
    exact small_increment N active H lam c hlam hsmall hbound t S T
  · intro t S
    exact mean_increment k pc N active H t hmean S
  · intro t S
    exact variance_increment k pc N active H t v hv hvar S

lemma family_noise_bound {sigma : Type*} [Fintype sigma]
    (k : ℕ) (pc : ℝ) (p : PMF (State n mu))
    (N : sigma → ℕ → Population n mu → Event n mu → ℝ)
    (active : Population n mu → Prop) [DecidablePred active]
    (H : ℕ) (lam c v bound : ℝ) (hlam : 0 ≤ lam) (hv : 0 ≤ v) (hsmall : lam * c ≤ 1)
    (hmean : ∀ z t P, t < H → active P → mean (eventLaw pc P) (N z t P) = 0)
    (hbound : ∀ z t P E, t < H → active P → |N z t P E| ≤ c)
    (hvar : ∀ z t P, t < H → active P → mean (eventLaw pc P) (fun E ↦ N z t P E ^ 2) ≤ v) :
    (pathLaw (stopped (driver k pc) {S | active S.1}) p H).toOuterMeasure
      {h | ∃ z : sigma, ∃ T : Fin (H + 1), bound ≤
        |accumulate (increment (N z) active H) T.val (before H T.val (by have := T.isLt; omega) h)|} ≤
      ENNReal.ofReal ((Fintype.card sigma : ℝ) * ((H : ℝ) + 1) *
        (2 * Real.exp (-lam * bound + H * lam ^ 2 * v))) := by
  let events : sigma → Set (Fin (H + 1) → State n mu) := fun z ↦
    {h | ∃ T : Fin (H + 1), bound ≤
      |accumulate (increment (N z) active H) T.val (before H T.val (by have := T.isLt; omega) h)|}
  have ht := FiniteEvents.finite_union_bound
    (pathLaw (stopped (driver k pc) {S | active S.1}) p H) (Finset.univ : Finset sigma) events
    (((H : ℝ) + 1) * (2 * Real.exp (-lam * bound + H * lam ^ 2 * v))) (by positivity)
    (fun z _ ↦ prefix_noise_bound k pc p (N z) active H lam c v bound hlam hv hsmall
      (hmean z) (hbound z) (hvar z))
  simpa only [events, Set.mem_ofPred_eq, Finset.mem_univ, true_and, Finset.card_univ, mul_assoc] using ht

lemma budget_noise_bound {sigma : Type*} [Fintype sigma]
    (k : ℕ) (pc : ℝ) (p : PMF (State n mu))
    (N : sigma → ℕ → Population n mu → Event n mu → ℝ)
    (active : Population n mu → Prop) [DecidablePred active]
    (H : ℕ) (c v bound L : ℝ) (hv : 0 ≤ v) (hboundpos : 0 < bound) (hL : 0 < L)
    (hsmall : 2 * c * L ≤ bound) (hvariance : 4 * H * v * L ≤ bound ^ 2)
    (hmean : ∀ z t P, t < H → active P → mean (eventLaw pc P) (N z t P) = 0)
    (hbound : ∀ z t P E, t < H → active P → |N z t P E| ≤ c)
    (hvar : ∀ z t P, t < H → active P → mean (eventLaw pc P) (fun E ↦ N z t P E ^ 2) ≤ v) :
    (pathLaw (stopped (driver k pc) {S | active S.1}) p H).toOuterMeasure
      {h | ∃ z : sigma, ∃ T : Fin (H + 1), bound ≤
        |accumulate (increment (N z) active H) T.val (before H T.val (by have := T.isLt; omega) h)|} ≤
      ENNReal.ofReal (2 * (Fintype.card sigma : ℝ) * ((H : ℝ) + 1) * Real.exp (-L)) := by
  have hlam : 0 ≤ 2 * L / bound := by positivity
  have hsmall' : (2 * L / bound) * c ≤ 1 := by
    have hh : (2 * c * L) / bound ≤ 1 := (div_le_one hboundpos).mpr hsmall
    convert hh using 1; first | rfl | ring
  have ht := family_noise_bound k pc p N active H (2 * L / bound) c v bound hlam hv hsmall' hmean hbound hvar
  have hquad : 4 * H * v * L ^ 2 / bound ^ 2 ≤ L := by
    apply (div_le_iff₀ (sq_pos_of_pos hboundpos)).mpr
    have hh := mul_le_mul_of_nonneg_left hvariance hL.le
    nlinarith
  have heq : -(2 * L / bound) * bound + (H : ℝ) * (2 * L / bound) ^ 2 * v =
      -2 * L + 4 * H * v * L ^ 2 / bound ^ 2 := by field_simp; ring
  apply ht.trans
  apply ENNReal.ofReal_le_ofReal
  rw [heq]
  have hexp := Real.exp_le_exp.mpr (show -2 * L + 4 * H * v * L ^ 2 / bound ^ 2 ≤ -L by linarith)
  have hscale := mul_le_mul_of_nonneg_left hexp
    (show 0 ≤ 2 * (Fintype.card sigma : ℝ) * ((H : ℝ) + 1) by positivity)
  nlinarith

end
end Lax343628Proofs.DrivenNoise

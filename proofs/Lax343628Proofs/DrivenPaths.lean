import Lax343628Proofs.UniformTrackingNoise

namespace Lax343628Proofs.DrivenPaths

open Lax343628.Algorithm Lax343628Proofs.TaggedDynamics Lax343628Proofs.DrivenNoise
open Lax343628Proofs.Trajectories Lax343628Proofs.PathNoise Lax343628Proofs.FiniteDrift
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} {n k R : ℕ} {mu : ℕ+}

def extend (h : Fin (R + 1) → α) (t : ℕ) : α := h ⟨min t R, by omega⟩

lemma extend_at (h : Fin (R + 1) → α) (t : ℕ) (ht : t ≤ R) :
    extend h t = h ⟨t, by omega⟩ := by
  unfold extend
  simp only [Nat.min_eq_left ht]

lemma before_eq (h : Fin (R + 1) → α) (T : ℕ) (hT : T ≤ R) :
    before R T hT h = fun j ↦ extend h j.val := by
  funext j
  rw [extend_at h j.val (by have := j.isLt; omega)]
  rfl

lemma accumulate_sum (d : ℕ → α → α → ℝ) (S : ℕ → α) (T : ℕ) :
    accumulate d T (fun j ↦ S j.val) = ∑ t ∈ Finset.range T, d t (S t) (S (t + 1)) := by
  induction T with
  | zero => simp only [accumulate, Finset.sum_range_zero]
  | succ T ih =>
    change accumulate d T (fun j ↦ S j.val) + d T (S T) (S (T + 1)) = _
    rw [ih, Finset.sum_range_succ]

lemma before_accumulate (d : ℕ → α → α → ℝ) (h : Fin (R + 1) → α) (T : ℕ) (hT : T ≤ R) :
    accumulate d T (before R T hT h) = ∑ t ∈ Finset.range T, d t (extend h t) (extend h (t + 1)) := by
  rw [before_eq, accumulate_sum]

lemma extend_step_support (K : α → PMF α) (p : PMF α) (h : Fin (R + 1) → α)
    (hh : h ∈ (pathLaw K p R).support) (t : ℕ) (ht : t < R) :
    extend h (t + 1) ∈ (K (extend h t)).support := by
  rw [extend_at h (t + 1) (by omega), extend_at h t ht.le]
  exact path_step_support K p h hh ⟨t, ht⟩

abbrev population (h : Fin (R + 1) → State n mu) (t : ℕ) : Population n mu := (extend h t).1

abbrev event (h : Fin (R + 1) → State n mu) (t : ℕ) : Event n mu := (extend h (t + 1)).2

lemma next_of_active (pc : ℝ) (active : Population n mu → Prop) [DecidablePred active]
    (p : PMF (State n mu)) (h : Fin (R + 1) → State n mu)
    (hh : h ∈ (pathLaw (stopped (driver k pc) {S | active S.1}) p R).support)
    (t : ℕ) (ht : t < R) (hactive : active (population h t)) :
    population h (t + 1) = next k (population h t) (event h t) := by
  have hs := extend_step_support (stopped (driver k pc) {S | active S.1}) p h hh t ht
  rw [stopped] at hs
  simp only [Set.mem_ofPred_eq, if_pos hactive] at hs
  obtain ⟨E, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
  have hp := congrArg Prod.fst heq
  have he := congrArg Prod.snd heq
  change next k (population h t) E = population h (t + 1) at hp
  change E = event h t at he
  rw [he] at hp
  exact hp.symm

lemma noise_sum {ell : ℕ} {rs : ℕ+} (sigma : SparseEnvironment.Net n k R (SparseGroups.count R ell) rs)
    (pc : ℝ) (i : Fin n) (b : Fin 2) (a : ℝ) (active : Population n mu → Prop) [DecidablePred active]
    (h : Fin (R + 1) → State n mu) (T : Fin (R + 1))
    (hactive : ∀ t, t < T.val → active (population h t)) :
    accumulate (increment (SparseNoise.noise sigma pc i b a) active R) T.val
      (before R T.val (by have := T.isLt; omega) h) =
        ∑ t ∈ Finset.range T.val, SparseNoise.noise sigma pc i b a t (population h t) (event h t) := by
  rw [before_accumulate]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  exact if_pos ⟨by have := T.isLt; omega, hactive t ht'⟩

lemma full_accumulate (d : ℕ → α → α → ℝ) (h : Fin (R + 1) → α) :
    accumulate d R h = ∑ t ∈ Finset.range R, d t (extend h t) (extend h (t + 1)) := by
  have heq : before R R le_rfl h = h := rfl
  simpa only [heq] using before_accumulate d h R le_rfl

lemma noise_bound {ell : ℕ} {rs : ℕ+} (sigma : SparseEnvironment.Net n k R (SparseGroups.count R ell) rs)
    (pc : ℝ) (i : Fin n) (b : Fin 2) (a bound : ℝ) (active : Population n mu → Prop) [DecidablePred active]
    (h : Fin (R + 1) → State n mu)
    (hn : h ∉ UniformTrackingNoise.noiseBad (k := k) (ell := ell) (rs := rs) pc i b a bound active)
    (hactive : ∀ t, t < sigma.1.val → active (population h t)) :
    |∑ t ∈ Finset.range sigma.1.val, SparseNoise.noise sigma pc i b a t (population h t) (event h t)| ≤ bound := by
  have hh : ¬ bound ≤ |accumulate (increment (SparseNoise.noise sigma pc i b a) active R) sigma.1.val
      (before R sigma.1.val (by have := sigma.1.isLt; omega) h)| := fun hh ↦ hn ⟨sigma, sigma.1, hh⟩
  rw [noise_sum sigma pc i b a active h sigma.1 hactive] at hh
  exact (lt_of_not_ge hh).le

lemma count_le_full (i : Fin n) (active : Population n mu → Prop) [DecidablePred active]
    (h : Fin (R + 1) → State n mu) (H : Fin (R + 1))
    (hactive : ∀ t, t < H.val → active (population h t)) :
    (∑ t ∈ Finset.range H.val, if ClassChannels.channel i 1 (population h t) (event h t) then 1 else 0) ≤
      accumulate (ChannelCounts.tick i 1 active R) R h := by
  rw [full_accumulate]
  have heq : (∑ t ∈ Finset.range H.val, if ClassChannels.channel i 1 (population h t) (event h t) then (1 : ℝ) else 0) =
      ∑ t ∈ Finset.range H.val, ChannelCounts.tick i 1 active R t (extend h t) (extend h (t + 1)) := by
    apply Finset.sum_congr rfl
    intro t ht
    have htime := Finset.mem_range.mp ht
    exact (if_pos ⟨by have := H.isLt; omega, hactive t htime⟩).symm
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by have := H.isLt; omega))
    (fun t _ _ ↦ (ChannelCounts.tick_bounds i 1 active R t (extend h t) (extend h (t + 1))).1)

lemma count_bound (i : Fin n) (fmax L : ℝ) (active : Population n mu → Prop) [DecidablePred active]
    (h : Fin (R + 1) → State n mu) (H : Fin (R + 1))
    (hn : h ∉ UniformTrackingNoise.countBad i fmax L active)
    (hactive : ∀ t, t < H.val → active (population h t)) :
    (∑ t ∈ Finset.range H.val, if ClassChannels.channel i 1 (population h t) (event h t) then 1 else 0) ≤
      6 * R * fmax + 2 * L := by
  have hc : accumulate (ChannelCounts.tick i 1 active R) R h < 6 * R * fmax + 2 * L := lt_of_not_ge hn
  exact (count_le_full i active h H hactive).trans hc.le

end
end Lax343628Proofs.DrivenPaths

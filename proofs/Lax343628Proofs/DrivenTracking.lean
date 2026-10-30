import Lax343628Proofs.DrivenPaths
import Lax343628Proofs.RunTracking
import Lax343628Proofs.RunSampling

namespace Lax343628Proofs.DrivenTracking

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open Lax343628Proofs.DrivenNoise Lax343628Proofs.DrivenPaths
open Lax343628Proofs.Trajectories Lax343628Proofs.FiniteDrift
open Lax343628Proofs.ClassChannels Lax343628Proofs.RunLogOdds
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu rs : ℕ+}

lemma track [Nonempty (Genotypes.Genotype n k)]
    (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hell : 1 ≤ ell) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (i : Fin n) {a : ℝ} (ha : 0 ≤ a) (halpha : a = pc / ((mu : ℕ) + 1 : ℝ))
    (hcell : (ell : ℝ) * a ≤ 1) (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (active : Population n mu → Prop) [DecidablePred active] (p : PMF (State n mu))
    (h : Fin (R + 1) → State n mu)
    (hh : h ∈ (pathLaw (stopped (driver k pc) {S | active S.1}) p R).support)
    (H : Fin (R + 1)) (hactive : ∀ t, t < H.val → active (population h t))
    (hP : ∀ t, t ≤ H.val → ∀ u, (Sampling.zeros (population h t u)).card = k)
    (hf : ∀ t, t ≤ H.val → ∀ b : Fin 2, 0 < fraction i b (population h t))
    (fmin amin fmax L omega : ℝ) (hfmin : 0 < fmin) (hamin : 0 < amin) (homega : 0 < omega)
    (hmut : ∀ t, t < H.val → fmin ≤ fraction i 1 (population h t))
    (hres : ∀ t, t < H.val → amin ≤ fraction i 0 (population h t))
    (hcap : ∀ t, t < H.val → ∀ z : BitString n, EmpiricalKernels.frequency (population h t) z ≤ 1 - omega)
    (hbias : (3 : ℝ) ^ k * ((k : ℝ) + 1) / n ≤ 1)
    (hsmall : 2 / ((mu : ℕ) + 1 : ℝ) + a * (3 : ℝ) ^ k +
      ((3 : ℝ) ^ k / ((mu : ℕ) * fmin) + 3 * (3 : ℝ) ^ k / (mu : ℕ)) ≤ 1 / 2)
    (hdb : H.val * ((a * (3 : ℝ) ^ k + (3 : ℝ) ^ k * (((k : ℝ) + 1) + 1 / amin) / n) /
      ((mu : ℕ) + 1 : ℝ)) ≤ 1 / 32)
    (hqb : 3 * (H.val * (2 / ((mu : ℕ) + 1 : ℝ)) ^ 2 + H.val * (a * (3 : ℝ) ^ k) ^ 2 +
      2 * ((3 : ℝ) ^ k / ((mu : ℕ) * fmin)) ^ 2 * (6 * R * fmax + 2 * L) +
        18 * H.val * ((3 : ℝ) ^ k / (mu : ℕ)) ^ 2) ≤ 1 / 64)
    (hsampling : 2 * (a * H.val * MismatchTotals.cost (mu : ℕ) ell a ((3 : ℝ) ^ k) +
      (a * H.val * (3 : ℝ) ^ k) / (2 * Real.sqrt (rs : ℕ))) ≤ 1 / 32)
    (hlists : (count R ell : ℝ) * (4 / ((rs : ℕ) * omega ^ 2)) ≤ 1 / 8)
    (hnoiseM : h ∉ UniformTrackingNoise.noiseBad (k := k) (ell := ell) (rs := rs) pc i 1 a (1 / 64) active)
    (hnoiseR : h ∉ UniformTrackingNoise.noiseBad (k := k) (ell := ell) (rs := rs) pc i 0 a (1 / 64) active)
    (hcount : h ∉ UniformTrackingNoise.countBad i fmax L active) :
    ∃ env : Lists n k (count R ell) rs,
      (∀ j : Fin (count R ell), (group H.val ell j.val).Nonempty →
        ∀ u, EmpiricalCap.frequency (env j) u < 1 - omega / 2) ∧
      Real.log (fraction i 1 (population h H.val) / fraction i 0 (population h H.val)) ≥
        Real.log (weighted (H, env) (population h) i 1 a 0 / weighted (H, env) (population h) i 0 a 0) - 1 / 4 := by
  have hnext (t : ℕ) (ht : t < H.val) : population h (t + 1) =
      TaggedDynamics.next k (population h t) (event h t) :=
    next_of_active pc active p h hh t (by have := H.isLt; omega) (hactive t ht)
  obtain ⟨env, hg, hm⟩ := RunSampling.exists_environment hk hn hell H i ha hcell horizon (population h) (event h)
    hnext (fun t ht ↦ hP t ht.le) (fun t ht ↦ hf t ht.le) omega homega hcap hsampling hlists
  refine ⟨env, hg, ?_⟩
  exact RunTracking.track hk hn pc hpc H env i ha halpha horizon (population h) (event h) hnext hP hf
    fmin amin (6 * R * fmax + 2 * L) hfmin hamin hmut hres hbias hsmall hdb
    (count_bound i fmax L active h H hcount hactive) hqb hm
    (noise_bound (H, env) pc i 1 a (1 / 64) active h hnoiseM hactive)
    (noise_bound (H, env) pc i 0 a (1 / 64) active h hnoiseR hactive)

end
end Lax343628Proofs.DrivenTracking

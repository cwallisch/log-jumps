import Lax343628Proofs.PartnerCaps
import Lax343628Proofs.SparseSelection

namespace Lax343628Proofs.RunSampling

open Lax343628.Algorithm Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open Lax343628Proofs.MismatchTotals Lax343628Proofs.SparseSelection Lax343628Proofs.RunPartnerLaws
open Lax343628Proofs.ClassChannels
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu rs : ℕ+}

lemma exists_environment [Nonempty (Genotypes.Genotype n k)]
    (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hell : 1 ≤ ell)
    (H : Fin (R + 1)) (i : Fin n) {a : ℝ} (ha : 0 ≤ a) (hcell : (ell : ℝ) * a ≤ 1)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : ℕ → Population n mu) (E : ℕ → TaggedDynamics.Event n mu)
    (hnext : ∀ t, t < H.val → P (t + 1) = TaggedDynamics.next k (P t) (E t))
    (hP : ∀ t, t < H.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ t, t < H.val → ∀ b : Fin 2, 0 < fraction i b (P t))
    (omega : ℝ) (homega : 0 < omega)
    (hcap : ∀ t, t < H.val → ∀ z : BitString n, EmpiricalKernels.frequency (P t) z ≤ 1 - omega)
    (hsampling : 2 * (a * H.val * cost (mu : ℕ) ell a ((3 : ℝ) ^ k) +
      (a * H.val * (3 : ℝ) ^ k) / (2 * Real.sqrt (rs : ℕ))) ≤ 1 / 32)
    (hlists : (count R ell : ℝ) * (4 / ((rs : ℕ) * omega ^ 2)) ≤ 1 / 8) :
    ∃ env : Lists n k (count R ell) rs,
      (∀ j : Fin (count R ell), (group H.val ell j.val).Nonempty →
        ∀ u, EmpiricalCap.frequency (env j) u < 1 - omega / 2) ∧
      total H env P i 1 a + total H env P i 0 a ≤ 1 / 8 := by
  let p := FiniteProduct.distribution (fun j : Fin (count R ell) ↦ EmpiricalSampling.samples (laws H P hP j) (rs : ℕ))
  let V := fun env : Lists n k (count R ell) rs ↦ total H env P i 1 a + total H env P i 0 a
  let good := fun env : Lists n k (count R ell) rs ↦ ∀ j : Fin (count R ell), (group H.val ell j.val).Nonempty →
    ∀ u, EmpiricalCap.frequency (env j) u < 1 - omega / 2
  have hmean : FiniteDrift.mean p V ≤ 1 / 32 :=
    (expected_joint hk hn hell H i ha hcell horizon P E hnext hP hf).trans hsampling
  have hgood : FiniteDrift.mean p (fun env ↦ if good env then 0 else 1) ≤ 1 / 8 :=
    (PartnerCaps.bad_lists_mean H P hP omega homega hcap).trans hlists
  have hgood' : FiniteDrift.mean p (fun env ↦ @ite ℝ (good env) (Classical.propDecidable _) 0 1) ≤ 1 / 8 := by
    convert hgood using 1
    congr 1
    funext env
    split_ifs <;> rfl
  obtain ⟨env, _, hg, hv⟩ := exists_small_good p V
    (fun env ↦ add_nonneg (total_nonneg H env P i 1 a) (total_nonneg H env P i 0 a)) good hmean hgood'
  exact ⟨env, hg, hv⟩

end
end Lax343628Proofs.RunSampling

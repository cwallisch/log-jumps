import Lax343628Proofs.MismatchTotals

namespace Lax343628Proofs.SparseSelection

open Lax343628.Algorithm Lax343628Proofs.MismatchTotals
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open Lax343628Proofs.RunPartnerLaws Lax343628Proofs.FiniteDrift
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {rs mu : ℕ+}

lemma expected_joint [Nonempty (Genotypes.Genotype n k)]
    (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hell : 1 ≤ ell)
    (H : Fin (R + 1)) (i : Fin n) {a : ℝ} (ha : 0 ≤ a) (hcell : (ell : ℝ) * a ≤ 1)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : ℕ → Population n mu) (E : ℕ → TaggedDynamics.Event n mu)
    (hnext : ∀ t, t < H.val → P (t + 1) = TaggedDynamics.next k (P t) (E t))
    (hP : ∀ t, t < H.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ t, t < H.val → ∀ b : Fin 2, 0 < ClassChannels.fraction i b (P t)) :
    mean (FiniteProduct.distribution (fun j : Fin (count R ell) ↦
      EmpiricalSampling.samples (laws H P hP j) (rs : ℕ)))
      (fun env ↦ total H env P i 1 a + total H env P i 0 a) ≤
        2 * (a * H.val * cost (mu : ℕ) ell a ((3 : ℝ) ^ k) +
          (a * H.val * (3 : ℝ) ^ k) / (2 * Real.sqrt (rs : ℕ))) := by
  rw [mean_add]
  have h1 := expected_total (rs := rs) hk hn hell H i 1 ha hcell horizon P E hnext hP (fun t ht ↦ hf t ht 1)
  have h0 := expected_total (rs := rs) hk hn hell H i 0 ha hcell horizon P E hnext hP (fun t ht ↦ hf t ht 0)
  linarith

lemma exists_small_good {α : Type*} [Fintype α] (p : PMF α) (V : α → ℝ)
    (hV : ∀ x, 0 ≤ V x) (good : α → Prop)
    (hmean : mean p V ≤ 1 / 32)
    (hgood : mean p (fun x ↦ if good x then 0 else 1) ≤ 1 / 8) :
    ∃ x ∈ p.support, good x ∧ V x ≤ 1 / 8 := by
  by_contra h
  have hp (x : α) (hx : x ∈ p.support) : (1 : ℝ) ≤ 8 * V x + (if good x then 0 else 1) := by
    by_cases hg : good x
    · have hv : ¬ V x ≤ 1 / 8 := fun hv ↦ h ⟨x, hx, hg, hv⟩
      simp only [if_pos hg, add_zero]
      linarith
    · simp only [if_neg hg]
      linarith [hV x]
  have hh := mean_mono_on_support p hp
  rw [mean_const, mean_add, mean_mul] at hh
  linarith

lemma total_nonneg (H : Fin (R + 1)) (env : Lists n k (count R ell) rs)
    (P : ℕ → Population n mu) (i : Fin n) (b : Fin 2) (a : ℝ) : 0 ≤ total H env P i b a :=
  Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

end
end Lax343628Proofs.SparseSelection

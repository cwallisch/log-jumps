import Lax343628Proofs.RunLogOdds

namespace Lax343628Proofs.TrackingSums

open Lax343628.Algorithm Lax343628Proofs.SparseEnvironment
open Lax343628Proofs.SparseGroups Lax343628Proofs.MismatchTotals
open Lax343628Proofs.RunLogOdds Lax343628Proofs.SparseDynamics
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu rs : ℕ+}

lemma group_sum (H : Fin (R + 1)) (f : ℕ → ℝ) :
    (∑ j : Fin (count R ell), ∑ t ∈ group H.val ell j.val, f t) = ∑ t ∈ Finset.range H.val, f t := by
  simp only [group, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have heq : (fun j : Fin (count R ell) ↦ if (H.val - 1 - t) / ell = j.val then f t else 0) =
      (fun j ↦ if j = index R H.val ell t (by have := H.isLt; omega) then f t else 0) := by
    funext j
    have hi : (H.val - 1 - t) / ell = j.val ↔ j = index R H.val ell t (by have := H.isLt; omega) := by
      constructor
      · intro h; exact Fin.ext h.symm
      · rintro rfl; rfl
    simp only [hi]
  rw [heq]
  simp

lemma total_controls (H : Fin (R + 1)) (env : Lists n k (count R ell) rs)
    (P : ℕ → Population n mu) (i : Fin n) (b : Fin 2) (a : ℝ) :
    |∑ t ∈ Finset.range H.val, mismatch (H, env) P i b a t| ≤ total H env P i b a := by
  rw [← group_sum (ell := ell) H]
  exact Finset.abs_sum_le_sum_abs _ _

lemma budget (hkn : k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (H : Fin (R + 1)) (env : Lists n k (count R ell) rs) (i : Fin n) (a : ℝ) (ha : 0 ≤ a)
    (halpha : a = pc / ((mu : ℕ) + 1 : ℝ))
    (P : ℕ → Population n mu) (E : ℕ → TaggedDynamics.Event n mu)
    (hnext : ∀ t, t < H.val → P (t + 1) = TaggedDynamics.next k (P t) (E t))
    (hP : ∀ t, t ≤ H.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ t, t ≤ H.val → ∀ b : Fin 2, 0 < ClassChannels.fraction i b (P t))
    (hx : ∀ t, t < H.val → |step (H, env) pc P E i 1 a t| ≤ 1 / 2)
    (Bd Bm Bn Bq : ℝ)
    (hd : -Bd ≤ ∑ t ∈ Finset.range H.val, (drift (H, env) pc i 1 a t (P t) - drift (H, env) pc i 0 a t (P t)))
    (hm : total H env P i 1 a + total H env P i 0 a ≤ Bm)
    (hn1 : |∑ t ∈ Finset.range H.val, SparseNoise.noise (H, env) pc i 1 a t (P t) (E t)| ≤ Bn)
    (hn0 : |∑ t ∈ Finset.range H.val, SparseNoise.noise (H, env) pc i 0 a t (P t) (E t)| ≤ Bn)
    (hq : (∑ t ∈ Finset.range H.val, step (H, env) pc P E i 1 a t ^ 2) ≤ Bq) :
    Real.log (ClassChannels.fraction i 1 (P H.val) / ClassChannels.fraction i 0 (P H.val)) ≥
      Real.log (weighted (H, env) P i 1 a 0 / weighted (H, env) P i 0 a 0) -
        (Bd + Bm + 2 * Bn + 2 * Bq) := by
  have ht := RunLogOdds.telescope hkn pc hpc (H, env) i a ha halpha P E hnext hP hf hx
  have hm1 := (abs_le.mp (total_controls H env P i 1 a)).1
  have hm0 := (abs_le.mp (total_controls H env P i 0 a)).2
  have hn1' := (abs_le.mp hn1).1
  have hn0' := (abs_le.mp hn0).2
  have heq : (∑ t ∈ Finset.range H.val,
      (step (H, env) pc P E i 1 a t - step (H, env) pc P E i 0 a t - 2 * step (H, env) pc P E i 1 a t ^ 2)) =
      (∑ t ∈ Finset.range H.val, (drift (H, env) pc i 1 a t (P t) - drift (H, env) pc i 0 a t (P t))) +
      (∑ t ∈ Finset.range H.val, mismatch (H, env) P i 1 a t) -
      (∑ t ∈ Finset.range H.val, mismatch (H, env) P i 0 a t) +
      (∑ t ∈ Finset.range H.val, SparseNoise.noise (H, env) pc i 1 a t (P t) (E t)) -
      (∑ t ∈ Finset.range H.val, SparseNoise.noise (H, env) pc i 0 a t (P t) (E t)) -
      2 * ∑ t ∈ Finset.range H.val, step (H, env) pc P E i 1 a t ^ 2 := by
    simp only [RunLogOdds.step, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  rw [heq] at ht
  linarith

end
end Lax343628Proofs.TrackingSums

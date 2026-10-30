import Lax343628Proofs.SparseDynamics
import Lax343628Proofs.LogOdds

namespace Lax343628Proofs.RunLogOdds

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.SparseDynamics Lax343628Proofs.SparseEnvironment
open Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields
open Lax343628Proofs.ClassChannels Lax343628Proofs.TaggedDynamics
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu rs : ℕ+}

def weighted (sigma : Net n k R (count R ell) rs) (P : ℕ → Population n mu)
    (i : Fin n) (b : Fin 2) (a : ℝ) (t : ℕ) : ℝ := average (P t) (liftClass (field sigma i b a t))

def step (sigma : Net n k R (count R ell) rs) (pc : ℝ) (P : ℕ → Population n mu)
    (E : ℕ → Event n mu) (i : Fin n) (b : Fin 2) (a : ℝ) (t : ℕ) : ℝ :=
  drift sigma pc i b a t (P t) + MismatchTotals.mismatch sigma P i b a t +
    SparseNoise.noise sigma pc i b a t (P t) (E t)

lemma weighted_pos (sigma : Net n k R (count R ell) rs) (P : ℕ → Population n mu)
    (i : Fin n) (b : Fin 2) {a : ℝ} (ha : 0 ≤ a) (t : ℕ)
    (hP : ∀ u, (Sampling.zeros (P t u)).card = k) (hf : 0 < fraction i b (P t)) :
    0 < weighted sigma P i b a t :=
  hf.trans_le (GroupSampling.average_one_lower (P t) hP _ (field_one sigma i b ha t))

lemma weighted_terminal (sigma : Net n k R (count R ell) rs) (P : ℕ → Population n mu)
    (i : Fin n) (b : Fin 2) (a : ℝ)
    (hP : ∀ u, (Sampling.zeros (P sigma.1.val u)).card = k) :
    weighted sigma P i b a sigma.1.val = fraction i b (P sigma.1.val) := by
  have hf (x : ColumnClass n k i b) : field sigma i b a sigma.1.val x = 1 := by
    simp only [field, Nat.sub_self, ReproductiveValues.value]
  have hh := average_bounds (P sigma.1.val) hP (field sigma i b a sigma.1.val) 1 1
    (fun x ↦ by rw [hf x]; exact ⟨le_rfl, le_rfl⟩)
  change average _ _ = _
  simpa only [mul_one] using le_antisymm hh.2 hh.1

lemma telescope (hkn : k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (sigma : Net n k R (count R ell) rs) (i : Fin n) (a : ℝ) (ha : 0 ≤ a)
    (halpha : a = pc / ((mu : ℕ) + 1 : ℝ))
    (P : ℕ → Population n mu) (E : ℕ → Event n mu)
    (hnext : ∀ t, t < sigma.1.val → P (t + 1) = next k (P t) (E t))
    (hP : ∀ t, t ≤ sigma.1.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ t, t ≤ sigma.1.val → ∀ b : Fin 2, 0 < fraction i b (P t))
    (hx : ∀ t, t < sigma.1.val → |step sigma pc P E i 1 a t| ≤ 1 / 2) :
    Real.log (fraction i 1 (P sigma.1.val) / fraction i 0 (P sigma.1.val)) -
      Real.log (weighted sigma P i 1 a 0 / weighted sigma P i 0 a 0) ≥
        ∑ t ∈ Finset.range sigma.1.val,
          (step sigma pc P E i 1 a t - step sigma pc P E i 0 a t - 2 * step sigma pc P E i 1 a t ^ 2) := by
  have hpos (b : Fin 2) (t : ℕ) (ht : t ≤ sigma.1.val) : 0 < weighted sigma P i b a t :=
    weighted_pos sigma P i b ha t (hP t ht) (hf t ht b)
  have hid (b : Fin 2) (t : ℕ) (ht : t < sigma.1.val) :
      (weighted sigma P i b a (t + 1) - weighted sigma P i b a t) / weighted sigma P i b a t =
        step sigma pc P E i b a t + imm sigma i b a t (P t) (E t) := by
    unfold weighted step MismatchTotals.mismatch
    rw [hnext t ht]
    exact normalized_step hkn pc hpc sigma i b a halpha t ht (P t) (hP t ht.le) (E t)
  have hl (t : ℕ) (ht : t < sigma.1.val) :
      weighted sigma P i 1 a t * (1 + step sigma pc P E i 1 a t) ≤ weighted sigma P i 1 a (t + 1) := by
    have hh : step sigma pc P E i 1 a t ≤
        (weighted sigma P i 1 a (t + 1) - weighted sigma P i 1 a t) / weighted sigma P i 1 a t := by
      rw [hid 1 t ht]
      linarith [imm_mutant_nonneg sigma i ha t (P t) (E t) hkn]
    have hh' := (le_div_iff₀ (hpos 1 t ht.le)).mp hh
    nlinarith
  have hu (t : ℕ) (ht : t < sigma.1.val) :
      weighted sigma P i 0 a (t + 1) ≤ weighted sigma P i 0 a t * (1 + step sigma pc P E i 0 a t) := by
    have hh : (weighted sigma P i 0 a (t + 1) - weighted sigma P i 0 a t) / weighted sigma P i 0 a t ≤
        step sigma pc P E i 0 a t := by
      rw [hid 0 t ht]
      linarith [imm_resident_nonpos sigma i ha t (P t) (E t)]
    have hh' := (div_le_iff₀ (hpos 0 t ht.le)).mp hh
    nlinarith
  have hs := LogOdds.telescope sigma.1.val (weighted sigma P i 1 a) (weighted sigma P i 0 a)
    (step sigma pc P E i 1 a) (step sigma pc P E i 0 a) (hpos 1) (hpos 0) hx hl hu
  rw [weighted_terminal sigma P i 1 a (hP _ le_rfl), weighted_terminal sigma P i 0 a (hP _ le_rfl)] at hs
  exact hs

end
end Lax343628Proofs.RunLogOdds

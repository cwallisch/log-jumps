import Lax343628Proofs.NoiseNormalization
import Lax343628Proofs.ColumnFieldBounds
import Lax343628Proofs.ClassNoise

namespace Lax343628Proofs.NormalizedClassNoise

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ColumnFieldBounds Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassChannels Lax343628Proofs.ClassIncrements
open Lax343628Proofs.TaggedDynamics Lax343628Proofs.FiniteDrift
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+} {i : Fin n} {b : Fin 2}

def fieldNoise (pc : ℝ) (P : Population n μ) (i : Fin n) (ψ : BitString n → ℝ) (y : ℝ) : Event n μ → ℝ :=
  NoiseNormalization.noise (eventLaw pc P) (nonImmChange k i ψ P) (μ : ℕ) y

lemma field_normalized (pc : ℝ) (P : Population n μ) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (h : ColumnClass n k i b → ℝ) (ref : ColumnClass n k i b) (D gamma fmin y : ℝ)
    (hD : 1 ≤ D) (hgamma : 0 ≤ gamma) (hfmin : 0 < fmin) (hf : fmin ≤ fraction i b P)
    (hone : ∀ z, 1 ≤ h z) (hratio : ∀ x z, h z ≤ D * h x)
    (hy : average P (liftClass h) ≤ y) (A : Set (Event n μ))
    (hz : ∀ E, E ∉ A → nonImmChange k i (liftClass h) P E = 0)
    (hp : mean (eventLaw pc P) (fun E ↦ if E ∈ A then 1 else 0) ≤ gamma * fraction i b P) :
    (∀ E, |fieldNoise (k := k) pc P i (liftClass h) y E| ≤ (1 + gamma) * D ^ 2 / ((μ : ℕ) * fmin)) ∧
      mean (eventLaw pc P) (fun E ↦ fieldNoise (k := k) pc P i (liftClass h) y E ^ 2) ≤
        gamma * D ^ 4 / (((μ : ℕ) : ℝ) ^ 2 * fmin) := by
  have hb := reference_bounds P hP h ref D hD hone hratio
  have hM : 0 ≤ D * h ref := by have hh := hone ref; positivity
  have hypos : 0 < y := by linarith [hb.2.1]
  have hMY : (D * h ref) * fraction i b P ≤ D ^ 2 * y := by
    have ht := mul_le_mul_of_nonneg_left hy (sq_nonneg D)
    linarith [hb.2.2]
  have ht := NoiseNormalization.normalized_bounds (eventLaw pc P) A
    (nonImmChange k i (liftClass h) P) (μ : ℕ) y (D * h ref) (D ^ 2) gamma (fraction i b P) fmin
    (by exact_mod_cast μ.pos) hypos hM (sq_nonneg D) hgamma hfmin hf (fraction_bounds i b P).2
    hMY (nonImm_abs i (liftClass h) _ (lift_bounds h _ hM hb.1) P) hz hp
  constructor
  · exact ht.1
  · convert ht.2 using 1 <;> first | rfl | ring

lemma mutant_normalized (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (P : Population n μ)
    (hP : ∀ u, (Sampling.zeros (P u)).card = k) (h : ColumnClass n k i 1 → ℝ)
    (ref : ColumnClass n k i 1) (D fmin y : ℝ) (hD : 1 ≤ D) (hfmin : 0 < fmin)
    (hf : fmin ≤ fraction i 1 P) (hone : ∀ z, 1 ≤ h z) (hratio : ∀ x z, h z ≤ D * h x)
    (hy : average P (liftClass h) ≤ y) :
    (∀ E, |fieldNoise (k := k) pc P i (liftClass h) y E| ≤ 4 * D ^ 2 / ((μ : ℕ) * fmin)) ∧
      mean (eventLaw pc P) (fun E ↦ fieldNoise (k := k) pc P i (liftClass h) y E ^ 2) ≤
        3 * D ^ 4 / (((μ : ℕ) : ℝ) ^ 2 * fmin) := by
  have ht := field_normalized pc P hP h ref D 3 fmin y hD (by norm_num) hfmin hf hone hratio hy
    {E | channel i 1 P E}
    (mutant_off_channel i (liftClass h) (lift_bit h) P) (channel_bound pc hpc i 1 P)
  norm_num only at ht
  exact ht

lemma resident_normalized (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (P : Population n μ)
    (hP : ∀ u, (Sampling.zeros (P u)).card = k) (h : ColumnClass n k i 0 → ℝ)
    (ref : ColumnClass n k i 0) (D amin y : ℝ) (hD : 1 ≤ D) (hamin : 0 < amin)
    (ha : amin ≤ fraction i 0 P) (hone : ∀ z, 1 ≤ h z) (hratio : ∀ x z, h z ≤ D * h x)
    (hy : average P (liftClass h) ≤ y) (himm : fraction i 1 P / n ≤ fraction i 0 P) :
    (∀ E, |fieldNoise (k := k) pc P i (liftClass h) y E| ≤ 5 * D ^ 2 / ((μ : ℕ) * amin)) ∧
      mean (eventLaw pc P) (fun E ↦ fieldNoise (k := k) pc P i (liftClass h) y E ^ 2) ≤
        4 * D ^ 4 / (((μ : ℕ) : ℝ) ^ 2 * amin) := by
  have hp : mean (eventLaw pc P) (fun E ↦ if E ∈ {E | residentChannel i P E} then 1 else 0) ≤
      4 * fraction i 0 P := by
    simp only [Set.mem_ofPred_eq]
    linarith [resident_channel_bound pc hpc i P]
  have ht := field_normalized pc P hP h ref D 4 amin y hD (by norm_num) hamin ha hone hratio hy
    {E | residentChannel i P E}
    (resident_nonImm_off_channel i (liftClass h) (lift_bit h) P) hp
  norm_num only at ht
  exact ht

end
end Lax343628Proofs.NormalizedClassNoise

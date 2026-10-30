import Lax343628Proofs.CloneProtection
import Lax343628Proofs.LastExit
import Lax343628Proofs.PathBarriers

namespace Lax343628Proofs.BandPaths

open Lax343628.Algorithm Lax343628Proofs.Genotypes Lax343628Proofs.SpeciesState
open Lax343628Proofs.PopulationRatio Lax343628Proofs.PlateauDynamics
open Lax343628Proofs.SpeciesEntry Lax343628Proofs.SpeciesProtection
open Lax343628Proofs.Trajectories Lax343628Proofs.LastExit
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma numerical_overshoot (old next N M : ℝ) (hM : 200 ≤ M) (hN : M < N)
    (hold : 1 / 25 ≤ old) (hstep : |next - old| ≤ (5 / 4 + old) / (N - 1)) :
    1 / 25 - 3 / M ≤ next := by
  have hden : 0 < N - 1 := by linarith
  have hupper : old - next ≤ (5 / 4 + old) / (N - 1) := by
    have h := (abs_le.mp hstep).1
    linarith
  have hscaled := (le_div_iff₀ hden).mp hupper
  have hmon := mul_nonneg (sub_nonneg.mpr hold) (show 0 ≤ N - 2 by linarith)
  have hnum : (1 / 25 - next) * (N - 1) ≤ (129 / 100 : ℝ) := by nlinarith
  have hfrac := (le_div_iff₀ hden).mpr hnum
  have hsmall : (129 / 100 : ℝ) / (N - 1) ≤ 3 / M := by
    apply (div_le_div_iff₀ hden (by linarith : 0 < M)).mpr
    linarith
  linarith

lemma ratio_entry_overshoot {n k : ℕ} {μ : ℕ+} {p0 : ℝ}
    (hμ : 200 ≤ (μ : ℕ) * p0) (B : Genotype n k) (p_c : ℝ)
    (P Q : Population n μ) (hN : (μ : ℕ) * p0 < count (toString B) P)
    (hold : 1 / 25 ≤ ratio (weightFunction B) (toString B) P)
    (hQ : Q ∈ (auxiliaryStep k p_c P).support) :
    1 / 25 - ratioStep μ p0 ≤ ratio (weightFunction B) (toString B) Q := by
  exact numerical_overshoot _ _ _ _ hμ hN hold
    (auxiliary_ratio_abs (weightFunction B) (toString B) (weightFunction_anchor B)
      (weightFunction_bounds B) p_c P (by linarith) Q hQ)

lemma count_frozen_exit {n k : ℕ} {μ : ℕ+} {p0 : ℝ} (B : Genotype n k) {t : ℕ}
    (h : Fin (t + 1) → Population n μ) (hbad : ∀ i, h i ∈ badSet B p0)
    (hlast : 2 * (μ : ℕ) * p0 < count (toString B) (h (Fin.last t))) :
    2 * (μ : ℕ) * p0 < count (toString B) (frozen (CloneProtection.countBand B p0) h) := by
  apply frozen_exit (CloneProtection.countBand B p0) (badSet B p0)
    {P | 2 * (μ : ℕ) * p0 < count (toString B) P} h hbad
  · intro hp
    exact (not_le_of_gt hlast) hp.2.2.1
  · intro P hp
    by_contra hn
    apply hp.2
    exact ⟨hp.1.1, hp.1.2.1, le_of_not_gt hn, hp.1.2.2.le⟩

lemma ratio_frozen_exit {n k : ℕ} {μ : ℕ+} {p0 : ℝ} (B : Genotype n k) {t : ℕ}
    (h : Fin (t + 1) → Population n μ) (hbad : ∀ i, h i ∈ badSet B p0)
    (hlast : ratio (weightFunction B) (toString B) (h (Fin.last t)) < 1 / 50) :
    ratio (weightFunction B) (toString B) (frozen (ratioBand B p0) h) < 1 / 50 := by
  apply frozen_exit (ratioBand B p0) (badSet B p0)
    {P | ratio (weightFunction B) (toString B) P < 1 / 50} h hbad
  · intro hp
    exact (not_le_of_gt hlast) hp.2.2.1
  · intro P hp
    by_contra hn
    apply hp.2
    exact ⟨hp.1.1, hp.1.2.1, le_of_not_gt hn, hp.1.2.2.le⟩

end
end Lax343628Proofs.BandPaths

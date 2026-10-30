import Lax343628Proofs.MixedShadow
import Lax343628Proofs.ReproductiveAdmissibility

namespace Lax343628Proofs.ShadowComparison

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.ColumnKernels Lax343628Proofs.PhysicalShadow
open Lax343628Proofs.ReproductiveValues
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {i : Fin n}

lemma value_comparison (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (partners : ℕ → PMF (BitString n))
    (hp : ∀ s u, u ∈ (partners s).support → (zeros u).card = r + 1)
    (omega : ℝ) (homega : 0 ≤ omega)
    (hcap : ∀ s (y : ColumnClass n (r + 1) i 0), (partners s y.val).toReal ≤ 1 - omega)
    {a : ℝ} (ha : 0 ≤ a) (H : ℕ)
    (horizon : H * a * ReproductiveAdmissibility.error n (r + 1) ≤ 1)
    (hsmall : a * (128 * (r + 1 : ℝ) ^ 2 / n) * (3 : ℝ) ^ (r + 1) ≤ 1)
    (hdim : (128 * (r + 1 : ℝ) ^ 2 / n) * (3 : ℝ) ^ (r + 1) * (1 + (3 : ℝ) ^ (r + 1)) ≤
      ShadowGaps.delta (r + 1) * omega / 2)
    (s : ℕ) (x : ColumnClass n (r + 1) i 1) (y : ColumnClass n (r + 1) i 0) (hxy : Related x y) :
    (1 + a * (ShadowGaps.delta (r + 1) * omega) /
        (2 * (1 + a) * (3 : ℝ) ^ (r + 1))) ^ H *
      value (fun t ↦ mixedKernel (partners t)) a s H y ≤
        value (fun t ↦ mixedKernel (partners t)) a s H x := by
  have hD : (1 : ℝ) ≤ (3 : ℝ) ^ (r + 1) := one_le_pow₀ (by norm_num)
  have heps : 0 ≤ ShadowGaps.delta (r + 1) * omega :=
    mul_nonneg (ShadowGaps.delta_pos (by omega)).le homega
  have herr : 0 ≤ (128 * (r + 1 : ℝ) ^ 2 / n) := by positivity
  have hratio {b : Fin 2} (s' H' : ℕ) (hH : H' ≤ H) (z w : ColumnClass n (r + 1) i b) :
      value (fun t ↦ mixedKernel (partners t)) a s' H' w ≤
        (3 : ℝ) ^ (r + 1) * value (fun t ↦ mixedKernel (partners t)) a s' H' z := by
    have hHreal : (H' : ℝ) ≤ H := by exact_mod_cast hH
    have ht := mul_le_mul_of_nonneg_right hHreal
      (mul_nonneg ha (ReproductiveAdmissibility.error_nonneg n (r + 1)))
    have hhorizon : H' * a * ReproductiveAdmissibility.error n (r + 1) ≤ 1 := by nlinarith
    exact ReproductiveAdmissibility.value_ratio (by omega) hn partners hp ha H' hhorizon s' z w
  exact ReproductiveComparison.value_comparison Related
    (fun t ↦ mixedKernel (partners t)) (fun t ↦ mixedKernel (partners t))
    ha hD heps herr hsmall hdim H
    (fun t ↦ MixedShadow.birth_comparison hn (partners t) (hp t) omega (hcap t))
    (fun s' H' hH z w ↦ hratio s' H' hH z w)
    (fun s' H' hH z w ↦ hratio s' H' hH z w) s H (by rfl) x y hxy

end
end Lax343628Proofs.ShadowComparison

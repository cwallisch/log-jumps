import Lax343628Proofs.ShadowWitness
import Lax343628Proofs.PartnerCaps

namespace Lax343628Proofs.SparseComparison

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields
open Lax343628Proofs.ReproductiveValues Lax343628Proofs.ReproductiveLocality
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r R ell : ℕ} {rs : ℕ+}

def clamped (sigma : Net n (r + 1) R (count R ell) rs) (t : ℕ) : PMF (BitString n) :=
  path sigma (min t (sigma.1.val - 1))

lemma clamped_field (sigma : Net n (r + 1) R (count R ell) rs) (i : Fin n) (b : Fin 2) (a : ℝ) :
    value (fun t ↦ mixedKernel (clamped sigma t)) a 0 sigma.1.val = field sigma i b a 0 := by
  unfold field
  simp only [Nat.sub_zero]
  funext x
  apply congrFun (value_congr_interval (fun t ↦ mixedKernel (clamped sigma t))
    (fun t ↦ mixedKernel (path sigma t)) a 0 sigma.1.val ?_) x
  intro t _ ht
  have ht' : t ≤ sigma.1.val - 1 := by omega
  simp only [clamped, Nat.min_eq_left ht']

lemma arbitrary_fields (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (H : Fin (R + 1)) (env : Lists n (r + 1) (count R ell) rs) (i : Fin n)
    (omega : ℝ) (homega : 0 ≤ omega)
    (hgood : ∀ j : Fin (count R ell), (group H.val ell j.val).Nonempty →
      ∀ u, EmpiricalCap.frequency (env j) u < 1 - omega / 2)
    {a : ℝ} (ha : 0 ≤ a)
    (horizon : H.val * a * ReproductiveAdmissibility.error n (r + 1) ≤ 1)
    (hsmall : a * (128 * (r + 1 : ℝ) ^ 2 / n) * (3 : ℝ) ^ (r + 1) ≤ 1)
    (hdim : (128 * (r + 1 : ℝ) ^ 2 / n) * (3 : ℝ) ^ (r + 1) * (1 + (3 : ℝ) ^ (r + 1)) ≤
      ShadowGaps.delta (r + 1) * (omega / 2) / 2)
    (x : ColumnClass n (r + 1) i 1) (y : ColumnClass n (r + 1) i 0) :
    (1 + a * (ShadowGaps.delta (r + 1) * (omega / 2)) /
        (2 * (1 + a) * (3 : ℝ) ^ (r + 1))) ^ H.val * field (H, env) i 0 a 0 y ≤
      (3 : ℝ) ^ (r + 1) * field (H, env) i 1 a 0 x := by
  by_cases hH : H.val = 0
  · simp only [field, hH, Nat.sub_zero, value, pow_zero, mul_one]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  · have hp (s : ℕ) (u : BitString n) (hu : u ∈ (clamped (H, env) s).support) :
        (Sampling.zeros u).card = r + 1 := path_support (H, env) _ u hu
    have hc (s : ℕ) (z : ColumnClass n (r + 1) i 0) :
        (clamped (H, env) s z.val).toReal ≤ 1 - omega / 2 :=
      PartnerCaps.path_cap H env omega hgood _ (by change min s (H.val - 1) < H.val; have := Nat.min_le_right s (H.val - 1); omega) z.val z.property.1
    have hv := ShadowWitness.arbitrary_values hr hn (clamped (H, env)) hp (omega / 2) (by positivity) hc
      ha H.val horizon hsmall hdim 0 x y
    rw [clamped_field (H, env) i 0 a, clamped_field (H, env) i 1 a] at hv
    exact hv

end
end Lax343628Proofs.SparseComparison

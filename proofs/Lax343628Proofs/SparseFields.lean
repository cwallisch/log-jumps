import Lax343628Proofs.SparseGroups
import Lax343628Proofs.ReproductiveLocality
import Lax343628Proofs.ReproductiveAdmissibility
import Lax343628Proofs.ClassFields
import Lax343628Proofs.FiniteConditioning

namespace Lax343628Proofs.SparseFields

open Lax343628.Algorithm
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open Lax343628Proofs.ColumnKernels Lax343628Proofs.ReproductiveValues
open Lax343628Proofs.ReproductiveLocality
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {rs : ℕ+}

def field (sigma : Net n k R (count R ell) rs) (i : Fin n) (b : Fin 2) (a : ℝ) (t : ℕ) :
    ColumnClass n k i b → ℝ :=
  value (fun s ↦ mixedKernel (path sigma s)) a t (sigma.1.val - t)

lemma path_after_congr (H : Fin (R + 1)) (xs ys : Lists n k (count R ell) rs) (j : ℕ)
    (hell : 1 ≤ ell) (hprev : ∀ g : Fin (count R ell), g.val < j → xs g = ys g)
    (t : ℕ) (ht : t < H.val) (hend : groupEnd H.val ell j ≤ t) :
    path (H, xs) t = path (H, ys) t := by
  unfold path
  congr 1
  apply hprev
  exact later_group H.val ell j t hell ht hend

lemma field_end_congr (H : Fin (R + 1)) (xs ys : Lists n k (count R ell) rs) (j : ℕ)
    (hell : 1 ≤ ell) (hprev : ∀ g : Fin (count R ell), g.val < j → xs g = ys g)
    (i : Fin n) (b : Fin 2) (a : ℝ) :
    field (H, xs) i b a (groupEnd H.val ell j) = field (H, ys) i b a (groupEnd H.val ell j) := by
  unfold field
  apply value_congr_interval
  intro t hlo hhi
  change t < groupEnd H.val ell j + (H.val - groupEnd H.val ell j) at hhi
  have hend : groupEnd H.val ell j ≤ H.val := Nat.sub_le _ _
  have ht : t < H.val := by omega
  rw [path_after_congr H xs ys j hell hprev t ht hlo]

lemma field_end_independent (H : Fin (R + 1)) (j : Fin (count R ell))
    (rest : {g : Fin (count R ell) // g ≠ j} → Fin (rs : ℕ) → Genotypes.Genotype n k)
    (xs ys : Fin (rs : ℕ) → Genotypes.Genotype n k) (hell : 1 ≤ ell)
    (i : Fin n) (b : Fin 2) (a : ℝ) :
    field (H, FiniteConditioning.fill j rest xs) i b a (groupEnd H.val ell j.val) =
      field (H, FiniteConditioning.fill j rest ys) i b a (groupEnd H.val ell j.val) := by
  apply field_end_congr H _ _ j.val hell
  intro g hg
  have hne : g ≠ j := fun h ↦ by subst g; omega
  simp only [FiniteConditioning.fill, dif_neg hne]

lemma field_difference (sigma : Net n k R (count R ell) rs) (i : Fin n) (b : Fin 2)
    {a : ℝ} (ha : 0 ≤ a) (s t : ℕ) (hst : s ≤ t) (ht : t ≤ sigma.1.val)
    (hsmall : ((t - s : ℕ) : ℝ) * a ≤ 1) (M : ℝ) (hM : 0 ≤ M)
    (hterminal : ∀ x, field sigma i b a t x ≤ M) (x : ColumnClass n k i b) :
    0 ≤ field sigma i b a s x - field sigma i b a t x ∧
      field sigma i b a s x - field sigma i b a t x ≤ 2 * ((t - s : ℕ) : ℝ) * a * M := by
  unfold field at hterminal ⊢
  have hh := tail_small_difference (fun u ↦ mixedKernel (path sigma u)) ha s (t - s)
    (sigma.1.val - t) hsmall M hM (by
      simpa only [Nat.add_sub_of_le hst] using hterminal) x
  simpa only [show t - s + (sigma.1.val - t) = sigma.1.val - s by omega,
    Nat.add_sub_of_le hst] using hh

lemma field_step (sigma : Net n k R (count R ell) rs) (i : Fin n) (b : Fin 2) (a : ℝ)
    (t : ℕ) (ht : t < sigma.1.val) (x : ColumnClass n k i b) :
    field sigma i b a t x = field sigma i b a (t + 1) x +
      a * action (mixedKernel (path sigma t)) (field sigma i b a (t + 1)) x := by
  unfold field
  rw [show sigma.1.val - t = (sigma.1.val - (t + 1)) + 1 by omega, value]

lemma field_one (sigma : Net n k R (count R ell) rs) (i : Fin n) (b : Fin 2) {a : ℝ}
    (ha : 0 ≤ a) (t : ℕ) (x : ColumnClass n k i b) : 1 ≤ field sigma i b a t x :=
  value_one_le _ ha _ _ x

lemma average_field_step {mu : ℕ+} (P : Population n mu) (sigma : Net n k R (count R ell) rs)
    (i : Fin n) (b : Fin 2) {a : ℝ} (ha : 0 ≤ a) (t : ℕ) (ht : t < sigma.1.val) :
    ClassBirthEstimates.average P (liftClass (field sigma i b a (t + 1))) ≤
      ClassBirthEstimates.average P (liftClass (field sigma i b a t)) := by
  apply FiniteDrift.mean_mono
  intro u
  unfold liftClass
  split_ifs with hz
  · rw [field_step sigma i b a t ht]
    have hnon := action_nonneg (mixedKernel (path sigma t)) (field sigma i b a (t + 1))
      (fun x ↦ le_trans (by norm_num : (0 : ℝ) ≤ 1) (field_one sigma i b ha (t + 1) x)) (⟨P u, hz⟩ : ColumnClass n k i b)
    nlinarith
  · rfl

lemma field_ratio (hk : 2 ≤ k) (hn : 4 * k ≤ n) (sigma : Net n k R (count R ell) rs)
    (i : Fin n) (b : Fin 2) {a : ℝ} (ha : 0 ≤ a)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1) (t : ℕ)
    (x y : ColumnClass n k i b) : field sigma i b a t y ≤ (3 : ℝ) ^ k * field sigma i b a t x := by
  have hle : sigma.1.val - t ≤ R := by have hh := sigma.1.isLt; omega
  have hreal : ((sigma.1.val - t : ℕ) : ℝ) ≤ R := by exact_mod_cast hle
  have hscale := mul_le_mul_of_nonneg_right hreal
    (mul_nonneg ha (ReproductiveAdmissibility.error_nonneg n k))
  apply ReproductiveAdmissibility.value_ratio hk hn (path sigma) (path_support sigma) ha
    (sigma.1.val - t) _ t x y
  nlinarith

end
end Lax343628Proofs.SparseFields

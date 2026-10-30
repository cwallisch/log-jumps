import Lax343628Proofs.RunEnvironment
import Lax343628Proofs.MismatchPoint

namespace Lax343628Proofs.RunMismatch

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassChannels Lax343628Proofs.SparseEnvironment
open Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields Lax343628Proofs.SparseSampling
open Lax343628Proofs.RunEnvironment Lax343628Proofs.EmpiricalKernels
open Lax343628Proofs.AveragedOperators Lax343628Proofs.WeightedFieldControl
open Lax343628Proofs.GroupSampling Lax343628Proofs.TaggedDynamics
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {rs mu : ℕ+}

lemma point_bound (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hell : 1 ≤ ell)
    (H : Fin (R + 1)) (env : Lists n k (count R ell) rs) (i : Fin n) (b : Fin 2)
    {a : ℝ} (ha : 0 ≤ a) (hcell : (ell : ℝ) * a ≤ 1)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : ℕ → Population n mu) (E : ℕ → Event n mu)
    (hnext : ∀ t, t < H.val → P (t + 1) = next k (P t) (E t))
    (j : Fin (count R ell)) [Nonempty (group H.val ell j.val)]
    (hPG : ∀ s ∈ group H.val ell j.val, ∀ u, (Sampling.zeros (P s u)).card = k)
    (t : ℕ) (ht : t ∈ group H.val ell j.val) (hf : 0 < fraction i b (P t)) :
    |difference (P t) (mixedKernel (empirical (P t))) (mixedKernel (partnerLaw (env j)))
          (field (H, env) i b a (t + 1)) / average (P t) (liftClass (field (H, env) i b a t)) -
      difference (P t) (mixedKernel ((groupLaw (group H.val ell j.val) P hPG).map Genotypes.toString))
          (mixedKernel (partnerLaw (env j))) (terminalFields H i b a j env) /
            average (P t) (liftClass (terminalFields H i b a j env))| ≤
      ((ell : ℝ) / (mu : ℕ)) * (3 : ℝ) ^ k + (2 * ell * a) * (3 : ℝ) ^ k +
        (2 * ell * a) * ((3 : ℝ) ^ k) ^ 2 := by
  let sigma : Net n k R (count R ell) rs := (H, env)
  let finish := groupEnd H.val ell j.val
  let D : ℝ := (3 : ℝ) ^ k
  let f := field sigma i b a (t + 1)
  let g := field sigma i b a finish
  let y := average (P t) (liftClass (field sigma i b a t))
  let z := average (P t) (liftClass g)
  let Mnext := D * y / fraction i b (P t)
  let Mend := D * z / fraction i b (P t)
  have hP := hPG t ht
  have hb := group_member_bounds H.val ell j.val t hell ht
  have htH : t < H.val := (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)
  have htEnd : t < finish := hb.1
  have hEndH : finish ≤ sigma.1.val := hb.2.1
  have hu : finish - t ≤ ell := hb.2.2
  have hu' : finish - (t + 1) ≤ ell := by omega
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have honeT := field_one sigma i b ha t
  have honeF := field_one sigma i b ha (t + 1)
  have honeG := field_one sigma i b ha finish
  have ratioF := field_ratio hk hn sigma i b ha horizon (t + 1)
  have ratioG := field_ratio hk hn sigma i b ha horizon finish
  have hy : 0 < y := hf.trans_le (average_one_lower (P t) hP _ honeT)
  have hz : 0 < z := hf.trans_le (average_one_lower (P t) hP g honeG)
  have hMn : 0 ≤ Mnext := by dsimp [Mnext]; positivity
  have hMe : 0 ≤ Mend := by dsimp [Mend]; positivity
  have hMYn : Mnext * fraction i b (P t) = D * y := by dsimp [Mnext]; field_simp
  have hMYe : Mend * fraction i b (P t) = D * z := by dsimp [Mend]; field_simp
  have hFavg : average (P t) (liftClass f) ≤ y := average_field_step (P t) sigma i b ha t htH
  have hFbound : ∀ x, 0 ≤ f x ∧ f x ≤ Mnext := by
    intro x
    exact ⟨le_trans (by norm_num) (honeF x), child_bound (P t) hP f D y hD ratioF hFavg hf x⟩
  have hGbound : ∀ x, g x ≤ Mend := child_bound (P t) hP g D z hD ratioG (by rfl) hf
  have hsmall : ((finish - t : ℕ) : ℝ) * a ≤ 1 := by
    have hr : ((finish - t : ℕ) : ℝ) ≤ ell := by exact_mod_cast hu
    nlinarith
  have hsmall' : ((finish - (t + 1) : ℕ) : ℝ) * a ≤ 1 := by
    have hr : ((finish - (t + 1) : ℕ) : ℝ) ≤ ell := by exact_mod_cast hu'
    nlinarith
  have hdelta (x : ColumnClass n k i b) : 0 ≤ f x - g x ∧ f x - g x ≤ (2 * ell * a) * Mend := by
    have hh := field_difference sigma i b ha (t + 1) finish (by omega) hEndH hsmall' Mend hMe hGbound x
    have hr : ((finish - (t + 1) : ℕ) : ℝ) ≤ ell := by exact_mod_cast hu'
    have hscale := mul_le_mul_of_nonneg_right hr (mul_nonneg ha hMe)
    exact ⟨hh.1, by nlinarith [hh.2]⟩
  have hcurdelta (x : ColumnClass n k i b) : 0 ≤ field sigma i b a t x - g x ∧
      field sigma i b a t x - g x ≤ (2 * ell * a) * Mend := by
    have hh := field_difference sigma i b ha t finish (by omega) hEndH hsmall Mend hMe hGbound x
    have hr : ((finish - t : ℕ) : ℝ) ≤ ell := by exact_mod_cast hu
    have hscale := mul_le_mul_of_nonneg_right hr (mul_nonneg ha hMe)
    exact ⟨hh.1, by nlinarith [hh.2]⟩
  have hcompare := MismatchPoint.field_average_comparison (P t) hP (field sigma i b a t) g Mend
    (2 * ell * a) D hMe (by positivity) hz hMYe.le hcurdelta
  have hAB (x : ColumnClass n k i b) :
      |ReproductiveValues.action (mixedKernel (empirical (P t))) f x -
        ReproductiveValues.action (mixedKernel ((groupLaw (group H.val ell j.val) P hPG).map Genotypes.toString)) f x| ≤
      ((ell : ℝ) / (mu : ℕ)) * Mnext := by
    have hh := group_kernel_difference P E H.val ell j.val hell hnext hPG f Mnext hMn hFbound t ht x
    convert hh using 1; first | rfl | ring
  exact MismatchPoint.mismatch_bound (P t) hP _ _ _ f g Mnext Mend
    ((ell : ℝ) / (mu : ℕ)) (2 * ell * a) D y hMn hMe (by positivity) (by positivity) hD hy hz
    hcompare.1 hcompare.2 hMYn.le hMYe.le (fun x ↦ le_trans (by norm_num) (honeG x)) ratioG hdelta hAB

end
end Lax343628Proofs.RunMismatch

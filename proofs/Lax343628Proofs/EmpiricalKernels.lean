import Lax343628Proofs.FiniteComparison
import Lax343628Proofs.Species

namespace Lax343628Proofs.EmpiricalKernels

open Lax343628.Algorithm Lax343628Proofs.BitProduct
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.Species Lax343628Proofs.Genotypes
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} [Fintype α] [Fintype β]

lemma uniform_pair [Nonempty α] [Nonempty β] :
    PMF.uniformOfFintype (α × β) = joint (PMF.uniformOfFintype α) (PMF.uniformOfFintype β) := by
  ext ⟨a, b⟩
  simp only [joint_apply, PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv]
  all_goals simp

lemma mean_joint (p : PMF α) (q : PMF β) (f : α → β → ℝ) :
    mean (joint p q) (fun ab ↦ f ab.1 ab.2) = mean p (fun a ↦ mean q (f a)) := by
  rw [joint_bind, mean_bind]
  simp only [mean_bind, mean_pure]

lemma mean_uniform_pair [Nonempty α] [Nonempty β] (f : α → β → ℝ) :
    mean (PMF.uniformOfFintype (α × β)) (fun ab ↦ f ab.1 ab.2) =
      mean (PMF.uniformOfFintype α) (fun a ↦ mean (PMF.uniformOfFintype β) (f a)) := by
  rw [uniform_pair, mean_joint]

def empirical {μ : ℕ+} (P : Fin (μ : ℕ) → α) : PMF α :=
  (PMF.uniformOfFintype (Fin (μ : ℕ))).map P

def frequency {μ : ℕ+} (P : Fin (μ : ℕ) → α) (x : α) : ℝ := (empirical P x).toReal

def pairMean (p : PMF α) (F : α → α → ℝ) : ℝ := mean p (fun x ↦ mean p (F x))

lemma empirical_pairMean {μ : ℕ+} (P : Fin (μ : ℕ) → α) (F : α → α → ℝ) :
    mean (PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ)))
      (fun uv ↦ F (P uv.1) (P uv.2)) = pairMean (empirical P) F := by
  rw [mean_uniform_pair (fun u v ↦ F (P u) (P v))]
  unfold pairMean empirical
  rw [mean_map]
  simp_rw [mean_map]

lemma pairMean_comparison (p : PMF α) (F G : α → α → ℝ) (E : ℝ)
    (h : ∀ x y, |F x y - G x y| ≤ E) : |pairMean p F - pairMean p G| ≤ E := by
  unfold pairMean
  rw [← mean_sub]
  apply (abs_mean_le p _).trans
  apply (mean_mono p _).trans_eq (mean_const p E)
  intro x
  rw [← mean_sub]
  exact (abs_mean_le p _).trans ((mean_mono p (h x)).trans_eq (mean_const p E))

lemma pairMean_mul (p : PMF α) (c : ℝ) (F : α → α → ℝ) :
    pairMean p (fun x y ↦ c * F x y) = c * pairMean p F := by
  unfold pairMean
  simp_rw [mean_mul]

lemma pairMean_add (p : PMF α) (F G : α → α → ℝ) :
    pairMean p (fun x y ↦ F x y + G x y) = pairMean p F + pairMean p G := by
  unfold pairMean
  simp_rw [mean_add]

lemma pairMean_sub (p : PMF α) (F G : α → α → ℝ) :
    pairMean p (fun x y ↦ F x y - G x y) = pairMean p F - pairMean p G := by
  unfold pairMean
  simp_rw [mean_sub]

lemma pairMean_const (p : PMF α) (c : ℝ) : pairMean p (fun _ _ ↦ c) = c := by
  unfold pairMean
  simp_rw [mean_const]

lemma pairMean_mono (p : PMF α) {F G : α → α → ℝ} (h : ∀ x y, F x y ≤ G x y) :
    pairMean p F ≤ pairMean p G := mean_mono p (fun x ↦ mean_mono p (h x))

lemma pairMean_anchor [DecidableEq α] (p : PMF α) (B : α) (c : ℝ) :
    pairMean p (fun x y ↦ if x = B ∧ y = B then c else 0) = (p B).toReal ^ 2 * c := by
  unfold pairMean
  have hinner (x : α) :
      mean p (fun y ↦ if x = B ∧ y = B then c else 0) =
        if x = B then (p B).toReal * c else 0 := by
    by_cases hx : x = B
    · simp only [hx, true_and, mean_pick, ite_true]
    · simp only [hx, false_and, ite_false, mean_const]
  simp_rw [hinner]
  rw [mean_pick]
  ring

lemma pairMean_eq_pairValue {n k : ℕ} (p : PMF (Genotype n k))
    (F : Genotype n k → Genotype n k → ℝ) :
    pairMean p F = pairValue (fun x ↦ (p x).toReal) F := by
  unfold pairMean mean pairValue
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

end
end Lax343628Proofs.EmpiricalKernels

import Lax343628Proofs.ClassChannels
import Lax343628Proofs.CloneMutationTest

namespace Lax343628Proofs.ClassBirth

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.PhysicalOffspring Lax343628Proofs.TaggedDynamics
open Lax343628Proofs.ColumnKernels Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.EmpiricalKernels
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α]

lemma pairMean_swap (p : PMF α) (F : α → α → ℝ) :
    pairMean p (fun x y ↦ F y x) = pairMean p F := by
  unfold pairMean mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

def own (B : α → Prop) [DecidablePred B] (F : α → α → ℝ) (x y : α) : ℝ :=
  if B x then (if B y then 1 else 2) * F x y else 0

def other (B : α → Prop) [DecidablePred B] (F : α → α → ℝ) (x y : α) : ℝ :=
  if ¬B x ∧ ¬B y then F x y else 0

lemma pair_decomposition (p : PMF α) (B : α → Prop) [DecidablePred B]
    (F : α → α → ℝ) (hF : ∀ x y, F x y = F y x) :
    pairMean p F = pairMean p (own B F) + pairMean p (other B F) := by
  have hpoint : F = fun x y ↦ (1 / 2 : ℝ) * own B F x y +
      (1 / 2 : ℝ) * own B F y x + other B F x y := by
    funext x y
    by_cases hx : B x <;> by_cases hy : B y <;> simp [own, other, hx, hy, hF y x]; ring
  conv_lhs => rw [hpoint]
  rw [pairMean_add, pairMean_add, pairMean_mul, pairMean_mul, pairMean_swap]
  ring

variable {n : ℕ} {μ : ℕ+}

def pairTest (ψ : BitString n → ℝ) (x y : BitString n) : ℝ :=
  mean (pairMutation x y (1 / n)) ψ

def fromOpposite (pc : ℝ) (P : Population n μ) (i : Fin n) (b : Fin 2)
    (ψ : BitString n → ℝ) : ℝ :=
  mean (parentLaw μ pc) (fun uv ↦
    if P uv.1 i ≠ b ∧ P uv.2 i ≠ b then pairTest ψ (P uv.1) (P uv.2) else 0)

def ownCross (P : Population n μ) (i : Fin n) (b : Fin 2) (ψ : BitString n → ℝ) : ℝ :=
  pairMean (empirical P) (fun x y ↦ if x i = b then classFactor i b y * pairTest ψ x y else 0)

def ownClone (P : Population n μ) (i : Fin n) (b : Fin 2) (ψ : BitString n → ℝ) : ℝ :=
  mean (PMF.uniformOfFintype (Fin (μ : ℕ)))
    (fun u ↦ if P u i = b then pairTest ψ (P u) (P u) else 0)

lemma pairTest_symm (ψ : BitString n → ℝ) (x y : BitString n) : pairTest ψ x y = pairTest ψ y x := by
  have hp : (0 : ℝ) ≤ 1 / n ∧ 1 / (n : ℝ) ≤ 1 := by
    by_cases hn : n = 0
    · simp [hn]
    · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact ⟨by positivity, (div_le_one (by positivity)).mpr hnR⟩
  have heq : pairMutation x y (1 / n) = pairMutation y x (1 / n) := by
    rw [pairMutation_eq_product x y _ hp, pairMutation_eq_product y x _ hp]
    congr 1
    funext j
    ext b
    rw [siteLaw_apply _ _ _ _ hp, siteLaw_apply _ _ _ _ hp]
    by_cases hxy : x j = y j
    · rw [hxy]
    · simp [siteProbability, hxy, Ne.symm hxy]
  exact congrArg (fun p ↦ mean p ψ) heq

lemma offspring_decomposition (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (P : Population n μ)
    (i : Fin n) (b : Fin 2) (ψ : BitString n → ℝ) :
    mean (offspring pc P) ψ = pc * ownCross P i b ψ + (1 - pc) * ownClone P i b ψ +
      fromOpposite pc P i b ψ := by
  let B : BitString n → Prop := fun x ↦ x i = b
  have hcross := pair_decomposition (empirical P) B (pairTest ψ) (pairTest_symm ψ)
  have hown : ownCross P i b ψ = pairMean (empirical P) (own B (pairTest ψ)) := by
    unfold ownCross
    congr 1
    funext x y
    simp only [own, B, classFactor, eq_comm]
  rw [← hown] at hcross
  let badClone := mean (PMF.uniformOfFintype (Fin (μ : ℕ)))
    (fun u ↦ if P u i ≠ b then pairTest ψ (P u) (P u) else 0)
  have hclone : mean (PMF.uniformOfFintype (Fin (μ : ℕ))) (fun u ↦ pairTest ψ (P u) (P u)) =
      ownClone P i b ψ + badClone := by
    rw [ownClone, ← mean_add]
    congr 1
    funext u
    dsimp [badClone]
    by_cases hu : P u i = b <;> simp [hu]
  have hother : fromOpposite pc P i b ψ = pc * pairMean (empirical P) (other B (pairTest ψ)) +
      (1 - pc) * badClone := by
    rw [fromOpposite, mean_parentLaw pc hpc]
    rw [← empirical_pairMean P (other B (pairTest ψ))]
    simp only [other, B, badClone, and_self]
  rw [ActualBirthKernels.offspring_mean pc hpc]
  change pc * mean (PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ)))
      (fun uv ↦ pairTest ψ (P uv.1) (P uv.2)) +
    (1 - pc) * mean (PMF.uniformOfFintype (Fin (μ : ℕ))) (fun u ↦ pairTest ψ (P u) (P u)) = _
  rw [empirical_pairMean P (pairTest ψ), hcross, hclone, hother]
  ring

end
end Lax343628Proofs.ClassBirth

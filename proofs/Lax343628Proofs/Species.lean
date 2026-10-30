import Lax343628Proofs.Genotypes
import Lax343628Proofs.RatioBounds

namespace Lax343628Proofs.Species

open Lax343628Proofs.Genotypes Lax343628Proofs.Weights Lax343628Proofs.RatioBounds
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α]

def offSum (B : α) (f : α → ℝ) : ℝ := ∑ x ∈ Finset.univ.erase B, f x

lemma sum_split (B : α) (f : α → ℝ) : (∑ x, f x) = f B + offSum B f :=
  (Finset.add_sum_erase Finset.univ f (Finset.mem_univ B)).symm

lemma offSum_add (B : α) (f g : α → ℝ) :
    offSum B (fun x ↦ f x + g x) = offSum B f + offSum B g := Finset.sum_add_distrib

lemma offSum_mul (B : α) (c : ℝ) (f : α → ℝ) :
    offSum B (fun x ↦ c * f x) = c * offSum B f := (Finset.mul_sum _ _ _).symm

lemma offSum_mul_right (B : α) (c : ℝ) (f : α → ℝ) :
    offSum B (fun x ↦ f x * c) = offSum B f * c := (Finset.sum_mul _ _ _).symm

lemma offSum_nonneg (B : α) {f : α → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ offSum B f :=
  Finset.sum_nonneg fun x _ ↦ h x

lemma offSum_mono (B : α) {f g : α → ℝ} (h : ∀ x, x ≠ B → f x ≤ g x) :
    offSum B f ≤ offSum B g :=
  Finset.sum_le_sum fun x hx ↦ h x (Finset.mem_erase.mp hx).1

lemma pair_split (B : α) (f : α → α → ℝ) :
    (∑ x, ∑ y, f x y) = f B B + offSum B (fun x ↦ f B x + f x B) +
      offSum B (fun x ↦ offSum B (f x)) := by
  rw [sum_split B (fun x ↦ ∑ y, f x y), sum_split B (f B)]
  simp_rw [sum_split B]
  rw [offSum_add, offSum_add]
  ring

def pairValue (p : α → ℝ) (K : α → α → ℝ) : ℝ := ∑ x, ∑ y, p x * p y * K x y

def cloudValue (B : α) (p W : α → ℝ) : ℝ := offSum B (fun x ↦ p x * W x)

variable {n k : ℕ}

def cloud (B : Genotype n k) (p : Genotype n k → ℝ) : ℝ :=
  cloudValue B p (fun x ↦ weight (distance B x))

def massOne (B : Genotype n k) (p : Genotype n k → ℝ) : ℝ :=
  offSum B (fun x ↦ if distance B x = 1 then p x else 0)

def farCloud (B : Genotype n k) (p : Genotype n k → ℝ) : ℝ :=
  offSum B (fun x ↦ if 2 ≤ distance B x then p x * weight (distance B x) else 0)

def copyMass (B : Genotype n k) (p : Genotype n k → ℝ) : ℝ :=
  offSum B (fun x ↦ p x * (4 : ℝ)⁻¹ ^ distance B x)

def cloudPair (B : Genotype n k) (p : Genotype n k → ℝ) : ℝ :=
  offSum B (fun x ↦ offSum B (fun y ↦ p x * p y * weightedKernel B x y))

def copyPair (B : Genotype n k) (p : Genotype n k → ℝ) : ℝ :=
  offSum B (fun x ↦ offSum B (fun y ↦ p x * p y * cloneKernel B x y))

def otherPair (B : Genotype n k) (p : Genotype n k → ℝ) : ℝ :=
  offSum B (fun x ↦ offSum B (fun y ↦ if distance B x = 1 ∧ distance B y = 1 then 0
    else p x * p y * weightedKernel B x y))

lemma cloud_split (B : Genotype n k) (p : Genotype n k → ℝ) :
    cloud B p = massOne B p + farCloud B p := by
  rw [cloud, cloudValue, massOne, farCloud, ← offSum_add]
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only
  have hpos := distance_pos B x (Finset.mem_erase.mp hx).1
  by_cases h1 : distance B x = 1
  · simp [h1]
  · have h2 : 2 ≤ distance B x := by omega
    simp only [if_neg h1, if_pos h2, zero_add]

lemma weighted_anchor_sum (B : Genotype n k) (p : Genotype n k → ℝ) :
    offSum B (fun x ↦ p x * (weightedKernel B B x + weightedKernel B x B)) =
      cloud B p + (1 / 16 : ℝ) * farCloud B p := by
  rw [cloud, cloudValue, farCloud, ← offSum_mul, ← offSum_add]
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only
  have hpos := distance_pos B x (Finset.mem_erase.mp hx).1
  rw [weightedKernel_symm B x B]
  by_cases h1 : distance B x = 1
  · have h2 : ¬2 ≤ distance B x := by omega
    rw [if_neg h2]
    have h := weightedKernel_anchor_one B x h1
    nlinarith [congrArg (fun z : ℝ ↦ p x * z) h]
  · have h2 : 2 ≤ distance B x := by omega
    rw [if_pos h2]
    have h := weightedKernel_anchor_far B x h2
    nlinarith [congrArg (fun z : ℝ ↦ p x * z) h]

lemma weighted_pair_value (B : Genotype n k) (p : Genotype n k → ℝ) :
    pairValue p (weightedKernel B) = p B * (cloud B p + (1 / 16 : ℝ) * farCloud B p) +
      cloudPair B p := by
  rw [pairValue, pair_split B, weightedKernel_anchor_self, mul_zero, zero_add]
  change offSum B (fun x ↦ p B * p x * weightedKernel B B x +
    p x * p B * weightedKernel B x B) + cloudPair B p = _
  have heq : offSum B (fun x ↦ p B * p x * weightedKernel B B x +
      p x * p B * weightedKernel B x B) =
      p B * offSum B (fun x ↦ p x * (weightedKernel B B x + weightedKernel B x B)) := by
    rw [← offSum_mul]
    apply Finset.sum_congr rfl
    intro x _
    dsimp only
    ring
  rw [heq, weighted_anchor_sum]

lemma clone_pair_value (B : Genotype n k) (p : Genotype n k → ℝ) :
    pairValue p (cloneKernel B) = p B ^ 2 + 2 * p B * copyMass B p + copyPair B p := by
  rw [pairValue, pair_split B, cloneKernel_anchor, distance_self, pow_zero, mul_one]
  change p B * p B + offSum B (fun x ↦ p B * p x * cloneKernel B B x +
    p x * p B * cloneKernel B x B) + copyPair B p = _
  have heq : offSum B (fun x ↦ p B * p x * cloneKernel B B x +
      p x * p B * cloneKernel B x B) = 2 * p B * copyMass B p := by
    rw [copyMass, ← offSum_mul]
    apply Finset.sum_congr rfl
    intro x _
    dsimp only
    rw [cloneKernel_symm B x B, cloneKernel_anchor]
    ring
  rw [heq, pow_two]

lemma ratio_identity (B : Genotype n k) (p : Genotype n k → ℝ) (hp : p B ≠ 0) :
    pairValue p (weightedKernel B) - (cloud B p / p B) * pairValue p (cloneKernel B) =
      (1 / 16 : ℝ) * p B * farCloud B p + cloudPair B p -
        2 * cloud B p * copyMass B p - (cloud B p / p B) * copyPair B p := by
  rw [weighted_pair_value, clone_pair_value]
  field_simp
  ring

lemma cloud_nonneg (B : Genotype n k) (p : Genotype n k → ℝ) (hp : ∀ x, 0 ≤ p x) :
    0 ≤ cloud B p := offSum_nonneg B (fun x ↦ mul_nonneg (hp x) (weight_nonneg _))

lemma massOne_nonneg (B : Genotype n k) (p : Genotype n k → ℝ) (hp : ∀ x, 0 ≤ p x) :
    0 ≤ massOne B p := by
  apply offSum_nonneg
  intro x
  split_ifs
  · exact hp x
  · exact le_rfl

lemma farCloud_nonneg (B : Genotype n k) (p : Genotype n k → ℝ) (hp : ∀ x, 0 ≤ p x) :
    0 ≤ farCloud B p := by
  apply offSum_nonneg
  intro x
  split_ifs
  · exact mul_nonneg (hp x) (weight_nonneg _)
  · exact le_rfl

lemma copyMass_nonneg (B : Genotype n k) (p : Genotype n k → ℝ) (hp : ∀ x, 0 ≤ p x) :
    0 ≤ copyMass B p := offSum_nonneg B (fun x ↦ mul_nonneg (hp x) (by positivity))

lemma copyMass_bound (B : Genotype n k) (p : Genotype n k → ℝ) (hp : ∀ x, 0 ≤ p x) :
    copyMass B p ≤ massOne B p / 4 + (5 / 96 : ℝ) * farCloud B p := by
  rw [copyMass, massOne, farCloud, div_eq_mul_inv, ← offSum_mul_right, ← offSum_mul,
    ← offSum_add]
  apply offSum_mono
  intro x hx
  have hpos := distance_pos B x hx
  by_cases h1 : distance B x = 1
  · simp only [h1, show ¬2 ≤ 1 by omega, if_false, weight_one, mul_one,
      mul_zero, add_zero, pow_one]
    exact le_rfl
  · have h2 : 2 ≤ distance B x := by omega
    simp only [if_neg h1, if_pos h2, zero_mul, zero_add]
    have h := mul_le_mul_of_nonneg_left (copy_le_small_weight h2) (hp x)
    nlinarith

lemma copyPair_bound (B : Genotype n k) (p : Genotype n k → ℝ) (hp : ∀ x, 0 ≤ p x) :
    copyPair B p ≤ copyMass B p ^ 2 := by
  calc
    _ ≤ offSum B (fun x ↦ offSum B (fun y ↦
        (p x * (4 : ℝ)⁻¹ ^ distance B x) * (p y * (4 : ℝ)⁻¹ ^ distance B y))) := by
      apply offSum_mono
      intro x _
      apply offSum_mono
      intro y _
      have h := mul_le_mul_of_nonneg_left (cloneKernel_le B x y) (mul_nonneg (hp x) (hp y))
      nlinarith
    _ = copyMass B p ^ 2 := by
      simp_rw [offSum_mul]
      rw [offSum_mul_right, pow_two]
      rfl

lemma cloudPair_bound (B : Genotype n k) (p : Genotype n k → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (51 / 80 : ℝ) * massOne B p ^ 2 + otherPair B p ≤ cloudPair B p := by
  let a : Genotype n k → ℝ := fun x ↦ if distance B x = 1 then p x else 0
  have hpoint : ∀ x y,
      (51 / 80 : ℝ) * a x * a y +
        (if distance B x = 1 ∧ distance B y = 1 then 0 else p x * p y * weightedKernel B x y) ≤
      p x * p y * weightedKernel B x y := by
    intro x y
    by_cases hx : distance B x = 1 <;> by_cases hy : distance B y = 1
    · simp only [a, if_pos hx, if_pos hy, if_pos (And.intro hx hy), add_zero]
      have h := mul_le_mul_of_nonneg_left (distance_one_kernel_lower B x y hx hy)
        (mul_nonneg (hp x) (hp y))
      nlinarith
    all_goals simp [a, hx, hy]
  have hsum : offSum B (fun x ↦ offSum B (fun y ↦
      (51 / 80 : ℝ) * a x * a y +
        (if distance B x = 1 ∧ distance B y = 1 then 0 else p x * p y * weightedKernel B x y))) ≤
      cloudPair B p :=
    offSum_mono B (fun x _ ↦ offSum_mono B (fun y _ ↦ hpoint x y))
  simp_rw [offSum_add, offSum_mul] at hsum
  have heq : offSum B (fun x ↦ 51 / 80 * a x * offSum B a) =
      (51 / 80 : ℝ) * massOne B p ^ 2 := by
    rw [offSum_mul_right, offSum_mul]
    change 51 / 80 * massOne B p * massOne B p = _
    ring
  rw [heq] at hsum
  exact hsum

lemma ideal_drift (B : Genotype n k) (p : Genotype n k → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hpB : 0 < p B) (hiso : cloud B p / p B ≤ 1 / 25) :
    34 / 1000 * p B * farCloud B p + 135 / 1000 * massOne B p ^ 2 + otherPair B p ≤
      pairValue p (weightedKernel B) - (cloud B p / p B) * pairValue p (cloneKernel B) := by
  rw [ratio_identity B p hpB.ne']
  have hmass : massOne B p + farCloud B p = cloud B p / p B * p B := by
    rw [div_mul_cancel₀ _ hpB.ne', ← cloud_split]
  have h := ideal_ratio_drift (p B) (massOne B p) (farCloud B p) (cloud B p / p B)
    (copyMass B p) (copyPair B p) (cloudPair B p) (otherPair B p) hpB.le
    (massOne_nonneg B p hp) (farCloud_nonneg B p hp)
    (div_nonneg (cloud_nonneg B p hp) hpB.le) hiso hmass
    (copyMass_nonneg B p hp) (copyMass_bound B p hp) (copyPair_bound B p hp) (cloudPair_bound B p hp)
  rw [← cloud_split] at h
  exact h

lemma ideal_strict_drift (B : Genotype n k) (p : Genotype n k → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hpB : 0 < p B) (hiso : cloud B p / p B ≤ 1 / 25)
    (hentry : 1 / 50 ≤ cloud B p / p B) :
    (337 / 10000 : ℝ) * (1 / 50) * (cloud B p / p B) * p B ^ 2 + otherPair B p ≤
      pairValue p (weightedKernel B) - (cloud B p / p B) * pairValue p (cloneKernel B) := by
  have hmass : massOne B p + farCloud B p = cloud B p / p B * p B := by
    rw [div_mul_cancel₀ _ hpB.ne', ← cloud_split]
  have h := ideal_ratio_strict_drift (p B) (massOne B p) (farCloud B p) (cloud B p / p B)
    hpB.le (massOne_nonneg B p hp) (farCloud_nonneg B p hp) hentry hmass
  exact (add_le_add h (le_refl (otherPair B p))).trans (ideal_drift B p hp hpB hiso)

end
end Lax343628Proofs.Species

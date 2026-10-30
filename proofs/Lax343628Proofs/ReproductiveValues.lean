import Lax343628Proofs.FiniteComparison

namespace Lax343628Proofs.ReproductiveValues

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

structure Kernel (α : Type*) [Fintype α] where
  mass : α → α → ℝ
  nonneg : ∀ x y, 0 ≤ mass x y
  row_le : ∀ x, ∑ y, mass x y ≤ 1

variable {α : Type*} [Fintype α]

def action (A : Kernel α) (h : α → ℝ) (x : α) : ℝ := ∑ y, A.mass x y * h y

lemma action_nonneg (A : Kernel α) (h : α → ℝ) (hh : ∀ y, 0 ≤ h y) (x : α) :
    0 ≤ action A h x := Finset.sum_nonneg (fun y _ ↦ mul_nonneg (A.nonneg x y) (hh y))

lemma action_mono (A : Kernel α) (h g : α → ℝ) (hhg : ∀ y, h y ≤ g y) (x : α) :
    action A h x ≤ action A g x :=
  Finset.sum_le_sum (fun y _ ↦ mul_le_mul_of_nonneg_left (hhg y) (A.nonneg x y))

lemma action_le (A : Kernel α) (h : α → ℝ) (M : ℝ) (hM : 0 ≤ M) (hh : ∀ y, h y ≤ M)
    (x : α) : action A h x ≤ M := by
  calc
    _ ≤ action A (fun _ ↦ M) x := action_mono A h _ hh x
    _ = (∑ y, A.mass x y) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right (A.row_le x) hM
    _ = M := one_mul _

def value (A : ℕ → Kernel α) (a : ℝ) (s : ℕ) : ℕ → α → ℝ
  | 0 => fun _ ↦ 1
  | R + 1 => fun x ↦ value A a (s + 1) R x + a * action (A s) (value A a (s + 1) R) x

lemma value_one_le (A : ℕ → Kernel α) {a : ℝ} (ha : 0 ≤ a) (s R : ℕ) (x : α) :
    1 ≤ value A a s R x := by
  induction R generalizing s x with
  | zero => rfl
  | succ R ih =>
    exact (ih (s + 1) x).trans (le_add_of_nonneg_right
      (mul_nonneg ha (action_nonneg _ _ (fun y ↦ (by norm_num : (0 : ℝ) ≤ 1).trans (ih _ y)) x)))

lemma value_nonneg (A : ℕ → Kernel α) {a : ℝ} (ha : 0 ≤ a) (s R : ℕ) (x : α) :
    0 ≤ value A a s R x := le_trans (by norm_num) (value_one_le A ha s R x)

def Cone (adj : α → α → Prop) (rho : ℝ) (h : α → ℝ) : Prop :=
  ∀ x y, adj x y → h y ≤ rho * h x

lemma cone_step (adj : α → α → Prop) (A : Kernel α) (h : α → ℝ)
    {rho a err : ℝ} (ha : 0 ≤ a) (herr : 0 ≤ err)
    (hh : ∀ x, 0 ≤ h x) (hcone : Cone adj rho h)
    (hbirth : ∀ x y, adj x y → action A h y ≤ rho * action A h x + err * h x) :
    Cone adj (rho + a * err) (fun x ↦ h x + a * action A h x) := by
  intro x y hxy
  have hpoint := hcone x y hxy
  have hact := mul_le_mul_of_nonneg_left (hbirth x y hxy) ha
  have hnonneg := action_nonneg A h hh x
  have hprod := mul_nonneg (mul_nonneg ha herr) (mul_nonneg ha hnonneg)
  nlinarith

lemma value_cone (adj : α → α → Prop) (A : ℕ → Kernel α)
    {a err rho0 rhoMax : ℝ} (ha : 0 ≤ a) (herr : 0 ≤ err)
    (hrho0 : 1 ≤ rho0) (R : ℕ) (horizon : rho0 + R * a * err ≤ rhoMax)
    (hbirth : ∀ s rho h, rho0 ≤ rho → rho ≤ rhoMax → (∀ x, 0 ≤ h x) → Cone adj rho h →
      ∀ x y, adj x y → action (A s) h y ≤ rho * action (A s) h x + err * h x)
    (s : ℕ) :
    Cone adj (rho0 + R * a * err) (value A a s R) := by
  induction R generalizing s with
  | zero =>
    intro x y _
    simpa [value] using hrho0
  | succ R ih =>
    have hR : rho0 + R * a * err ≤ rhoMax := by
      have hnonneg := mul_nonneg ha herr
      norm_num only [Nat.cast_add, Nat.cast_one] at horizon
      nlinarith
    have hcone := ih hR (s + 1)
    have hlo : rho0 ≤ rho0 + R * a * err := by
      have hnonneg := mul_nonneg (Nat.cast_nonneg R : (0 : ℝ) ≤ R) (mul_nonneg ha herr)
      nlinarith
    have hc := cone_step adj (A s) (value A a (s + 1) R) ha herr
      (value_nonneg A ha (s + 1) R) hcone
      (hbirth s _ _ hlo hR (value_nonneg A ha (s + 1) R) hcone)
    convert hc using 1
    · norm_num only [Nat.cast_add, Nat.cast_one]
      ring
    · rfl

end
end Lax343628Proofs.ReproductiveValues

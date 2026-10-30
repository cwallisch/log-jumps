import Lax343628Proofs.PhysicalOffspring
import Lax343628Proofs.FiniteComparison
import Lax343628Proofs.Genotypes
import Lax343628Proofs.ReproductiveValues

namespace Lax343628Proofs.ColumnKernels

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.PhysicalOffspring Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

abbrev ColumnClass (n k : ℕ) (i : Fin n) (b : Fin 2) :=
  {x : BitString n // (zeros x).card = k ∧ x i = b}

def classFactor {n : ℕ} (i : Fin n) (b : Fin 2) (partner : BitString n) : ℝ :=
  if b = partner i then 1 else 2

lemma classFactor_bounds {n : ℕ} (i : Fin n) (b : Fin 2) (partner : BitString n) :
    0 ≤ classFactor i b partner ∧ classFactor i b partner ≤ 2 := by
  unfold classFactor
  split_ifs <;> norm_num

def kernel {n k : ℕ} {i : Fin n} {b : Fin 2} (source : ColumnClass n k i b)
    (partner : BitString n) (child : ColumnClass n k i b) : ℝ :=
  classFactor i b partner * (pairMutation source.val partner (1 / n) child.val).toReal

lemma kernel_nonneg {n k : ℕ} {i : Fin n} {b : Fin 2} (source : ColumnClass n k i b)
    (partner : BitString n) (child : ColumnClass n k i b) : 0 ≤ kernel source partner child :=
  mul_nonneg (classFactor_bounds i b partner).1 ENNReal.toReal_nonneg

lemma pairMutation_eval {n : ℕ} (x y : BitString n) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) (i : Fin n) :
    (pairMutation x y p).map (fun child ↦ child i) = siteLaw (x i) (y i) p := by
  rw [pairMutation_eq_product x y p hp, Lax343628Proofs.BitProduct.product_eval]

lemma pairMutation_class_mass {n : ℕ} (x y : BitString n) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) (i : Fin n) (b : Fin 2) :
    mean (pairMutation x y p) (fun child ↦ if child i = b then 1 else 0) =
      (siteLaw (x i) (y i) p b).toReal := by
  have h := mean_map (pairMutation x y p) (fun child ↦ child i)
    (fun z ↦ if z = b then 1 else 0)
  rw [pairMutation_eval x y p hp i, mean_pick, mul_one] at h
  exact h.symm

lemma kernel_mass_le_one {n k : ℕ} {i : Fin n} {b : Fin 2}
    (source : ColumnClass n k i b) (partner : BitString n) :
    (∑ child, kernel source partner child) ≤ 1 := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) ≤ 1 / n ∧ 1 / (n : ℝ) ≤ 1 := ⟨by positivity, by
    exact (div_le_one (by positivity : (0 : ℝ) < n)).mpr hnR⟩
  have hsum := injective_sum_le_indicator (pairMutation source.val partner (1 / n))
    (fun child : ColumnClass n k i b ↦ child.val) Subtype.val_injective
    (fun child ↦ child i = b) (fun child ↦ child.property.2)
  have hm := pairMutation_class_mass source.val partner (1 / n) hp i b
  simp only [kernel, ← Finset.mul_sum]
  by_cases hsame : b = partner i
  · simp only [classFactor, if_pos hsame, one_mul]
    exact hsum.trans ((mean_mono _ (fun child : BitString n ↦ show (if child i = b then (1 : ℝ) else 0) ≤ 1 by
      split_ifs <;> norm_num)).trans_eq (mean_const _ 1))
  · have hdiff : source.val i ≠ partner i := by rw [source.property.2]; exact hsame
    rw [siteLaw_different _ _ hdiff _ hp] at hm
    have hcoin : (coin (1 / 2) b).toReal = (1 / 2 : ℝ) := by
      fin_cases b <;> norm_num [coin]
    rw [hcoin] at hm
    simp only [classFactor, if_neg hsame]
    linarith

def action {n k : ℕ} {i : Fin n} {b : Fin 2} (partner : BitString n)
    (h : ColumnClass n k i b → ℝ) (source : ColumnClass n k i b) : ℝ :=
  ∑ child, kernel source partner child * h child

def liftClass {n k : ℕ} {i : Fin n} {b : Fin 2}
    (h : ColumnClass n k i b → ℝ) (x : BitString n) : ℝ :=
  if hx : (zeros x).card = k ∧ x i = b then h ⟨x, hx⟩ else 0

lemma liftClass_self {n k : ℕ} {i : Fin n} {b : Fin 2}
    (h : ColumnClass n k i b → ℝ) (x : ColumnClass n k i b) : liftClass h x.val = h x := by
  simp [liftClass, x.property]

lemma mean_liftClass {n k : ℕ} {i : Fin n} {b : Fin 2}
    (h : ColumnClass n k i b → ℝ) (p : PMF (BitString n)) :
    mean p (liftClass h) = ∑ child : ColumnClass n k i b, (p child.val).toReal * h child := by
  have hs := Finset.sum_subtype (F := inferInstance)
    (Finset.univ.filter (fun x : BitString n ↦ (zeros x).card = k ∧ x i = b))
    (by simp : ∀ x : BitString n,
      x ∈ Finset.univ.filter (fun x : BitString n ↦ (zeros x).card = k ∧ x i = b) ↔
        (zeros x).card = k ∧ x i = b)
    (fun x : BitString n ↦ (p x).toReal * liftClass h x)
  simp only [liftClass_self] at hs
  rw [← hs]
  unfold mean
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : (zeros x).card = k ∧ x i = b
  · rw [if_pos hx]
  · simp only [liftClass, dif_neg hx, mul_zero, if_neg hx]

lemma action_eq_mean {n k : ℕ} {i : Fin n} {b : Fin 2} (partner : BitString n)
    (h : ColumnClass n k i b → ℝ) (source : ColumnClass n k i b) :
    action partner h source = classFactor i b partner *
      mean (pairMutation source.val partner (1 / n)) (liftClass h) := by
  rw [mean_liftClass, action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro child _
  unfold kernel
  ring

lemma action_nonneg {n k : ℕ} {i : Fin n} {b : Fin 2} (partner : BitString n)
    (h : ColumnClass n k i b → ℝ) (hh : ∀ child, 0 ≤ h child) (source : ColumnClass n k i b) :
    0 ≤ action partner h source :=
  Finset.sum_nonneg (fun child _ ↦ mul_nonneg (kernel_nonneg _ _ _) (hh child))

lemma action_le {n k : ℕ} {i : Fin n} {b : Fin 2} (partner : BitString n)
    (h : ColumnClass n k i b → ℝ) (M : ℝ) (hM : 0 ≤ M) (hh : ∀ child, h child ≤ M)
    (source : ColumnClass n k i b) : action partner h source ≤ M := by
  calc
    _ ≤ ∑ child, kernel source partner child * M :=
      Finset.sum_le_sum (fun child _ ↦ mul_le_mul_of_nonneg_left (hh child) (kernel_nonneg _ _ _))
    _ = (∑ child, kernel source partner child) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right (kernel_mass_le_one source partner) hM
    _ = M := one_mul M

def mixedKernel {n k : ℕ} {i : Fin n} {b : Fin 2} (partners : PMF (BitString n)) :
    ReproductiveValues.Kernel (ColumnClass n k i b) where
  mass source child := mean partners (fun partner ↦ kernel source partner child)
  nonneg source child := mean_nonneg partners (fun partner ↦ kernel_nonneg source partner child)
  row_le source := by
    have hs : (∑ child : ColumnClass n k i b,
        mean partners (fun partner ↦ kernel source partner child)) =
        mean partners (fun partner ↦ ∑ child : ColumnClass n k i b, kernel source partner child) := by
      unfold mean
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    rw [hs]
    exact (mean_mono partners (kernel_mass_le_one source)).trans_eq (mean_const partners 1)

lemma mixed_action {n k : ℕ} {i : Fin n} {b : Fin 2} (partners : PMF (BitString n))
    (h : ColumnClass n k i b → ℝ) (source : ColumnClass n k i b) :
    ReproductiveValues.action (mixedKernel partners) h source =
      mean partners (fun partner ↦ action partner h source) := by
  unfold ReproductiveValues.action mixedKernel action mean
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro partner _
  apply Finset.sum_congr rfl
  intro child _
  ring

end
end Lax343628Proofs.ColumnKernels

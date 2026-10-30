import Lax343628Proofs.SwapMutation
import Lax343628Proofs.SeedDrift

namespace Lax343628Proofs.SeedFounding

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.SeedGeometry Lax343628Proofs.SwapMutation
open Lax343628Proofs.ColumnKernels Lax343628Proofs.SeedIdeal Lax343628Proofs.SeedMutation
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+} {i : Fin n}

lemma family_indicator (C : Finset (Fin n)) (z : BitString n) :
    liftClass (familyClass (r := r) (i := i) C) z =
      if (zeros z).card = r + 1 ∧ family C i z then 1 else 0 := by
  unfold liftClass familyClass family
  split_ifs <;> simp_all

lemma clone_lower (hn : 2 ≤ n) (hlarge : 2 * (r + 1) ≤ n)
    (C : Finset (Fin n)) (hi : i ∈ C) (x : BitString n)
    (hx : (zeros x).card = r + 1) (hCx : ordinary C x) :
    1 / (16 * (n : ℝ)) ≤ mean (pairMutation x x (1 / n))
      (liftClass (familyClass (r := r) (i := i) C)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hp : (0 : ℝ) ≤ 1 / n ∧ 1 / (n : ℝ) ≤ 1 :=
    ⟨by positivity, (div_le_one hnpos).mpr (by linarith)⟩
  have hxi := hCx hi
  let G := {g : Fin n // g ∉ zeros x}
  let e : G → BitString n := fun g ↦ swapZero x i g.val
  have he : Function.Injective e := by
    intro g h hh
    exact Subtype.ext (swap_injective x i g.property h.property hh)
  have hsum := injective_sum_le_indicator (pairMutation x x (1 / n)) e he
    (fun z ↦ (zeros z).card = r + 1 ∧ family C i z)
    (fun g ↦ ⟨swap_card x hx i g hxi g.property, swap_family C x i g hCx hi g.property⟩)
  have hconst (g : G) : (pairMutation x x (1 / n) (e g)).toReal =
      (1 / (n : ℝ)) ^ 2 * (1 - 1 / (n : ℝ)) ^ (n - 2) :=
    swap_probability x i g hxi g.property _ hp
  have hcard : Fintype.card G = n - (r + 1) := by
    change Fintype.card {g : Fin n // g ∉ zeros x} = _
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hx]
  simp_rw [hconst] at hsum
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] at hsum
  have hpow : (1 / 8 : ℝ) ≤ (1 - 1 / (n : ℝ)) ^ (n - 2) :=
    (ElementaryBounds.no_mutation_lower n hn).trans
      (pow_le_pow_of_le_one (sub_nonneg.mpr hp.2) (by linarith) (Nat.sub_le n 2))
  have hnk : (n : ℝ) / 2 ≤ (n - (r + 1) : ℕ) := by
    rw [Nat.cast_sub (by omega : r + 1 ≤ n)]
    have hh : 2 * (r + 1 : ℝ) ≤ n := by exact_mod_cast hlarge
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hprod := mul_le_mul hnk hpow (by norm_num : (0 : ℝ) ≤ 1 / 8) (by positivity)
  have hscale := mul_le_mul_of_nonneg_right hprod (sq_nonneg (1 / (n : ℝ)))
  have hlo : 1 / (16 * (n : ℝ)) ≤
      (n - (r + 1) : ℕ) * (1 / (n : ℝ)) ^ 2 * (1 - 1 / (n : ℝ)) ^ (n - 2) := by
    calc
      _ = (n : ℝ) / 2 * (1 / 8) * (1 / (n : ℝ)) ^ 2 := by
        field_simp; ring
      _ ≤ _ := hscale
      _ = _ := by ring
  have hf : liftClass (familyClass (r := r) (i := i) C) =
      (fun z ↦ if (zeros z).card = r + 1 ∧ family C i z then (1 : ℝ) else 0) :=
    funext (family_indicator C)
  rw [hf]
  apply hlo.trans
  simpa only [mul_assoc] using hsum

lemma crossover_lower (hn : 2 ≤ n) (hlarge : 2 * (r + 1) ≤ n)
    (C : Finset (Fin n)) (hi : i ∈ C) (P : Population n mu)
    (hP : ∀ u, (zeros (P u)).card = r + 1) :
    (1 - rho C P) * ((1 / 4 : ℝ) ^ (r + 1) / (16 * n)) ≤
      mean (offspring 1 P) (liftClass (familyClass (r := r) (i := i) C)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) ≤ 1 / n ∧ 1 / (n : ℝ) ≤ 1 :=
    ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  let ψ := liftClass (familyClass (r := r) (i := i) C)
  let b : ℝ := (1 / 4 : ℝ) ^ (r + 1) / (16 * n)
  have hpair (u v : Fin (mu : ℕ)) :
      (if ordinary C (P u) then b else 0) ≤ mean (pairMutation (P u) (P v) (1 / n)) ψ := by
    by_cases hu : ordinary C (P u)
    · rw [if_pos hu]
      have hc := mul_le_mul_of_nonneg_left (clone_lower hn hlarge C hi (P u) (hP u) hu)
        (show 0 ≤ (1 / 4 : ℝ) ^ (r + 1) by positivity)
      have hd := PairCloneLower.mean_lower (P u) (P v) (hP u) (hP v) (1 / n) hp ψ
        (fun z ↦ (family_bounds C z).1)
      apply le_trans _ hd
      convert hc using 1; first | rfl | ring
    · rw [if_neg hu]
      exact mean_nonneg _ (fun z ↦ (family_bounds C z).1)
  have hinner (u : Fin (mu : ℕ)) := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) (hpair u)
  simp only [mean_const] at hinner
  have hh := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) hinner
  rw [SeedViability.crossover_mean]
  change (1 - rho C P) * b ≤ _
  have heq : (fun u ↦ if ordinary C (P u) then b else 0) =
      (fun u ↦ b * (if ordinary C (P u) then 1 else 0)) := by funext u; split_ifs <;> ring
  rw [heq, mean_mul, ordinary_mean] at hh
  simpa only [mul_comm, EmpiricalKernels.pairMean, ψ] using hh

lemma offspring_lower (hn : 2 ≤ n) (hlarge : 2 * (r + 1) ≤ n)
    (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (C : Finset (Fin n)) (hi : i ∈ C) (P : Population n mu)
    (hP : ∀ u, (zeros (P u)).card = r + 1) (hrho : rho C P ≤ 1 / 4) :
    pc * (1 / 4 : ℝ) ^ (r + 1) / (32 * n) ≤
      mean (offspring pc P) (liftClass (familyClass (r := r) (i := i) C)) := by
  have hc := mul_le_mul_of_nonneg_left (crossover_lower hn hlarge C hi P hP) hpc.1
  have hnon : 0 ≤ (1 - pc) * mean (offspring 0 P) (liftClass (familyClass (r := r) (i := i) C)) :=
    mul_nonneg (sub_nonneg.mpr hpc.2) (mean_nonneg _ (fun z ↦ (family_bounds C z).1))
  have hlo : pc * (1 / 4 : ℝ) ^ (r + 1) / (32 * n) ≤
      pc * ((1 - rho C P) * ((1 / 4 : ℝ) ^ (r + 1) / (16 * n))) := by
    have hmul := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 - rho C P by linarith)
      (mul_nonneg hpc.1 (show 0 ≤ (1 / 4 : ℝ) ^ (r + 1) / (16 * n) by positivity))
    convert hmul using 1 <;> first | rfl | ring
  rw [offspring_affine pc hpc]
  linarith

lemma zero_drift (hn : 2 ≤ n) (hlarge : 2 * (r + 1) ≤ n)
    (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (C : Finset (Fin n)) (hi : i ∈ C) (P : Population n mu)
    (hP : ∀ u, (zeros (P u)).card = r + 1) (hrho : rho C P ≤ 1 / 4)
    (hzero : phi C i P = 0) :
    pc * (1 / 4 : ℝ) ^ (r + 1) / (64 * n) ≤ mean (TaggedDynamics.eventLaw pc P)
      (ClassIncrements.change (r + 1) (liftClass (familyClass (r := r) (i := i) C)) P) := by
  have hkn : r + 1 ≤ n := by omega
  have hp : PlateauDynamics.plateauPopulation (r + 1) P := fun u ↦
    PlateauKernelApproximation.plateau_of_zero_card hkn _ (hP u)
  have hm := ClassMeanDynamics.full_mean hkn pc P hp
    (liftClass (familyClass (r := r) (i := i) C)) (SparseDynamics.lift_off_plateau hkn _)
  rw [family_average C P hP, hzero, mul_zero, sub_zero] at hm
  have hb := offspring_lower hn hlarge pc hpc C hi P hP hrho
  have hscaled := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (mu : ℕ))
  have hmR : (1 : ℝ) ≤ (mu : ℕ) := by exact_mod_cast mu.pos
  have heq : pc * (1 / 4 : ℝ) ^ (r + 1) / (32 * n) =
      2 * (pc * (1 / 4 : ℝ) ^ (r + 1) / (64 * n)) := by field_simp; ring
  rw [heq] at hscaled
  have hnon : 0 ≤ pc * (1 / 4 : ℝ) ^ (r + 1) / (64 * n) :=
    div_nonneg (mul_nonneg hpc.1 (by positivity)) (by positivity)
  apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (mu : ℕ) + 1)).mp
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ ((mu : ℕ) : ℝ) - 1 by linarith) hnon]

end
end Lax343628Proofs.SeedFounding

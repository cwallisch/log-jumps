import Lax343628Proofs.OrdinaryBirth
import Lax343628Proofs.RuntimeInvariant
import Lax343628Proofs.RuntimeTail
import Lax343628Proofs.Plateau
import Lax343628Proofs.PlateauDynamics

namespace Lax343628Proofs.SingleJump

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.Dynamics
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison Lax343628Proofs.FiniteChain
open Lax343628Proofs.PlateauDynamics
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {mu : ℕ+}

lemma offspring (hn : 2 ≤ n) (pc : ℝ) (hpc : 0 < pc ∧ pc ≤ 1)
    (P : Population n mu) (hP : plateauPopulation 1 P) :
    pc / (64 * n) ≤ (Sampling.offspring pc P (optimum n)).toReal := by
  have hones : ∀ u, ones (P u) = n - 1 := hP
  have htest : OrdinaryBirth.test (n - 1) n = (fun z : BitString n ↦ if z = optimum n then 1 else 0) := by
    funext z
    unfold OrdinaryBirth.test
    have hiff : n - 1 < ones z ∧ ones z ≤ n ↔ ones z = n := by have := ones_le z; omega
    simp only [hiff, ones_eq_iff]
  have ha : OrdinaryBirth.above (n - 1) P = 0 := by
    simp only [OrdinaryBirth.above, hones, lt_self_iff_false, Finset.filter_false, Finset.card_empty]
  have hz : n - (n - 1) = 1 := by omega
  have hh := OrdinaryBirth.near hn (by omega : n - 1 < n) le_rfl pc ⟨hpc.1.le, hpc.2⟩ P
    (fun u ↦ ⟨(hones u).ge, by rw [hones]; omega⟩)
  rw [htest, mean_pick, mul_one, ha, hz] at hh
  norm_num only [Nat.cast_zero, zero_div, zero_add, pow_one, Nat.cast_one] at hh
  linear_combination hh

lemma failure (hn : 2 ≤ n) (pc : ℝ) (hpc : 0 < pc ∧ pc ≤ 1)
    (P : Population n mu) (hP : plateauPopulation 1 P) :
    (step (jump 1) pc P).toOuterMeasure missing ≤ 1 - ENNReal.ofReal (pc / (64 * n)) := by
  have hchild := (ENNReal.ofReal_le_ofReal (offspring hn pc hpc P hP)).trans_eq
    (ENNReal.ofReal_toReal ((Sampling.offspring pc P).apply_ne_top _))
  have hs := hchild.trans (Plateau.offspring_le_success (by norm_num : 0 < (1 : ℕ)) pc P)
  apply ENNReal.le_sub_of_add_le_right (by simp)
  exact (add_le_add le_rfl hs).trans_eq (event_add_compl _ missing)

lemma runtime (hn : 2 ≤ n) (pc : ℝ) (hpc : 0 < pc ∧ pc ≤ 1)
    (P : Population n mu) (hP : plateauPopulation 1 P) :
    (∑' t, (law (step (jump 1) pc) (PMF.pure P) t).toOuterMeasure missing) ≤ ENNReal.ofReal (64 * n / pc) := by
  let K := step (jump 1) pc (n := n) (μ := mu)
  let I : Set (Population n mu) := {P | plateauPopulation 1 P ∨ P ∉ missing}
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hW : 1 ≤ 64 * (n : ℝ) / pc := (le_div_iff₀ hpc.1).mpr (by linarith [hpc.2])
  have hinit : ∀ Q ∈ (PMF.pure P).support, Q ∈ I := by
    intro Q hQ
    have heq := (PMF.mem_support_pure_iff _ _).mp hQ
    exact Or.inl (heq ▸ hP)
  have hInv : ∀ Q ∈ I, ∀ R ∈ (K Q).support, R ∈ I := by
    intro Q hQ R hR
    by_cases hm : R ∈ missing
    · rcases hQ with hpl | hopt
      · exact Or.inl (plateau_step_invariant (by norm_num) (by omega : 1 ≤ n) pc Q hpl R hR hm)
      · exact False.elim (step_retains_optimum (by norm_num) pc Q hopt R hR hm)
    · exact Or.inr hm
  apply RuntimeInvariant.escape K (PMF.pure P) I missing hinit hInv (step_missing_eq_zero (by norm_num) pc) _ hW
  intro Q hQ
  have hpl : plateauPopulation 1 Q := hQ.1.resolve_right (not_not.mpr hQ.2)
  have heq : 1 / (64 * (n : ℝ) / pc) = pc / (64 * n) := by field_simp
  rw [heq]
  exact failure hn pc hpc Q hpl

def length (n : ℕ) (pc : ℝ) : ℕ := Nat.ceil (512 * n / pc)

lemma block (hn : 2 ≤ n) (pc : ℝ) (hpc : 0 < pc ∧ pc ≤ 1)
    (P : Population n mu) (hP : plateauPopulation 1 P) :
    (law (step (jump 1) pc) (PMF.pure P) (length n pc)).toOuterMeasure missing ≤ ENNReal.ofReal (1 / 8) := by
  have hpp := hpc.1
  have hh := RuntimeTail.antitone_tail _
    (event_law_antitone (step (jump 1) pc) (PMF.pure P) missing (step_missing_eq_zero (by norm_num) pc))
    (64 * n / pc) (by positivity) (runtime hn pc hpc P hP) (length n pc)
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (length n pc : ℝ) + 1)).mpr
  have hc : 512 * (n : ℝ) / pc ≤ (length n pc : ℝ) := Nat.le_ceil _
  linear_combination hc / 8

lemma length_pos (hn : 2 ≤ n) (pc : ℝ) (hp : 0 < pc) : 0 < length n pc := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh : (0 : ℝ) < length n pc := (by positivity : (0 : ℝ) < 512 * n / pc).trans_le (Nat.le_ceil _)
  exact_mod_cast hh

lemma time (hn : 2 ≤ n) (pc : ℝ) (hp : 0 < pc ∧ pc ≤ 1) (mu : ℕ+) :
    (length n pc : ℝ) ≤ (1024 / pc) * (mu : ℕ) * (n : ℝ) := by
  have hpp := hp.1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (1 : ℝ) ≤ (mu : ℕ) := by exact_mod_cast mu.pos
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 512 * (n : ℝ) / pc by positivity)).le
  change (length n pc : ℝ) ≤ _ at hc
  have h1 : pc ≤ (n : ℝ) := by linarith [hp.2]
  have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ (n : ℝ) by positivity)
  have hc' := mul_le_mul_of_nonneg_right hc hp.1.le
  have heq : (512 * (n : ℝ) / pc + 1) * pc = 512 * n + pc := by field_simp
  rw [heq] at hc'
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ hp.1).mpr
  nlinarith

end
end Lax343628Proofs.SingleJump

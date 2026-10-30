import Lax343628Proofs.OneBitMutation
import Lax343628Proofs.FarBirth
import Lax343628Proofs.PairCloneLower

namespace Lax343628Proofs.OrdinaryBirth

open Lax343628.Algorithm Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.Sampling Lax343628Proofs.PhysicalOffspring Lax343628Proofs.EmpiricalKernels
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n i b : ℕ} {mu : ℕ+}

def test (i b : ℕ) (z : BitString n) : ℝ := if i < ones z ∧ ones z ≤ b then 1 else 0
def above (i : ℕ) (P : Population n mu) : ℕ := (Finset.univ.filter (fun u ↦ i < ones (P u))).card

lemma test_nonneg (i b : ℕ) (z : BitString n) : 0 ≤ test i b z := by unfold test; split_ifs <;> norm_num

lemma self_retention (hn : 2 ≤ n) (x : BitString n) : test i b x / 8 ≤ mean (pairMutation x x (1 / n)) (test i b) := by
  have hh := MutationLower.standard hn x x (test i b) (test_nonneg i b)
  rw [pairMutation_self, CrossoverCount.zero_mutation, PMF.pure_map, mutate_zero, mean_pure] at hh
  exact hh

lemma self_lower (hn : 2 ≤ n) (hib : i < b) (_hbn : b ≤ n) (x : BitString n)
    (hx : i ≤ ones x ∧ ones x ≤ b) :
    ((if i < ones x then (1 : ℝ) else 0) + ((n - i : ℕ) : ℝ) / n) / 16 ≤
      mean (pairMutation x x (1 / n)) (test i b) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hgamma : 0 ≤ ((n - i : ℕ) : ℝ) / n ∧ ((n - i : ℕ) : ℝ) / n ≤ 1 :=
    ⟨by positivity, (div_le_one hnR).mpr (by exact_mod_cast Nat.sub_le n i)⟩
  by_cases hgood : i < ones x
  · have hh := self_retention (i := i) (b := b) hn x
    simp only [test, if_pos (show i < ones x ∧ ones x ≤ b from ⟨hgood, hx.2⟩), if_pos hgood] at hh ⊢
    linarith
  · have heq : ones x = i := by omega
    have hh := OneBitMutation.ordinary hn i b hib x heq
    change ((n - i : ℕ) : ℝ) / (8 * n) ≤ mean (pairMutation x x (1 / n)) (test i b) at hh
    rw [if_neg hgood]
    norm_num only [zero_add]
    have hrel : (((n - i : ℕ) : ℝ) / n) / 16 ≤ ((n - i : ℕ) : ℝ) / (8 * n) := by
      rw [div_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    exact hrel.trans hh

lemma near_pair (hn : 2 ≤ n) (hib : i < b) (hbn : b ≤ n) (x y : BitString n)
    (hx : i ≤ ones x ∧ ones x ≤ b) (hy : i ≤ ones y ∧ ones y ≤ b) :
    ((1 / 4 : ℝ) ^ (n - i) / 16) * ((if i < ones x then 1 else 0) + ((n - i : ℕ) : ℝ) / n) ≤
      mean (pairMutation x y (1 / n)) (test i b) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1 :=
    ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  have hcard : (Finset.univ.filter (fun j ↦ x j ≠ y j)).card ≤ 2 * (n - i) := by
    rw [← CrossoverCount.differing_set]
    have hh := CrossoverCount.differing_le x y
    omega
  have hclone := PairCloneLower.mean_lower_of_card x y hcard (1 / n) hp (test i b) (test_nonneg i b)
  have hself := mul_le_mul_of_nonneg_left (self_lower hn hib hbn x hx)
    (show 0 ≤ (1 / 4 : ℝ) ^ (n - i) by positivity)
  apply le_trans _ (hself.trans hclone)
  ring_nf
  exact le_rfl

lemma far_pair {k : ℕ} (hn : 2 ≤ n) (hkn : k ≤ n) (hfar : 16 * (k + 1) ≤ n - k - i)
    (x y : BitString n) (hx : i ≤ ones x ∧ ones x ≤ n - k)
    (hy : i ≤ ones y ∧ ones y ≤ n - k) :
    (1 / 128 : ℝ) * ((if i < ones x then 1 else 0) + ((n - i : ℕ) : ℝ) / n) ≤
      mean (pairMutation x y (1 / n)) (test i (n - k)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hgamma : ((n - i : ℕ) : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast Nat.sub_le n i)
  by_cases hxy : x = y
  · subst y
    have hh := self_lower hn (by omega : i < n - k) (Nat.sub_le n k) x hx
    have hI : (0 : ℝ) ≤ if i < ones x then 1 else 0 := by split_ifs <;> norm_num
    have hgamma0 : (0 : ℝ) ≤ ((n - i : ℕ) : ℝ) / n := by positivity
    linarith
  · have hh := FarBirth.standard hn hkn hfar x y hx hy hxy
    have hI : (if i < ones x then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    change (1 / 64 : ℝ) ≤ mean (pairMutation x y (1 / n)) (test i (n - k)) at hh
    linarith

lemma mean_above (i : ℕ) (P : Population n mu) :
    mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun u ↦ if i < ones (P u) then 1 else 0) =
      (above i P : ℝ) / (mu : ℕ) := by
  rw [Deletion.uniform_mean, Fintype.card_fin]
  unfold above
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma average (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (c : ℝ) (_hc : 0 ≤ c)
    (P : Population n mu)
    (hpair : ∀ u v, c * ((if i < ones (P u) then 1 else 0) + ((n - i : ℕ) : ℝ) / n) ≤
      mean (pairMutation (P u) (P v) (1 / n)) (test i b)) :
    pc * c * ((above i P : ℝ) / (mu : ℕ) + ((n - i : ℕ) : ℝ) / n) ≤
      mean (offspring pc P) (test i b) := by
  have hh := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ) × Fin (mu : ℕ))) (fun uv ↦ hpair uv.1 uv.2)
  have hfirst : mean (PMF.uniformOfFintype (Fin (mu : ℕ) × Fin (mu : ℕ)))
      (fun uv ↦ if i < ones (P uv.1) then (1 : ℝ) else 0) = (above i P : ℝ) / (mu : ℕ) := by
    have hf := mean_uniform_pair (fun (u _v : Fin (mu : ℕ)) ↦ if i < ones (P u) then (1 : ℝ) else 0)
    simp only [mean_const] at hf
    exact hf.trans (mean_above i P)
  rw [mean_mul, mean_add, mean_const, hfirst] at hh
  rw [offspring_split, mean_bind, mean_coin pc hpc]
  simp only [if_true, Fin.zero_ne_one, if_false, mean_bind]
  have hclone : 0 ≤ mean (PMF.uniformOfFintype (Fin (mu : ℕ)))
      (fun u ↦ mean (pairMutation (P u) (P u) (1 / n)) (test i b)) :=
    mean_nonneg _ (fun u ↦ mean_nonneg _ (test_nonneg i b))
  have hscale := mul_le_mul_of_nonneg_left hh hpc.1
  have hrest := mul_nonneg (sub_nonneg.mpr hpc.2) hclone
  nlinarith

lemma far {k : ℕ} (hn : 2 ≤ n) (hkn : k ≤ n) (hfar : 16 * (k + 1) ≤ n - k - i)
    (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (P : Population n mu)
    (hP : ∀ u, i ≤ ones (P u) ∧ ones (P u) ≤ n - k) :
    (pc / 128) * ((above i P : ℝ) / (mu : ℕ) + ((n - i : ℕ) : ℝ) / n) ≤
      mean (offspring pc P) (test i (n - k)) := by
  have hh := average pc hpc (1 / 128) (by norm_num) P
    (fun u v ↦ far_pair hn hkn hfar (P u) (P v) (hP u) (hP v))
  simpa only [div_eq_mul_inv, one_mul] using hh

lemma near (hn : 2 ≤ n) (hib : i < b) (hbn : b ≤ n)
    (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (P : Population n mu)
    (hP : ∀ u, i ≤ ones (P u) ∧ ones (P u) ≤ b) :
    (pc * (1 / 4 : ℝ) ^ (n - i) / 16) *
      ((above i P : ℝ) / (mu : ℕ) + ((n - i : ℕ) : ℝ) / n) ≤ mean (offspring pc P) (test i b) := by
  have hh := average pc hpc ((1 / 4 : ℝ) ^ (n - i) / 16) (by positivity) P
    (fun u v ↦ near_pair hn hib hbn (P u) (P v) (hP u) (hP v))
  simpa only [mul_div_assoc] using hh

end
end Lax343628Proofs.OrdinaryBirth

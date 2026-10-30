import Lax343628Proofs.NearLevelCosts

namespace Lax343628Proofs.FarLevelCosts

open Lax343628Proofs.ArrivalRanks Lax343628Proofs.LevelCosts
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def levels (n k : ℕ) : Finset (Fin n) := Finset.univ.filter
  (fun v ↦ k ≤ v.val ∧ 16 * (k + 1) ≤ n - k - (v.val - k))

def index (n k : ℕ) (v : Fin n) : Fin n :=
  ⟨if k ≤ v.val then n - (v.val - k) - 1 else 0, by have := v.isLt; split_ifs <;> omega⟩

lemma index_value {n k : ℕ} (v : Fin n) (hv : k ≤ v.val) : (index n k v).val + 1 = n - (v.val - k) := by
  simp only [index, if_pos hv]
  have := v.isLt
  omega

lemma index_injective {n k : ℕ} : Set.InjOn (index n k) {v : Fin n | k ≤ v.val} := by
  intro v hv w hw hh
  change k ≤ v.val at hv
  change k ≤ w.val at hw
  have heq := congrArg Fin.val hh
  have hvv := index_value v hv
  have hww := index_value w hw
  have hnv := v.isLt
  have hnw := w.isLt
  apply Fin.ext
  omega

lemma sum_bound (n k : ℕ) (mu : ℕ+) (hn : 1 ≤ n) :
    (∑ v ∈ levels n k, ordinary n (n - (v.val - k)) mu) ≤
      (n : ℝ) * (1 + Real.log n) + 4 * (mu : ℕ) * n := by
  let f : Fin n → ℝ := fun j ↦ ordinary n (j.val + 1) mu
  have hinj : Set.InjOn (index n k) (levels n k) := by
    intro v hv w hw hh
    exact index_injective (Finset.mem_filter.mp hv).2.1 (Finset.mem_filter.mp hw).2.1 hh
  have heq : (∑ v ∈ levels n k, ordinary n (n - (v.val - k)) mu) =
      ∑ j ∈ (levels n k).image (index n k), f j := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro v hv
    unfold f
    rw [index_value v (Finset.mem_filter.mp hv).2.1]
  rw [heq]
  apply (Finset.sum_le_univ_sum_of_nonneg (fun j ↦ show 0 ≤ f j by unfold f ordinary; positivity)).trans
  have heq' : (∑ j : Fin n, f j) = ∑ j ∈ Finset.range n, ordinary n (j + 1) mu := by
    exact Fin.sum_univ_eq_sum_range (fun j ↦ ordinary n (j + 1) mu) n
  rw [heq']
  exact sum_ordinary n mu hn

lemma bound (n k : ℕ) (mu : ℕ+) (pc : ℝ) (hp : 0 < pc) (hn : 1 ≤ n) :
    (∑ v ∈ levels n k, ∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) ≤
      (128 / pc) * ((n : ℝ) * (1 + Real.log n) + 4 * (mu : ℕ) * n) := by
  have hpoint (v : Fin n) (hv : v ∈ levels n k) :
      (∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) ≤
        (128 / pc) * ordinary n (n - (v.val - k)) mu := by
    have hvc := (Finset.mem_filter.mp hv).2
    have hh := ordinary_level n k mu pc hp v hvc.1
    simpa only [coefficient, if_pos hvc.2, one_div_div] using hh
  have hh := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (sum_bound n k mu hn) (by positivity : (0 : ℝ) ≤ 128 / pc))

def valley (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun v ↦ v.val < k)

lemma valley_bound (n k : ℕ) (mu : ℕ+) (pc : ℝ) (hp : 0 < pc) :
    (∑ v ∈ valley n k, ∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) ≤
      (32 / pc) * (mu : ℕ) * (n : ℝ) := by
  have heq : (∑ v ∈ valley n k, ∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) =
      ((valley n k).card : ℝ) * ((mu : ℕ) * (32 / pc)) := by
    calc
      _ = ∑ _v ∈ valley n k, ((mu : ℕ) : ℝ) * (32 / pc) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact valley_level n k mu pc v (Finset.mem_filter.mp hv).2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((valley n k).card : ℝ) ≤ n := by
    have hh := Finset.card_le_univ (valley n k)
    rw [Fintype.card_fin] at hh
    exact_mod_cast hh
  rw [heq]
  have hh := mul_le_mul_of_nonneg_right hcard (show (0 : ℝ) ≤ (mu : ℕ) * (32 / pc) by positivity)
  apply hh.trans_eq
  ring

lemma partition (n k : ℕ) (mu : ℕ+) (pc : ℝ) :
    (∑ v : Fin n, ∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) =
      (∑ v ∈ valley n k, ∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) +
      (∑ v ∈ levels n k, ∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) +
      (∑ v ∈ NearLevelCosts.levels n k, ∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) := by
  simp only [valley, levels, NearLevelCosts.levels, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v.val < k
  · have hkv : ¬k ≤ v.val := by omega
    simp only [hv, hkv, if_true, if_false, false_and, add_zero]
  · have hkv : k ≤ v.val := by omega
    by_cases hf : 16 * (k + 1) ≤ n - k - (v.val - k)
    all_goals simp only [hv, hkv, hf, if_true, if_false, true_and, not_true_eq_false, not_false_eq_true, zero_add, add_zero]

end
end Lax343628Proofs.FarLevelCosts

import Lax343628Proofs.SparseEnvironment

namespace Lax343628Proofs.SparseGroups

open Lax343628.Algorithm Lax343628Proofs.SparseEnvironment
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

def count (R ell : ℕ) : ℕ := R / ell + 1

def index (R H ell t : ℕ) (hH : H ≤ R) : Fin (count R ell) :=
  ⟨(H - 1 - t) / ell, Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : H - 1 - t ≤ R))⟩

def group (H ell j : ℕ) : Finset ℕ :=
  (Finset.range H).filter (fun t ↦ (H - 1 - t) / ell = j)

def groupEnd (H ell j : ℕ) : ℕ := H - j * ell

lemma group_interval (H ell j : ℕ) (hell : 1 ≤ ell) :
    group H ell j = Finset.Ico (H - (j * ell + ell)) (H - j * ell) := by
  ext t
  simp only [group, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
    Nat.div_eq_iff (by omega : 0 < ell)]
  omega

lemma mem_index_group (R H ell t : ℕ) (hH : H ≤ R) (ht : t < H) :
    t ∈ group H ell (index R H ell t hH).val := by
  simp [group, index, ht]

lemma group_member_bounds (H ell j t : ℕ) (hell : 1 ≤ ell) (ht : t ∈ group H ell j) :
    t < groupEnd H ell j ∧ groupEnd H ell j ≤ H ∧ groupEnd H ell j - t ≤ ell := by
  rw [group_interval H ell j hell] at ht
  have hh := Finset.mem_Ico.mp ht
  unfold groupEnd
  omega

lemma later_group (H ell j t : ℕ) (hell : 1 ≤ ell) (ht : t < H) (hend : groupEnd H ell j ≤ t) :
    (H - 1 - t) / ell < j := by
  rw [Nat.div_lt_iff_lt_mul (by omega : 0 < ell)]
  unfold groupEnd at hend
  omega

lemma total_group_card (R H ell : ℕ) (hH : H ≤ R) :
    ∑ j : Fin (count R ell), (group H ell j.val).card = H := by
  classical
  have heq : ∑ j : Fin (count R ell), (group H ell j.val).card =
      ∑ t ∈ Finset.range H, ∑ j : Fin (count R ell), if (H - 1 - t) / ell = j.val then 1 else 0 := by
    simp only [group, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [heq]
  have hinner (t : ℕ) : (∑ j : Fin (count R ell), if (H - 1 - t) / ell = j.val then (1 : ℕ) else 0) = 1 := by
    have heq : (fun j : Fin (count R ell) ↦ if (H - 1 - t) / ell = j.val then (1 : ℕ) else 0) =
        (fun j ↦ if j = index R H ell t hH then 1 else 0) := by
      funext j
      have hh : (H - 1 - t) / ell = j.val ↔ j = index R H ell t hH := by
        constructor
        · intro he; exact Fin.ext he.symm
        · rintro rfl; rfl
      simp only [hh]
    rw [heq]
    simp
  simp_rw [hinner]
  simp

def path {n k R ell : ℕ} {rs : ℕ+} (sigma : Net n k R (count R ell) rs) : ℕ → PMF (BitString n) :=
  fun t ↦ partnerLaw (sigma.2 (index R sigma.1.val ell t (by have := sigma.1.isLt; omega)))

lemma path_support {n k R ell : ℕ} {rs : ℕ+} (sigma : Net n k R (count R ell) rs)
    (t : ℕ) (u : BitString n) (hu : u ∈ (path sigma t).support) : (Sampling.zeros u).card = k :=
  partner_support _ u hu

end
end Lax343628Proofs.SparseGroups

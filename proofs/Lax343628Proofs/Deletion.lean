import Lax343628Proofs.Sampling
import Lax343628Proofs.FiniteDrift
import Lax343628Proofs.Species

namespace Lax343628Proofs.Deletion

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.FiniteDrift
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma uniform_mean {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    mean (PMF.uniformOfFintype α) f = (∑ x, f x) / (Fintype.card α : ℝ) := by
  unfold mean
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← Finset.mul_sum]
  ring

lemma deletion_uniform {n : ℕ} {μ : ℕ+} (fitness : BitString n → ℝ)
    (Q : Fin ((μ : ℕ) + 1) → BitString n) (value : ℝ)
    (hQ : ∀ j, fitness (Q j) = value) :
    deletionIndex fitness Q = PMF.uniformOfFintype (Fin ((μ : ℕ) + 1)) := by
  simp [deletionIndex, hQ, PMF.uniformOfFintype]

lemma deletion_unique_last {n : ℕ} {μ : ℕ+} (fitness : BitString n → ℝ)
    (P : Population n μ) (z : BitString n) (value : ℝ)
    (hP : ∀ i, fitness (P i) = value) (hz : fitness z < value) :
    deletionIndex fitness (Fin.lastCases z P) = PMF.pure (Fin.last (μ : ℕ)) := by
  have hset : (Finset.univ.filter (fun d ↦ ∀ j,
      fitness (Fin.lastCases z P d) ≤ fitness (Fin.lastCases z P j))) =
      {Fin.last (μ : ℕ)} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hd
      by_cases hold : d.val < (μ : ℕ)
      · let i : Fin (μ : ℕ) := ⟨d.val, hold⟩
        have hdEq : d = i.castSucc := Fin.ext rfl
        have hdi : Fin.lastCases z P d = P i :=
          (congrArg (Fin.lastCases z P) hdEq).trans (Fin.lastCases_castSucc i)
        have h := hd (Fin.last (μ : ℕ))
        rw [hdi, Fin.lastCases_last, hP i] at h
        exact False.elim (not_lt_of_ge h hz)
      · exact Fin.ext (by have h' := d.isLt; simp; omega)
    · intro hd j
      rw [hd, Fin.lastCases_last]
      refine Fin.lastCases ?_ (fun i ↦ ?_) j
      · simp only [Fin.lastCases_last, le_refl]
      · simpa only [Fin.lastCases_castSucc, hP i] using hz.le
  ext d
  simp only [deletionIndex, PMF.uniformOfFinset_apply, hset, Finset.mem_singleton,
    Finset.card_singleton, Nat.cast_one, inv_one, PMF.pure_apply]
  by_cases hd : d = Fin.last (μ : ℕ) <;> simp [hd]

def replace {n : ℕ} {μ : ℕ+} (P : Population n μ) (z : BitString n)
    (d : Fin ((μ : ℕ) + 1)) : Population n μ :=
  if h : d.val < (μ : ℕ) then Function.update P ⟨d.val, h⟩ z else P

def total {n : ℕ} {μ : ℕ+} (ψ : BitString n → ℝ) (P : Population n μ) : ℝ := ∑ i, ψ (P i)

lemma total_update {n : ℕ} {μ : ℕ+} (ψ : BitString n → ℝ) (P : Population n μ)
    (i : Fin (μ : ℕ)) (z : BitString n) :
    total ψ (Function.update P i z) - total ψ P = ψ z - ψ (P i) := by
  rw [total, total,
    Lax343628Proofs.Species.sum_split i (fun j ↦ ψ (Function.update P i z j)),
    Lax343628Proofs.Species.sum_split i (fun j ↦ ψ (P j)), Function.update_self]
  have heq : Lax343628Proofs.Species.offSum i (fun j ↦ ψ (Function.update P i z j)) =
      Lax343628Proofs.Species.offSum i (fun j ↦ ψ (P j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [heq]
  ring

lemma total_replace_castSucc {n : ℕ} {μ : ℕ+} (ψ : BitString n → ℝ) (P : Population n μ)
    (z : BitString n) (i : Fin (μ : ℕ)) :
    total ψ (replace P z i.castSucc) - total ψ P = ψ z - ψ (P i) := by
  have hi : i.castSucc.val < (μ : ℕ) := i.isLt
  rw [replace, dif_pos hi]
  exact total_update ψ P i z

lemma total_replace_last {n : ℕ} {μ : ℕ+} (ψ : BitString n → ℝ) (P : Population n μ)
    (z : BitString n) :
    total ψ (replace P z (Fin.last (μ : ℕ))) - total ψ P = 0 := by
  simp [replace]

lemma uniform_replacement_drift {n : ℕ} {μ : ℕ+} (ψ : BitString n → ℝ)
    (P : Population n μ) (z : BitString n) :
    mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1)))
      (fun d ↦ total ψ (replace P z d) - total ψ P) =
        ((μ : ℕ) * ψ z - total ψ P) / ((μ : ℕ) + 1) := by
  rw [uniform_mean, Fin.sum_univ_castSucc]
  simp only [total_replace_last, total_replace_castSucc, add_zero, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Nat.cast_add, Nat.cast_one, total]

lemma insert_drift_equal_fitness {n : ℕ} {μ : ℕ+} (ψ fitness : BitString n → ℝ)
    (P : Population n μ) (z : BitString n) (value : ℝ)
    (hP : ∀ i, fitness (P i) = value) (hz : fitness z = value) :
    mean (insert fitness P z) (fun Q ↦ total ψ Q - total ψ P) =
      ((μ : ℕ) * ψ z - total ψ P) / ((μ : ℕ) + 1) := by
  have hQ : ∀ j, fitness (Fin.lastCases z P j) = value := by
    intro j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simpa only [Fin.lastCases_last] using hz
    · simpa only [Fin.lastCases_castSucc] using hP i
  have heq : insert fitness P z =
      (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))).bind (fun d ↦ PMF.pure (replace P z d)) := by
    unfold Lax343628Proofs.Sampling.insert
    rw [deletion_uniform fitness (Fin.lastCases z P) value hQ]
    rfl
  rw [heq, mean_bind]
  simp only [mean_pure]
  exact uniform_replacement_drift ψ P z

lemma insert_rejected {n : ℕ} {μ : ℕ+} (fitness : BitString n → ℝ)
    (P : Population n μ) (z : BitString n) (value : ℝ)
    (hP : ∀ i, fitness (P i) = value) (hz : fitness z < value) :
    Lax343628Proofs.Sampling.insert fitness P z = PMF.pure P := by
  unfold Lax343628Proofs.Sampling.insert
  rw [deletion_unique_last fitness P z value hP hz]
  simp only [Bind.bind, Pure.pure, PMF.pure_bind, Fin.val_last, lt_self_iff_false, dif_neg,
    not_false_eq_true]

end
end Lax343628Proofs.Deletion

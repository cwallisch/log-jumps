import Lax343628Proofs.Deletion

namespace Lax343628Proofs.ElitistCounts

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.Deletion
open Lax343628Proofs.FiniteDrift
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {mu : ℕ+}

def count (fitness : BitString n → ℝ) (v : ℝ) (P : Population n mu) : ℕ :=
  (Finset.univ.filter (fun u ↦ v ≤ fitness (P u))).card

lemma count_le (fitness : BitString n → ℝ) (v : ℝ) (P : Population n mu) : count fitness v P ≤ (mu : ℕ) := by
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

lemma count_total (fitness : BitString n → ℝ) (v : ℝ) (P : Population n mu) :
    (count fitness v P : ℝ) = total (fun x ↦ if v ≤ fitness x then 1 else 0) P := by
  unfold count total
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma full (fitness : BitString n → ℝ) (v : ℝ) (P : Population n mu)
    (hP : ∀ u, v ≤ fitness (P u)) : count fitness v P = (mu : ℕ) := by
  simp only [count, hP, implies_true, Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]

lemma exists_low (fitness : BitString n → ℝ) (v : ℝ) (P : Population n mu)
    (hP : count fitness v P < (mu : ℕ)) : ∃ u, fitness (P u) < v := by
  by_contra hn
  have hh : ∀ u, v ≤ fitness (P u) := by simpa only [not_exists, not_lt] using hn
  rw [full fitness v P hh] at hP
  omega

lemma replacement (fitness : BitString n → ℝ) (v : ℝ) (P : Population n mu) (z : BitString n)
    (d : Fin ((mu : ℕ) + 1)) (hmin : ∀ j, fitness (Fin.lastCases z P d) ≤ fitness (Fin.lastCases z P j))
    (hP : count fitness v P < (mu : ℕ)) :
    count fitness v (replace P z d) = count fitness v P + if v ≤ fitness z then 1 else 0 := by
  obtain ⟨u, hu⟩ := exists_low fitness v P hP
  have hdel : fitness (Fin.lastCases z P d) < v :=
    (hmin u.castSucc).trans_lt (by simpa only [Fin.lastCases_castSucc] using hu)
  by_cases hd : d.val < (mu : ℕ)
  · let di : Fin (mu : ℕ) := ⟨d.val, hd⟩
    have heq : d = di.castSucc := Fin.ext rfl
    rw [heq, Fin.lastCases_castSucc] at hdel
    have hh := total_update (fun x ↦ if v ≤ fitness x then (1 : ℝ) else 0) P di z
    simp only [if_neg (not_le_of_gt hdel), sub_zero] at hh
    have hreplace : replace P z d = Function.update P di z := by simp only [replace, dif_pos hd, di]
    have hr : (count fitness v (replace P z d) : ℝ) = (count fitness v P : ℝ) + if v ≤ fitness z then 1 else 0 := by
      rw [count_total, hreplace, count_total]
      linarith
    exact_mod_cast hr
  · have heq : d = Fin.last (mu : ℕ) := Fin.ext (by have := d.isLt; simp only [Fin.val_last]; omega)
    rw [heq, Fin.lastCases_last] at hdel
    simp only [replace, dif_neg hd, if_neg (not_le_of_gt hdel), Nat.add_zero]

lemma insertion (fitness : BitString n → ℝ) (v : ℝ) (P : Population n mu) (z : BitString n)
    (hP : count fitness v P < (mu : ℕ)) (Q : Population n mu)
    (hQ : Q ∈ (Sampling.insert fitness P z).support) :
    count fitness v Q = count fitness v P + if v ≤ fitness z then 1 else 0 := by
  obtain ⟨d, hd, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
  have heq := (PMF.mem_support_pure_iff _ _).mp hQ
  subst Q
  apply replacement fitness v P z d _ hP
  simpa only [deletionIndex, PMF.mem_support_uniformOfFinset_iff, Finset.mem_filter, Finset.mem_univ, true_and] using hd

lemma all_high (fitness : BitString n → ℝ) (v : ℝ) (P : Population n mu) (z : BitString n)
    (hP : ∀ u, v ≤ fitness (P u)) (Q : Population n mu)
    (hQ : Q ∈ (Sampling.insert fitness P z).support) : ∀ u, v ≤ fitness (Q u) := by
  obtain ⟨d, hd, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
  have heq := (PMF.mem_support_pure_iff _ _).mp hQ
  subst Q
  have hmin : ∀ j, fitness (Fin.lastCases z P d) ≤ fitness (Fin.lastCases z P j) := by
    simpa only [deletionIndex, PMF.mem_support_uniformOfFinset_iff, Finset.mem_filter, Finset.mem_univ, true_and] using hd
  intro u
  by_cases hslot : d.val < (mu : ℕ)
  · let di : Fin (mu : ℕ) := ⟨d.val, hslot⟩
    have hdi : d = di.castSucc := Fin.ext rfl
    have hz : v ≤ fitness z := by
      have hh := hmin (Fin.last (mu : ℕ))
      rw [hdi, Fin.lastCases_castSucc, Fin.lastCases_last] at hh
      exact (hP di).trans hh
    simp only [dif_pos hslot]
    by_cases hu : u = di
    · subst u
      simpa only [di, Function.update_self] using hz
    · simpa only [di] using (Function.update_of_ne hu z P ▸ hP u)
  · simpa only [replace, dif_neg hslot] using hP u

lemma full_iff (fitness : BitString n → ℝ) (v : ℝ) (P : Population n mu) :
    count fitness v P = (mu : ℕ) ↔ ∀ u, v ≤ fitness (P u) := by
  unfold count
  have hh := Finset.card_filter_eq_iff (s := (Finset.univ : Finset (Fin (mu : ℕ))))
    (p := fun u ↦ v ≤ fitness (P u))
  simpa only [Finset.card_univ, Fintype.card_fin, Finset.mem_univ, forall_const] using hh

lemma monotone (fitness : BitString n → ℝ) (v : ℝ) (P : Population n mu) (z : BitString n)
    (Q : Population n mu) (hQ : Q ∈ (Sampling.insert fitness P z).support) :
    count fitness v P ≤ count fitness v Q := by
  by_cases hP : count fitness v P < (mu : ℕ)
  · rw [insertion fitness v P z hP Q hQ]
    omega
  · have heq : count fitness v P = (mu : ℕ) := by have := count_le fitness v P; omega
    rw [heq, full fitness v Q (all_high fitness v P z ((full_iff fitness v P).mp heq) Q hQ)]

lemma step_monotone (fitness : BitString n → ℝ) (v pc : ℝ) (P Q : Population n mu)
    (hQ : Q ∈ (step fitness pc P).support) : count fitness v P ≤ count fitness v Q := by
  rw [step_eq] at hQ
  obtain ⟨z, _, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hQ
  exact monotone fitness v P z Q hz

lemma birth_mean (fitness : BitString n → ℝ) (v pc : ℝ) (P : Population n mu)
    (hP : count fitness v P < (mu : ℕ)) :
    mean (step fitness pc P) (fun Q ↦ if count fitness v P < count fitness v Q then 1 else 0) =
      mean (offspring pc P) (fun z ↦ if v ≤ fitness z then 1 else 0) := by
  rw [step_eq, mean_bind]
  congr 1
  funext z
  have hpoint (Q : Population n mu) (hQ : Q ∈ (Sampling.insert fitness P z).support) :
      (if count fitness v P < count fitness v Q then (1 : ℝ) else 0) = if v ≤ fitness z then 1 else 0 := by
    rw [insertion fitness v P z hP Q hQ]
    split_ifs <;> first | rfl | omega
  apply le_antisymm
  · exact (mean_mono_on_support _ (fun Q hQ ↦ (hpoint Q hQ).le)).trans_eq (mean_const _ _)
  · exact (mean_const _ _).symm.le.trans (mean_mono_on_support _ (fun Q hQ ↦ (hpoint Q hQ).ge))

end
end Lax343628Proofs.ElitistCounts

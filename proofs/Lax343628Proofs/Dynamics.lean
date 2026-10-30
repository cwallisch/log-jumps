import Lax343628.Algorithm
import Mathlib.Tactic.NormNum

namespace Lax343628Proofs.Dynamics

open Lax343628.Algorithm
open scoped ENNReal Classical BigOperators

noncomputable section

lemma ones_le {n : ℕ} (x : BitString n) : ones x ≤ n := by
  calc
    ones x ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum fun j _ ↦ by
      have h := (x j).isLt
      omega
    _ = n := by simp

@[simp] lemma ones_optimum (n : ℕ) : ones (optimum n) = n := by
  simp [ones, optimum]

lemma eq_optimum_of_ones_eq {n : ℕ} (x : BitString n) (h : ones x = n) :
    x = optimum n := by
  have hsum : ∑ j : Fin n, (x j : ℕ) = ∑ _ : Fin n, 1 := by simpa [ones] using h
  have hle : ∀ j ∈ (Finset.univ : Finset (Fin n)), (x j : ℕ) ≤ 1 := by
    intro j _
    have hj := (x j).isLt
    omega
  have hall := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
  funext j
  apply Fin.ext
  exact hall j (Finset.mem_univ j)

@[simp] lemma ones_eq_iff {n : ℕ} (x : BitString n) : ones x = n ↔ x = optimum n :=
  ⟨eq_optimum_of_ones_eq x, fun h ↦ h ▸ ones_optimum n⟩

@[simp] lemma jump_optimum (n k : ℕ) : jump k (optimum n) = (k + n : ℕ) := by
  simp [jump]

lemma jump_lt_optimum {n k : ℕ} (hk : 0 < k) (x : BitString n)
    (hx : x ≠ optimum n) : jump k x < jump k (optimum n) := by
  have hxn : ones x < n := lt_of_le_of_ne (ones_le x) (by simpa using hx)
  rw [jump_optimum]
  unfold jump
  split_ifs
  · exact_mod_cast Nat.add_lt_add_left hxn k
  · have hlt : n - ones x < k + n := by omega
    exact_mod_cast hlt

def missing {n : ℕ} {μ : ℕ+} : Set (Population n μ) := {P | ∀ i, P i ≠ optimum n}

lemma retained_optimum {n k : ℕ} {μ : ℕ+} (hk : 0 < k) (P : Population n μ)
    (z : BitString n) (d : Fin ((μ : ℕ) + 1))
    (hd : ∀ j, jump k (Fin.lastCases z P d) ≤ jump k (Fin.lastCases z P j))
    (i : Fin (μ : ℕ)) (hi : P i = optimum n) :
    ∃ j, (if h : d.val < (μ : ℕ) then Function.update P ⟨d.val, h⟩ z else P) j =
      optimum n := by
  split_ifs with h
  · let di : Fin (μ : ℕ) := ⟨d.val, h⟩
    by_cases heq : i = di
    · have hd_eq : d = di.castSucc := Fin.ext rfl
      have hz : z = optimum n := by
        by_contra hz
        have hdi : Fin.lastCases z P d = P i := by
          calc
            Fin.lastCases z P d = Fin.lastCases z P di.castSucc :=
              congrArg (Fin.lastCases z P) hd_eq
            _ = P di := Fin.lastCases_castSucc di
            _ = P i := congrArg P heq.symm
        have hmin := hd (Fin.last (μ : ℕ))
        rw [hdi, hi, Fin.lastCases_last] at hmin
        exact (not_lt_of_ge hmin) (jump_lt_optimum hk z hz)
      exact ⟨di, by rw [Function.update_self]; exact hz⟩
    · exact ⟨i, (Function.update_of_ne heq z P).trans hi⟩
  · exact ⟨i, hi⟩

lemma step_retains_optimum {n k : ℕ} {μ : ℕ+} (hk : 0 < k) (p_c : ℝ)
    (P : Population n μ) (hP : P ∉ missing) (Q : Population n μ)
    (hQ : Q ∈ (step (jump k) p_c P).support) : Q ∉ missing := by
  obtain ⟨i, hi⟩ : ∃ i, P i = optimum n := by simpa [missing] using hP
  obtain ⟨b, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
  have hfinish : ∀ y : BitString n, ∀ Q : Population n μ,
      Q ∈ ((independentBits n (1 / (n : ℝ))).bind fun mask ↦
        (deletionIndex (jump k) (Fin.lastCases (mutate y mask) P)).bind fun d ↦
          PMF.pure (if h : d.val < (μ : ℕ) then
            Function.update P ⟨d.val, h⟩ (mutate y mask) else P)).support → Q ∉ missing := by
    intro y Q hQ
    obtain ⟨mask, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    obtain ⟨d, hd, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    have hQ := (PMF.mem_support_pure_iff _ Q).mp hQ
    subst Q
    have hmin : ∀ j, jump k (Fin.lastCases (mutate y mask) P d) ≤
        jump k (Fin.lastCases (mutate y mask) P j) := by
      simpa [deletionIndex] using hd
    obtain ⟨j, hj⟩ := retained_optimum hk P (mutate y mask) d hmin i hi
    exact fun hmiss ↦ hmiss j hj
  dsimp only at hQ
  split_ifs at hQ with hb
  · obtain ⟨⟨u, v⟩, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    obtain ⟨mask, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    obtain ⟨y, hy, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    have hy := (PMF.mem_support_pure_iff _ y).mp hy
    subst y
    exact hfinish _ _ hQ
  · obtain ⟨u, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    obtain ⟨y, hy, hQ⟩ := (PMF.mem_support_bind_iff _ _ Q).mp hQ
    have hy := (PMF.mem_support_pure_iff _ y).mp hy
    subst y
    exact hfinish _ _ hQ

lemma step_missing_eq_zero {n k : ℕ} {μ : ℕ+} (hk : 0 < k) (p_c : ℝ)
    (P : Population n μ) (hP : P ∉ missing) :
    (step (jump k) p_c P).toOuterMeasure missing = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro Q hQ
  exact step_retains_optimum hk p_c P hP Q hQ

end
end Lax343628Proofs.Dynamics

import Lax343628Proofs.FiniteDrift

namespace Lax343628Proofs.FiniteGrowth

open scoped Classical

lemma reach {α : Type*} (h : ℕ → α) (done : α → Prop) (O : α → ℝ)
    (N R : ℕ) (upper : ℝ) (hO0 : 0 < O (h 0))
    (hupper : ∀ s, s ≤ N * R → ¬done (h s) → O (h s) ≤ upper)
    (hblock : ∀ s, s + R ≤ N * R → O (h 0) ≤ O (h s) → ¬done (h s) →
      ∃ t, t ≤ s + R ∧ (done (h t) ∨ 8 * O (h s) ≤ O (h t)))
    (hlarge : upper < (8 : ℝ) ^ N * O (h 0)) :
    ∃ t, t ≤ N * R ∧ done (h t) := by
  have hg : ∀ j, j ≤ N → ∃ s, s ≤ j * R ∧
      (done (h s) ∨ (8 : ℝ) ^ j * O (h 0) ≤ O (h s)) := by
    intro j hj
    induction j with
    | zero => exact ⟨0, by omega, Or.inr (by simp only [pow_zero, one_mul, le_refl])⟩
    | succ j ih =>
      obtain ⟨s, hs, hsd⟩ := ih (by omega)
      rcases hsd with hd | hprog
      · exact ⟨s, hs.trans (Nat.mul_le_mul_right R (Nat.le_succ j)), Or.inl hd⟩
      · by_cases hd : done (h s)
        · exact ⟨s, hs.trans (Nat.mul_le_mul_right R (Nat.le_succ j)), Or.inl hd⟩
        · have hbase : O (h 0) ≤ O (h s) := by
            have hh := mul_le_mul_of_nonneg_right
              (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 8) : (1 : ℝ) ≤ 8 ^ j) hO0.le
            have hbase0 : O (h 0) ≤ (8 : ℝ) ^ j * O (h 0) := by simpa only [one_mul] using hh
            exact hbase0.trans hprog
          obtain ⟨t, ht, htd⟩ := hblock s (by nlinarith [Nat.mul_le_mul_right R hj]) hbase hd
          refine ⟨t, by nlinarith, ?_⟩
          rcases htd with hd | hstep
          · exact Or.inl hd
          · right
            have hh := mul_le_mul_of_nonneg_left hprog (show (0 : ℝ) ≤ 8 by norm_num)
            rw [pow_succ]
            nlinarith
  obtain ⟨s, hs, hd⟩ := hg N le_rfl
  refine ⟨s, hs, ?_⟩
  rcases hd with hd | hh
  · exact hd
  · by_contra hn
    linarith [hupper s hs hn]

end Lax343628Proofs.FiniteGrowth

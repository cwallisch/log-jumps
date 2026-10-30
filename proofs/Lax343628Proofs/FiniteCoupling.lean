import Lax343628Proofs.FiniteOrder

namespace Lax343628Proofs.FiniteCoupling

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteOrder
open Lax343628Proofs.FiniteComparison
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

structure Coupling {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (q : PMF β) where
  mass : α → β → ℝ
  nonneg : ∀ a b, 0 ≤ mass a b
  row : ∀ a, ∑ b, mass a b = (p a).toReal
  col : ∀ b, ∑ a, mass a b = (q b).toReal

lemma positive_marginals {α β : Type*} [Fintype α] [Fintype β] {p : PMF α} {q : PMF β}
    (C : Coupling p q) (a : α) (b : β) (h : 0 < C.mass a b) :
    0 < (p a).toReal ∧ 0 < (q b).toReal := by
  constructor
  · rw [← C.row]
    exact h.trans_le (Finset.single_le_sum (fun c _ ↦ C.nonneg a c) (Finset.mem_univ b))
  · rw [← C.col]
    exact h.trans_le (Finset.single_le_sum (fun c _ ↦ C.nonneg c b) (Finset.mem_univ a))

lemma test_left {α β : Type*} [Fintype α] [Fintype β] {p : PMF α} {q : PMF β}
    (C : Coupling p q) (f : α → ℝ) : ∑ a, ∑ b, C.mass a b * f a = mean p f := by
  simp_rw [← Finset.sum_mul, C.row]
  rfl

lemma test_right {α β : Type*} [Fintype α] [Fintype β] {p : PMF α} {q : PMF β}
    (C : Coupling p q) (f : β → ℝ) : ∑ a, ∑ b, C.mass a b * f b = mean q f := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, C.col]
  rfl

lemma test_le {α β : Type*} [Fintype α] [Fintype β] {p : PMF α} {q : PMF β}
    (C : Coupling p q) (f : α → ℝ) (g : β → ℝ)
    (h : ∀ a b, 0 < C.mass a b → g b ≤ f a) : mean q g ≤ mean p f := by
  rw [← test_left C f, ← test_right C g]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases hab : 0 < C.mass a b
  · exact mul_le_mul_of_nonneg_left (h a b hab) hab.le
  · have hz : C.mass a b = 0 := le_antisymm (le_of_not_gt hab) (C.nonneg a b)
    simp only [hz, zero_mul, le_refl]

def independent {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (q : PMF β) : Coupling p q where
  mass a b := (p a).toReal * (q b).toReal
  nonneg _ _ := mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  row a := by rw [← Finset.mul_sum, sum_mass, mul_one]
  col b := by rw [← Finset.sum_mul, sum_mass, one_mul]

def identity {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) : Coupling p p where
  mass a b := if b = a then (p a).toReal else 0
  nonneg a b := by split_ifs <;> positivity
  row a := by simp
  col b := by simp

def reverse {α β : Type*} [Fintype α] [Fintype β] {p : PMF α} {q : PMF β}
    (C : Coupling p q) : Coupling q p where
  mass b a := C.mass a b
  nonneg b a := C.nonneg a b
  row b := C.col b
  col a := C.row a

lemma map_mass {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq γ]
    (p : PMF α) (f : α → γ) (c : γ) :
    (p.map f c).toReal = ∑ a, if f a = c then (p a).toReal else 0 := by
  have h := mean_map p f (fun z ↦ if z = c then (1 : ℝ) else 0)
  rw [mean_pick, mul_one] at h
  rw [h]
  unfold mean
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : f a = c <;> simp [ha]

def map {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq γ] [DecidableEq δ] {p : PMF α} {q : PMF β}
    (C : Coupling p q) (f : α → γ) (g : β → δ) : Coupling (p.map f) (q.map g) where
  mass c d := ∑ ab : α × β, if f ab.1 = c ∧ g ab.2 = d then C.mass ab.1 ab.2 else 0
  nonneg c d := Finset.sum_nonneg (fun ab _ ↦ by split_ifs; exact C.nonneg _ _; exact le_rfl)
  row c := by
    rw [Finset.sum_comm]
    have hinner (ab : α × β) :
        (∑ d : δ, if f ab.1 = c ∧ g ab.2 = d then C.mass ab.1 ab.2 else 0) =
          if f ab.1 = c then C.mass ab.1 ab.2 else 0 := by
      by_cases hc : f ab.1 = c <;> simp [hc]
    simp_rw [hinner]
    rw [Fintype.sum_prod_type, map_mass]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hc : f a = c
    · simp only [if_pos hc]
      exact C.row a
    · simp only [if_neg hc, Finset.sum_const_zero]
  col d := by
    rw [Finset.sum_comm]
    have hinner (ab : α × β) :
        (∑ c : γ, if f ab.1 = c ∧ g ab.2 = d then C.mass ab.1 ab.2 else 0) =
          if g ab.2 = d then C.mass ab.1 ab.2 else 0 := by
      by_cases hd : g ab.2 = d <;> simp [hd]
    simp_rw [hinner]
    rw [Fintype.sum_prod_type, Finset.sum_comm, map_mass]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hd : g b = d
    · simp only [if_pos hd]
      exact C.col b
    · simp only [if_neg hd, Finset.sum_const_zero]

lemma bind_mass {α γ : Type*} [Fintype α] [Fintype γ]
    (p : PMF α) (K : α → PMF γ) (x : γ) :
    (p.bind K x).toReal = ∑ a, (p a).toReal * (K a x).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro a _
    exact ENNReal.mul_ne_top (p.apply_ne_top a) ((K a).apply_ne_top x)

def bind {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    {p : PMF α} {q : PMF β} (C : Coupling p q) (K : α → PMF γ) (L : β → PMF δ)
    (D : ∀ a b, Coupling (K a) (L b)) : Coupling (p.bind K) (q.bind L) where
  mass x y := ∑ ab : α × β, C.mass ab.1 ab.2 * (D ab.1 ab.2).mass x y
  nonneg x y := Finset.sum_nonneg (fun ab _ ↦ mul_nonneg (C.nonneg _ _) ((D _ _).nonneg _ _))
  row x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (D _ _).row]
    rw [Fintype.sum_prod_type, bind_mass]
    simp_rw [← Finset.sum_mul, C.row]
  col y := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (D _ _).col]
    rw [Fintype.sum_prod_type, Finset.sum_comm, bind_mass]
    simp_rw [← Finset.sum_mul, C.col]

lemma map_support {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq γ] [DecidableEq δ] {p : PMF α} {q : PMF β}
    (C : Coupling p q) (f : α → γ) (g : β → δ) (c : γ) (d : δ)
    (h : 0 < (map C f g).mass c d) :
    ∃ a b, f a = c ∧ g b = d ∧ 0 < C.mass a b := by
  change 0 < ∑ ab : α × β, if f ab.1 = c ∧ g ab.2 = d then C.mass ab.1 ab.2 else 0 at h
  have hex : ∃ ab : α × β, 0 < (if f ab.1 = c ∧ g ab.2 = d then C.mass ab.1 ab.2 else 0) := by
    by_contra hn
    push Not at hn
    have hz := Finset.sum_nonpos (s := (Finset.univ : Finset (α × β))) (fun ab _ ↦ hn ab)
    linarith
  obtain ⟨ab, hab⟩ := hex
  split_ifs at hab with heq
  · exact ⟨ab.1, ab.2, heq.1, heq.2, hab⟩
  · exact False.elim (lt_irrefl _ hab)

lemma bind_support {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    {p : PMF α} {q : PMF β} (C : Coupling p q) (K : α → PMF γ) (L : β → PMF δ)
    (D : ∀ a b, Coupling (K a) (L b)) (x : γ) (y : δ)
    (h : 0 < (bind C K L D).mass x y) :
    ∃ a b, 0 < C.mass a b ∧ 0 < (D a b).mass x y := by
  change 0 < ∑ ab : α × β, C.mass ab.1 ab.2 * (D ab.1 ab.2).mass x y at h
  have hex : ∃ ab : α × β, 0 < C.mass ab.1 ab.2 * (D ab.1 ab.2).mass x y := by
    by_contra hn
    push Not at hn
    have hz := Finset.sum_nonpos (s := (Finset.univ : Finset (α × β))) (fun ab _ ↦ hn ab)
    linarith
  obtain ⟨ab, hab⟩ := hex
  exact ⟨ab.1, ab.2, (mul_pos_iff.mp hab).resolve_right
    (fun hn ↦ (not_lt_of_ge (C.nonneg _ _)) hn.1)⟩

def diagonal {N : ℕ} (p q : PMF (Fin N)) (i : Fin N) : ℝ :=
  cumulative q (i.val + 1) - cumulative p i.val

def rising {N : ℕ} (p q : PMF (Fin N)) (i : Fin N) : ℝ :=
  cumulative p (i.val + 1) - cumulative q (i.val + 1)

def bandMass {N : ℕ} (p q : PMF (Fin N)) (i j : Fin N) : ℝ :=
  if j = i then diagonal p q i else if j.val = i.val + 1 then rising p q i else 0

lemma bandMass_row {N : ℕ} (p q : PMF (Fin N)) (i : Fin N) :
    ∑ j, bandMass p q i j = (p i).toReal := by
  by_cases hnext : i.val + 1 < N
  · let j : Fin N := ⟨i.val + 1, hnext⟩
    have hij : i ≠ j := by intro h; have hv := congrArg Fin.val h; dsimp [j] at hv; omega
    rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij]
    · have hji : j ≠ i := Ne.symm hij
      simp only [bandMass, ite_true, if_neg hji, show j.val = i.val + 1 from rfl]
      unfold diagonal rising
      linarith [cumulative_step p i]
    · intro c _ hc
      have hcval : c.val ≠ i.val + 1 := by intro h; exact hc.2 (Fin.ext h)
      simp only [bandMass, if_neg hc.1, if_neg hcval]
  · have hiN : i.val + 1 = N := by have hi := i.isLt; omega
    rw [Finset.sum_eq_single i]
    · rw [bandMass, if_pos rfl]
      unfold diagonal
      have hpf := cumulative_full p N le_rfl
      have hqf := cumulative_full q N le_rfl
      have hpstep := cumulative_step p i
      rw [hiN] at hpstep
      rw [hiN, hqf]
      linarith
    · intro j _ hji
      have hval : j.val ≠ i.val + 1 := by have hj := j.isLt; omega
      simp only [bandMass, if_neg hji, if_neg hval]
    · intro hn
      exact False.elim (hn (Finset.mem_univ i))

lemma bandMass_col {N : ℕ} (p q : PMF (Fin N)) (j : Fin N) :
    ∑ i, bandMass p q i j = (q j).toReal := by
  by_cases hj0 : j.val = 0
  · rw [Finset.sum_eq_single j]
    · rw [bandMass, if_pos rfl]
      unfold diagonal
      have hstep := cumulative_step q j
      rw [hj0, cumulative_zero] at hstep ⊢
      linarith
    · intro i _ hij
      have hval : j.val ≠ i.val + 1 := by omega
      simp only [bandMass, if_neg (Ne.symm hij), if_neg hval]
    · intro hn
      exact False.elim (hn (Finset.mem_univ j))
  · let i : Fin N := ⟨j.val - 1, by have hj := j.isLt; omega⟩
    have hij : j ≠ i := by intro h; have hv := congrArg Fin.val h; dsimp [i] at hv; omega
    have hsucc : i.val + 1 = j.val := by dsimp [i]; omega
    rw [Finset.sum_eq_add_of_mem j i (Finset.mem_univ _) (Finset.mem_univ _) hij]
    · simp only [bandMass, ite_true, if_neg hij, ← hsucc, ite_true]
      unfold diagonal rising
      rw [hsucc]
      linarith [cumulative_step q j]
    · intro c _ hc
      have hval : j.val ≠ c.val + 1 := by
        intro h
        apply hc.2
        apply Fin.ext
        dsimp [i]
        omega
      simp only [bandMass, if_neg (Ne.symm hc.1), if_neg hval]

def ofCumulative {N : ℕ} (p q : PMF (Fin N))
    (hdom : ∀ r, cumulative q r ≤ cumulative p r)
    (hcover : ∀ r, cumulative p r ≤ cumulative q (r + 1)) : Coupling p q where
  mass := bandMass p q
  nonneg i j := by
    unfold bandMass
    split_ifs
    · exact sub_nonneg.mpr (hcover i.val)
    · exact sub_nonneg.mpr (hdom (i.val + 1))
    · exact le_rfl
  row := bandMass_row p q
  col := bandMass_col p q

lemma ofCumulative_support {N : ℕ} (p q : PMF (Fin N))
    (hdom : ∀ r, cumulative q r ≤ cumulative p r)
    (hcover : ∀ r, cumulative p r ≤ cumulative q (r + 1)) (i j : Fin N)
    (h : 0 < (ofCumulative p q hdom hcover).mass i j) :
    i.val ≤ j.val ∧ j.val ≤ i.val + 1 := by
  change 0 < bandMass p q i j at h
  unfold bandMass at h
  split_ifs at h with heq hsucc
  · subst j
    omega
  · omega
  · exact False.elim (lt_irrefl _ h)

end
end Lax343628Proofs.FiniteCoupling

import Lax343628Proofs.ArrivalFitness
import Lax343628Proofs.RankPotential

namespace Lax343628Proofs.ArrivalRanks

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.Dynamics
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain
open Lax343628Proofs.ArrivalFitness
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

def count (k : ℕ) (v : Fin n) (P : Population n mu) := ElitistCounts.count (jump k) ((v.val + 1 : ℕ) : ℝ) P

def coefficient (n k : ℕ) (pc : ℝ) (v : ℕ) : ℝ :=
  if 16 * (k + 1) ≤ n - k - (v - k) then pc / 128 else pc * (1 / 4 : ℝ) ^ (n - (v - k)) / 16

def rate (n k : ℕ) (mu : ℕ+) (pc : ℝ) (v l : ℕ) : ℝ :=
  if v < k then pc / 32 else coefficient n k pc v * ((l : ℝ) / (mu : ℕ) + ((n - (v - k) : ℕ) : ℝ) / n)

def cost (n k : ℕ) (mu : ℕ+) (pc : ℝ) (v l : ℕ) : ℝ := 1 / rate n k mu pc v l

lemma rate_pos (hn : 0 < n) (pc : ℝ) (hpc : 0 < pc) (v : Fin n) (l : ℕ) :
    0 < rate n k mu pc v.val l := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hz : 0 < n - (v.val - k) := by have := v.isLt; omega
  have hzR : (0 : ℝ) < (n - (v.val - k) : ℕ) := by exact_mod_cast hz
  unfold rate coefficient
  split_ifs <;> positivity

lemma ordinary_count (i : ℕ) (P : Population n mu) (hP : ∀ u, ones (P u) ≤ n - k)
    (v : Fin n) (hv : v.val = k + i) : count k v P = OrdinaryBirth.above i P := by
  unfold count ElitistCounts.count OrdinaryBirth.above
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hv]
  norm_num only [Nat.cast_add, Nat.cast_one]
  exact ordinary_elite i (P u) (hP u)

lemma birth (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) (pc : ℝ) (hpc : 0 < pc ∧ pc ≤ 1)
    (P : Population n mu) (hP : P ∈ active k) (v : Fin n) (hv : ∀ u, v.val ≤ score k (P u)) :
    rate n k mu pc v.val (count k v P) ≤
      mean (offspring pc P) (fun z ↦ if ((v.val + 1 : ℕ) : ℝ) ≤ jump k z then 1 else 0) := by
  have hkN : k ≤ n := by omega
  by_cases hvk : v.val < k
  · have hzeros := fun u ↦ valley_floor hkN v.val hvk (P u) (hP.1 u) (hv u)
    have hh := ValleyBirth.offspring hn (by omega : 2 * v.val ≤ n) pc ⟨hpc.1.le, hpc.2⟩ P hzeros
    rw [rate, if_pos hvk]
    apply hh.trans
    apply mean_mono
    intro z
    have he := valley_event v.val hvk z
    unfold ValleyBirth.test
    by_cases hz : v.val < (zeros z).card
    · have hg : ((v.val + 1 : ℕ) : ℝ) ≤ jump k z := by
        simpa only [Nat.cast_add, Nat.cast_one] using he hz
      rw [if_pos hz, if_pos hg]
    · rw [if_neg hz]
      split_ifs <;> norm_num
  · let i := v.val - k
    have hvi : v.val = k + i := by dsimp [i]; omega
    have hib : i < n - k := by have := v.isLt; omega
    have hOrd : ∀ u, i ≤ ones (P u) ∧ ones (P u) ≤ n - k := by
      intro u
      apply ordinary_floor hkN i (P u) (hP.1 u)
      rw [← hvi]
      exact hv u
    have hcount := ordinary_count i P (fun u ↦ (hOrd u).2) v hvi
    have hborn : coefficient n k pc v.val * ((OrdinaryBirth.above i P : ℝ) / (mu : ℕ) + ((n - i : ℕ) : ℝ) / n) ≤
        mean (offspring pc P) (OrdinaryBirth.test i (n - k)) := by
      unfold coefficient
      by_cases hf : 16 * (k + 1) ≤ n - k - i
      · rw [if_pos hf]
        exact OrdinaryBirth.far hn hkN hf pc ⟨hpc.1.le, hpc.2⟩ P hOrd
      · rw [if_neg hf]
        exact OrdinaryBirth.near hn hib (Nat.sub_le n k) pc ⟨hpc.1.le, hpc.2⟩ P hOrd
    rw [rate, if_neg hvk, hcount]
    apply hborn.trans
    apply mean_mono
    intro z
    have he := ordinary_event (k := k) i z
    unfold OrdinaryBirth.test
    rw [hvi]
    norm_num only [Nat.cast_add, Nat.cast_one]
    by_cases hz : i < ones z ∧ ones z ≤ n - k
    · rw [if_pos hz, if_pos (he hz)]
    · rw [if_neg hz]
      split_ifs <;> norm_num

lemma runtime_sum (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) (pc : ℝ) (hpc : 0 < pc ∧ pc ≤ 1)
    (p : PMF (Population n mu)) :
    (∑' t, (law (stopped (step (jump k) pc) (active k)) p t).toOuterMeasure (active k)) ≤
      ENNReal.ofReal (∑ v : Fin n, ∑ l ∈ Finset.range (mu : ℕ), cost n k mu pc v.val l) := by
  apply RankPotential.runtime (step (jump k) pc) (active k) (mu : ℕ) (fun v : Fin n ↦ cost n k mu pc v.val) (count k)
  · intro v l
    exact (div_pos (by norm_num) (rate_pos (by omega) pc hpc.1 v l)).le
  · intro P _ Q hQ v
    exact ElitistCounts.step_monotone (jump k) ((v.val + 1 : ℕ) : ℝ) pc P Q hQ
  · intro P hP
    obtain ⟨v, _, hv, u, hu⟩ := minimum hk (by omega) P hP
    have hc : count k v P < (mu : ℕ) := by
      have hle := ElitistCounts.count_le (jump k) ((v.val + 1 : ℕ) : ℝ) P
      change count k v P ≤ (mu : ℕ) at hle
      by_contra hh
      have heq : count k v P = (mu : ℕ) := by omega
      have hall := (ElitistCounts.full_iff (jump k) ((v.val + 1 : ℕ) : ℝ) P).mp heq u
      rw [← score_cast, hu] at hall
      have hnat : v.val + 1 ≤ v.val := by exact_mod_cast hall
      omega
    refine ⟨v, hc, ?_⟩
    have hbirth : mean (step (jump k) pc P) (fun Q ↦ if count k v P < count k v Q then 1 else 0) =
        mean (offspring pc P) (fun z ↦ if ((v.val + 1 : ℕ) : ℝ) ≤ jump k z then 1 else 0) :=
      ElitistCounts.birth_mean (jump k) ((v.val + 1 : ℕ) : ℝ) pc P hc
    rw [hbirth]
    unfold cost
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ (rate_pos (by omega) pc hpc.1 v (count k v P))).mpr
    simpa only [one_mul] using birth hn hk hkn pc hpc P hP v hv

end
end Lax343628Proofs.ArrivalRanks

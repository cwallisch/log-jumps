import Lax343628Proofs.CrossoverCount

namespace Lax343628Proofs.Complement

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def bits (x : BitString n) : BitString n := fun j ↦ 1 - x j

lemma bit_twice (b : Fin 2) : 1 - (1 - b) = b := by fin_cases b <;> norm_num

lemma twice (x : BitString n) : bits (bits x) = x := by funext j; exact bit_twice (x j)

lemma injective : Function.Injective (bits (n := n)) := by
  intro x y hh
  have heq := congrArg bits hh
  simpa only [twice] using heq

lemma ones (x : BitString n) : Lax343628.Algorithm.ones (bits x) = (zeros x).card := by
  unfold Lax343628.Algorithm.ones zeros
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  have hpoint (b : Fin 2) : ((1 - b : Fin 2) : ℕ) = if b = 0 then 1 else 0 := by
    fin_cases b <;> norm_num
  exact hpoint (x j)

lemma crossover (x y mask : BitString n) : bits (Lax343628.Algorithm.crossover x y mask) = Lax343628.Algorithm.crossover (bits x) (bits y) mask := by
  funext j
  unfold bits Lax343628.Algorithm.crossover
  split_ifs <;> rfl

lemma mutation (x mask : BitString n) : bits (mutate x mask) = mutate (bits x) mask := by
  funext j
  by_cases hm : mask j = 1
  · simp only [bits, mutate, if_pos hm, bit_twice]
  · simp only [bits, mutate, if_neg hm]

lemma pair (x y : BitString n) (p : ℝ) : (pairMutation x y p).map bits = pairMutation (bits x) (bits y) p := by
  simp only [pairMutation, PMF.map_bind, PMF.pure_map, mutation, crossover]

lemma mean (x y : BitString n) (p : ℝ) (f : ℕ → ℝ) :
    FiniteDrift.mean (pairMutation (bits x) (bits y) p) (fun z ↦ f (Lax343628.Algorithm.ones z)) =
      FiniteDrift.mean (pairMutation x y p) (fun z ↦ f ((zeros z).card)) := by
  rw [← pair, mean_map]
  simp only [ones]

end
end Lax343628Proofs.Complement

import Mathlib.Data.PNat.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
---
title: The $(\mu+1)$ GA and the function $\mathrm{Jump}_k$
type: definition
---
For $x\in\{0,1\}^n$, let $|x|_1$ be its number of ones. For a jump size $k\in\{1,\dots,n\}$,
the function $\mathrm{Jump}_k\colon\{0,1\}^n\to\mathbb N$ is
$$\mathrm{Jump}_k(x)=\begin{cases}k+|x|_1 & \text{if } |x|_1=n \text{ or } |x|_1\le n-k,\\
n-|x|_1 & \text{otherwise.}\end{cases}$$

The $(\mu+1)$ genetic algorithm with crossover probability $p_c\in[0,1]$ maintains a
population, a multiset of $\mu$ individuals from $\{0,1\}^n$. One iteration, maximizing a
fitness function $f$, proceeds as follows:

1. With probability $p_c$, choose two parents $x,y$ uniformly at random with replacement from
   the population. Create the offspring $z$ by uniform crossover of $x$ and $y$, which takes
   each bit from $x$ or $y$ independently with probability $1/2$, followed by standard bit
   mutation, which flips each bit independently with probability $1/n$.
2. Otherwise, choose a parent $x$ uniformly at random and create $z$ by standard bit mutation
   of $x$.
3. Add $z$ to the population and remove an individual with the lowest fitness, breaking ties
   uniformly at random.
-/

namespace Lax343628.Algorithm

open scoped ENNReal Classical BigOperators

noncomputable section

/-- A string in $\{0,1\}^n$. `Fin n` indexes positions $0,\ldots,n-1$;
`Fin 2` consists of the values zero and one. -/
abbrev BitString (n : ℕ) := Fin n → Fin 2

/-- A population of positive size $\mu$, with entries indexed separately even when equal.
An iteration writes the offspring into the slot of the deleted entry, or discards it if it
is deleted itself; up to the order of entries, this is adding it and then deleting. -/
abbrev Population (n : ℕ) (μ : ℕ+) := Fin (μ : ℕ) → BitString n

/-- The number of one-bits in a string. -/
def ones {n : ℕ} (x : BitString n) : ℕ :=
  ∑ j : Fin n, (x j : ℕ)

/-- The function $\mathrm{Jump}_k$ with jump size `k`, usually considered for $n\ge2$ and
$1\le k\le n/2$. Fitness values are real numbers; natural-number subtraction is truncated
at zero. -/
def jump {n : ℕ} (k : ℕ) (x : BitString n) : ℝ :=
  if ones x ≤ n - k ∨ ones x = n then (k + ones x : ℕ) else (n - ones x : ℕ)

/-- The all-one string $1^n$, the unique optimum of $\mathrm{Jump}_k$ when $1\le k\le n$. -/
def optimum (n : ℕ) : BitString n := fun _ ↦ 1

/-- A Bernoulli bit, equal to one with probability $p$ for $0\le p\le1$.
Outside this interval it always returns the bit 0; all algorithm claims use valid probabilities. -/
def coin (p : ℝ) : PMF (Fin 2) :=
  if h : 0 ≤ p ∧ p ≤ 1 then
    PMF.ofFintype (fun b : Fin 2 ↦ ENNReal.ofReal (if b = 1 then p else 1 - p))
      -- Lean checks this proof that the probabilities sum to one; readers can skip it.
      (by simp_all [Fin.sum_univ_two, ← ENNReal.ofReal_add])
  else PMF.pure 0

/-- Independent Bernoulli bits, each equal to one with probability $p$: a string $x$ has
probability $\prod_j \Pr[\text{coin}=x_j]$, which is $p^{|x|_1}(1-p)^{n-|x|_1}$ for
$0\le p\le1$. Here `coin p b` is the probability that the coin shows the bit `b`. -/
def independentBits (n : ℕ) (p : ℝ) : PMF (BitString n) :=
  PMF.ofFintype (fun x ↦ ∏ j, coin p (x j))
    -- Lean checks this proof that the probabilities sum to one; readers can skip it.
    (by
      have h := (coin p).tsum_coe
      rw [tsum_fintype] at h
      rw [← Fintype.prod_sum]
      simp [h])

/-- Uniform crossover: at each position an independent fair mask bit selects one parent.
Sampling the mask uniformly among all bit strings gives independent fair choices. -/
def crossover {n : ℕ} (x y mask : BitString n) : BitString n :=
  fun j ↦ if mask j = 1 then x j else y j

/-- Flip exactly the positions where the mutation mask is one. -/
def mutate {n : ℕ} (x mask : BitString n) : BitString n :=
  fun j ↦ if mask j = 1 then 1 - x j else x j

/-- Uniform deletion among the $\mu+1$ entries of minimal `fitness`, including the offspring.
The minimum exists because the enlarged population is finite and nonempty. -/
def deletionIndex {n : ℕ} (fitness : BitString n → ℝ) {μ : ℕ+}
    (Q : Fin ((μ : ℕ) + 1) → BitString n) : PMF (Fin ((μ : ℕ) + 1)) :=
  PMF.uniformOfFinset
    (Finset.univ.filter fun i ↦ ∀ j, fitness (Q i) ≤ fitness (Q j))
    -- Lean checks this proof that a minimal entry exists; readers can skip it.
    (by simpa [Finset.filter_nonempty_iff] using Finite.exists_min fun j ↦ fitness (Q j))

/-- One iteration of the $(\mu+1)$ GA, maximizing `fitness`.
Crossover parents are independent uniform draws with replacement; the mutation-only
parent is uniform. Mutation flips each bit independently with probability $1/n$.
The offspring is inserted even if it equals an existing entry, before a worst entry is deleted.
Each `←` draws a sample from the distribution on its right. -/
def step {n : ℕ} (fitness : BitString n → ℝ) {μ : ℕ+} (p_c : ℝ) (P : Population n μ) :
    PMF (Population n μ) := do
  let useCrossover ← coin p_c
  -- `z'` is the uniform crossover of the parents `P u` and `P v`, or the parent `P u` itself.
  let z' ← if useCrossover = 1 then do
      let (u, v) ← PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ))
      let crossMask ← PMF.uniformOfFintype (BitString n)
      pure (crossover (P u) (P v) crossMask)
    else do
      let u ← PMF.uniformOfFintype (Fin (μ : ℕ))
      pure (P u)
  let flipMask ← independentBits n (1 / (n : ℝ))
  let z := mutate z' flipMask
  -- `Q` lists the μ + 1 entries: the population `P`, followed by the offspring `z`.
  let Q := Fin.lastCases z P
  let d ← deletionIndex fitness Q
  -- Deleting an old entry puts z into its slot; deleting the offspring (the last entry of
  -- `Q`) leaves P unchanged.
  pure (if h : d.val < (μ : ℕ) then Function.update P ⟨d.val, h⟩ z else P)

end
end Lax343628.Algorithm

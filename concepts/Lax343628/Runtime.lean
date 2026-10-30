import Lax343628.Algorithm
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
---
title: Expected optimization time
type: definition
---
The $(\mu+1)$ genetic algorithm with crossover probability $p_c$ is run on
$\mathrm{Jump}_k$, starting from $\mu$ individuals chosen independently and uniformly at
random from $\{0,1\}^n$. Its optimization time $T$ is the number of iterations until the
population first contains the optimum $1^n$. The expected optimization time is $\mathbb E[T]$.
-/

namespace Lax343628.Runtime

open Lax343628.Algorithm
open scoped ENNReal Classical BigOperators

noncomputable section

/-- The population distribution after $t$ iterations of the $(\mu+1)$ GA.
Initialization is uniform over all indexed populations, equivalently independent uniform
initial individuals. Each subsequent iteration uses `step` with fitness $\mathrm{Jump}_k$. -/
def populationLaw (n k : ℕ) (μ : ℕ+) (p_c : ℝ) : ℕ → PMF (Population n μ)
  | 0 => PMF.uniformOfFintype (Population n μ)
  | t + 1 => do
      let P ← populationLaw n k μ p_c t
      step (jump k) p_c P

/-- The probability that the population after $t$ iterations does not contain $1^n$.
For $1\le k\le n$, this equals $\Pr[T>t]$: since $1^n$ has the unique
maximal fitness, it is deleted only when all $\mu+1$ entries equal $1^n$, so it is never
lost once present. -/
def tailProbability (n k : ℕ) (μ : ℕ+) (p_c : ℝ) (t : ℕ) : ℝ≥0∞ :=
  ∑ P : Population n μ with (∀ i, P i ≠ optimum n),
    populationLaw n k μ p_c t P

/-- The expected optimization time $\mathbb E[T]=\sum_{t=0}^{\infty}\Pr[T>t]$.
The sum is in nonnegative extended reals and may equal infinity. An optimum already present
in the initial population is found at time zero. -/
def expectedRuntime (n k : ℕ) (μ : ℕ+) (p_c : ℝ) : ℝ≥0∞ :=
  ∑' t : ℕ, tailProbability n k μ p_c t

end
end Lax343628.Runtime

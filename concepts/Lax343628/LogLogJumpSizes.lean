import Lax343628.Runtime
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: $O(\mu{}n)$ expected optimization time for jump sizes $k \le c \operatorname{ln} \operatorname{ln} n$
type: theorem
---
Let $T$ be the optimization time of the $(\mu+1)$ genetic algorithm with crossover probability
$p_c$ on $\mathrm{Jump}_k$, started from $\mu$ individuals chosen independently and uniformly
at random from $\{0,1\}^n$.

Let $p_c\in(0,1]$ and $a>0$ be constants. If $1\le k\le c\ln\ln n$ for a sufficiently small
constant $c>0$, and $Ck(\ln n)^2\le\mu\le n^{a}$ for a sufficiently large constant $C$, then
$\mathbb E[T]=O(\mu n)$.

The constants $c$, $C$ and the constant in $O(\mu n)$ depend only on $p_c$ and $a$.
The bound holds for all sufficiently large $n$, uniformly in $k$ and $\mu$.
-/

namespace Lax343628.LogLogJumpSizes

open Lax343628.Algorithm Lax343628.Runtime Filter
open scoped ENNReal

/-- $\mathbb E[T]\le B\mu n$ for jump sizes $1\le k\le c\ln\ln n$ and population sizes
$Ck(\ln n)^2\le\mu\le n^a$. Here $B$ is the constant in $O(\mu n)$. `∀ᶠ n in atTop` means
"for all sufficiently large $n$"; since $k$ and $\mu$ are quantified inside it, the threshold
for $n$ does not depend on them. -/
axiom runtime_bound
    (p_c a : ℝ) (hp_c : 0 < p_c ∧ p_c ≤ 1) (ha : 0 < a) :
    ∃ c C B : ℝ, 0 < c ∧ 0 < C ∧ 0 < B ∧
      ∀ᶠ (n : ℕ) in atTop,
        ∀ (k : ℕ) (μ : ℕ+),
          1 ≤ k → (k : ℝ) ≤ c * Real.log (Real.log (n : ℝ)) →
          C * (k : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ (μ : ℕ) →
          (μ : ℕ) ≤ (n : ℝ) ^ a →
          expectedRuntime n k μ p_c ≤
            ENNReal.ofReal (B * (μ : ℕ) * (n : ℝ))

end Lax343628.LogLogJumpSizes

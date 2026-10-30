# An $O(\mu n)$ runtime bound for the $(\mu+1)$ GA on $\mathrm{Jump}_k$ with crossover probability 1

A Lean 4 formalization of two upper bounds on the expected optimization time of
the $(\mu+1)$ genetic algorithm on $\mathrm{Jump}_k$. It is a [Lax Archive](https://laxarchive.org)
submission with the id [`lax-343628`](https://laxarchive.org/lax-343628/).

## Abstract

For the $(\mu+1)$ genetic algorithm (GA) on $\mathrm{Jump}_k$ with constant crossover
probability, the best previously known upper bound on the expected optimization time is
$O(n^{k-1})$ for $k\ge3$, attained for suitably chosen population sizes. This formalization
establishes that, for small jump sizes, the $(\mu+1)$ GA without diversity mechanisms
optimizes $\mathrm{Jump}_k$ in expected time $O(\mu n)$ with crossover probability $1$, and
more generally with every constant crossover probability $p_c\in(0,1]$. The bound holds
for jump sizes $k\le c\ln\ln n$ and population sizes $Ck(\ln n)^2\le\mu\le n^{O(1)}$, where
$c>0$ is a sufficiently small and $C$ a sufficiently large constant. It also holds for
$k\le c\ln n$ and $n^{\varepsilon}\le\mu\le n^{O(1)}$, where $\varepsilon>0$ is an arbitrary
constant.

The proof was found, and the result formalized in Lean, using GPT 6.1 Sol and
Claude Opus 5.5.

## Status

Both results are proved in Lean 4 (`v4.33.0`) with mathlib (commit `db584cd`). The proofs
contain no `sorry`, and they depend only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`. The submission passes a full local `lax build`.

## Building

With the [Lax CLI](https://www.npmjs.com/package/lax-archive) (`npm install -g lax-archive`),
run from the repository root:

```sh
lax build .
```

Lax provides the pinned Lean toolchain and a prebuilt mathlib. A build from scratch with a single
Lean thread took about 18 minutes on our machine, with a peak memory use of about 4.3 GB.

## License

Apache License 2.0; see [`LICENSE`](LICENSE).

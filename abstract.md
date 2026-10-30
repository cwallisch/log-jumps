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

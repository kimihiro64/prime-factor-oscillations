# Prime Factor Oscillations

**Prime-factor densities, double-exponential reversals, and recurring prime gaps.**

Formalized in Lean 4.34.0.

[Read the paper](paper/research-paper.pdf) · [Theorems](paper/THEOREM_STATUS.md) · [Verification](paper/VERIFICATION.md) · [Build](BUILD.md)

Fix a rank and ask how often each prime is the first, second, third, or later
distinct prime factor of an arithmetic output. As the prime increases, this
density can fall and then rise again. Each fixed rank eventually stops rising,
yet the number of these reversals can grow double-exponentially with the rank.

This project determines the exact upper growth rate for products of affine
prime sums and proves a precise connection between late ascents and recurring
short prime gaps.

## Main result

Consider a fixed, nonempty family

$$
F(p,q)=\prod_{j=1}^{m}\bigl(c_j(p+q)+d_j\bigr),
$$

where the $c_j$ are positive integers, the $d_j$ are integers, and the factors
have distinct rational roots: $c_i d_j\ne c_j d_i$ when $i\ne j$.

Sample all ordered prime pairs $p,q\le X$, including the diagonal, with
normalization $\pi(X)^2$. The theorem proves:

- **Existence:** for each fixed rank $k\ge1$ and prime $\ell$, the density of
  $\ell$ as the prime factor of rank $k$ in $|F(p,q)|$ exists, counting distinct
  prime factors in increasing order.
- **Finiteness:** at every fixed rank, the density is eventually nonincreasing.
  Its maximum number $N_F(k)$ of separated descent-then-ascent occurrences is
  finite and attained.
- **Exact growth:** the double-logarithmic upper growth rate is

$$
\limsup_{k\to\infty}\frac{\log\log\bigl(3+N_F(k)\bigr)}{k}
=\Lambda(m)\gt 0.
$$

The rate $\Lambda$ is determined by how frequently bounded prime gaps occur.
Its definition and the general local-law theorem are given below.

This includes $p+q$, $p+q+1$, $2(p+q)-1$, every fixed $c(p+q)+d$ with
$c\ge1$, and products of distinct such factors. Finite coefficient, common-factor
and root exceptions are retained.

The input-size limit is taken **first**, with family, rank and prime fixed.
Outputs are weighted by their prime-pair representations. The growth formula
is a limsup statement; it does not assert infinitely many reversals at one
fixed rank.

**Proof:** [affine spectrum](PrimeFactorOscillations/Assembly/AffineSpectrum.lean) ·
[arithmetic density limits](PrimeFactorOscillations/Proof/AffinePairs/RankDensity.lean)


## Canonical double-exponential bounds

For the ordinary integer density and the generic odd local law, the
[canonical theorem](PrimeFactorOscillations/Assembly/Headline.lean) gives,
for every $\varepsilon\gt 0$ and all sufficiently large $k$,

$$
\exp\bigl(\exp(ak)\bigr)
\le N(k)\le
\exp\bigl(\exp((1/3+\varepsilon)k)\bigr),
\qquad a=\frac1{602}.
$$

Their common exact limsup rate is $\Lambda(1)$. Each fixed-rank sequence is
eventually strictly decreasing.

The numerical constant uses a conservative, formally closed prime-window
input. The general transfer works for every $0\lt a\lt 1/(H+1)$ when windows of
width $H$ have an eventual positive-power counting lower bound. Bare
infinitude of bounded gaps is not enough for that counting statement.

## Why late ascents matter

The [recurrence theorem](PrimeFactorOscillations/Assembly/GapRecurrence.lean)
proves a two-way connection. For an integer $H\ge1$ and

$$
\frac1{H+2}\lt b\lt \frac1{H+1},
$$

recurring consecutive prime gaps at most $H$ are equivalent to simultaneous
ascents in both canonical densities with

$$
\log\log(p-1)\ge bk,
$$

at arbitrarily large ranks $k$ and lower primes $p$. Explicitly, for every
$K,Q$ there must be such an ascent with $k\ge K$ and $p\ge Q$.

If $h$ is the least recurring gap, the critical late-ascent coefficient is
$1/(h+1)$. Smaller positive coefficients admit unbounded simultaneous ascent
supply; larger coefficients force eventual strict descent. The boundary
coefficient is not covered.

The [inverse transfer](PrimeFactorOscillations/Proof/Upper/GapScaleCutoff.lean)
also proves that sufficiently late ascents beyond any fixed coefficient
$b\gt 1/5$ must cross twin primes. **An independent unbounded supply of such
ascents remains open.** The implication is proved; no new prime-gap bound
or twin-prime theorem is claimed.

## The spectrum behind the rate

Let $G_H(X)$ count consecutive prime gaps at most $H$ whose lower prime is
at most $X$. Then

$$
\gamma_H=\limsup_{X\to\infty}
\frac{\log\log\bigl(3+G_H(X)\bigr)}{\log\log X},
\qquad
\Lambda(\nu)=\sup_{H\ge2}\frac{\gamma_H}{H+\nu}.
$$

The [general theorem](PrimeFactorOscillations/Assembly/ReciprocalSmoothSpectrum.lean)
applies to each fixed local probability law with $\nu\gt 0$, $0\le\eta_p\le1$,
and

$$
\frac1{\eta_p}=\frac p\nu+b+o(1)
$$

along the primes. Forced and excluded primes are included. The weaker estimate
$\eta_p=\nu/p+O(p^{-2})$ alone is not the hypothesis of this theorem.

The [finite phase theorem](PrimeFactorOscillations/Assembly/GapSpectrumPhase.lean)
proves that the least $H_{\ast}$ with $\gamma_{H_{\ast}}=1$ exists, and that the supremum
is attained among $2\le H\le H_{\ast}$. For sufficiently large fixed $\nu$,

$$
\Lambda(\nu)=\frac1{\nu+H_{\ast}},
\qquad
\frac1{\Lambda(\nu)}-\nu=H_{\ast}.
$$

Here $\gamma_H=1$ is a double-logarithmic limsup condition. It does not assert
positive density or a power lower bound at every large cutoff. The theorem
does not determine $H_{\ast}$ numerically, and it makes no uniformity assertion
when the family, degree or exceptional primes grow with the rank.

## Formal verification

[Challenge](Challenge.lean) states the two public theorems using only Mathlib
primitives. [Solution](Solution.lean) contains their proofs. The two deliberate
Challenge placeholders do not enter the Solution proof dependencies.

| Initial-publication check | Result |
|---|---|
| Owned Lean modules | 167 verified in the pinned Windows environment |
| Public statements | 2 compiled Challenge/Solution type identities checked |
| Theorem axiom closures | 12 checked; standard Lean foundations only |
| Python tests | 51 passed |
| Dependency builds | 0 |

The allowed foundations are `propext`, `Classical.choice` and `Quot.sound`.
See the [verification record and logs](paper/VERIFICATION.md) for exact scope
and source hashes. Official Comparator/NanoDa replay has not been run.

## Build

Use the existing Windows Lean 4.34.0 environment and matching pinned artifacts:

~~~powershell
python scripts/build_project.py
python scripts/proof_audit.py
python scripts/check.py --profile research
~~~

**Start with [BUILD.md](BUILD.md) for prerequisites.** Erdos 690 supplies its
own [published cache](https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/releases/tag/v0.1.0-conditional.ef3c9311d42b);
this repository does not repackage or rebuild it. The full build also needs
the matching analytic port artifacts documented in
[dependency reuse](DEPENDENCY_REUSE.md). Their upstream compatibility
publication remains pending, so the Erdos cache alone is not a complete
fresh-machine setup.

Missing artifacts cause an error, never a dependency build. Do not substitute
`lake build` or `lake lint`. This repository currently has no CI or automated
dependency updates.

## Sources and open questions

The first-difference and symmetric-polynomial framework builds on
[Wang–Crapis](https://arxiv.org/html/2605.08542v1). The exact frequency spectrum
and affine-product application are separate developments. This is AI-assisted
research; novelty assessment and independent expert review remain outstanding.

The [research plan](RESEARCH_PLAN.md) records the next target: an independent
late-ascent supply argument that does not assume the stronger prime gaps it
aims to prove. Complete generic odd unimodality classification also remains
open. Fixed local density limits do not establish moving-tail Dickman laws,
Goldbach representation lower bounds, generated-state reachability, or an
RH/Robin result.

[Contributing](CONTRIBUTING.md) · [Mathlib candidates](MATHLIB_PORTING.md) ·
[Source alignment](formalization.yaml) ·
[Optional Palomar submission](https://submit.palomar-registry.org/)

Original material is licensed under [Apache-2.0](LICENSE). The paper also
offers CC-BY-4.0; see [licensing](LICENSING.md).

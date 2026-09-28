# Prime Factor Oscillations

**How often can a prime-factor density fall and rise again—and what do those reversals reveal about prime gaps?**

[Read the paper](paper/research-paper.pdf) · [TeX source](paper/research-paper.tex) · [Theorem ledger](paper/THEOREM_STATUS.md) · [Verification](paper/VERIFICATION.md)

**Paper:** *Prime-factor density reversals and the spectrum of bounded prime gaps*.

Fix a position in the ordered list of distinct prime factors. For each prime,
ask how often it occupies that position. The resulting density can drop and
later rise again. Every fixed rank eventually stops rising, yet the maximum
number of separated reversals grows double-exponentially with the rank.

This project proves the exact double-logarithmic upper growth rate for a class
of local laws, realizes it for products of affine prime sums, and connects late
ascents to recurring short prime gaps. The maintained results are formalized
in **Lean 4.34.0**.

## The arithmetic result

Fix a nonempty family

$$
F(p,q)=\prod_{j=1}^{m}\bigl(c_j(p+q)+d_j\bigr),
\qquad c_j\in\mathbb Z_{\gt0},\quad d_j\in\mathbb Z,
$$

with distinct rational roots: $c_i d_j\ne c_j d_i$ for $i\ne j$.
Sample all ordered prime pairs $p,q\le X$, including the diagonal.

For every fixed rank and prime, the limiting density of that prime as the
specified distinct prime factor of $|F(p,q)|$ exists. At every fixed rank,
the maximum number $N_F(k)$ of separated descent-then-ascent witnesses is
finite and attained. Its exact rate is

$$
\limsup_{k\to\infty}\frac{\log\log(3+N_F(k))}{k}
=\Lambda(m)\gt 0.
$$

The input-size limit comes **first**, with family, rank and prime fixed.
Outputs are weighted by their prime-pair representations. Exceptional
primes—including forced common factors—are retained.

Examples include $p+q$, $p+q+1$, $2(p+q)-1$, every fixed $c(p+q)+d$
with positive $c$, and products of distinct such factors. Each one-factor
example has rate $\Lambda(1)$, although their finite-rank densities differ.

[Arithmetic proof](PrimeFactorOscillations/Assembly/AffineSpectrum.lean) ·
[Density limits](PrimeFactorOscillations/Proof/AffinePairs/RankDensity.lean)

## What determines the rate?

Let $G_H(X)$ count consecutive prime gaps at most $H$ whose lower prime is
at most $X$. Define

$$
\gamma_H=\limsup_{X\to\infty}
\frac{\log\log(3+G_H(X))}{\log\log X},
\qquad
\Lambda(\nu)=\sup_{H\ge2}\frac{\gamma_H}{H+\nu}.
$$

The [general theorem](PrimeFactorOscillations/Assembly/ReciprocalSmoothSpectrum.lean)
applies to each fixed law with $0\le\eta_p\le1$, $\nu\gt0$, and

$$
\eta_p^{-1}=\frac p\nu+\beta+o(1)
$$

along sufficiently large primes. Finite forced and excluded coordinates are
allowed. The weaker estimate $\eta_p=\nu/p+O(p^{-2})$ alone is not its hypothesis.

The spectrum is a maximum over finitely many gap classes. If $H_{\ast}$ is the
least class with $\gamma_{H_{\ast}}=1$, then for sufficiently large fixed $\nu$,

$$
\Lambda(\nu)=\frac1{H_{\ast}+\nu}.
$$

This recovers $H_{\ast}$ from the rate. Its numerical value is not determined here.
The condition $\gamma_H=1$ is a double-logarithmic limsup condition, not a
positive-density claim.

## Why the proof works

The paper explains the mechanism in plain English before introducing notation:

1. **Compare one step exactly.** A symmetric-polynomial ratio competes with
   the next prime gap. Short gaps favor ascents; long gaps favor descents.
2. **Control the ratio as rank grows.** The natural location scale is the
   logarithm of the logarithm of the prime.
3. **Keep witnesses distinct.** Periodic composite blocks provide preceding
   long gaps. Selecting alternate occupied blocks loses only a fixed
   counting factor and yields strictly separated reversals.
4. **Match the rates.** Actual gap frequencies supply the lower bound; each
   ascent's individual gap imposes its upper location cutoff.

For the ordinary integer law and generic odd law, the
[canonical theorem](PrimeFactorOscillations/Assembly/Headline.lean) also gives,
for every $\varepsilon\gt0$ and every sufficiently large $k$,

$$
\exp(\exp(k/602))\le N(k)\le
\exp\bigl(\exp((1/3+\varepsilon)k)\bigr).
$$

The lower constant uses a conservative, formally closed width-600 prime-window
count. The general transfer allows every coefficient below $1/(H+1)$ when
windows of width $H$ have an eventual positive-power counting lower bound.
Bare infinitude of bounded gaps does not supply that count.

## Late ascents and prime gaps

The [recurrence equivalence](PrimeFactorOscillations/Assembly/GapRecurrence.lean)
says: for $H\ge1$ and

$$
\frac1{H+2}\lt b\lt\frac1{H+1},
$$

recurring gaps at most $H$ are equivalent to simultaneous ascents in both
canonical densities with $\log\log(p-1)\ge bk$, at arbitrarily large ranks
and lower primes. Both parameters must be unbounded.

If $h$ is the least recurring gap, the critical location coefficient is
$1/(h+1)$; no claim at equality is made. Sufficiently late ascents beyond
a fixed coefficient $b\gt1/5$ must cross twin primes.
**An independent unbounded supply of those ascents remains open.**
The implication is proved; no new prime-gap bound is claimed.

## Historical position and limits

Erdős posed the unimodality question in 1979. Cambie proved ranks 1–3
unimodal and checked counterexamples for ranks 4–20. Wang–Crapis proved
non-unimodality for every rank at least four. This work concerns quantitative
reversal counts, their exact spectrum, and affine arithmetic realizations.

The paper distinguishes this from Cambie's divisor-interval density in
Erdős 692 and discusses the Erdős–Tenenbaum correction to the density's mode.
See the [primary-source review](paper/SOURCE_REVIEW.md). This is AI-assisted
research; independent expert review and novelty assessment remain outstanding.

The results do not prove a Goldbach representation lower bound, a moving-tail
distribution law, or an RH/Robin statement. Current exploratory work toward
independent late-ascent supply is excluded from the paper.

## Verification and build

[Challenge](Challenge.lean) gives the public statements over Mathlib primitives;
[Solution](Solution.lean) contains real proofs. The deliberate Challenge
placeholders do not enter the Solution proof closures. The recorded audit
checks two compiled public statement identities and twelve theorem closures,
using only the standard foundations propext, Classical.choice and Quot.sound.

Start with [BUILD.md](BUILD.md). In the pinned Windows environment:

~~~powershell
python scripts/build_project.py
python scripts/proof_audit.py
python scripts/check.py --profile research
~~~

Erdos 690 supplies its own
[published cache](https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/releases/tag/v0.1.0-conditional.ef3c9311d42b);
this repository neither repackages nor rebuilds it. The full build also needs
the matching analytic artifacts in [DEPENDENCY_REUSE.md](DEPENDENCY_REUSE.md).
Their compatibility publication is pending, so a complete fresh-machine
bootstrap is not yet supplied. Missing artifacts cause an error, never a
dependency build. Do not substitute lake build or lake lint.

[Verification records](paper/VERIFICATION.md) separate proof checks from the
paper revision. Official Comparator/NanoDa replay has not been run.
There is no CI or automated dependency-update workflow.

[Contributing](CONTRIBUTING.md) · [Research plan](RESEARCH_PLAN.md) ·
[Source alignment](formalization.yaml) · [Mathlib candidates](MATHLIB_PORTING.md) ·
[Optional Palomar submission](https://submit.palomar-registry.org/)

Original material: [Apache-2.0](LICENSE). The paper also offers CC-BY-4.0;
see [LICENSING.md](LICENSING.md).

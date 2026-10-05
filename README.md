# Prime Factor Oscillations

**How do prime gaps control prime-factor density reversals, and what does their precisely centered coefficient ratio reveal about RH?**

[Read the paper](paper/research-paper.pdf) · [TeX source](paper/research-paper.tex) · [Theorem ledger](paper/THEOREM_STATUS.md) · [Verification](paper/VERIFICATION.md)

**Paper:** *Prime-factor densities: bounded-gap spectra and a Riemann hypothesis criterion*.

Fix a position in the ordered list of distinct prime factors. For each prime,
ask how often it occupies that position. The resulting density can drop and
later rise again. Every fixed rank eventually stops rising, yet the maximum
number of separated reversals grows double-exponentially with the rank.

This project proves the exact double-logarithmic upper growth rate for a class
of local laws, realizes it for products of affine prime sums, and connects late
ascents to recurring short prime gaps. It also proves an RH equivalence for
the actual ordinary-density coefficient ratio at a growing rank, by transferring
the classical Nicolas prime-product error with its sign intact.
The maintained results use **Lean 4.34.0**. RH and Hardy–Littlewood assumptions
remain explicit in every conditional statement.

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
positive-density claim. This is an exact upper envelope of gap frequencies;
it does not determine every individual frequency exponent.

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
5. **Retain the full reference for RH.** A paired coefficient comparison
   isolates the Nicolas error; a finite inverse-log-log expansion is too coarse
   to preserve this much smaller signal.

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

## A moving-rank criterion for RH

The RH theorem below concerns the **ordinary integer law**. Its automatic
extension to every affine prime-pair family is not claimed.

For a real cutoff $x$, let

$$
G_x(z)=\prod_{p\le x}\left(1+\frac z{p-1}\right),
\qquad
a_r(x)=[z^r]G_x(z),
\qquad
R_r(x)=\frac{a_{r-1}(x)}{a_r(x)}.
$$

At the prefix $x=p-1$, an actual next gap $g$ produces a rank $k$ ascent
exactly when $R_{k-1}(x)\gt g+1$, with a positive denominator.
The real-valued gap threshold is $R_{k-1}(x)-1$.

Use the full reference

$$
\mathcal H(z)=\prod_p\left(1+\frac z{p-1}\right)(1-1/p)^z,
\qquad
C_r(u)=[z^r]\mathcal H(z)e^{uz},
$$

and set $L(x)=\gamma+\log\log\theta(x)$,
$r(x)=\lfloor\alpha L(x)\rfloor$ for a fixed $\alpha\gt0$.
For all sufficiently large cutoffs the relevant denominators are positive.
The [maintained two-way criterion](Solution.lean) is

$$
\mathrm{RH}
\quad\Longleftrightarrow\quad
R_{r(x)}(x)\lt\frac{C_{r(x)-1}(L(x))}{C_{r(x)}(L(x))}
\quad\text{eventually}.
$$

This holds for **each fixed positive** $\alpha$. It concerns a centered ratio
whose rank grows with the endpoint. Every fixed-rank raw density still
eventually decreases.

The decisive estimate compares the actual ratio with the full reference.
Writing $\Delta_r$ for their difference and

$$
F(x)=\log\left(e^\gamma\log\theta(x)
               \prod_{p\le x}(1-1/p)\right),
$$

the error is bounded uniformly in fixed positive compact rank bands by

$$
\left|\Delta_r(x)-\frac r{L(x)^2}F(x)\right|
\le K\left(\frac{|F(x)|}{L(x)^2}+\frac1{rx}\right).
$$

Under RH, Nicolas's classical expansion gives the negative prime-square bias
and its bounded zeta-zero wave. If RH is false, the completed actual-ratio
theorem gives one $b\in(0,1/2)$ such that, for every fixed $\alpha\gt0$,

$$
\limsup_{x\to\infty}x^bL(x)\Delta_{r(x)}(x)=+\infty,
\qquad
\liminf_{x\to\infty}x^bL(x)\Delta_{r(x)}(x)=-\infty.
$$

Endpoints may depend on $\alpha$ and the sign. The nonlinear correction to
the Nicolas integral is retained; an RH estimate is not used under false RH.

[Coefficient transfer](PrimeFactorOscillations/Helpers/PrimeProfileCanonicalLinearization.lean) ·
[Power excursions](PrimeFactorOscillations/Helpers/PrimeProfilePowerExcursions.lean) ·
[Public consumers](Solution.lean)

## What RH and Hardy–Littlewood contribute

Under RH, the prime-product clock differs from $\theta(x)$ by
$(2+W(x)+o(1))\sqrt{x}$, with $|W(x)|\le 2+\gamma-\log(4\pi)\approx0.04619$.
This refines the reference location at which a specified gap can produce
an ascent. The center is $\theta(x)$, not $x$.

The ordinary reversal count also satisfies the sharper RH upper bound

$$
\log\log N(k)\le
\frac{k-1}{3}-\gamma-\frac{\mathcal H'(3)}{\mathcal H(3)}
+\frac C{k-1}
$$

eventually, for a fixed constant $C$. This is a capacity bound and does not
supply additional small gaps.

A separate, explicit hypothesis
$\pi_2(X)\sim C_2X/(\log X)^2$ with $C_2\gt0$ supplies twins in every
sufficiently large interval of fixed proportional width. It implies that
the last actual ascent $P_k$ is the last eligible twin and $P_k/X_k\to1$,
where $X_k$ is the potential twin-ascent cutoff.
The paper includes the proof; the compiled conditional relative-location
consumer still awaits a maintained public export.

| Input | Consequence |
|---|---|
| Infinitely many gaps at most $H$ | Late-ascent location coefficient at least $1/(H+1)$, in the limsup sense |
| Infinitely many twins | Critical late-ascent location coefficient exactly $1/3$ |
| Positive global twin-count asymptotic | Last ascent approaches its potential cutoff along the full rank sequence; sharp canonical count rate $1/3$ |
| RH | Precise signed reference displacement and stronger ascent/count upper bounds |

The global twin asymptotic gives no square-root or polylogarithmic bound on
$X_k-P_k$. RH supplies no independent twin-prime count here. The connection
to Robin and Lagarias is through their known equivalences with RH; no new
colossally abundant optimization theorem is claimed.


## Historical position and limits

Erdős posed the unimodality question in 1979. Cambie proved ranks 1–3
unimodal and checked counterexamples for ranks 4–20. Wang–Crapis proved
non-unimodality for every rank at least four. Their first-difference criterion,
the finite generating product, and fixed-rank eventual decrease are prior work.
Our quantitative spectrum extends that starting point.

The paper distinguishes this from Cambie's divisor-interval density in
Erdős 692 and discusses the Erdős–Tenenbaum correction to the density's mode.
See the [primary-source review](paper/SOURCE_REVIEW.md). This is AI-assisted
research; independent expert review and novelty assessment remain outstanding.

Nicolas's RH criterion, its spectral error, the prime-square constant two,
and the normalized Euler-product profile are established mathematics.
The **potentially new** contributions are the exact reversal-frequency
spectrum and the uniform transfer of that signed error into the actual
moving-rank coefficients, together with their stated applications.
See [Nicolas (2012)](https://arxiv.org/abs/1202.0729v2) and
[Kowalski–Nikeghbali](https://arxiv.org/abs/0905.0318v2).

The results do not prove RH, a new numerical prime-gap bound, a Goldbach
representation lower bound, or a moving-tail distribution law.
Speculative proof strategies and unfinished supply estimates are excluded
from the paper's theorem claims.

## Verification and build

[Challenge](Challenge.lean) gives the public statements over Mathlib primitives;
[Solution](Solution.lean) contains real proofs. The deliberate Challenge
placeholders do not enter the Solution proof closures. The recorded audit
checks two compiled public statement identities and 218 selected theorem
closures, using only the standard foundations propext, Classical.choice and
Quot.sound. The two Challenge statements concern the original reversal and
affine-spectrum results. The later RH results have maintained Solution
consumers with their conditional hypotheses explicit.

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

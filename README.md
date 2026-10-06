# Prime Factor Oscillations

**How do prime gaps control prime-factor density reversals, and what does their precisely centered coefficient ratio reveal about RH?**

[Read the paper](paper/research-paper.pdf) · [TeX source](paper/research-paper.tex) · [Theorem ledger](paper/THEOREM_STATUS.md) · [Verification](paper/VERIFICATION.md)

**Paper:** *Prime-factor densities: bounded-gap spectra and Riemann hypothesis criteria*.

Fix a position in the ordered list of distinct prime factors. For each prime,
ask how often it occupies that position. The resulting density can drop and
later rise again. Every fixed rank eventually stops rising, yet the maximum
number of separated reversals grows double-exponentially with the rank.

This project proves the exact double-logarithmic upper growth rate for a class
of local laws, realizes it for products of affine prime sums, and connects late
ascents to recurring short prime gaps. It also proves RH equivalences for
growing-rank coefficient ratios throughout a class of local laws, including
the actual affine prime-pair families, by transferring the classical Nicolas
prime-product error with its sign intact and retaining forced-prime rank shifts. Further
criteria use positive excursion area and prescribed localized reversal counts.
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

We first give the **ordinary integer law** as an example. The following section
states the generalized theorem and its precise family qualifications.

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

## RH criteria for qualifying families

An arithmetic family must realize the independent finite-prime limiting law;
marginal probabilities alone are insufficient. The full coefficient theorem
applies to each **fixed** independent local law whose
nonnegative odds satisfy, for some fixed $\nu\gt0$ and $D\ge0$,

$$
w_p=\frac{\eta_p}{1-\eta_p},
\qquad
\left|w_p-\frac{\nu}{p-1}\right|\le\frac{D}{(p-1)^2}.
$$

At a forced prime $\eta_p=1$, set $w_p=0$ and retain its exact rank shift.
For probabilities $0\le\eta_p\le1$, the weaker estimate
$\eta_p=\nu/p+O(p^{-2})$ suffices for this RH theorem.
A limiting reciprocal offset is still required by the separate
reversal-spectrum theorem.

Define the **full family profile** and reference coefficients by

$$
\mathcal H_\eta(z)=\prod_p(1+w_pz)(1-1/p)^{\nu z},
\qquad
C_{\eta,r}(u)=[z^r]\mathcal H_\eta(z)e^{uz}.
$$

Let $U=\nu(\gamma+\log\log\theta(N))$, $r=\lfloor\alpha U\rfloor$ with
fixed $\alpha\gt0$, and let $a_{\eta,r}(N)$ be the coefficient of $z^r$
in $\prod_{p\le N}(1+w_pz)$. Then

$$
\mathrm{RH}
\iff
\frac{a_{\eta,r-1}(N)}{a_{\eta,r}(N)}
\lt
\frac{C_{\eta,r-1}(U)}{C_{\eta,r}(U)}
\quad\text{eventually}.
$$

The non-strict comparison is equivalent too. Both denominators are proved
positive on the relevant rank band. If the prefix has $f_N$ forced primes,
the actual probability-mass ratio uses ranks $f_N+r-1$ and $f_N+r$,
and the corresponding distinct-factor rank is $k=f_N+r+1$.

**Every reciprocal-smooth law and every affine prime-pair family above
qualifies.** For an affine family, $\nu=m$; a general law may have any
positive $\nu$. All finite exceptions enter the profile. These equivalences
need no bounded-gap or short-interval assumption.

The product criterion has exact constant
$\Gamma_\eta(z)=e^{\nu z\gamma}\mathcal H_\eta(z)$ for each fixed $z\gt0$.
The reference location for level $1+g/\nu$ satisfies

$$
\log\log T_{\eta,r,g}
=
\frac{r}{g+\nu}-\gamma
-\frac1\nu
 \frac{\mathcal H_\eta'(1+g/\nu)}{\mathcal H_\eta(1+g/\nu)}
+O_{\eta,g}(r^{-1}).
$$

This is a **reference cutoff**; identifying the last actual ascent still
requires the appropriate local-threshold precision and prime-gap supply.

A broader normalized logarithmic-tail condition suffices for the product
criterion alone. Neither qualification is claimed to classify every possible
family. Sparse support families need their own check. Fixed finite combinations
of the qualified family errors retain a single explicit multiple of the Nicolas
error; canceling that multiple cancels the RH signal at this precision.

[Family exports](PrimeFactorOscillations/Assembly/FamilyRHResults.lean) ·
[General coefficient criterion](PrimeFactorOscillations/Helpers/QuadraticProfileRH.lean) ·
[Actual affine mass criterion](PrimeFactorOscillations/Helpers/AffineRatioRH.lean) ·
[Full derivation](paper/research-paper.tex)

## Positive-area and localized-count RH criteria

The later results retain the small **signed difference from the full reference**.
They do not infer RH from the leading double-exponential reversal rate.

For any fixed positive moving-rank parameter, let
$S_\alpha(x)=L(x)^2\Delta_{\lfloor\alpha L(x)\rfloor}(x)/
\lfloor\alpha L(x)\rfloor$.
The maintained positive-area theorem gives

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\int_X^{2X}\max(S_\alpha(t),0)\,dt
=O\bigl(X^{1/4}(\log X)^B\bigr)
\quad\text{for some fixed }B\ge0.
$$

The same criterion holds for the Nicolas logarithm $F$.
False RH produces positive intervals long enough to violate this bound.
These are equivalences; an independent quarter-power upper bound remains open.

[Positive-area proof](PrimeFactorOscillations/Helpers/PrimeProfilePositiveArea.lean) ·
[Persistent excursions](PrimeFactorOscillations/Helpers/NicolasPowerPersistence.lean)

The paper also proves a criterion using **prescribed separated reversal cells**.
Choose the fixed width $H$ supplied by the short-interval theorem of
[Alweiss–Luo, Corollary 1.2](https://arxiv.org/html/1707.05437v1).
Use about $X^{1/10}/30$ separate cells, rank
$r_X+1$ with $r_X=\lfloor(H+2)L(X)\rfloor$, and the grid
$t_j=1+j/\lceil\sqrt X\rceil$ in $[1,H+1]$.
The local law is $\eta_p(t)=t/(p-1+t)$, whose exact ascent test is
$g+t\lt R_{r_X}(p-1)$.

Let $C_H(X)$ count these actual descent–ascent witnesses across the grid.
Let $\overline C_H(X)$ count the full-reference predictions on the
**same actual pairs and grid**. Then

$$
\mathrm{RH}
\quad\Longleftrightarrow\quad
C_H(X)\le\overline C_H(X)\quad\text{eventually},
$$

and also

$$
\mathrm{RH}
\quad\Longleftrightarrow\quad
\exists C\gt0:\qquad
C_H(X)-\overline C_H(X)\le C X^{1/10}
\quad\text{eventually}.
$$

Under false RH, the normalized signed excess is unbounded above.
The cell construction includes a fixed long-gap descent before each
selected short gap, so its witnesses are genuinely separated.

This is a localized count over a growing finite grid of laws, **not**
the original maximal count for one fixed law. Its reference retains
the actual theta prefix and the entire coefficient profile.
A globally recurring gap width such as 186 cannot replace the
all-short-interval sampling input. No smaller gap or independent
signed-count upper bound is proved here.

**Formalization boundary:** both count equivalences and the explicit cell
construction have maintained, audited Lean proofs. Their sole external
arithmetic premise is the qualitative all-short-interval prime-pair input
at exponent $3/5$, with both endpoints in the interval. The published
Alweiss–Luo theorem supplies that premise in ordinary mathematics; its
proof is not installed as a Lean dependency. No project axiom asserts it.

[Count equivalences and sampling](PrimeFactorOscillations/Helpers/LocalReversalSampling.lean) ·
[Actual finite counts](PrimeFactorOscillations/Helpers/TiltedReversalCount.lean) ·
[RH count upper bound](PrimeFactorOscillations/Helpers/TiltedCountRHUpper.lean) ·
[Uniform window bands](PrimeFactorOscillations/Helpers/PrimeProfileWindowBands.lean) ·
[False-RH detection margin](PrimeFactorOscillations/Helpers/TiltedCountExcursion.lean)

The maintained **ascent-only** versions use every actual short pair in
$[X+1,X+1+\lceil2X^{7/10}\rceil]$. They characterize RH by either eventual
$A_H\le B_H$ or eventual $A_H-B_H\le C X^{7/10}$ for some fixed $C\gt0$.
The quantitative all-short-interval pair count at exponent $3/5$ is an
explicit premise, with the same source boundary as above.

[Ascent-only criteria](PrimeFactorOscillations/Helpers/LocalAscentSampling.lean) ·
[Exact signed excess and rounding](PrimeFactorOscillations/Helpers/TiltedSignedExcess.lean)

Growing tilts also retain RH criteria. For each fixed $c\gt0$, the paper
computes the next term when the tilt is $c\sqrt{x}$, using a uniform cubic
remainder and the prime-square tail.
[Growing-tilt proof](PrimeFactorOscillations/Helpers/NicolasGrowingTiltAsymptotic.lean).

The [growing-moment theorem](PrimeFactorOscillations/Helpers/NicolasMomentConsumer.lean)
gives another sufficient condition for RH. Its proposed analytic moment
bound remains open. The fixed-second-moment consumer gives an area envelope
that is too weak to imply RH.

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

eventually, for a fixed constant $C$. If actual consecutive gaps are
eventually at least $h$, the maintained general theorem replaces $3$ by
$h+1$ throughout this reference. It retains finite exceptions and the
attained maximum. This capacity bound supplies no additional gaps.

[General RH capacity](PrimeFactorOscillations/Assembly/GeneralRHSharpCapacity.lean)

A separate, explicit hypothesis
$\pi_2(X)\sim C_2X/(\log X)^2$ with $C_2\gt0$ supplies twins in every
sufficiently large interval of fixed proportional width. It implies that
the last actual ascent $P_k$ is the last eligible twin and $P_k/X_k\to1$,
where $X_k$ is the potential twin-ascent cutoff.
The full conditional proof, including the cutoff and last-ascent
identification, is maintained and audited in
[the Hardy–Littlewood location development](PrimeFactorOscillations/Assembly/ConditionalLocation/TwinCountAsymptoticBridge.lean).

| Input | Consequence |
|---|---|
| Infinitely many gaps at most $H$ | Late-ascent location coefficient at least $1/(H+1)$, in the limsup sense |
| Infinitely many twins | Critical late-ascent location coefficient exactly $1/3$ |
| Positive global twin-count asymptotic | Last ascent approaches its potential cutoff along the full rank sequence; sharp canonical count rate $1/3$ |
| RH | Precise signed reference displacement and stronger ascent/count upper bounds |

The global twin asymptotic gives no square-root or polylogarithmic bound on
$X_k-P_k$. The maintained exact-gap coverage theorem proves that an error
$o(\sqrt X/\log^4 X)$ around the full $c_h\operatorname{Li}_2(X)$ main term
would force an actual gap of width $h$ in every sufficiently late interval
of length $\sqrt X/\log^2 X$. That stronger error estimate is a hypothesis.
See the [exact-gap coverage proof](PrimeFactorOscillations/Helpers/GapFrequencyCoverage.lean).

If smaller gaps occur only finitely often, that local coverage tracks the
actual last ascent to square-root accuracy relative to the full reference
clock. Under RH it gives

$$
\frac{T_{k-1,h}-\theta(P_k-1)}{\sqrt{P_k}}
=2+W(P_k-1)+o(1),
$$

where $T_{r,h}=\exp(\exp(u_{r,h+1}-\gamma))$ and the reference root satisfies
$C_{r-1}(u_{r,h+1})/C_r(u_{r,h+1})=h+1$ near $r/(h+1)$.
The proof constructs these roots and derives the last-ascent location;
spatial closeness is not an extra hypothesis. The wave remains evaluated
at the actual prefix $P_k-1$.
[Fine location and RH wave](PrimeFactorOscillations/Assembly/ConditionalLocation/FineLocationRH.lean).
RH supplies no independent twin-prime count here. The connection
to Robin and Lagarias is through their known equivalences with RH; no new
colossally abundant optimization theorem is claimed.

If twins were finite, the eventual minimum gap would be at least four
and the corresponding reference threshold would change from three to five.
If, additionally, the ordinary count coefficient were exactly $1/5$,
the spectrum formula would force $\gamma_4=1$ and
$\Lambda(\nu)=1/(4+\nu)$ for every fixed $\nu\gt0$.
The RH upper envelope changes consistently with that threshold; these
statements yield no contradiction. More generally, the current RH sign
comparison has no transition at any fixed positive gap width.


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
checks two compiled public statement identities and 539 selected theorem
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

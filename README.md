# Prime Factor Oscillations

Exact reversal spectra for prime-factor rank densities, formalized in Lean 4.34.0.

[Paper (PDF)](paper/research-paper.pdf) · [LaTeX source](paper/research-paper.tex) ·
[Theorem ledger](paper/THEOREM_STATUS.md) ·
[Build instructions](BUILD.md) · [Verification](paper/VERIFICATION.md)

## Arithmetic headline

Fix a nonempty family

    F(p,q) = product_(j=1..m) [c_j*(p+q)+d_j],

where the c_j are positive integers, the d_j are integers, and
c_i*d_j != c_j*d_i for distinct indices. Sample all ordered prime pairs
p,q <= X, including the diagonal, with denominator pi(X)^2.

[Assembly/AffineSpectrum.lean](PrimeFactorOscillations/Assembly/AffineSpectrum.lean)
proves `AffineSumFamily.exists_sharp_arithmetic_reversal_rate_all_ranks`:

- For each fixed positive rank k and prime ell, the density of ell as the kth
  smallest distinct prime factor of |F(p,q)| exists.
- At every fixed rank, its sequence over ell is eventually nonincreasing and
  has an attained finite maximum N_F(k) of separated descent-then-ascent
  occurrences.
- Its exact positive upper growth rate is

      limsup_k log(log(3+N_F(k)))/k = Lambda(m) > 0,
      Lambda(nu) = sup_(H>=2) gamma_H/(H+nu),
      gamma_H = limsup_X log(log(3+G_H(X)))/log(log X).

G_H(X) counts actual consecutive prime gaps at most H with lower prime at
most X. The input-size limit is taken first, separately for each fixed
family, rank and prime. The rate formula is a limsup statement.

This includes p+q, p+q+1, 2(p+q)-1, every fixed c*(p+q)+d with c>=1,
and the displayed products. All finite coefficient and root exceptions are
retained. Outputs are weighted by their prime-pair representations.

[RankDensity.lean](PrimeFactorOscillations/Proof/AffinePairs/RankDensity.lean)
proves the arithmetic interpretation from fixed-modulus prime input limits,
exact CRT pattern counts, the finite Bernoulli rank sum, and a vanishing
finite zero-output correction. It assumes no local-independence hypothesis.

[Challenge.lean](Challenge.lean) states the arithmetic headline and the earlier
canonical bound using only Mathlib primitives, with two deliberate statement
placeholders. [Solution.lean](Solution.lean) supplies their real proofs.
The public arithmetic declaration is
`PrimeFactorOscillations.publicAffinePrimePairSpectrum`.

## General law and dimension profile

[Assembly/ReciprocalSmoothSpectrum.lean](PrimeFactorOscillations/Assembly/ReciprocalSmoothSpectrum.lean)
proves the same exact rate for each fixed real local law with nu>0,
probabilities eta_p in [0,1], and

    1/eta_p = p/nu + b + o(1)

along the primes. Forced and excluded primes are included. Actual finite
maximal reversal counts exist at every rank. The weaker assumption
eta_p=nu/p+O(p^-2) alone is not the hypothesis of this theorem.

[Assembly/GapSpectrumPhase.lean](PrimeFactorOscillations/Assembly/GapSpectrumPhase.lean)
proves that the least H_* with gamma_(H_*)=1 exists unconditionally.
For each nu>0 the supremum is attained among 2<=H<=H_*. For sufficiently
large fixed nu,

    Lambda(nu) = 1/(nu+H_*),    1/Lambda(nu)-nu = H_*.

The arithmetic family has nu=m, so the same recovery holds across fixed
families of sufficiently large degree. It does not determine H_* numerically
or improve a bounded-prime-gap theorem. Here gamma_H=1 is a double-logarithmic
limsup condition; it does not assert positive density or a power lower bound
at every large cutoff. There is no uniformity assertion
when the family, degree, or exceptional primes grow with the rank.

## Retained canonical bound

[Assembly/Headline.lean](PrimeFactorOscillations/Assembly/Headline.lean)
proves the unconditional double-exponential bounds for ordinary integer
densities and the generic odd local law:

    exp(exp(a*k)) <= N(k) <= exp(exp((1/3+epsilon)*k))

for every epsilon>0 and all sufficiently large k, with one fixed a>0.
The implementation uses a=1/602. Its general transfer accepts any fixed
width H with an eventual positive-power supply of prime windows and every
0<a<1/(H+1). The numerical input is a conservative formally closed baseline.

[Assembly/Spectrum.lean](PrimeFactorOscillations/Assembly/Spectrum.lean)
also identifies the common canonical limsup rate as Lambda(1).

The first-difference and symmetric-polynomial framework builds on
[Wang--Crapis](https://arxiv.org/html/2605.08542v1).
The exact frequency spectrum and actual affine-product application are
separate developments. They are potentially new results; broader literature
comparison and independent expert assessment remain necessary.

## Late ascents and recurring gaps

[Assembly/GapRecurrence.lean](PrimeFactorOscillations/Assembly/GapRecurrence.lean)
proves an exact converse as well as the forward transfer. For an integer H>=1
and 1/(H+2)<b<1/(H+1), recurring consecutive gaps at most H are equivalent to:

    for every K,Q, there exist k>=K and consecutive primes p<q with p>=Q,
    log(log(p-1)) >= b*k, and strict ascents in both canonical densities.

If h is the least recurring gap, the critical late-ascent coefficient is
1/(h+1): every smaller positive coefficient has arbitrarily late simultaneous
ascents, while every larger coefficient has eventual strict descent.
These are threshold statements; no assertion is made at equality.

[GapScaleCutoff.lean](PrimeFactorOscillations/Proof/Upper/GapScaleCutoff.lean)
also proves that sufficiently late ascents beyond any fixed coefficient
b>1/5 must cross twin primes. An independent unbounded supply would therefore
prove twin-prime infinitude. That supply remains open. A single finite
ascent does not prove an infinitude statement.

## Shared build and verification

Research probes and maintained modules use the same Windows Lean 4.34.0
compiler, maintained object directory and pinned analytic artifact view.

    python scripts/build_project.py
    python scripts/proof_audit.py
    python scripts/check.py --profile research

The build compiles only owned source. The audit compiles Challenge, compares
both public theorem types in separate environments, and checks twelve theorem
closures against standard foundational axioms. Complete local logs are
retained separately from the official Comparator/NanoDa release checks.

See [BUILD.md](BUILD.md) for prerequisites and commands.
[data/analytic-artifacts.json](data/analytic-artifacts.json) records the exact
artifact view. Erdos 690 supplies its own published cache; this repository
does not redistribute it. The full build additionally requires the matching
analytic port artifacts listed in that manifest. Their upstream compatibility
publication remains pending, so the Erdos cache alone is not a complete
fresh-machine setup. Missing or changed artifacts cause an error, never a
dependency build.

The original [Erdos 690 repository](https://github.com/kimihiro64/erdos-690-prime-factor-unimodality)
is pinned at `ef3c9311d42b61db59f81d99741b5819d1986436`.
Released oleans are reused without rebuilding it or promoting its conditional
classification. See [DEPENDENCY_REUSE.md](DEPENDENCY_REUSE.md).
Do not substitute `lake build` or `lake lint`, whose dependency scheduling
can violate the cache-only requirement.

## Scope and next work

[RESEARCH_PLAN.md](RESEARCH_PLAN.md) records the proof chain and open questions.
Complete generic odd unimodality classification remains open. Fixed local
limits do not establish moving-tail Dickman laws, Goldbach representation
lower bounds, generated-state reachability, or an RH energy contraction.
Finite fixed-rank reversal counts do not assert infinitely many reversals
at a single rank.

Small probes and audits live in this main repository's ignored .research
directory and share the public environment. Completed proofs move promptly
to maintained owners.

This initial public source repository has no CI or automated dependency
updates. It is an AI-assisted research formalization; independent expert
review has not been obtained. The
[Palomar submission form](https://submit.palomar-registry.org/) remains a
separate optional submission after its required checks.
[MATHLIB_PORTING.md](MATHLIB_PORTING.md) records reusable candidates;
[SIBLING_CAPABILITIES.md](SIBLING_CAPABILITIES.md) is a discovery catalog.
Original material is [Apache-2.0](LICENSE); the paper also permits CC-BY-4.0.
See [LICENSING.md](LICENSING.md) for third-party licences.

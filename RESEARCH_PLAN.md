# Research plan and exact obligations

## Proved headline

For every fixed reciprocal-smooth probability law

    nu > 0,   eta_p in [0,1],   1/eta_p = p/nu + b + o(1),

every fixed-rank density sequence is eventually nonincreasing and has an
attained finite maximal count N_eta(k) of separated strict
descent-then-ascent occurrences. The exact sharp upper growth rate is

    limsup_k log(log(3+N_eta(k)))/k = Lambda(nu),
    Lambda(nu) = sup_(H>=2) gamma_H/(H+nu),
    gamma_H = limsup_X log(log(3+G_H(X)))/log(log X).

G_H(X) counts actual consecutive prime gaps at most H whose lower prime is
at most X. The rate is positive. Its supremum is a finite maximum over
2<=H<=H_*, where H_* is the least class with gamma_(H_*)=1. For every
sufficiently large fixed nu, Lambda(nu)=1/(nu+H_*).

The arithmetic application is also proved. For a fixed nonempty family

    product_(j=1..m) [c_j*(p+q)+d_j],

with positive integer coefficients and distinct rational roots, sample all
ordered prime pairs p,q<=X. The kth-distinct-prime-factor densities of the
absolute output exist and satisfy the theorem with nu=m. Finite coefficient,
common-factor and root-collision exceptions are retained in the exact local
probabilities. The limit X->infinity is taken at each fixed family, rank and
prime; only then is rank allowed to grow. This is representation weighting,
not uniform weighting of output integers.

The maintained owners are Assembly/ReciprocalSmoothSpectrum.lean,
Assembly/AffineSpectrum.lean, and Proof/AffinePairs/RankDensity.lean.
Challenge/Solution expose the arithmetic theorem directly over Mathlib
primitives as publicAffinePrimePairSpectrum. The canonical positive-constant
theorem and publicDoubleExponentialReversalBounds are preserved.

## Proof chain

1. Exact finite Bernoulli masses and deterministic rank shifts retain forced
   and excluded primes. The first-difference threshold is
   1/eta_q-1/eta_p+1 at consecutive primes p<q.
2. Mertens bounds and largest-weight symmetric-polynomial estimates give
   ratios uniformly over arbitrarily fast-growing prime cutoffs as k grows.
3. The lower rate keeps actual bounded-gap frequency supply, exact
   endpoint-to-rank rounding, preceding factorial-cell descents, bounded
   multiplicity and strict disjointness. Its limsup direction needs
   arbitrarily late frequency supply, not an assumed all-scale count.
4. The upper rate retains each gap's individual cutoff before bounding a
   finite sum. This produces the exact spectrum, not only a numerical bound.
5. For each fixed degree r>=1, the predecessor mass is eventually at most
   half the degree-r mass. Splitting exactly by the number of forced
   coordinates handles zero tails. The signed first difference then proves
   weak descent at every fixed rank, hence actual finite maxima at all ranks.
6. The fixed-modulus prime-pair law comes from normalized input progression
   counts. Nonunit input classes vanish, diagonals remain included, and
   intrinsic unit CRT counts prove full finite divisibility independence.
7. Summing fixed-cardinality pattern atoms gives the arithmetic rank formula.
   Zero outputs satisfy p+q<=sum_j |d_j|. Deleting this fixed finite set has
   vanishing probability, completing the literal factor-rank interpretation.
8. Quantitative prime windows supply a full-frequency gap class, proving
   positivity and the finite phase reduction. The conservative source is
   width 600; improving only the imported numerical width is not the target.

The all-prime local formula and its reciprocal remainder are proved in the
AffineLocalResidues and AffineReciprocalSmooth helpers. The stated family
includes p+q, p+q+1, 2(p+q)-1 and every fixed c*(p+q)+d with c>=1.
Proportional forms require removal of repeated roots before applying the
distinct-root statement.

The reciprocal profile's finite-minimum/concavity description is a
mathematical consequence of the finite maximum after restricting to classes
with gamma_H>0. No separately compiled concavity declaration is advertised.

## Quantitative status

The canonical baseline gives, for every epsilon>0 and all sufficiently
large k,

    exp(exp(k/602)) <= N(k) <= exp(exp((1/3+epsilon)*k)).

Its general transfer accepts fixed H, delta>0, an eventual X^delta supply
of prime windows, and any 0<a<1/(H+1). The exact spectrum determines the
leading limsup rate symbolically, not numerically. The actual affine
application installs the same sharp rate for a new arithmetic ensemble;
it does not increase the previously proved coefficient or determine H_*.

No numerical scan is used to certify any asymptotic conclusion. A
coefficient above 1/5 in the canonical problem would impose quantitative
twin-prime frequency information; no independent such estimate is proved.

## Next research target: independent late-ascent supply

The maintained theorem recurrent_short_gaps_iff_late_ascents identifies
recurring gaps at most H with simultaneous canonical ascents at every
threshold 1/(H+2)<b<1/(H+1), with both rank and lower prime unbounded.
The theorem late_ascent_critical_scale proves the exact threshold 1/(h+1)
when h is the least recurring gap. It does not assert a maximum or a limit
at the threshold.

The next mathematical objective is an independent density argument supplying
arbitrarily late ascents at some fixed b strictly above an established
1/(H0+1), then applying the converse to obtain recurring gaps smaller than H0.
Both H0 and its source assumptions must be recorded before claiming an
improvement. Stronger gaps cannot be assumed in the ascent-supply argument.
For any b>1/5, such unbounded supply would imply twin-prime infinitude.

The precise missing input is a uniform positive lower bound for the signed
first-difference numerator in that late range, with enough arithmetic control
to force actual consecutive-prime ascents. No such estimate is established
here. Finite experiments and analogy with CA optimization are not substitutes.

Minimal regularity under eta_p=nu/p+O(p^-2) remains a separate question.
The sharp-spectrum theorem above assumes the stronger reciprocal remainder.
Earlier repeated-CRT constructions and their all-interval PNT input are
background research, not additional proved headlines in this publication.

## Other retained directions

- Complete generic odd unimodality classification: low-rank witnesses and
  eventual non-unimodality do not classify every intermediate rank.
- Exact disjoint-ownership cancellation: retain the complete signed RH/CA
  target and its surviving supply. No energy contraction follows from the
  local/global analogy.
- Actual affine prime-pair moments and joint factorization: keep determinant
  exceptions and the named families; fixed finite local laws do not establish
  unbounded moments or moving-tail Dickman laws.
- Conditional last-ascent location: retain the Hardy-Littlewood twin-count
  hypothesis explicitly. This does not prove a new unconditional gap bound.

## Source and release boundary

Wang--Crapis, arXiv:2605.08542v1, proves ordinary non-unimodality for every
k>=4 using one descent followed by an ascent. Its exact first-difference
and symmetric-polynomial methods are background for this development.
The current official version, theorem text and conclusion were rechecked
on 27 September 2026. Narrow searches found no matching sharp-spectrum
or affine-product theorem; this is not a novelty certificate.

Classification: potentially new theorem, with known analytic inputs and
new arithmetic applications. Independent expert review remains necessary
for publication claims.

The local verification covers source, architecture, metadata, Python, owned
Lean, compiled public type identity and dependency axioms. Official
Comparator/NanoDa and expert review remain separate checks. This initial
publication contains source and artifact manifests, with no CI and no cache
redistribution. Erdos 690 publishes its own cache; additional analytic
compatibility publication remains deferred. See BUILD.md for the precise
cached-environment prerequisite. Legacy release/API-documentation helpers
are not part of the supported build and must not be used to schedule
dependency builds.

Work in the main repository and its ignored .research layer, using the
same Windows Lean 4.34.0 compiler and caches. No separate worktree or OS
switch is authorized. The initial public commit is a source publication;
it does not complete the independent late-ascent research target.

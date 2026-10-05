# Paper theorem and provenance ledger


## Completed RH development and conditional location - 4 October 2026

The revised paper keeps classical analytic inputs separate from new consumers.
The latest completed maintained audit covers 218 selected theorem closures
and two original Challenge/Solution statement pairs. Conditional hypotheses
are part of theorem types, not discharged by this audit.

| Paper result | Maintained consumer / owner | Mathematical and formal scope |
|---|---|---|
| Full-profile coefficient transfer, Theorem thm:linearization | publicDensityRatioLinearization in Solution; PrimeProfileCanonicalLinearization | Maintained, audited. The paper restricts the stronger formal statement to positive compact rank bands and provides the ordinary proof. |
| Moving-rank RH equivalence, Theorem thm:rh-ratio | publicMovingRankRHCriterion in Solution | Maintained, audited; each fixed alpha>0; actual ratio and theta-centered full reference. |
| Normalized actual-ratio wave, equation eq:ratio-wave | Consequence of publicDensityRatioLinearization and publicRHLogSpectralExpansion | Fully justified ordinary corollary; its separate normalized-wave declaration has not been compiled. Do not describe that combined declaration as audited. |
| Zero-dependent integral excursions | publicZeroDependentIntegralExcursions | Maintained, audited; actual zero rho, 1-Re(rho)<b<=1/2; both signs and arbitrarily large amplitudes. |
| Corrected logarithm excursions | publicZeroDependentLogarithmExcursions; publicFalseRHLogarithmExcursions; NicolasPowerPeak | Maintained, audited; nonlinear correction retained without an RH estimate. |
| Actual moving-rank power excursions | publicFalseRHMovingRankPowerExcursions; PrimeProfilePowerExcursions | Maintained, audited; one b in (0,1/2), every fixed positive alpha, endpoints may differ. |
| Integral and clock RH criteria | publicThetaTailRHCriterion; publicPrimeProductClockRHCriterion | Maintained, audited; classical analytic reformulations transported through exact identities. |
| Nicolas spectral formula and clock displacement | publicRHLogSpectralExpansion; publicRHSpatialClockExpansion | Maintained, audited; explicit RH premise. Zero wave is defined by real projection; separate reality-before-projection proof is not claimed. |
| Positive tilts and kernels | publicTiltedPrimeProductCriterion; publicAllPositiveTiltedPrimeProductCriterion; publicTiltedIntegralCriterion; publicTiltedIntegralSpectralExpansion | Maintained, audited, with fixed positive tilt or the explicitly stated common-cutoff quantifier. These transport the same leading error. |
| Classical pointwise and endpoint correction bounds | publicRHPointwiseLogarithmicBound; publicRHLogarithmicCorrection | Maintained, audited; sqrt(x) log(x)^2 and log(x)^3/x under RH, credited as classical estimates/application. |
| Sharp reference-root shift | publicSharpReferenceCrossing | Maintained, audited; each fixed positive reference level; uniqueness only in its stated local window. |
| Local spatial sign tests | publicLocalDensityRatioThreshold | Maintained, audited; compact clock window, comparison constant and positivity hypotheses retained; uncertainty K log N. |
| RH last-ascent and count capacity | publicRHLastAscentSharpReference; publicRHReversalCountLogBound; publicRHGapFilteredCounts | Maintained, audited; upper envelopes with actual attained maxima; no new small-gap supply. |
| Hardy-Littlewood relative last-ascent limit | both_last_ascent_ratio_tendsto_one_of_twinCountAsymptotic, compiled research consumer | Conditional proof completed; maintained public export pending. Paper includes the full ordinary proof. Its extra log-log and reversal-count limits are ordinary consequences of the stated transfers. |
| Robin/Lagarias implications | Known equivalences combined with publicMovingRankRHCriterion | Ordinary logical consequences, not a newly compiled direct Robin consumer and not a new CA optimization theorem. |

The proof evidence for the maintained RH additions is the successful
rh-ratio-power-public-audit334b-20261004 log, together with its owned build.
The earlier twelve-closure figures below describe the September publication
and are historical. No current research estimate is inserted as a hypothesis
of an advertised unconditional theorem.


This ledger distinguishes mathematical hypotheses from implementation
dependencies. All names below have the namespace `PrimeFactorOscillations`
unless otherwise specified. The paper is a research exposition of maintained
proofs; novelty and independent expert review remain unsettled.

| Paper result or input | Declaration / maintained owner | Implementation and source | Scope |
|---|---|---|---|
| Canonical double-exponential bounds | `doubleExponentialReversalBounds`, [Headline](../PrimeFactorOscillations/Assembly/Headline.lean) | Project assembly of the uniform sign estimates, counting and existing quantitative prime-window input | Proved; every epsilon>0, all sufficiently large ranks; a=1/602 |
| Quantitative width-600 windows | `PrimeGaps.eventually_many_prime_windows_600`; source extraction under Proof/PrimeClusters | Compatibility/count extraction from pinned PrimeGapsLib and its analytic imports; Maynard's cluster theory is the mathematical background | Existing analytic input, not a new prime-gap bound; at least X^(1/3) starts for all sufficiently large X |
| Local first difference | `localStep_difference`, Helpers/LocalFirstDifference | Project generalization of the finite Bernoulli identity; ordinary threshold framework from Wang--Crapis and Erdos 690 | Explicit nonzero-denominator and finite-support conditions |
| Symmetric-polynomial bounds | Erdos 690 Helpers/SymmetricBounds; project uniform growing-rank consumers | Imported ordinary inequalities and project extensions; Wang--Crapis Lemmas 3.1--3.2 | Positivity, supported degree and complementary-sum hypotheses retained |
| Exact reciprocal-smooth spectrum | `ReciprocalSmoothLaw.exists_sharp_reversal_rate_all_ranks`, [ReciprocalSmoothSpectrum](../PrimeFactorOscillations/Assembly/ReciprocalSmoothSpectrum.lean) | Project proof combining lower witness construction, upper gap envelope and fixed-rank tails | Proved; fixed law, nu>0 and 1/eta_p=p/nu+b+o(1); attained finite maxima |
| Actual affine arithmetic spectrum | `AffineSumFamily.exists_sharp_arithmetic_reversal_rate_all_ranks`, [AffineSpectrum](../PrimeFactorOscillations/Assembly/AffineSpectrum.lean) | Project application plus exact unit-CRT counting and fixed-modulus prime input limits | Proved; fixed distinct-root family, positive coefficients, ordered prime pairs including diagonal, input limit first |
| Affine local limits | [RankDensity](../PrimeFactorOscillations/Proof/AffinePairs/RankDensity.lean) and its arithmetic closure | Project finite pattern/rank argument, with imported prime progression limits | Zero outputs and finite exceptional primes retained; no moving-cutoff independence |
| Finite phase and full-frequency recovery | `exists_affine_arithmetic_rate_recovers_full_gap_class`, AffineSpectrum and [GapSpectrumPhase](../PrimeFactorOscillations/Assembly/GapSpectrumPhase.lean) | Project spectral consequence of an existing positive-power cluster count | Proved; gamma=1 is a double-log limsup condition, not positive density |
| Recurring gaps iff late ascents | `recurrent_short_gaps_iff_late_ascents`, [GapRecurrence](../PrimeFactorOscillations/Assembly/GapRecurrence.lean) | Project two-sided use of uniform symmetric-ratio estimates and rank rounding | Proved; H>=1, 1/(H+2)<b<1/(H+1); both rank and lower prime unbounded |
| Critical late-ascent coefficient | `late_ascent_critical_scale`, GapRecurrence | Project combination of recurrence below a gap bound and eventual exclusion above it | Proved given the least recurring gap h; threshold 1/(h+1), no equality claim |
| Late ascents force twins | `ascent_above_one_fifth_forces_twins`, [GapScaleCutoff](../PrimeFactorOscillations/Proof/Upper/GapScaleCutoff.lean) | Project inverse transfer plus parity of sufficiently large prime gaps | Proved for fixed b>1/5 and sufficiently large rank/lower prime |
| Unbounded late supply implies infinitely many twins | `infinitely_many_twins_of_late_ascent_supply`, GapScaleCutoff | Project conditional consumer | Implication proved; the required unbounded supply is open |
| Public statement bridges | `publicDoubleExponentialReversalBounds`, `publicAffinePrimePairSpectrum`, [Solution](../Solution.lean) | Definition/coercion transport from the maintained assemblies | Real proof terms; two intentional statement placeholders occur only in Challenge |

No numerical certificate supplies an asymptotic step in these results.
The canonical constant is the exact rational 1/602, chosen strictly below
1/(600+1). The full dependency closure, rather than the source name, determines
the imported assumptions: [proof_audit.py](../scripts/proof_audit.py) checks
twelve closures against `propext`, `Classical.choice` and `Quot.sound`.
These are standard Lean foundations, not assumptions of prime distribution.
The conditional inverse theorem retains its supply premise in its type.

See [formalization.yaml](../formalization.yaml) for source alignment and
[DEPENDENCY_REUSE.md](../DEPENDENCY_REUSE.md) for exact source revisions and
artifact provenance. No claim of an unconditional new prime-gap theorem,
Goldbach lower bound, moving-tail law, or RH/Robin inequality is included.

## Expanded proof crosswalk

The revised manuscript uses TeX labels to keep this mapping stable under
renumbering. These are exposition of existing proofs, not new proof claims
created by the editorial revision.

| Paper label / argument | Maintained evidence | Exact scope |
|---|---|---|
| eq:diff | localStep_difference; [LocalFirstDifference](../PrimeFactorOscillations/Helpers/LocalFirstDifference.lean) | Finite Bernoulli recurrence with nonzero denominators; supported degree is checked before division. |
| lem:symmetric | Existing ordinary symmetric bounds plus the displayed finite subset expansion | The prose gives an elementary weighted proof; its generalized formulation is an ordinary mathematical argument, not advertised as a newly compiled declaration. |
| eq:mertens; lem:bands | odds_sum_mertens_bound; odds_global_majorant; rank_density_gap_signs_on_broad_band; rank_density_descent_beyond_gap_scale in Helpers/ReciprocalSmooth* | Fixed law and exceptional coordinates; uniform growing-rank bounds and strict sign margins. |
| Fixed-rank tails | eventually_rank_density_nonincreasing; exists_reversal_number_all_ranks in [ReciprocalSmoothAllRanks](../PrimeFactorOscillations/Proof/Upper/ReciprocalSmoothAllRanks.lean) | Forced-rank zero tails and degree zero retained; every rank has an attained maximum. |
| lem:cells | [prime_windows_separated_gap_pairs](../PrimeFactorOscillations/Helpers/PrimeWindowTransfer.lean), using factorial_cells_separated_gap_pairs | Exact factor 2(D!+H), endpoint containment and strict separation. |
| eq:bandcount | reversal_counts_of_gap_frequency_band in [ReciprocalSmoothWindows](../PrimeFactorOscillations/Proof/Lower/ReciprocalSmoothWindows.lean) | Initial deletion at most X; final endpoint Y+H. |
| cor:power | Ordinary consequence of the preceding two compiled inputs and scale comparison; canonical specialization both_reversal_supply_of_positive_power_windows | The general-nu corollary is presented with its proof, not as a separately compiled corollary. |
| Lower spectrum | frequently_reversal_supply_below_gap_exponent in [ReciprocalSmoothRate](../PrimeFactorOscillations/Proof/Lower/ReciprocalSmoothRate.lean) | Actual limsup subsequences, rank rounding, initial deletion and fixed counting losses. |
| Upper spectrum | reversal_count_le_sharp_gap_envelope; reversal_counts_eventually_le_spectrum in [ReciprocalSmoothSpectrumRate](../PrimeFactorOscillations/Proof/Upper/ReciprocalSmoothSpectrumRate.lean) | Individual gap cutoffs before taking a finite sum. |
| eq:rootcount; eq:genericlocal | Affine unit-pair counting and localProbability_reciprocal_control in [AffineReciprocalSmooth](../PrimeFactorOscillations/Helpers/AffineReciprocalSmooth.lean) | The root-set display is the ordinary finite counting explanation; finite exceptions use exact probabilities. |

Historical claims and current source versions are recorded separately in
[SOURCE_REVIEW.md](SOURCE_REVIEW.md). The expanded paper does not incorporate
the unfinished independent-ascent-supply work.

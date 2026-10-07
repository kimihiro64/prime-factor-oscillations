# Paper theorem and provenance ledger

## Growing families, power degrees, and divisor sums — 6 October 2026

The paper now integrates the completed family-search results and the
modified-LCM theorem. The power-degree implication was already maintained;
this revision rechecks its exact statement and proof closure and supplies
the missing paper exposition. No new unconditional zero-free region is
claimed.

| Paper label | Maintained declaration / owner | Exact scope |
|---|---|---|
| thm:correction-interval | `riemannHypothesis_iff_eventually_family_interval_le` and its strict variant; FamilyIntervalTransfer | Fixed positive signal coefficient; a proved correction interval whose width decays at every power below one half. |
| thm:root-exact | `consecutiveRootLaw_logError_exact`, ConsecutiveRootCriterion; `primeAddedRootTail_bounds`, PrimeAddedRootBudget | Actual consecutive-root polynomial plus one prime, all excluded small primes retained, cutoff at least the degree and 3. |
| thm:log-root-sign | `publicLogarithmicRootSignedBound`, LogarithmicRootCriterion | Unconditional negative complete error for degree `1+floor(N/log(N)^j)`, every fixed integer `j>=1`; no uniform growing-j claim. |
| thm:two-prime-bracket | `FinitePrimeResidueFamily.doublePrimeAddition_logError_bracket`, DoublePrimeAdditionCriterion | Uniform attained bracket between the two endpoint laws for every nonnegative tilt. The cubic-tail asymptotic and further-prime specialization are ordinary consequences, not separately audited declarations. |
| thm:power-degree | `no_zeta_zero_right_of_power_degree_signed_profile`, [ConsecutiveRootZeroFree](../PrimeFactorOscillations/Helpers/ConsecutiveRootZeroFree.lean) | Fixed `C>0`, `1/2<=alpha<1`, eventual degree bound `d(N)<=C*N^alpha`, and eventual complete sign for the SAME family sequence exclude zeros with `alpha<Re(rho)<1`. The sign is an explicit, unproved hypothesis. |
| cor:sqrt-degree-RH | `riemannHypothesis_of_sqrt_degree_signed_profile`, ConsecutiveRootZeroFree | At square-root degree, the same eventual sign implies RH. No independent proof of that sign is supplied. |
| eq:lcm-exact-log; lem:lcm-finite | `lcmRobinRatio_log_identity`, `modifiedLcm_logRatio_finite_window_lower`; LcmNormalizedComparison and its arithmetic closure | Actual Mobius divisor sum, actual modified-LCM height, finite prime support and every signed correction. |
| thm:lcm-window, RH part | `eventually_modifiedLcm_window_of_RH`, ModifiedLcmRHWindow | Every sufficiently large NATURAL cutoff, simultaneously throughout the real parameter window. RH is explicit. |
| thm:lcm-window, false-RH case | `nicolasLog_integer_sqrt_negative_supply_of_not_RH`, `modifiedLcm_negative_signed_supply_of_not_RH`; ModifiedLcmNegativeSupply | Unbounded integer cutoffs with the complete negative correction; the RH upper envelope is not used in this case. |
| thm:lcm-window; cor:lcm-counterexamples | `exists_modifiedLcm_window`, `exists_lcmRobinRatio_gt_one`; [ModifiedLcmCriticalWindow](../PrimeFactorOscillations/Helpers/ModifiedLcmCriticalWindow.lean) | Unconditional common window `1<kappa<=3/2+2/(5*loglog(M_N))` at unbounded cutoffs; arbitrarily large actual integers for each fixed `1<kappa<=3/2`. Kappa is not factor rank. |

All named project owners in this table are under
`PrimeFactorOscillations/Helpers/`. Public reachability is through
Assembly/FamilyRHResults and Solution. The fresh 18-statement audit contains
all four power-degree declarations, with only the standard foundational
axioms; see [verification](VERIFICATION.md).

Broader primitive-polynomial optimizers, mixed-grid and coefficient-height
extensions, Frobenius families, and proposed CA/smooth-number sign estimates
remain outside the newly advertised maintained theorem package. The private
register retains their exact ordinary-proof or open status.

## General family RH transfer — 5 October 2026

The new transfer assumes a fixed law of nonnegative odds satisfying
|w_p - nu/(p-1)| <= D/(p-1)^2 for fixed nu>0 and D>=0. This is
discharged for every probability law in [0,1] with
eta_p = nu/p + O(p^-2), allowing an arbitrary finite exceptional head.
No RH, prime-gap recurrence or short-interval supply is part of qualification.

| Result | Maintained declaration / owner | Exact scope |
|---|---|---|
| Probability-tail constructor | quadraticPrimeLawOfEventualProbability, QuadraticProbabilityRH | Explicit tail constant and cutoff; exact finite head absorbed. |
| General product RH equivalence | QuadraticPrimeLaw.riemannHypothesis_iff_eventually_product | Each fixed positive tilt; exact family Euler-product constant. |
| Broader product qualification | riemannHypothesis_iff_eventually_localProduct_of_log_reference | An inverse-cutoff normalized logarithmic tail suffices; no claim of necessity. |
| Uniform coefficient linearization | QuadraticPrimeLaw.exists_eventually_densityRatio_linearization | Actual prefix coefficients; positive denominators and uniform fixed rank band. |
| Moving-rank RH equivalences | QuadraticPrimeLaw.riemannHypothesis_iff_eventually_densityRatio_lt_reference and its non-strict variant | Each fixed alpha>0; floor rank at the family theta clock. |
| Actual probability masses | riemannHypothesis_iff_eventually_quadraticProbabilityMass_ratio | Exact count of forced probabilities added to the free rank. |
| Actual affine prime-pair families | AffineSumFamily.riemannHypothesis_iff_eventually_prefixMass_ratio and its non-strict variant | Exact residue laws; nu equals the number of distinct affine factors. Input-size limit remains first. |
| Generalized reference constant | QuadraticPrimeLaw.exists_reference_scale_with_sharp_constant | Leading rank/(g+nu), correction gamma + H'(1+g/nu)/(nu H(1+g/nu)); reference crossing, not an unconditional last-ascent location. |
| Finite family combinations | family_log_combination_bound; riemannHypothesis_iff_eventually_family_log_combination_neg | Fixed finite collection and coefficients; positive common-signal coefficient gives RH equivalence. Zero coefficient leaves O(1/N). |

The public facade is Assembly/FamilyRHResults. Solution directly consumes the
product and actual probability-law criteria. The added audit inventory has
98 targets, preserving all 441 earlier targets. The new proof package contains
no research-target axiom. The general family extension does not automatically
extend the ordinary positive-area, localized reversal-count, or growing-tilt
theorems: those require their own uniformity and sampling arguments.
The qualification conditions are explicit sufficient conditions, not a
necessary-and-sufficient classification of every conceivable arithmetic family.


## Post-paper results — 5 October 2026

The manuscript now includes the complete ordinary localized-count argument.
The exact status below takes precedence over older descriptions of unfinished
components. A theorem conditional on arithmetic sampling is not an
unconditional Lean proof of the published short-interval input.

| Paper result | Declaration / maintained owner | Proof and implementation status |
|---|---|---|
| Controlled positive peaks | NicolasPowerPeakSupply: exists_nicolasK_power_peak_of_zero; exists_nicolasK_power_peak_exponent_of_not_RH | Maintained, built and axiom-audited. Zero/RH-failure hypotheses remain explicit. |
| Finite interval loss and power persistence, lem:persistence | NicolasIntervalPersistence; NicolasPowerPersistence; NicolasCriticalPersistence: exists_nicolasLog_critical_intervals_of_not_RH | Maintained, built and audited, including the exact critical length sqrt(A)/100 times x^(1-b/2)/sqrt(log x), its finite loss and false-RH corollary. |
| Nicolas positive-area RH criterion, thm:area | NicolasPositiveArea: riemannHypothesis_iff_nicolasPositiveArea_bound | Maintained and audited; actual nonnegative integral on [X,2X], quarter-power upper bound with fixed logarithmic factor. |
| Moving-rank positive-area criterion, thm:area | PrimeProfilePositiveArea: riemannHypothesis_iff_primeProfilePositiveArea_bound | Maintained and audited, each fixed alpha>0. The coefficient/area comparisons retain absolute error and initial cutoffs. |
| Conditional zero restrictions | NicolasPositiveArea: zeta_re_le_of_nicolasPositiveArea_bound; zeta_re_le_of_nicolasPositiveArea_subpower_bound | Maintained and audited for the Nicolas area. The moving-rank version follows by the proved area comparison; no unconditional strip is claimed. |
| Growing high-moment sufficient estimate, eq:moment-target | NicolasMomentConsumer: riemannHypothesis_of_growing_nicolas_moments; MomentSecondArea: eventually_nicolasPositiveArea_of_second_moment | Maintained and audited. The moment estimate remains unproved. The fixed-second-moment input gives the proved 8C sqrt(X)/log X area envelope; failure of this envelope to imply RH does not refute a sharper joint estimate. |
| Square-root growing-tilt criteria and sharp correction | NicolasGrowingTilt; NicolasGrowingTiltAsymptotic: tendsto_nicolasGrowingTilt_correction | Maintained, built and audited. Both RH criteria and the unconditional normalized -c/2 correction hold for every fixed c>0. The proof retains real x and floor x, the PNT prime-square tail, and a remainder uniform for every nonnegative tilt. |
| Actual tilted density signs | TiltedDensity: oddsTilt_rank_ascent_iff; oddsTilt_rank_descent_iff; TiltedReversalCount index versions | Maintained and audited; actual local-law densities, positive supported coefficients, exact strict endpoints. |
| Finite grid counts, eq:grid-rounding | TiltedAscentCount: tiltAscentSet_card_eq_ceil; tiltAscentSet_signed_error_lt_one | Maintained and audited; both thresholds in the stated interval and positive mesh denominator. |
| Actual prescribed reversals and signed excess | TiltedReversalCount: prescribedTiltReversalCount_signed_lower; prescribedTilt_cells_have_reversals | Maintained and audited; explicit descents, support, separation and actual prime gaps. |
| Three-window separation | Nat.separated_gap_pairs_of_three_windows, Mathlib/Data/Nat/Prime/ThreeWindowCells | Maintained, built and audited; finite arithmetic theorem with occupied windows and factorial spacing explicit. |
| Fixed-window ratio bands | PrimeProfileWindowBands: eventually_primeProfile_fixed_window_bands | Maintained, built and audited; one fixed rank throughout each [X,2X], actual support and both half-unit bands. |
| False-RH mesh margin | TiltedCountExcursion: exists_densityRatio_uniform_mesh_excess_of_not_RH | Maintained and audited; arbitrary fixed multiples of n^(-1/2) on full [n,n+n^d] windows, d<=3/4. No prime-gap premise. |
| RH count upper comparison | TiltedCountRHUpper: eventually_prescribedTiltReversalCount_le_reference_of_RH | Maintained and audited; uniform over grids and selected finite families with endpoints in the window. |
| Both count equivalences, thm:count-rh | LocalizedReversalCriterion: riemannHypothesis_iff_eventually_localReversalCount_le_reference; riemannHypothesis_iff_eventually_localReversalCount_power_upper | Maintained, built and audited. Explicit arithmetic sampling only; no density-sign premise. |
| Complete explicit cell construction and source consumer | LocalReversalSampling: localReversalSampling_of_shortIntervalPairInput; allShortIntervalPairs_rh_iff_local_count; allShortIntervalPairs_rh_iff_local_count_power | Maintained, built and audited. AllShortIntervalPairs is precisely the qualitative source premise on every late [Y-h,Y], h>=Y^(3/5), with both prime endpoints retained. Geometry, selectors, rank support, strict separation and the lower cell count are proved. The external Alweiss–Luo theorem itself remains unformalized. |
| Ascent-only count variants | LocalAscentSampling: quantitativeShortIntervalPairs_rh_iff_local_ascent; quantitativeShortIntervalPairs_rh_iff_local_ascent_power | Maintained, built and audited. Exact all-pair window [X+1,X+1+ceil(2X^(7/10))], strict grid tests and one rounding loss per pair. QuantitativeShortIntervalPairs at exponent 3/5 is explicit; the external analytic source remains unformalized. |
| Finite twins and coefficient 1/5 | FiniteTwinsSpectrum: finite_twins_and_spectrum_fifth_determine_all_spectra | Maintained, built and audited. Actual eventual finiteness of gap-two indices plus Lambda(1)=1/5 imply gamma_4=1 and Lambda(nu)=1/(4+nu), for every nu>0. No RH contradiction follows. |
| Generic reversal-count monotonicity counterexample | ReversalCountCounterexample: ascent_inclusion_does_not_preserve_reversal_count | Maintained, built and audited. Explicit real sequences, actual two-witness construction and impossibility for the reference sequence. No prime-density realization is asserted. |
| General fixed-gap RH capacities, eq:general-gap-capacity | GeneralRHAscentEnvelope; GeneralRHAscentCapacity; GeneralRHSharpCapacity: exists_ordinary_loglog_capacity_of_RH_gap_lower | Maintained and audited for every natural H under RH and an eventual lower bound H on actual consecutive gaps. Attained maxima, finite exceptions, threshold H+1 and sharp reference-root displacement are retained. |
| Local coverage and square-root tracking, eq:local-tracking | Assembly/ConditionalLocation/FineLocationRH: exists_last_ascent_reference_tracking_and_RH_wave; LastAscentFineTracking: tendsto_last_ascent_div_gap_cutoff | Maintained, built and audited. Local exact-gap coverage and the eventual lower gap bound are explicit. Roots are constructed; the actual last ascent is bracketed, square-root tracking is proved, and the RH wave remains at P-1. No spatial-location premise is added. |
| Unconditional physical clock precision | NicolasQuantitativeClock: tendsto_nicolasLog_mul_log_zero_unconditionally; tendsto_nicolasPrimeProductClock_div_self | Maintained and audited. Quantitative PNT controls the additive exponent error before proving C(x)/x tends to one. |
| Global error implies local exact-gap coverage | GapFrequencyCoverage: eventually_exact_gap_coverage_of_liTwo_error | Maintained and audited for all sufficiently large real starting points. Assumes the actual exact-gap count minus c Li2 is o(sqrt(X)/log(X)^4), c>0; gives a consecutive pair of precisely the specified width. |
| Coarse frequency loses density information | CoarseFrequencyExample: full_coarse_exponent_allows_zero_density | Maintained and audited for an explicit nonnegative real-valued model, not a claimed shape of actual prime-gap counts. |
| Signed excess/deficit and fixed-tilt cancellation | TiltedSignedExcess: tiltAscentCount_sub_eq_excess_sub_deficit; tiltAscentCount_sum_signed_error_le; FixedTiltCombinations | Maintained and audited. Exact finite support and strict/weak endpoints; aggregate rounding bounded by the pair count. Fixed coefficients cancelling the F signal leave O(1/N). No positive signed-frequency estimate is asserted. |

The ordinary count construction fixes its cells at X+1, so all selected
prefixes p-1 lie in [X,X+X^(7/10)]. This explicitly resolves the one-unit
endpoint shift before applying interval persistence. The paper's
ascent-only variant separately absorbs its rounding with a longer fixed
power window.

The extra analytic input is Alweiss–Luo, Corollary 1.2,
arXiv:1707.05437v1, inspected at its actual all-short-interval quantifiers.
It supplies some fixed H; a numerical global bounded-gap infinitude theorem
does not supply those quantifiers. No project axiom has been added.

All fifteen groups in the post-paper formalization scope are now maintained
and exported. The 5 October full audit checks 441 selected theorem closures
and two compiled public statement identities. Only standard foundational
axioms occur. Open analytic moment estimates and the independent ascent
supply remain open; proving their conditional consumers does not prove them.


## Completed RH development and conditional location - 4 October 2026

The revised paper keeps classical analytic inputs separate from new consumers.
The 4 October maintained audit covered 218 selected theorem closures
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
| Hardy-Littlewood relative last-ascent limit | Assembly/ConditionalLocation/TwinCountAsymptoticBridge: both_last_ascent_ratio_tendsto_one_of_twinCountAsymptotic | Maintained, full build and public axiom audit passed for both actual canonical families. Positive global twin asymptotic is explicit. The extra log-log and reversal-count limits are ordinary consequences of the stated transfers. |
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
the imported assumptions. The initial audit checked twelve closures;
[proof_audit.py](../scripts/proof_audit.py) now checks 441 selected closures
against `propext`, `Classical.choice` and `Quot.sound`.
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

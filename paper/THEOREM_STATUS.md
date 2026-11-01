# Paper theorem and provenance ledger

## Complete universal native vanishing-profile law (2026-11-01)

All twenty-seven claims below have maintained Lean proofs, warning-free focused builds and completed new-only assumption audits. They belong to `PrimeFactorOscillations.FiniteFieldIntegerSignature`. For every fixed strict graph G on arbitrary actual prime vertices P, every prescribed zero/nonzero trace profile and central/noncentral native-weight profile has frequency N_even(P,G)/2^|G| if all even Eulerian mask sign products are1, and0 otherwise. No vertex/gap independence is assumed. True specifies a nonzero trace or noncentral weight; false specifies a zero trace or central weight. Every incompatible profile is eventually impossible; compatible profiles occur at arbitrarily large actual field primes.

| Claim | Lean declaration | Status |
| --- | --- | --- |
| Zero paired trace exactly means negative row product | native_trace_zero_iff_paired_negative | Proved; maintained, compiled and audited. |
| Exact zero/nonzero status and paired-sign equivalence | native_trace_status_iff_paired_sign | Proved; maintained, compiled and audited. |
| Actual finite profile equals its supported Boolean selector | native_paired_profile_selector | Proved; maintained, compiled and audited. |
| Full paired-profile signed mask expansion | native_paired_profile_full_mask_expansion | Proved; maintained, compiled and audited. |
| Every qualifying cycle has physical character product exactly one | native_cycle_paired_character_product_one | Proved; maintained, compiled and audited. |
| Every actual late-field profile satisfies all cycle constraints | native_vanishing_profile_event_compatible | Proved; maintained, compiled and audited. |
| Exact physical vanishing-profile selector | native_vanishing_profile_pointwise_selector | Proved; maintained, compiled and audited. |
| Full finite-band profile mass expansion with all masks | native_vanishing_profile_mass_expansion | Proved; maintained, compiled and audited. |
| Eventual whole-band profile expansion | native_vanishing_profile_mass_expansion_eventually | Proved; maintained, compiled and audited. |
| An incompatible profile has exactly zero late-band mass | native_vanishing_incompatible_mass_zero | Proved; maintained, compiled and audited. |
| Incompatible profile mass is eventually exactly zero | native_vanishing_incompatible_mass_zero_eventually | Proved; maintained, compiled and audited. |
| General physical profile limit before finite mask classification | native_vanishing_profile_general_ratio_tendsto | Proved; maintained, compiled and audited. |
| Compatible profiles have the exact common frequency | native_vanishing_compatible_rate | Proved; maintained, compiled and audited. |
| Incompatible profiles have rate exactly zero | native_vanishing_incompatible_rate | Proved; maintained, compiled and audited. |
| Complete compatible/forbidden profile rate formula | native_vanishing_profile_rate_eq | Proved; maintained, compiled and audited. |
| Complete unconditional physical profile law | native_vanishing_profile_ratio_tendsto | Proved; maintained, compiled and audited. |
| Incompatible profiles are absent above a fixed field-prime threshold | native_vanishing_incompatible_eventually_absent | Proved; maintained, compiled and audited. |
| Every compatible profile has an actual field-prime realizer above every bound | native_vanishing_compatible_realization_above | Proved; maintained, compiled and audited. |
| Actual field-prime profile recurrence is equivalent to compatibility | native_vanishing_profile_recurrence_iff | Proved; maintained, compiled and audited. |
| Exact full central-weight and vanishing-profile equivalence | native_central_profile_iff_vanishing | Proved; maintained, compiled and audited. |
| Exact finite-band central-profile mass transfer | native_central_profile_mass_eq | Proved; maintained, compiled and audited. |
| Exact eventual-band central-profile mass transfer | native_central_profile_mass_eq_eventually | Proved; maintained, compiled and audited. |
| Complete actual central/noncentral native-weight profile law | native_central_profile_ratio_tendsto | Proved; maintained, compiled and audited. |
| Every profile with at most three edges is compatible | native_small_vanishing_profile_compatible | Proved; maintained, compiled and audited. |
| Universal fair profile frequency for at most three edges | native_small_central_profile_ratio_tendsto | Proved; maintained, compiled and audited. |
| Four-cycle compatibility is exactly one full-cycle sign test | native_four_cycle_vanishing_profile_compatible_iff | Proved; maintained, compiled and audited. |
| Exact actual-weight four-cycle profile law | native_four_cycle_central_profile_ratio_tendsto | Proved; maintained, compiled and audited. |

Definition interfaces (not additional theorem claims): `nativeVanishingProfileEvent`, `nativeVanishingProfileMass`, `nativeVanishingProfileCoefficient`, `nativeVanishingProfileCompatible`, `nativeVanishingProfileRate`, `nativeCentralProfileEvent`, `nativeCentralProfileMass`. These are explicit noncomputable probability-section interfaces, not additional arithmetic assumptions.

Maintained owners: `PrimeFactorOscillations/Helpers/NativeVanishingProfileAlgebra.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeVanishingEvents.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeVanishingProfiles.lean`. All twenty-seven new closures use only `propext`, `Classical.choice` and `Quot.sound`; earlier unchanged closures were not re-audited. The paper includes the full signed expansion, exact physical cycle product, compatible/forbidden classification, unbounded field-prime realization proof and actual-weight transfer.

benchmark_status: full universal profile classification and recurrence criterion proved.
old_bound: the universal central atom covered only the all-zero/all-central profile; the full signed lower/upper word law required a specially constructed independent prime class.
new_bound: every fixed Boolean profile on every actual prime graph has exact reciprocal-band frequency N_even/2^m when compatible and0 otherwise. Incompatible profiles are absent beyond all fixed vertices and field prime2. Every compatible profile occurs above every field-prime bound. All profiles on at most three edges are fair with frequency2^(-m); a four-cycle has frequency1/8 or0 according to its full-cycle sign test.
components: exact paired Boolean selectors; all signed mask coefficients; universal diagonal square classifier; physical product of every even Eulerian mask equals1 because it is nonnegative and has square1; exact forbidden-event absence; positive compatible limit; invertible actual native central readout.
actuals: twenty-seven new audited Lean proofs and seven definition interfaces. Every small-graph claim is symbolic in all allowed prime labels and profiles; no finite experiment supplies a universal statement.
first_nonpositive_domain: incompatible profiles have frequency exactly0; compatible profiles have positive frequency because the empty cycle mask is retained. Empty graphs, isolated vertices and vertex2 are included. Every graph and profile is fixed before the independently varying field prime. Recurrence is in that field prime, not in integer prime gaps. No growing-graph uniformity, effective class growth or RH/QRH gain is asserted; the installed boundary remains7/8. Publication priority remains under review.

## Universal central native-output law (2026-11-01)

All fifteen claims below have maintained Lean proofs, warning-free focused builds and completed new-only assumption audits. They belong to `PrimeFactorOscillations.FiniteFieldIntegerSignature`. For every fixed strict graph G on arbitrary actual prime vertices P, the simultaneous zero-trace frequency and the frequency of all native weights equaling (ell-1)/(ell-3) are exactly N_even(P,G)/2^|G|. Neither statement assumes vertex/gap square independence. The empty graph is included, with probability1.

| Claim | Lean declaration | Status |
| --- | --- | --- |
| Exact endpoint product as vertex incidence powers | native_vertex_endpoint_product | Proved; maintained, compiled and audited. |
| Exact diagonal natural product with all gap squares retained | native_diagonal_natural_product | Proved; maintained, compiled and audited. |
| Each distinct prime reads its own prescribed exponent | native_prime_power_product_valuation | Proved; maintained, compiled and audited. |
| A square prime-power product has only even exponents | native_prime_power_product_even_of_square | Proved; maintained, compiled and audited. |
| Universal signed diagonal square classifier without gap independence | native_signed_diagonal_isSquare_iff | Proved; maintained, compiled and audited. |
| Every noncycle diagonal has zero principal indicator | native_graph_diagonal_indicator_zero_outside_cycles | Proved; maintained, compiled and audited. |
| Universal exact zero-trace rate for arbitrary actual prime labels | native_graph_zero_rate_eq_universal | Proved; maintained, compiled and audited. |
| Unconditional universal physical zero-trace limit | native_graph_zero_universal_ratio_tendsto | Proved; maintained, compiled and audited. |
| Exact central/nonzero decomposition of the general agreement rate | native_graph_agreement_central_decomposition | Proved; maintained, compiled and audited. |
| Actual weight equals the central value exactly when its trace is zero | native_graph_central_weight_iff_zero | Proved; maintained, compiled and audited. |
| Exact finite-band central-weight/zero-trace mass identity | native_graph_central_weight_mass_eq | Proved; maintained, compiled and audited. |
| Exact eventual-band central-weight/zero-trace mass identity | native_graph_central_weight_mass_eq_eventually | Proved; maintained, compiled and audited. |
| Universal actual central-weight frequency | native_graph_central_weight_universal_ratio_tendsto | Proved; maintained, compiled and audited. |
| Generic central-weight probability for at most three edges | native_graph_small_central_weight_ratio_tendsto | Proved; maintained, compiled and audited. |
| Actual four-cycle central-weight frequency is one eighth for arbitrary prime labels | native_graph_four_cycle_central_weight_ratio_tendsto | Proved; maintained, compiled and audited. |

Definition interfaces (not additional theorem claims): `nativeGraphCentralWeightEvent`, `nativeGraphCentralWeightMass`. Both belong to an explicitly noncomputable real probability section.

Maintained owners: `PrimeFactorOscillations/Helpers/NativePrimeDiagonalCycles.lean` and `PrimeFactorOscillations/Assembly/FiniteFieldNativeUniversalZero.lean`. All fifteen new proof closures use only `propext`, `Classical.choice` and `Quot.sound`; unchanged old closures were not re-audited. The paper gives the full prime-valuation argument, exact signed zero-mask substitution and actual central-weight transfer.

benchmark_status: universal exact central-output law proved.
old_bound: the preceding comparison provided a zero-event lower bound for arbitrary prime labels and equality under full vertex/gap independence.
new_bound: the zero-event bound is always equality, N_even(P,G)/2^|G|, on arbitrary actual prime labels. The full agreement rate is this fixed central atom plus the two limiting nonzero constant-trace word probabilities. Central probability is2^(-m) for every graph with m<=3 edges and1/8 for every strict four-cycle.
components: exact paired coefficient sign; every gap retained as a positive square; distinct-prime valuation parity; exact zero-event mask expansion; exact finite-band affine endpoint transfer. No signed remainder is estimated by absolute coefficient mass.
actuals: fifteen audited Lean proofs and two definition interfaces; no numerical experiment supplies a universal assertion.
first_nonpositive_domain: empty graphs, isolated vertices and prime2 are included. Field primes2,3 and fixed vertex factors are outside the eventual band. Every graph is fixed before the independent field scale tends to infinity. No growing-graph uniformity, effective class growth, integer prime-gap value or RH/QRH improvement is asserted; the certified boundary remains7/8. Publication priority remains under review.

## Sharp universal simultaneous native graph coincidence (2026-11-01)

All fifty-eight claims below have maintained Lean proofs, warning-free focused builds and completed new-only assumption audits. They belong to `PrimeFactorOscillations.FiniteFieldIntegerSignature`. For every fixed nonempty strict graph G on arbitrary actual prime vertices P, the actual simultaneous native-weight agreement limit A(P,G) exists and is at least N_even(P,G)*(2^(-m)+2^(1-2*m)), where m=|G| and N_even counts the even-sized, even-degree masks C contained in G. One fixed computable infinite class inside every admissible decidable prime reservoir attains equality on every finite graph inside it. No gap independence is assumed for the lower bound.

| Claim | Lean declaration | Status |
| --- | --- | --- |
| Positive unsigned part of every complete signed product | native_signed_unsigned_product_positive | Proved; maintained, compiled and audited. |
| Every supported signed coefficient product is nonzero | native_signed_row_product_ne_zero | Proved; maintained, compiled and audited. |
| Odd paired masks have negative signed product | native_signed_paired_row_product_neg_of_odd | Proved; maintained, compiled and audited. |
| Every even Eulerian mask supplies a square unconditionally | native_signed_cycle_product_isSquare | Proved; maintained, compiled and audited. |
| General centered mixed moment without independence | native_signed_row_moment_centered_general | Proved; maintained, compiled and audited. |
| General normalized mixed moment equals the square indicator | native_signed_row_moment_general_ratio_tendsto | Proved; maintained, compiled and audited. |
| Exact computable even-cycle membership predicate | native_even_cycle_masks_mem_iff | Proved; maintained, compiled and audited. |
| The even-cycle count is positive | native_even_cycle_count_positive | Proved; maintained, compiled and audited. |
| Exact zero-trace selector product | native_trace_zero_selector_product | Proved; maintained, compiled and audited. |
| Full signed zero-trace mask expansion | native_trace_zero_full_mask_expansion | Proved; maintained, compiled and audited. |
| Exact coupled three-event agreement selector | native_trace_agreement_selector_product | Proved; maintained, compiled and audited. |
| Physical zero-trace pointwise selector | native_graph_zero_pointwise_selector | Proved; maintained, compiled and audited. |
| Physical disjoint agreement decomposition | native_graph_agreement_pointwise_decomposition | Proved; maintained, compiled and audited. |
| Exact zero-trace mass mask expansion | native_graph_zero_mass_expansion | Proved; maintained, compiled and audited. |
| Exact coupled agreement mass decomposition | native_graph_agreement_mass_decomposition | Proved; maintained, compiled and audited. |
| The entire eventual band exceeds every fixed vertex | native_graph_field_window_eventually | Proved; maintained, compiled and audited. |
| Eventual physical zero-trace expansion | native_graph_zero_mass_expansion_eventually | Proved; maintained, compiled and audited. |
| Eventual physical three-event agreement decomposition | native_graph_agreement_mass_decomposition_eventually | Proved; maintained, compiled and audited. |
| General word limit for arbitrary prime labels | native_signed_word_general_ratio_tendsto | Proved; maintained, compiled and audited. |
| General zero-trace limit for arbitrary prime labels | native_graph_zero_ratio_tendsto | Proved; maintained, compiled and audited. |
| General agreement limit for arbitrary prime labels | native_graph_agreement_ratio_tendsto | Proved; maintained, compiled and audited. |
| Every square indicator is nonnegative | native_graph_square_indicator_nonneg | Proved; maintained, compiled and audited. |
| Every even Eulerian mask has principal indicator one | native_graph_cycle_indicator_eq_one | Proved; maintained, compiled and audited. |
| Odd masks cancel before the zero-trace estimate | native_graph_zero_mask_nonneg | Proved; maintained, compiled and audited. |
| Every qualifying cycle supplies one zero-trace term | native_graph_zero_mask_eq_one_of_cycle | Proved; maintained, compiled and audited. |
| Universal zero-trace lower bound | native_graph_zero_rate_lower_bound | Proved; maintained, compiled and audited. |
| Constant-sign words combined with every mask pair | native_graph_constant_word_sum_expansion | Proved; maintained, compiled and audited. |
| All combined mask coefficients are nonnegative | native_graph_paired_mask_nonneg | Proved; maintained, compiled and audited. |
| Every qualifying cycle supplies two paired-word terms | native_graph_paired_mask_eq_two_of_cycle | Proved; maintained, compiled and audited. |
| Universal constant-sign-word lower bound | native_graph_constant_word_rate_lower_bound | Proved; maintained, compiled and audited. |
| Sharp universal graph-coincidence lower bound | native_graph_agreement_rate_lower_bound | Proved; maintained, compiled and audited. |
| Actual trace limit with the universal lower bound | native_graph_agreement_limit_lower_bound | Proved; maintained, compiled and audited. |
| Noncycle masks vanish on the independent class | native_graph_noncycle_indicator_eq_zero | Proved; maintained, compiled and audited. |
| Exact zero-trace rate on the independent class | native_graph_zero_rate_eq_of_independent | Proved; maintained, compiled and audited. |
| Exact paired-word rate on the independent class | native_graph_constant_word_rate_eq_of_independent | Proved; maintained, compiled and audited. |
| Exact graph-coincidence floor on the independent class | native_graph_agreement_rate_eq_of_independent | Proved; maintained, compiled and audited. |
| Sharp physical graph limit throughout the reservoir class | native_reservoir_graph_agreement_ratio_tendsto | Proved; maintained, compiled and audited. |
| One infinite reservoir class attaining every finite graph floor | native_infinite_graph_coincidence_family_in_reservoir | Proved; maintained, compiled and audited. |
| Unconditional infinite full-prime sharp graph family | native_infinite_graph_coincidence_family | Proved; maintained, compiled and audited. |
| Exact invertible native-weight and trace agreement equivalence | native_graph_weight_agreement_iff | Proved; maintained, compiled and audited. |
| Exact finite-band weight and trace mass equality | native_graph_weight_mass_eq | Proved; maintained, compiled and audited. |
| Exact eventual-band weight and trace mass equality | native_graph_weight_mass_eq_eventually | Proved; maintained, compiled and audited. |
| Actual native-weight agreement limit | native_graph_weight_agreement_ratio_tendsto | Proved; maintained, compiled and audited. |
| Universal lower bound for actual native-weight agreement | native_graph_weight_limit_lower_bound | Proved; maintained, compiled and audited. |
| Sharp actual-weight limit throughout the reservoir class | native_reservoir_graph_weight_ratio_tendsto | Proved; maintained, compiled and audited. |
| One infinite reservoir class attaining every native-weight floor | native_infinite_graph_weight_family_in_reservoir | Proved; maintained, compiled and audited. |
| Only the empty even-cycle mask occurs with at most three edges | native_even_cycle_masks_small | Proved; maintained, compiled and audited. |
| Even-cycle count equals one with at most three edges | native_even_cycle_count_small | Proved; maintained, compiled and audited. |
| Four-cycle qualifying masks are exactly empty and full | native_even_cycle_masks_four_cycle | Proved; maintained, compiled and audited. |
| Four-cycle even-cycle count equals two | native_even_cycle_count_four_cycle | Proved; maintained, compiled and audited. |
| Exact one-edge agreement rate | native_graph_one_edge_rate | Proved; maintained, compiled and audited. |
| Exact two-edge agreement rate | native_graph_two_edge_rate | Proved; maintained, compiled and audited. |
| Exact three-edge agreement rate | native_graph_three_edge_rate | Proved; maintained, compiled and audited. |
| Exact four-cycle agreement rate | native_graph_four_cycle_rate | Proved; maintained, compiled and audited. |
| Actual one-edge native-weight limit is one | native_graph_one_edge_weight_ratio_tendsto | Proved; maintained, compiled and audited. |
| Actual two-edge native-weight limit is three eighths | native_graph_two_edge_weight_ratio_tendsto | Proved; maintained, compiled and audited. |
| Actual three-edge native-weight limit is five over thirty-two | native_graph_three_edge_weight_ratio_tendsto | Proved; maintained, compiled and audited. |
| Actual four-cycle native-weight limit is nine over sixty-four | native_graph_four_cycle_weight_ratio_tendsto | Proved; maintained, compiled and audited. |

Definition interfaces (not additional theorem claims): `nativeEvenCycleMasks`, `nativeEvenCycleCount`, `nativeGraphZeroTraceEvent`, `nativeGraphAgreementEvent`, `nativeGraphZeroTraceMass`, `nativeGraphAgreementMass`, `nativeSignedGeneralWordRate`, `nativeGraphZeroTraceRate`, `nativeGraphAgreementRate`, `nativeGraphWeightAgreementEvent`, `nativeGraphWeightAgreementMass`. The two finite even-cycle definitions are computable. The nine real-valued event/mass/rate interfaces are explicitly in noncomputable sections; no additional arithmetic assumption is hidden there.

Maintained owners: `PrimeFactorOscillations/Definitions/NativePrimeEvenCycleMasks.lean`, `PrimeFactorOscillations/Helpers/NativePrimeUniversalCycles.lean`, `PrimeFactorOscillations/Helpers/NativePrimeEvenCycleMasks.lean`, `PrimeFactorOscillations/Helpers/NativeTraceAgreementAlgebra.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeGeneralMoments.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeGraphCoincidenceEvents.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeGraphCoincidenceLaw.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeGraphOutputs.lean`. All fifty-eight new closures use only `propext`, `Classical.choice` and `Quot.sound`. Earlier unchanged closures were not re-audited. The paper includes the full signed consumer, odd-mask cancellation, the unconditional cycle-square supply, simultaneous sharpness, exact affine transfer to native weights and all four symbolic small-graph cases.

benchmark_status: universal sharp graph-coincidence comparison and actual-weight transfer proved.
old_bound: the completed signed word law determined the independent-class distribution; it did not prove a universal simultaneous native-output lower bound for arbitrary prime labels.
new_bound: A(P,G)>=N_even(P,G)*(2^(-m)+2^(1-2*m)), with equality on every fixed finite graph in one computable infinite reservoir class. Exact native-weight values are 1,3/8,5/32 for one,two,three edges and 9/64 for a strict four-cycle.
components: full zero-trace signed sum plus both coupled constant-sign word sums; odd paired masks have zero principal indicator; all remaining combined coefficients are nonnegative; every even Eulerian mask supplies one zero-event and two paired-word terms; independent-class square classification proves sharpness; invertible affine endpoint readout preserves actual equality.
actuals: fifty-eight audited real Lean proofs and eleven definition interfaces. The small cases are universal symbolic theorems; no numerical sample supplies an estimate.
first_nonpositive_domain: the graph is nonempty and fixed before the independently varying field-prime band. Empty-graph raw three-event rates are not interpreted as probabilities. Exceptional field primes 2,3 and all fixed vertex factors are excluded by an eventual whole-band bound. No effective class-growth rate, growing-graph uniformity, integer prime-gap value, RH or QRH gain is asserted; the certified boundary remains7/8. Publication priority remains under review.

## Complete signed native word law and optimal seven-row independence (2026-11-01)

All thirty-eight claims below have maintained Lean proofs, warning-free focused builds and completed new-only assumption audits. They belong to `PrimeFactorOscillations.FiniteFieldIntegerSignature`. The same fixed computable infinite prime class works for every fixed finite graph and sign word, inside any decidable prime reservoir whose actual relative frequency does not tend to zero. Lower and upper rows are distinct indexed coordinates. The independent field-prime band is `[preciseCore U+1, preciseCore U*preciseCore U+1)`, with reciprocal-prime weights and its exact reciprocal-band normalizer.

| Claim | Lean declaration | Status |
| --- | --- | --- |
| Complete signed integer row-product factorization | native_signed_row_product_factorization | Proved; maintained, compiled and audited. |
| Signed square kernel: matching masks, even degrees and even edge count | native_signed_row_product_isSquare_iff | Proved; maintained, compiled and audited. |
| Principal character indicator for every nonzero signed integer | numerator_principal_indicator_int_eq_square | Proved; maintained, compiled and audited. |
| Unconditional centered character mean for signed integers | prime_correlation_centered_int_square_tendsto_zero | Proved; maintained, compiled and audited. |
| Exact finite-product character multiplicativity | real_kernel_finset_product | Proved; maintained, compiled and audited. |
| Actual native trace equals its two signed character rows | native_trace_eq_signed_rows | Proved; maintained, compiled and audited. |
| Complete physical mixed moment equals one signed character correlation | native_signed_row_moment_eq_correlation | Proved; maintained, compiled and audited. |
| Normalized limit from the eventual positive band mass | native_prime_band_ratio_tendsto_of_centered | Proved; maintained, compiled and audited. |
| Centered signed-cycle mixed moment tends to zero | native_signed_cycle_moment_centered_tendsto_zero | Proved; maintained, compiled and audited. |
| Full normalized mixed-moment cycle indicator | native_signed_cycle_moment_ratio_tendsto | Proved; maintained, compiled and audited. |
| Boolean sign values square to one | native_word_sign_square | Proved; maintained, compiled and audited. |
| Exact one-row Boolean selector | native_word_bit_eq_indicator | Proved; maintained, compiled and audited. |
| Exact supported product of word selectors | native_word_selector_product | Proved; maintained, compiled and audited. |
| Full finite two-support Boolean expansion | native_word_full_mask_expansion | Proved; maintained, compiled and audited. |
| All signed rows are signs above the fixed vertex bound | native_signed_edge_kernel_squares | Proved; maintained, compiled and audited. |
| Actual word event equals the full selector product | native_signed_word_pointwise_selector | Proved; maintained, compiled and audited. |
| Exact physical word mass expanded over every mask pair | native_signed_word_mass_expansion | Proved; maintained, compiled and audited. |
| Entire eventual prime band satisfies the exact word expansion | native_signed_word_mass_expansion_eventually | Proved; maintained, compiled and audited. |
| Complete finite signed word law | native_signed_word_ratio_tendsto | Proved; maintained, compiled and audited. |
| Complete word law on every finite reservoir-class subset | native_reservoir_signed_word_ratio_tendsto | Proved; maintained, compiled and audited. |
| One infinite computable reservoir family with all finite word laws | native_infinite_signed_word_family_in_reservoir | Proved; maintained, compiled and audited. |
| Unconditional full-prime infinite signed-word family | native_infinite_signed_word_family | Proved; maintained, compiled and audited. |
| Exact degree as a finite sum of endpoint indicators | native_cycle_degree_eq_sum | Proved; maintained, compiled and audited. |
| Two distinct strict edges cannot have even degree everywhere | native_even_cycle_card_ne_two | Proved; maintained, compiled and audited. |
| An even-sized Eulerian mask with at most three edges is empty | native_small_even_cycle_empty | Proved; maintained, compiled and audited. |
| Every surviving mask on at most seven tested rows is empty | native_signed_small_mask_empty | Proved; maintained, compiled and audited. |
| Exact fair product probability for at most seven rows | native_signed_word_rate_seven | Proved; maintained, compiled and audited. |
| Physical seven-row independence limit | native_signed_word_ratio_tendsto_seven | Proved; maintained, compiled and audited. |
| Physical seven-row independence inside the same reservoir class | native_reservoir_signed_word_ratio_tendsto_seven | Proved; maintained, compiled and audited. |
| Four arbitrary increasing vertices give valid strict edges | native_four_cycle_support | Proved; maintained, compiled and audited. |
| The strict four-cycle has exactly four distinct edges | native_four_cycle_card | Proved; maintained, compiled and audited. |
| Every four-cycle vertex degree is even, including outside vertices | native_four_cycle_degrees_even | Proved; maintained, compiled and audited. |
| The only surviving four-cycle masks are empty and complete | native_four_cycle_mask_iff | Proved; maintained, compiled and audited. |
| Exact eight-row four-cycle word formula | native_four_cycle_word_rate | Proved; maintained, compiled and audited. |
| All-positive four-cycle rate is exactly one over 128 | native_four_cycle_all_positive_rate | Proved; maintained, compiled and audited. |
| Physical exact eight-row word-law limit | native_four_cycle_word_ratio_tendsto | Proved; maintained, compiled and audited. |
| Physical all-positive four-cycle limit is one over 128 | native_four_cycle_all_positive_ratio_tendsto | Proved; maintained, compiled and audited. |
| Actual four reservoir witnesses and failure of the independent one-over-256 limit | native_reservoir_signed_eight_row_failure | Proved; maintained, compiled and audited. |

Definition interfaces (not additional theorem claims): `nativeSignedLowerCoefficient`, `nativeSignedUpperCoefficient`, `nativeSignedRowProduct`, `nativeSignedRowMoment`, `nativeWordSign`, `nativeWordBit`, `nativeSignedWordEvent`, `nativeSignedWordMass`, `nativeSignedWordMaskCoefficient`, `nativeSignedCycleMask`, `nativeSignedWordRate`, `nativePrimeFourCycle`. Integer coefficients, four-cycle supports and Boolean signs are computable; real-valued selectors, events, moments, masses and limiting-rate expressions use the explicitly noncomputable probability section. The computable infinite prime class is the previously promoted construction.

Maintained owners: `PrimeFactorOscillations/Definitions/NativePrimeSignedRows.lean`, `PrimeFactorOscillations/Helpers/NativePrimeSignedCycleKernel.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeSignedCharacter.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeSignedMoments.lean`, `PrimeFactorOscillations/Definitions/NativePrimeWordSigns.lean`, `PrimeFactorOscillations/Helpers/NativeWordBooleanAlgebra.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeWordEvents.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeWordLaw.lean`, `PrimeFactorOscillations/Helpers/NativePrimeSmallCycles.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeSevenRows.lean`, `PrimeFactorOscillations/Definitions/NativePrimeFourCycle.lean`, `PrimeFactorOscillations/Helpers/NativePrimeFourCycle.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeFourCycleLaw.lean`, `PrimeFactorOscillations/Assembly/FiniteFieldNativeSignedFamilies.lean`. The public NativePacking facade exports the full signed family. All thirty-eight new closures use only `propext`, `Classical.choice` and `Quot.sound`; unchanged old closures were not re-audited. The paper gives the full signed product argument, exact eventual selector expansion, finite moment limit and both sharpness calculations.

benchmark_status: the full physical finite-word law, seven-row independence and actual eight-row failure are proved.
old_bound: the promoted infinite prime graph had a complete positive square-product cycle classifier; its actual signed physical joint word law and optimal independence order were not yet installed.
new_bound: every k<=7 indexed signed rows have every sign word with limiting probability 2^(-k). On every strict four-cycle the eight-row word probability is (1+product_e(a_e*b_e))/256. The all-positive limit is 1/128, and the independent 1/256 limit is formally excluded inside every admissible reservoir.
components: complete signed integer product; full nonzero signed numerator character; exact physical mixed moments; every Boolean mask and product term; the fixed-vertex exceptional-prime condition on the entire eventual band; even-degree and even-cardinality cycle classification; witnessed four-vertex selection from the same infinite class.
actuals: thirty-eight maintained real Lean proof closures, thirty-eight new-only foundational audits, twelve definition interfaces and fourteen new maintained owners. No finite experiment supplies a universal probability statement.
first_nonpositive_domain: inconsistent four-cycle sign words have limiting probability zero. Finite initial bands can be empty; division uses Lean's zero convention and the normalizer is bounded below by log(2)/2 eventually. Empty supports, isolated vertices and vertex prime2 are included. No uniform growing-graph limit, effective vertex density or growth, integer prime-gap value, RH proof or QRH exponent gain is claimed. General quadratic-character equidistribution and Boolean inversion are classical; publication priority for the specific infinite prime-graph application remains under review.

## Raw and averaged finite-field pair-law separation - 30 October 2026

**Fully matched: 36 declarations in four maintained owners.** For odd finite fields, nonzero shift, and q>=16, the original normalized irreducible-quadratic law u and flat admissibility law f satisfy H(u,f)<=1-1/(64q), while the trace-free law v satisfies 1-H(v,f)<=5/q^2. For q>=2048, H(u,v)<=1-1/(256q). On every complete finite product the upper bounds exponentiate with the reciprocal-cardinality sum; the averaged/flat affinity is at least 1-sum(5/q_i^2). Every forbidden row and all square-root cross terms remain. These are finite-law comparisons, with no Hasse or integer primality assumption. No positive incomplete integer pair mass, new H_1 bound, or zero-free improvement is claimed. The independent critical-height integer mass remains open. The specific comparison is an originality prospect; general product-affinity theory is classical.

All declarations below are compiled and focused-axiom-audited; the only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

- `PrimeFactorOscillations.FiniteFieldPairAffinity.affinity_nonneg` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairAffinity.affinity_symm` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairAffinity.sqrt_energy_identity` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairAffinity.affinity_le_one` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairAffinity.scalar_square_gap_le` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairAffinity.square_distance_le_affinity_defect` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairAffinity.affinity_defect_triangle` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairAffinity.overlap_le_affinity` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.pair_count_bounds` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.normalization_total` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.denominator_pos` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.raw_density_quotient` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.raw_density_bounds` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.sum_raw_density` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.raw_mul_mask` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.flat_density_bounds` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.sum_flat_density` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.raw_flat_cross_moment` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.flat_second_moment` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.raw_flat_square_distance_eq` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.raw_second_moment_lower` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.raw_flat_square_distance_lower` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldRawHellinger.raw_flat_affinity_upper` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldTwistHellinger.scalar_sqrt_defect_le_square` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldTwistHellinger.twist_density_nonneg` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldTwistHellinger.sum_twist_density` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldTwistHellinger.twist_flat_sqrt_gap_le` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldTwistHellinger.twist_flat_affinity_defect_upper` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldTwistHellinger.raw_twist_affinity_upper` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairProductSeparation.sqrt_product` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairProductSeparation.packet_affinity_factorization` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairProductSeparation.affinity_product_exp_bound` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairProductSeparation.product_defect_bound` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairProductSeparation.raw_flat_packet_upper` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairProductSeparation.raw_twist_packet_upper` - compiled and focused-audited.
- `PrimeFactorOscillations.FiniteFieldPairProductSeparation.twist_flat_packet_lower` - compiled and focused-audited.

## Exact split-norm Fourier packet and principal row — 28 October 2026

**Fully matched: 13 declarations in one maintained owner.** Over every finite field with distinct roots `r+s=-1`, `r*s=1`, the complete norm-coordinate Fourier sum is `chi(3)*tau(chi)^2*chi^-1(N(w))` for every nonprincipal multiplicative character. No primitive additive-character assumption is needed for that identity. For primitive additive characters the full principal row is exactly `1-q*1_(N(w)=0)+q*(q-1)*1_(w=0)`. Both isotropic lines, their intersection and all nonzero frequencies remain. Characteristic three is excluded by the root hypotheses themselves. The actual Eisenstein quotient/trace specialization, assembled phase-centering consumer and full signed reciprocal-L estimate remain open. No arithmetic power improvement is claimed: the certified boundary is **7/8**, with target **at most 3/4**.

- `PrimeFactorOscillations.CubicNormFourier.hyperbolic_factor` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicNormFourier.hyperbolic_nonprincipal` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicNormFourier.principal_gauss_shift` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicNormFourier.hyperbolic_principal` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicNormFourier.norm_split` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicNormFourier.trace_split` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicNormFourier.norm_hyperbolic` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicNormFourier.difference_sq` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicNormFourier.three_ne_zero` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicNormFourier.split_dual_norm` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicNormFourier.inverse_norm_div_three` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicNormFourier.norm_nonprincipal` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicNormFourier.norm_principal` — compiled and focused-audited.

## Actual Gauss-phase ascent transfer — 28 October 2026

**Fully matched: six declarations in one maintained owner.** The actual phase-balanced kernel gives nonnegative prime weights and a floor of one half on primes coprime to the full inducing modulus `N`. The same `N`, rather than only the prime conductor `q`, controls the witness-deletion budget. Under the explicit existing `LocalAscentSampling` hypothesis and eventual `N(X)<=X^(m(X)/2)`, the complete signed weighted local ascent excess is eventually nonpositive if and only if RH; equivalently it has an eventual `C*X^(7/10)` upper bound. Failure of RH makes that normalized excess unbounded. Infinite twins alone do not discharge the sampling hypothesis. This is a criterion transfer, with no new prime-character estimate: the certified boundary remains **7/8**, and the target remains **at most 3/4**.

- `PrimeFactorOscillations.CarmichaelPhaseAscent.primeWeight_nonneg` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseAscent.primeWeight_ge_half` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseAscent.unit_weights` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseAscent.unbounded_of_not_RH` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseAscent.rh_iff_eventually_nonpos` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseAscent.rh_iff_eventually_power_upper` — compiled and focused-audited.

## Actual Gauss phases and the positive phase-balanced kernel — 28 October 2026

**Fully matched: 30 declarations in three maintained owners.** Primitive additive characters at prime conductor give actual unit Gauss phases compatible with character inversion. Complete finite Fourier matching gives the actual cross coefficients `k_chi=c_chi*(1+g_chi)/2`, with principal coefficient one, nonnegative real parts and exact phase balance. Their native coefficient budget proves the kernel floor `1-1/(d-1)`, hence **at least 1/2 for d>=3**. The actual weighted readout retains principal zeros of arbitrary shared multiplicity. No RH assumption is used. The full native carrier map and signed reciprocal-L arithmetic estimate remain open; the certified boundary is **7/8**, with target **at most 3/4**.

- `PrimeFactorOscillations.DirichletEvenGaussPhase.phase_principal` — compiled and focused-audited.
- `PrimeFactorOscillations.DirichletEvenGaussPhase.phase_norm` — compiled and focused-audited.
- `PrimeFactorOscillations.DirichletEvenGaussPhase.phase_inverse` — compiled and focused-audited.
- `PrimeFactorOscillations.DirichletEvenGaussPhase.cubic_even` — compiled and focused-audited.
- `PrimeFactorOscillations.DirichletEvenGaussPhase.phase_cubic` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.unit_inverse_value` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.unit_inverse_input` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.unit_mixed_sum` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.characterSum_inverse` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.hermitian_series` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.real_series_cast` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.real_series_characterSum` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.coefficient_inverse` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.amplitude_inverse` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.filteredAmplitude_formula` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.filteredAmplitude_inverse` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.filteredProfile_realSeries` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelFilteredSpectrum.filteredProfile_characterSum` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseKernel.principal` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseKernel.expansion` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseKernel.coefficient_amplitude` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseKernel.coefficient_formula` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseKernel.coefficient_re_nonneg` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseKernel.coefficient_phase_balance` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseKernel.coefficient_norm_le` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseKernel.real_expansion` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseKernel.kernel_ge_mass` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseKernel.kernel_ge_half` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseKernel.actual_gauss_kernel_ge_half` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseKernel.actual_gauss_principal_signal` — compiled and focused-audited.

## Weighted principal-zero signal — 28 October 2026

**Fully matched: five declarations in one maintained owner.** For every nonzero Dirichlet modulus, principal coefficient one and nonnegative real parts of all other character weights preserve every principal zero away from one. Arbitrary shared-zero multiplicities are retained: the full scaled logarithmic derivative tends to `-A`, with `Re(A)>0`, and is not analytic at that zero. No RH, zero-free-strip or simple-zero assumption is used. This proves signal retention, not an independent arithmetic bound. The certified boundary remains **7/8**; the target remains **at most 3/4**.

- `PrimeFactorOscillations.CarmichaelWeightedSignal.L_factor_exists` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelWeightedSignal.weighted_limit` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelWeightedSignal.residue_re_bound` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelWeightedSignal.principal_zero_scaled_residue` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelWeightedSignal.principal_zero_not_analytic` — compiled and focused-audited.


## Actual Gaussian physical transfer and unit row — 28 October 2026

**Fully matched: 16 declarations in four maintained owners.** The actual infinite four-Gaussian physical sum is convergent and satisfies exact cubic pair anti-reflection. Projected coprime transpose pairs cancel at their own self-dual scale with no phase-one, kernel-symmetry or Schwartz-profile hypothesis. The actual unit-to-primitive row has the explicit bound `sqrt(q)*B_V*(1+E_O)`. All four compensation scales are retained. The local logarithmic-derivative limit handles arbitrary multiplicity. The finite weighted residue is now proved in the section above. Filtered Fourier matching at prime conductor is now proved above. The complete native carrier map and independent reciprocal-L prime estimate remain open; the certified boundary is **7/8**, with target **at most 3/4**.

- `PrimeFactorOscillations.CubicGaussianPair.gaussian_rescale` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianPair.periodic_gaussian` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianPair.gaussian_pair_poisson` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianWindow.profile_eq_gaussian_sum` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianWindow.pair_gaussian_summable` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianWindow.physical_hasSum` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianWindow.physical_eq_gaussian_sum` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianWindow.reciprocal_four_sum` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianWindow.physical_anti_reflection` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianCancellation.physical_at_one_bound` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianCancellation.physical_at_conductor_bound` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianCancellation.physical_unit_primitive_bound` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianCancellation.physical_balanced_pair_zero` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianCancellation.physical_projected_pair_zero` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicGaussianCancellation.physical_four_reflection` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelWeightedResidue.factor_logDeriv_limit` — compiled and focused-audited.

## Cross profiles and unit-to-primitive rows — 28 October 2026

**Fully matched: 13 declarations in two maintained owners.** The actual nonnegative cross-correlation retains relative Fourier phase, has mean one, and has principal coefficient one. These earlier cubic kernel bounds retain the anti-Fourier Schwartz-profile premise. The actual Gaussian transfer and unit bound are now proved without that premise in the section above. Estimating the full prime-weighted reciprocal-L packet remains open. The certified boundary is **7/8**, with target **at most 3/4**.

- `PrimeFactorOscillations.CarmichaelCrossCorrelation.rawCross_character_sum` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelCrossCorrelation.rawCross_sum` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelCrossCorrelation.crossKernel_character_sum` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelCrossCorrelation.crossKernel_nonneg` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelCrossCorrelation.crossKernel_mean` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelCrossCorrelation.crossCoefficient_principal` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelCrossCorrelation.crossKernel_expansion` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicUnitMixed.pair_at_one_bound` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicUnitMixed.pair_at_conductor_bound` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicUnitMixed.unit_admissible` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicUnitMixed.unit_pairScale` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicUnitMixed.unit_primitive_bound` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicUnitMixed.fourPacket_reflection` — compiled and focused-audited.

## Native phase-filter probability profiles — 28 October 2026

**Fully matched: 16 declarations** in [CarmichaelPhaseFilter.lean](../PrimeFactorOscillations/Assembly/CarmichaelPhaseFilter.lean). The actual single-return spectrum gives an exact unit amplitude budget. Every contractive phase function produces a profile between zero and two of mean one. Dividing it by two gives an acceptance weight between zero and one, of mean one half, with actual principal correlation coefficient one. Prescribed unit-phase amplitudes satisfy phase balance. The actual Gauss phases at prime conductor and their complete Fourier spectrum are now matched in the phase-kernel section above, including its kernel floor and principal-zero readout. Uniform prime sampling and an arithmetic exponent improvement remain separate.

- `PrimeFactorOscillations.CarmichaelPhaseFilter.amplitude_nonprincipal_norm` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.amplitude_norm_sum` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.filteredAmplitude_norm_le` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.filteredAmplitude_norm_sum_le` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.filteredProfile_nonneg` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.filtered_principal` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.filtered_amplitude_balance` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.amplitude_sq_eq_coefficient` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.unit_character_inverse_sum_zero` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.filteredProfile_weightSum` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.filteredProfile_mean` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.filteredProfile_le_two` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.probabilityWeight_bounds` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.probabilityWeight_mean` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.probabilityWeight_sum_pos` — compiled and focused-audited.
- `PrimeFactorOscillations.CarmichaelPhaseFilter.probabilityWeight_principal` — compiled and focused-audited.

## Coupled cubic phases — 28 October 2026

**Fully matched: 13 declarations** in [CubicCoupledPhase.lean](../PrimeFactorOscillations/Helpers/CubicCoupledPhase.lean). For arbitrary admissible coprime ideals, phase-projected coefficients cancel with their transpose at the actual pair-specific self-dual scale. Individual phase-one and kernel-symmetry assumptions are absent. The anti-Fourier Schwartz-window premise remains. Recovering the original coefficients retains the exact mixed-quadrature residual; no signed exponent improvement is claimed.

- `PrimeFactorOscillations.CubicCoupledPhase.project_balance` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicCoupledPhase.quadrature_recovery` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicCoupledPhase.coefficient_phase_swap` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicCoupledPhase.phase_unit_of_norm` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicCoupledPhase.gauss_phase_unit` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicCoupledPhase.balanced_pair_zero` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicCoupledPhase.projected_pair_zero` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicCoupledPhase.four_term_projection` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicCoupledPhase.four_term_pair_assembly` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicCoupledPhase.selfdual_full_residual` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicCoupledPhase.project_compensation` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicCoupledPhase.project_one_real` — compiled and focused-audited.
- `PrimeFactorOscillations.CubicCoupledPhase.phase_weight_re_nonneg` — compiled and focused-audited.

## Infinite physical Carmichael window — 28 October 2026

**Fully matched: 33 declarations in four maintained owners.** Initial Mellin convergence is proved on `Re(s)>1`; the complete quartic readout preserves supported zero poles on `1/2<Re(s)<1`, using the installed unconditional seven-eighths theorem for its reference. The principal character and all prime-power coefficients remain present. These are structural results: the certified boundary remains **7/8**, and the target is **at most 3/4**.

[CubicInfiniteLaplace.lean](../PrimeFactorOscillations/Helpers/CubicInfiniteLaplace.lean) — **compiled and audited**:

- `PrimeFactorOscillations.CubicInfiniteLaplace.lseries_summable` — fully matched.
- `PrimeFactorOscillations.CubicInfiniteLaplace.norm_weights_summable` — fully matched.
- `PrimeFactorOscillations.CubicInfiniteLaplace.laplace_summable` — fully matched.
- `PrimeFactorOscillations.CubicInfiniteLaplace.scaled_norm_weights_summable` — fully matched.
- `PrimeFactorOscillations.CubicInfiniteLaplace.mellin_term_integrable` — fully matched.
- `PrimeFactorOscillations.CubicInfiniteLaplace.integral_norm_mellin_term` — fully matched.
- `PrimeFactorOscillations.CubicInfiniteLaplace.laplace_convergent` — fully matched.
- `PrimeFactorOscillations.CubicInfiniteLaplace.laplace_hasMellin` — fully matched.

[CubicInfiniteWindow.lean](../PrimeFactorOscillations/Helpers/CubicInfiniteWindow.lean) — **compiled and audited**:

- `PrimeFactorOscillations.CubicInfiniteWindow.rate_pos` — fully matched.
- `PrimeFactorOscillations.CubicInfiniteWindow.directMultiplier_eq_carrierMultiplier` — fully matched.
- `PrimeFactorOscillations.CubicInfiniteWindow.windowLaplace_hasSum` — fully matched.
- `PrimeFactorOscillations.CubicInfiniteWindow.windowLaplace_hasMellin` — fully matched.
- `PrimeFactorOscillations.CubicInfiniteWindow.carrierMultiplier_order_mul` — fully matched.

[CarmichaelInfiniteWindow.lean](../PrimeFactorOscillations/Assembly/CarmichaelInfiniteWindow.lean) — **compiled and audited**:

- `PrimeFactorOscillations.CarmichaelInfiniteWindow.physicalPacket_hasSum` — fully matched.
- `PrimeFactorOscillations.CarmichaelInfiniteWindow.physicalPacket_hasMellin` — fully matched.
- `PrimeFactorOscillations.CarmichaelInfiniteWindow.quartic_physical_mellin` — fully matched.
- `PrimeFactorOscillations.CarmichaelInfiniteWindow.comparison_physical_hasMellin` — fully matched.
- `PrimeFactorOscillations.CarmichaelInfiniteWindow.comparison_quartic_mellin` — fully matched.
- `PrimeFactorOscillations.CarmichaelInfiniteWindow.windowReadout_order_iff_zero` — fully matched.
- `PrimeFactorOscillations.CarmichaelInfiniteWindow.nativeWindowReadout_order_iff_product_zero` — fully matched.
- `PrimeFactorOscillations.CarmichaelInfiniteWindow.native_principal_zero_signal` — fully matched.

[CarmichaelNativeWindow.lean](../PrimeFactorOscillations/Assembly/CarmichaelNativeWindow.lean) — **compiled and audited**:

- `PrimeFactorOscillations.CarmichaelNativeWindow.native_product_logDeriv` — fully matched.
- `PrimeFactorOscillations.CarmichaelNativeWindow.nativeCorrection_analyticAt` — fully matched.
- `PrimeFactorOscillations.CarmichaelNativeWindow.nativePacket_hasMellin` — fully matched.
- `PrimeFactorOscillations.CarmichaelNativeWindow.nativePacket_hasSum` — fully matched.
- `PrimeFactorOscillations.CarmichaelNativeWindow.native_lambda_hasSum` — fully matched.
- `PrimeFactorOscillations.CarmichaelNativeWindow.native_quartic_mellin` — fully matched.
- `PrimeFactorOscillations.CarmichaelNativeWindow.native_observed_zero_readout` — fully matched.
- `PrimeFactorOscillations.CarmichaelNativeWindow.native_reference_analyticAt` — fully matched.
- `PrimeFactorOscillations.CarmichaelNativeWindow.native_compensated_order_iff_product_zero` — fully matched.
- `PrimeFactorOscillations.CarmichaelNativeWindow.native_compensated_observed_zero` — fully matched.
- `PrimeFactorOscillations.CarmichaelNativeWindow.native_compensated_principal_signal` — fully matched.
- `PrimeFactorOscillations.CarmichaelNativeWindow.native_quartic_mellin_eq_compensated` — fully matched.

Still open: the actual prime-selected paired-coset adapter and the signed Abel-endpoint estimate `I_(D,G) << D^(3/2+epsilon)`. The proved unit-lattice tail is not a bound on the arithmetic coefficient `C_G`. No strengthened character estimate is claimed.

## Recent paper claims — reconciliation of 25 October 2026

All **147 labelled claims in the recent-paper repair ledger** have explicit current statuses: **90 fully matched, 13 partially matched, and 44 with no exact maintained full-statement match identified**. There are **zero default pending matches** and **zero completed proofs awaiting promotion**. The formalization backlog is not complete; the separate review of unlabelled paper assertions remains open.

“Fully matched” records existing Lean proofs of the complete statement. “Partial match” records proved clauses and lists the remaining clauses. “No exact match identified” records the result of the maintained-source comparison; related inputs alone do not establish the stated theorem. Existing proof verification is reused here. No unchanged proof closure or axiom audit was rerun.

The table includes every claim in this ledger, in ledger order. Owner links identify a recorded input or proof owner; the declaration count is the recorded match count, not a new build count. The complete declaration lists and verification receipts remain in the canonical claim records.

| # | Paper claim | Current status | Recorded evidence and remaining clauses |
|---|---|---|---|
| 1 | A computable prime-Poisson overlap criterion for RH (`thm:prime-Poisson-repair-RH`) | **No exact match identified** | No exact full-statement declaration match identified. Construct the stated countable Poisson product probability measures and prove their exact affinities. Prove the mutual absolute-continuity versus singularity dichotomy and its Euler summability equivalence. Connect the fixed rational repair models to the unconditional bad-zero response and the quantified RH equivalence. Prove the stated computability of finite affinities. |
| 2 | The signed repair--energy comparison (`prop:signed-repair-Hellinger`) | **Fully matched** | 10 matched declarations. Recorded owner: [RepairHellinger.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/RepairHellinger.lean). No remaining clause. |
| 3 | Underweight transfer along the real axis (`thm:underweight-real-axis-transfer`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the general character-portfolio Euler quotient with its stated continuation and real-axis nonvanishing hypotheses. Prove the implication from the underweight count bound to zero exclusion, including the unconditional zeta dyadic response. Retain the possible exceptional real zero in the general Dirichlet statement. |
| 4 | A predefined deleted-prime RH criterion (`thm:computable-deleted-prime-RH`) | **Partial match** | 5 matched declarations. Recorded owner: [PartialCapacityCounts.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PartialCapacityCounts.lean). Implement and prove termination/correctness of the specified deterministic rational optimal-vertex and rounding construction. Prove the fractional-coordinate bound 2*k*u^(1/(2*k)) for the actual constructed weights. Prove the independently favorable full Euler continuation, unconditional zero-response readout and all stated RH/strip equivalences for these particular classes. |
| 5 | Few nonbinary coordinates at an optimal rational vertex (`lem:rational-LP-binary-vertex`) | **No exact match identified** | No exact full-statement declaration match identified. Prove at most k nonbinary coordinates at every optimal rational LP vertex, including constant-dual and mass-deficit cases. Prove existence and deterministic selection of a minimizing rational vertex. Prove the stated rounded moment accuracy and optimal repair-mass bounds. |
| 6 | The exact deleted-count ledger (`lem:deleted-count-deficit-ledger`) | **Fully matched** | 7 matched declarations. Recorded owner: [PartialCapacityCounts.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PartialCapacityCounts.lean). No remaining clause. |
| 7 | Computable prime classes retaining critical-line zeros (`thm:critical-deleted-prime-model`) | **Partial match** | 3 matched declarations. Recorded owner: [PartialCapacityCounts.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PartialCapacityCounts.lean). Formalize the specified critical cell scale and deterministic rational model with decidable actual prime membership. Prove the full favorable product representation s/(s-1)*exp(G) on Re(s)>0. Prove the 2*k*u^(1/k) bound for the actual model and the beta>1/k zero readout. Derive unconditional infinitude and infinitely-often square-root-size dyadic counts for the specified classes. |
| 8 | The zero supremum recovered from literal prime counts (`thm:prime-count-exponents-zero-supremum`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the actual D_k^0 classes and lambda_k from the critical rational model. Prove Theta_zeta<=lambda_k<=min(1,Theta_zeta+1/k), its k-limit/infimum, and the stated RH equivalences. |
| 9 | One computable prime class with the exact zero exponent (`thm:single-computable-prime-RH`) | **No exact match identified** | No exact full-statement declaration match identified. Implement the specific fixed computable diagonal class D_* and prove effective prime membership. Prove its exact unconditional counting exponent Theta_zeta and all eta-strip equivalences. Prove the claimed unconditional infinitude and dyadic lower counts for D_*. |
| 10 | Prime-count error to the right of the zero supremum (`lem:prime-error-zero-supremum`) | **Fully matched** | 2 matched declarations. Recorded owner: [PrimeCountingZeroSupremum.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimeCountingZeroSupremum.lean). No remaining clause. |
| 11 | Both one-sided Euler masses diverge at a zero (`thm:two-sided-prime-endpoint-divergence`) | **No exact match identified** | No exact full-statement declaration match identified. Construct the full weighted Euler quotient for the stated arbitrary nonnegative weights and continue it with both positive/negative parts retained. Prove that a zero rho with Re(rho)=beta>tau forces divergence of BOTH P_d(beta) and P_e(beta), without a rightmost-zero hypothesis. |
| 12 | Logarithmic one-sided cost of a boundary zero (`thm:prime-zero-logarithmic-cost`) | **No exact match identified** | No exact full-statement declaration match identified. Prove convergence of the overweight series for every sigma>beta from the stated underweight assumption. Formalize the full Euler-quotient multiplicity argument giving BOTH lower bounds (m/2)*log(1/h)-O_{rho,w}(1), as h decreases to zero. |
| 13 | Endpoint size of the computable prime class (`cor:computed-prime-endpoint-size`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the specified D_* class and its root-reciprocal divergence. Prove the multiplicity-dependent endpoint reciprocal lower bound and the count limsup m/(2*beta). Prove the unconditional critical-line count limsup at least m, including infinity when RH fails. |
| 14 | Root-summable exclusions preserve the signal (`cor:computed-prime-root-summable-exclusions`) | **Partial match** | 3 matched declarations. Recorded owner: [PrimeClassSparseDeletion.lean](../PrimeFactorOscillations/Helpers/PrimeClassSparseDeletion.lean). Instantiate the general root-summable exclusion theorem for the specified D_*, whose construction and endpoint statements are not formalized. Transfer the exact count exponent, all strip/RH equivalences, and the multiplicity-dependent root-size limsup under the general root-summability assumption. |
| 15 | Theta-upcrossing cutoffs retain Nicolas violations (`thm:theta-upcrossing-RH-test`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the actual theta-upcrossing classes U and S_+ used by the paper. Prove that Not RH yields infinitely many F(p)>0 cutoffs inside U, and derive both eventual-sign equivalences without a density assumption. |
| 16 | Greedy cap and optimal deletion cost (`thm:greedy-prime-cap`) | **Fully matched** | 1 matched declaration. Recorded owner: [GreedyPrimeRealCutoffs.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/GreedyPrimeRealCutoffs.lean). No remaining clause. |
| 17 | The selected class already has the product sign (`prop:greedy-prime-product-sign`) | **Fully matched** | 52 matched declarations. Recorded owner: [GreedyPrimeEulerSummability.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/GreedyPrimeEulerSummability.lean). No remaining clause. |
| 18 | The size condition retains every off-line zero (`thm:greedy-prime-RH-size`) | **Fully matched** | 15 matched declarations. Recorded owner: [GreedyPrimeExcursionTransfer.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/GreedyPrimeExcursionTransfer.lean). No remaining clause. |
| 19 | Exact size burden for the certified good class (`thm:certified-good-prime-size`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the paper's actual G and B prime classes and the unconditional good-count exponent 1. Prove the bad-count exponent dichotomy: 0 under RH and 1 under Not RH. Compile the exact resulting equivalence with B(X)=O(X^(1-delta)) for some fixed 0<delta<1. |
| 20 | Persistence through consecutive prime indices (`lem:prime-index-persistence`) | **No exact match identified** | No exact full-statement declaration match identified. Prove the uniform consecutive-prime bound abs(F(p)-F(q))<=C_kappa*X^(kappa-2)*log(X)^2 for 1/2<=kappa<=1 and X<=p<=2X. Prove both signed prime-count consequences B(2P),G(2P)>=c_kappa*P^(2-kappa-b)/log(P)^2 for 0<b<1/2 and kappa+b>1. |
| 21 | Rank domination and exact optimality (`thm:capped-prime-rank-extremum`) | **Fully matched** | 1 matched declaration. Recorded owner: [CappedPrimeWeights.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/CappedPrimeWeights.lean). No remaining clause. |
| 22 | Stochastic and coefficient extremality (`thm:capped-prime-probability-extremum`) | **Fully matched** | 1 matched declaration. Recorded owner: [CappedPrimeProbability.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/CappedPrimeProbability.lean). No remaining clause. |
| 23 | The deletion envelope of a periodic leading error (`thm:greedy-prime-wave-envelope`) | **Fully matched** | 1 matched declaration. Recorded owner: [PrimeWavePeriodic.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimeWavePeriodic.lean). No remaining clause. |
| 24 | Joint almost-periodic waves (`thm:greedy-prime-joint-wave-envelope`) | **Fully matched** | 1 matched declaration. Recorded owner: [PrimeWaveJoint.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimeWaveJoint.lean). No remaining clause. |
| 25 | Explicit response to one leading harmonic (`thm:greedy-prime-cosine-envelope`) | **Fully matched** | 1 matched declaration. Recorded owner: [CosineEnvelope.lean](../PrimeFactorOscillations/Helpers/CosineEnvelope.lean). No remaining clause. |
| 26 | A forbidden zero forces deletions at every large cutoff (`thm:greedy-prime-uniform-zero-response`) | **Fully matched** | 34 matched declarations. Recorded owner: [LogGaussianRealTilt.lean](../PrimeFactorOscillations/Helpers/LogGaussianRealTilt.lean). No remaining clause. |
| 27 | Infinitely-often deletion-size criterion (`thm:greedy-prime-liminf-RH`) | **Fully matched** | 3 matched declarations. Recorded owner: [GreedyPrimeCountLiminf.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/GreedyPrimeCountLiminf.lean). No remaining clause. |
| 28 | Stabilizing probability-profile rank test (`thm:greedy-prime-RH-rank-clock`) | **Partial match** | 2 matched declarations. Recorded owner: [GreedyPrimeCountLimit.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/GreedyPrimeCountLimit.lean). Identify pi(n)-degree(P_{S,n}) with the actual deleted-prime count in a maintained declaration. Define and prove stabilization and both quantified bit/RH equivalences for the exact displayed bit. Prove effective computation of the specified class and the exact threshold comparison; eventual constancy alone does not prove this prescribed algorithm computable. |
| 29 | Signed Gaussian explicit formula with the prime powers retained (`lem:greedy-prime-Gaussian-explicit`) | **Fully matched** | 9 matched declarations. Recorded owner: [LogGaussianAbsoluteMoment.lean](../PrimeFactorOscillations/Helpers/LogGaussianAbsoluteMoment.lean). No remaining clause. |
| 30 | A Gaussian shift exposes a strictly dominant zero (`lem:greedy-prime-Gaussian-exposure`) | **Fully matched** | 14 matched declarations. Recorded owner: [ZetaZeroGeometry.lean](../PrimeFactorOscillations/Helpers/ZetaZeroGeometry.lean). No remaining clause. |
| 31 | An unconditional square-root floor for deleted primes (`thm:greedy-prime-critical-record-floor`) | **Partial match** | 1 matched declaration. Recorded owner: [GaussianPositiveSignal.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/GaussianPositiveSignal.lean). Prove the unconditional all-real-cutoff R(X)>=c*sqrt(X) and N_D(X)>=c*sqrt(X)/log(X), including the RH/critical-line case. Compile the unconditional infinitude and the effectivity assertion for the stated fixed class. |
| 32 | An exact all-scale exponent and its inverse prime sequence (`thm:greedy-prime-all-scale-exponent`) | **Partial match** | 2 matched declarations. Recorded owner: [GreedyPrimeCountLimit.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/GreedyPrimeCountLimit.lean). Prove the missing critical lower count bound and assemble the unconditional real-cutoff count-exponent limit. Define the actual infinite deleted-prime enumeration and prove log(d_j)/log(j)->1/Theta. Prove unconditional d_j<<j^2*log(j)^2, the RH characterization, and both RH inverse bounds. |
| 33 | Compact positive window with the square-prime term retained (`lem:greedy-prime-compact-critical-profile`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the specified triangular W_h, tilted K_h, sinc-squared w and the exact critical Fourier series. Prove the fixed-h normalized asymptotic including the full square-prime constant -1. Prove absolute/uniform convergence in v and uniform almost periodicity of this specific series. |
| 34 | Coherent critical frequencies exceed the square-prime bias (`lem:greedy-prime-critical-coherence`) | **No exact match identified** | No exact full-statement declaration match identified. Prove f_h(-2*h)=(1/2)*log(1/h)+O(1) as h decreases to zero with a uniform constant. Derive existence of a fixed h with positive compact critical profile from that estimate. |
| 35 | Exact record-to-count calibration and logarithmic concentration (`thm:greedy-prime-record-count-calibration`) | **No exact match identified** | No exact full-statement declaration match identified. Prove N_D(X)~M(X)/log(X)~R(X)/log(X) for the actual deleted class. Prove N_D(X^a)/N_D(X)->0 for every fixed 0<=a<1. Formalize the stated uniform finite-prime sample and its convergence in probability. |
| 36 | A full prime-power law with a uniform sampling error (`thm:deleted-component-sampling-law`) | **Fully matched** | 179 matched declarations. Recorded owner: [ComponentEmpiricalStatistics.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/ComponentEmpiricalStatistics.lean). No remaining clause. |
| 37 | The exact statistical convergence exponent (`thm:deleted-component-exact-rate`) | **No exact match identified** | No exact full-statement declaration match identified. Prove positivity and matching lower/upper exponents for full-component TV, largest-prime-factor TV and Kolmogorov distances. Compile the exact strip and RH convergence-rate equivalences, including the critical case. Available completed input: claim 36, including the infinite component law and geometric independence. |
| 38 | A positive divisor identity gives the full moment spectrum (`thm:deleted-component-moment-spectrum`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the positive divisor/Jordan identity for A_D(m)^t and its full infinite-class moment consumer. Prove the exponent max(0,Theta+t-1), limiting Euler moment and strictly positive deficit with its exact exponent. Prove U_{1/2}(N)>>loglog(N), its exact exponent and the resulting RH equivalence. |
| 39 | Every reciprocal tail has an exact exponent (`lem:deleted-prime-weighted-tail`) | **Partial match** | 1 matched declaration. Recorded owner: [GreedyPrimeCountLimit.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/GreedyPrimeCountLimit.lean). Prove T_s(X)=X^(Theta-s+o(1)) for EVERY fixed s>Theta, with matching lower bounds and the RH/critical case. Do not replace T_s by the different retained-prime Nicolas Euler tail bounded in GreedyPrimeEulerTailBound. |
| 40 | The greedy deletion law is the least concave-cost law (`thm:greedy-geometric-concave-extremum`) | **No exact match identified** | No exact full-statement declaration match identified. Construct the full geometric product laws, including competitors with value infinity. Prove expectation domination for every nonnegative nondecreasing concave g. Prove strict capped-mean inequality for EVERY x>1 when the capped class differs, and uniqueness. |
| 41 | Maximal retained density and minimal component entropy (`thm:greedy-component-density-entropy`) | **Partial match** | 2 matched declarations. Recorded owner: [CappedPrimeMissingCost.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/CappedPrimeMissingCost.lean). Prove natural density of every competitor's supported integer class, including zero-product cases, and the stated strict density comparison. Construct the infinite component entropy, prove its exact series formula and finiteness for the greedy class. Prove entropy minimality and both uniqueness/equality conclusions. |
| 42 | Adaptive finite caps cannot reduce the moment exponent (`thm:adaptive-capped-moment-exponent`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the finite admissible-subset optimization V_t(N) over the exact logarithmic cap constraints. Prove the uniform positive full-component moment floor with c_t=(1-2^(-t))/2 for every finite admissible selection. Prove the exact optimized exponent, square-root loglog floor and strip equivalence. Prove the stated effective computation of the optimal value and attaining subset. |
| 43 | Geometric prime factors are ordered by every concave loss (`lem:geometric-prime-concave-order`) | **No exact match identified** | No exact full-statement declaration match identified. Construct G_p and Z_p for every real p>1 and prove the exact capped-mean formula with k=floor(log(x)/log(p)). Prove strict decrease of S_p(x) in real p for each x>1, across all floor transitions. Prove the expectation comparison for all allowed concave g, including infinite expectations. |
| 44 | Greedy rank optimality with arbitrary budgets (`thm:ordered-stream-greedy-optimality`) | **Fully matched** | 7 matched declarations. Recorded owner: [CapacitySelectionFinite.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/CapacitySelectionFinite.lean). No remaining clause. |
| 45 | Reciprocal indices of growth and rare probabilities (`thm:thin-prime-rare-profile`) | **Partial match** | 3 matched declarations. Recorded owner: [PrimeClassCountProfileLaw.lean](../PrimeFactorOscillations/Helpers/PrimeClassCountProfileLaw.lean). Prove M(r)=P(r), the exact entire-order limit alpha, and strict positivity of every point mass and tail including the asserted b0. Prove the ordered-prime product lower bound, the stated optimized tail upper bound q_k (not only a point bound), and both exact rare-probability limits 1/alpha. |
| 46 | Arithmetic and independent records agree (`thm:thin-prime-record-duality`) | **No exact match identified** | No exact full-statement declaration match identified. Define the exact arithmetic support maximum H_P and prove its alpha*log(N)/loglog(N) asymptotic. Construct the iid count samples and prove the almost-sure extreme-value asymptotic and W_P/H_P limit. |
| 47 | Uniform relative recovery at growing ranks (`thm:thin-prime-growing-rank-recovery`) | **Partial match** | 1 matched declaration. Recorded owner: [PrimeClassCountProfileLaw.lean](../PrimeFactorOscillations/Helpers/PrimeClassCountProfileLaw.lean). Supply the rare-mass positive lower bound required to divide the absolute error uniformly over k<=floor(c*log(N)/loglog(N)). Compile the exact domains c<alpha*(1-alpha), delta<1-alpha-c/alpha, simultaneous mass/tail relative bounds, eventual positivity and growing-rank exponents. |
| 48 | Exact adaptive minimax for the factor-count record (`thm:greedy-adaptive-support-minimax`) | **Partial match** | 1 matched declaration. Recorded owner: [CappedPrimeCoordinateOrder.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/CappedPrimeCoordinateOrder.lean). Define the exact maximum number of excluded prime divisors under m<=N and prove the finite minimax equality with H_D(N), including attainment. Compile the all-cutoff uniqueness statement and the asymptotic record constant, with the critical count-index input explicitly supplied. |
| 49 | A fully discrete rare-count readout of the zero supremum (`cor:greedy-discrete-rare-RH`) | **Partial match** | 1 matched declaration. Recorded owner: [PrimeClassCountProfileLaw.lean](../PrimeFactorOscillations/Helpers/PrimeClassCountProfileLaw.lean). Prove the exact rare-count asymptotics and invert them to recover the actual zero supremum, including the critical/RH case. Compile the specified binary rank, c<7/64 parameter domain, delta<1/8-8*c/7, uniform k<=log(N)/(10*loglog(N)) and O(N^(-1/100)) bounds. Prove the displayed rare-count strip/RH equivalences and effective computation for the literal count/rank prescription. |
| 50 | Full affine law with its forced component (`thm:affine-thin-full-law`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the literal A+q*n full-component sampling law, with q0=q/g versus q coordinate masks kept distinct. Prove the full l1/TV estimate B*R^sigma/M, the rank shift K_P(g)+K_Q, and the joint local valuation distribution. Include prime 2, M=1, g>1 and each v_p(A) versus v_p(q) case in the exact formal statement. |
| 51 | Uniform affine recovery of rare profiles (`thm:affine-thin-rare-recovery`) | **No exact match identified** | No exact full-statement declaration match identified. Prove the literal progression law and a positive supply uniform over the modulus mask, then divide its error by the retained model masses. Compile all stated h,gamma,rho,c,delta hypotheses, the shifted r+k bins, uniform family constants and exact Y^(-c/alpha+o(1)) limits. |
| 52 | Exact optimal filter under a product budget (`thm:thin-prime-product-filter-optimality`) | **No exact match identified** | No exact full-statement declaration match identified. Define the product-budget filter class and prove that deleting the first H_P(B) class primes minimizes every infinite Bernoulli tail. Prove uniqueness for every positive tail rank, without claiming false point-mass monotonicity. |
| 53 | Sharp budget threshold for erasing a rare-event exponent (`thm:thin-prime-filter-budget-phase`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the minimum point mass and tail over all product-budget filters. Prove the full phase function 1+(1/alpha-1)*max(1,s), prefix attainment of both limiting exponents, and the stated uniform result for s<=1. |
| 54 | Uniform positive supply after a moving finite filter (`lem:masked-thin-positive-supply`) | **No exact match identified** | No exact full-statement declaration match identified. Prove the lower bound b_k^S>=c_P*p_(J+k)^(-k), b_0^S>=c_P and the stated tail comparisons. Compile the modulus-uniform Y^(-c/alpha-epsilon) positive supply throughout k<=floor(c*log(Y)/loglog(Y)), including its eventual cutoff and constants. |
| 55 | An optimal disappearing law still carries the zero index (`cor:primorial-filter-zero-index`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the literal primorial progression and minimum over all unit residue classes q<=B_X, and prove their common nonzero-count exponent and TV convergence to delta_0. Prove both greedy-class zero-index/RH equivalences and the binary rank 1/20 mass/tail asymptotics with O(X^(-1/200)) relative error. Compile the exact integer prescriptions and their computability, preserving the budget b<1-alpha. |
| 56 | A growing rare profile determined by the zero bin (`thm:zero-bin-poisson-reconstruction`) | **No exact match identified** | No exact full-statement declaration match identified. Define the actual progression zero-bin parameter and prove its eventual positivity and asymptotic identification with lambda_J. Prove relative Poisson approximation uniformly through floor(J^(1/2-epsilon)), with J^(-2*epsilon+o(1)) error. |
| 57 | The conditional surviving component is one localized prime (`thm:conditional-thin-single-prime-localization`) | **No exact match identified** | No exact full-statement declaration match identified. Prove that the actual progression full component, conditional on exceeding one, is prime with probability 1-O(J^(-v+o(1))). Prove the stated conditional log-size localization with t=min(1,alpha*eta/2), including both prime-power and multiple-distinct-prime errors. |
| 58 | Computable conditional quantiles recover the zero supremum (`cor:conditional-thin-quantile-RH`) | **No exact match identified** | No exact full-statement declaration match identified. Define the literal conditional lower quantile and prove existence and log(m_tau)/loglog(X)->1/alpha uniformly over compact tau intervals. Prove computability for the greedy class and assemble the exact zero-supremum limit, median RH equivalences and 3/4 strip equivalence, including the critical case. |
| 59 | Rational reconstruction from the first three empirical bins (`thm:three-bin-rational-reconstruction`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize W_hat, q_hat and the rational reference from the actual progression bins; prove eventual 0<q_hat<1 and exact matching of bins 0,1,2. Prove the full uniform relative bound J^(-3*epsilon+o(1)) through rank J^(2/3-epsilon) and the stated effective rational computation. |
| 60 | A uniform pair-collision correction (`lem:uniform-pair-collision-correction`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize finite/countable iid no-collision probabilities and their strict positivity under m<=1/4 and n*m<=1/4. Prove both explicit logarithmic error bounds with constants 8 and 10, retaining theta_3+theta_2^2 and the positive-log arguments. |
| 61 | A genuine transition for the uncorrected Poisson law (`cor:three-bin-poisson-transition`) | **No exact match identified** | No exact full-statement declaration match identified. Prove the actual empirical mass/zero-bin Poisson ratio tends to one for 0<u<1/2. Prove exp(-J^(2*u-1+o(1))) decay for 1/2<u<2/3 and continued relative accuracy of the corrected three-bin reference. |
| 62 | The empirical finite-bin hierarchy (`thm:empirical-finite-bin-hierarchy`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the signed integer-power empirical parameters Gamma_j and their exact interpolation of bins 0 through r, including positive denominators. Prove the fixed-order uniform relative estimate through J^(r/(r+1)-epsilon), with exponent -(r+1)*epsilon and computable rational references. |
| 63 | Uniform interpolation of collision logarithms (`lem:all-order-collision-interpolation`) | **No exact match identified** | No exact full-statement declaration match identified. Construct F(n)=log(D_n) for finite/countable probability vectors and prove every required D_i positive when m*max(n,r)<=1/16. Prove the full Newton remainder C_r*n^(r+1)*m^r with C_r=8^r*(1+2^r*r^(r+1)/r!), for every integer r>=1 and n>=0. |
| 64 | Finite data recover every fixed sublinear power (`cor:finite-bin-every-sublinear-power`) | **No exact match identified** | No exact full-statement declaration match identified. Compile the specialization r>u/(1-u) of the empirical hierarchy and its uniform J^(-(r-(r+1)*u)+o(1)) relative error. Include the four-bin u<3/4 and five-bin u<4/5 consequences over the exact empirical progression counts. |
| 65 | Sharp scale for the canonical interpolation formula (`cor:uniform-collision-interpolation-sharpness`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize uniform-N no-collision probabilities and the canonical degree-r Newton reference. Prove the exact asymptotic -n^(r+1)/(r*(r+1)*N^r)*(1+o(1)) for n->infinity with n=o(N), and the stated critical-scale ratio limit. |
| 66 | An empirical reconstruction at almost linear rank (`thm:adaptive-bin-almost-linear`) | **No exact match identified** | No exact full-statement declaration match identified. Implement the specified discrete selector, order (A+3)*binaryLength(J), measured maximum and cutoff, with eventual positive observed bins. Prove growing-order stability and the stated error O(J^(-A)+X^(-delta)) uniformly through L_X, with all interpolation amplification charged. Prove L_X=J^(1+o(1))=O(J), the exact c/delta domain and computability from literal integer counts and rational arithmetic. |
| 67 | Stability with every interpolation power charged (`lem:adaptive-bin-stability`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize the positive model nodes beta_k, observed reference, minima u and v, and amplification S(L,r). Prove the fully explicit exp(E+eta)-1+(Delta/v)*exp(E+eta) bound, node interpolation and S(L,r)<=(r+1)*(1+2*L)^r under every stated hypothesis. |
| 68 | A linear window under power asymptotics (`cor:adaptive-bin-linear-power-law`) | **No exact match identified** | No exact full-statement declaration match identified. Under p_j~C*j^(1/alpha), prove the actual adaptive cutoff satisfies L_X/J->min(1/(512*v),c/(alpha*b))>0. Assemble its O(log(J))-bin relative reconstruction consumer with error O(J^(-A)). |
| 69 | An unconditional adaptive profile for the greedy class (`cor:adaptive-bin-greedy-class`) | **No exact match identified** | No exact full-statement declaration match identified. Specialize the actual adaptive progression reconstruction to greedy deletion with b=1/16 and c=1/20. Prove its unconditional O_A(J^(-A)+X^(-1/200)) relative bound and L_X=J^(1+o(1)), including the critical count-index input. |
| 70 | An almost optimal cutoff measured from the bins (`thm:empirical-moment-cutoff`) | **No exact match identified** | No exact full-statement declaration match identified. Implement normalized observed coefficients, signed Newton moment recovery, rational upper-root prescription and the cutoffs at t_X=binaryLength(J)^2. Prove 1<=m_tilde/m_J<=1+O(1/log(J)) and cutoff loss O(1/log(J)), preserving all sampling and amplification errors. Prove the exp(-(log(J))^2)+X^(-delta) uniform relative bound, the exact parameter domain, computability and the unconditional greedy specialization delta=1/200. |
| 71 | Uniform stability of collision-moment recovery (`lem:empirical-collision-moment-stability`) | **No exact match identified** | No exact full-statement declaration match identified. Formalize finite/countable elementary symmetric coefficients and the signed triangular identities for recovered moments. Prove \|theta_hat_s-theta_s\|<=s*4^s*epsilon, m^s<=theta_s<=m^(s-1) and the positive upper-root bound, uniformly in t and moment signs. |
| 72 | The same calibration within a logarithmic bin budget (`cor:empirical-cutoff-logarithmic-budget`) | **No exact match identified** | No exact full-statement declaration match identified. Prove the t_X=(A+3)*binaryLength(J) measured maximum lies between m_J and (2^(1/(A+3))+o(1))*m_J. Compile the liminf/limsup cutoff ratio bounds and O_A(J^(-A)+X^(-delta)) uniform reconstruction with only O_A(loglog(X)) empirical bins. |
| 73 | Exact calibrated linear limits under power asymptotics (`cor:empirical-cutoff-linear-limits`) | **No exact match identified** | No exact full-statement declaration match identified. Under p_j~C*j^(1/alpha), prove the two actual measured cutoffs have limits min(1/(256*v),c/(alpha*b)) and min(1/(256*2^(1/(A+3))*v),c/(alpha*b)). Prove positivity and connect those exact constants to the respective fully empirical constructions, rather than to the prime-assisted cutoff. |
| 74 | Exact prime labels from finite integer sign tests (`thm:finite-integer-prime-decoding`) | **Fully matched** | 1 matched declaration. Recorded owner: [PrimeClassDecoderComplete.lean](../PrimeFactorOscillations/Helpers/PrimeClassDecoderComplete.lean). No remaining clause. |
| 75 | The exact critical decoding exponent (`thm:prime-decoding-critical-exponent`) | **Fully matched** | 1 matched declaration. Recorded owner: [PrimeClassDecoderClassification.lean](../PrimeFactorOscillations/Helpers/PrimeClassDecoderClassification.lean). No remaining clause. |
| 76 | Sampling on a growing complex disc (`lem:finite-decoding-complex-error`) | **Fully matched** | 2 matched declarations. Recorded owner: [PrimeClassDecoderComplexError.lean](../PrimeFactorOscillations/Helpers/PrimeClassDecoderComplexError.lean). No remaining clause. |
| 77 | A finite integer-sign criterion for RH (`cor:prime-decoding-RH`) | **Partial match** | 5 matched declarations. Recorded owner: [PrimeClassCountingExponent.lean](../PrimeFactorOscillations/Helpers/PrimeClassCountingExponent.lean). Compile the actual greedy-class identification C_dec(D)=1/Theta_zeta and its RH and 3/4 equivalences, with every required greedy-class power-summability or count-index input explicitly discharged. Compile the exact rational eventual-prefix formulation and the explicit h=10/9, sigma=8/9, c=8/81 specialization, including the O(N^(-1/1000)) complex-disc error and labels 2 and 3. |
| 78 | Prime values of exponential sequences have infinite capacity (`cor:prime-decoding-sparse-special-classes`) | **Fully matched** | 1 matched declaration. Recorded owner: [PrimeClassSpecialValueCapacity.lean](../PrimeFactorOscillations/Helpers/PrimeClassSpecialValueCapacity.lean). No remaining clause. |
| 79 | Exact distance between full component laws (`thm:component-reference-exact-distance`) | **Fully matched** | 21 matched declarations. Recorded owner: [GreedyPrimeGeometricLaw.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/GreedyPrimeGeometricLaw.lean). No remaining clause. |
| 80 | Exact inverse norm of multiplicative prime-component noise (`thm:component-carrier-exact-inverse-norm`) | **Fully matched** | 32 matched declarations. Recorded owner: [PrimeComponentCarrierArithmetic.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimeComponentCarrierArithmetic.lean). No remaining clause. |
| 81 | Sharp stability of multiplicative prime-component noise (`thm:component-carrier-sharp-probability-stability`) | **Fully matched** | 31 matched declarations. Recorded owner: [ArithmeticFunctionDirichletL1.lean](../PrimeFactorOscillations/Helpers/ArithmeticFunctionDirichletL1.lean). No remaining clause. |
| 82 | Exact inverse geometry and optimal finite-prime approximation (`thm:component-carrier-exact-geometry`) | **Fully matched** | 16 matched declarations in [PrimeComponentCarrierDistance.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimeComponentCarrierDistance.lean) and [PrimeComponentCarrierCutoff.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimeComponentCarrierCutoff.lean). Exact general and nested inverse distances, convergence of finite-prime inverses, and the optimal uniform convolution error constant. Both owners and all five affected public consumers compiled. No remaining clause. |
| 83 | Centered record energy on a long interval (`lem:centered-record-interval`) | **Fully matched** | Six proved declarations in [ClockRecordEnergy.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/ClockRecordEnergy.lean) and [PrimeRecordEnergy.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimeRecordEnergy.lean). Exact centered identities with terminal corrections, interval quadratic variation, and a conditional clock barrier. Both changed owners compiled. The signed-energy estimate remains a hypothesis; no new zero-free boundary or square-root count bound is asserted. No remaining clause of this lemma. |
| 84 | Balanced records for a sublinear clock (`lem:balanced-sublinear-records`) | **Fully matched** | Three proved declarations in [ClockRecordEnergy.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/ClockRecordEnergy.lean) and [PrimeRecordEnergy.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimeRecordEnergy.lean). Every unbounded sublinear monotone clock has arbitrarily late balanced record endpoints, with its jump correction. For the actual prime record, either the record is bounded or arbitrarily large prime records satisfy R(p)-log(p)<=2R(floor(p/2)). Uses the existing unconditional mass limit. Both changed owners and the energy-bound consumer compiled. No remaining clause of this lemma; no improved zero-free boundary is claimed. |
| 85 | Signed psi work and complete midpoint compensation (`lem:signed-psi-record-work`) | **Fully matched** | The actual psi clock, proper-prime-power correction, complete endpoint and record-jump terms, two-sided signed bounds, and positive retained self-work compile in [PrimeRecordEnergy.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimeRecordEnergy.lean), using the proved coupled clock identities in [ClockRecordProduct.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/ClockRecordProduct.lean). Both changed owners and the energy-bound consumer compiled. The finite midpoint identity retains the final-cutoff correction; it does not assert an infinite Abel limit. No remaining clause of this lemma. The independent root-scale upper bound and square-root deletion sequence remain open; boundary7/8 is unchanged. |
| 86 | Complete retained-prime feedback (`lem:retained-prime-feedback`) | **Fully matched** | Every accepted prime logarithm and elapsed prime gap is present in `primeClock_retained_source_step`. The exact headroom feedback, signed retained-work bounds, and surviving deleted-prime quadratic diagonal compile in [PrimeRecordEnergy.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimeRecordEnergy.lean), with generic proofs in [ClockRecordProduct.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/ClockRecordProduct.lean). Both changed owners, the necessary energy-bound consumer, and the paper compile. No remaining clause of this finite lemma. Long quiet windows and the independent square-root estimate remain open; boundary7/8 is unchanged. |
| 87 | Prime-return overlap delay (`lem:prime-return-overlap-delay`) | **Fully matched** | [LeastPrimeOwner.lean](../PrimeFactorOscillations/Mathlib/NumberTheory/ArithmeticFunction/LeastPrimeOwner.lean) compiles `prime_owner_square_le`, both exact signed overlap-packet vanishing theorems before the square, and `prime_square_minFac`. All smaller-prime overlaps and full product moduli are retained. The changed owner and paper compile without warnings. No remaining clause of this finite lemma; no early restoring bound, quiet-window sequence, or improved analytic exponent is claimed. |
| 88 | The logarithmic prime-return field (`lem:logarithmic-prime-return-field`) | **Fully matched** | Nine maintained declarations in [PrimeReturnWave.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimeReturnWave.lean) prove the complete birth-plus-return identity, prime and nonprime cases, nonnegative power compensation, the exact W increment, its factorial-compensated primitive and the signed squared-increment readout 2*W. The changed owner and wave assembly compile without warnings. All proper prime returns and higher-power compensation are retained; no independent quiet-window bound or exponent gain is claimed. |
| 89 | Retained-wave transfer and the uniform square-horizon obstruction (`lem:retained-wave-square-horizon`) | **Fully matched** | Six maintained declarations in [PrimeWaveFrozenBarrier.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimeWaveFrozenBarrier.lean) prove the exact full/retained signed-square transfer, its frozen-mass equivalence, the finite rejection-barrier induction, and a signed-square failure forced by a crest above sqrt(p)+log(p). The changed leaf, wave assembly and paper compile. The classical oscillation corollary is separately identified as an ordinary consequence; selected cofinal quiet windows remain open. No exponent gain. |
| 90 | The deterministic source fixed by the past prime waves (`lem:deterministic-past-prime-source`) | **Fully matched** | Eight maintained declarations and four definitions in [PrimePastWave.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/PrimePastWave.lean) identify primality through Y^2, retain unequal proper-return supports for past births and full supports for future openings, keep every two-time mixed return term and prove cutoff stability through the smaller cutoff's square, and express the actual future theta and W increments using the fixed past mask. No independence or periodic averaging is assumed. The focused leaf, facade, and saved paper compile successfully; evidence is recorded in the canonical claim receipt. No analytic exponent gain. |
| 91 | The short-gap deletion class (`thm:short-gap-prime-class`) | **Fully matched** | Twelve maintained theorems and six definitions in [ShortGapPrimeClass.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/ShortGapPrimeClass.lean) prove the original-error increment, exact nonnegative headroom ledger, natural and real theta caps, and actual greedy deletion-count comparison. The saved focused compile is reused; the changed import module and paper compile. No sparse deletion estimate is claimed. |
| 92 | Buffered prime classes preserve the cofinal zero criterion (`thm:buffered-prime-class-zero-criterion`) | **Fully matched** | Eight maintained theorems in [BufferedPrimeClass.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/BufferedPrimeClass.lean) prove the finite mass/count comparison and transfer cofinal sparse counts with a subpower buffer to the existing unconditional zero criterion. The square-root cap still implies RH when the complementary count condition holds for every positive epsilon. The leaf, changed import module and paper compile. The sparse bound remains open; no unconditional exponent gain. |
| 93 | Exact termination of the buffered greedy prime class (`thm:buffered-greedy-termination`) | **Fully matched** | Twenty maintained theorems and five definitions in [GreedyClockTermination.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/GreedyClockTermination.lean) and [BufferedGreedyPrimeClass.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/BufferedGreedyPrimeClass.lean) prove the full complement-mass clock, the literal deleted-set finiteness equivalence, a count bound from the complete buffered excess with only a log(2) overshoot allowance, and feasibility for nonnegative monotone buffers. Both leaves, changed import module and paper compile. Boundedness of a root-scale buffered excess remains open; no unconditional exponent gain or priority claim. |
| 94 | A fixed buffered finiteness criterion for RH (`thm:root-log-cube-finite-RH`) | **Fully matched** | Twelve maintained theorems and one definition in [BufferedPrimeFiniteRH.lean](../PrimeFactorOscillations/Proof/PrimeClassDeletion/BufferedPrimeFiniteRH.lean) prove that RH is equivalent to finiteness of the actual deleted set for the fixed buffer sqrt(x) log(x)^3, together with the full retained-theta cap. The leaf, public import module and saved paper compile. The exact real selection rule is explicitly defined; executable membership and tie exclusion are not proved. Finiteness is not proved unconditionally, and the certified zero-free boundary is unchanged. |
| 95 | Negative-one Carmichael seeds and separated periods (`thm:carmichael-negative-one-seed`) | **Fully matched** | Five theorems and one certificate definition in [CarmichaelSeed.lean](../PrimeFactorOscillations/Helpers/CarmichaelSeed.lean) prove all Korselt arithmetic clauses from the complete seed hypotheses, the even-factor modular product, gcd(q-1,p-1)=2, and the exceptional prime-two separation. Leaf and public probability-profile import compile. This is a finite seed theorem. Claims96-98 now supply the native joint law, exact indices and separated-seed attainment. External seed existence and the RH equivalence remain unformalized. |
| 96 | Full prime-order return law and vacancy floor (`thm:prime-order-return-law`) | **Fully matched** | [FiniteHomProbability.lean](../PrimeFactorOscillations/Helpers/FiniteHomProbability.lean) and [PrimeOrderReturnLaw.lean](../PrimeFactorOscillations/Helpers/PrimeOrderReturnLaw.lean) prove exact uniform fibers, simultaneous CRT surjectivity, every binary pattern under full group sampling, the canonical image-size bound and the vacancy floor. Applies to the entire unit group of every Carmichael modulus, including prime-two and empty packets. Both leaves and public groupings compile. Claims97-98 supply exact prime-factor image indices and finite seed attainment. External seed existence and the full RH criterion remain open formalization work. |
| 97 | Exact squarefree return indices and period multiplicity (`thm:squarefree-return-multiplicity`) | **Fully matched** | Eleven theorems and four definitions in [PrimeOrderReturnIndex.lean](../PrimeFactorOscillations/Helpers/PrimeOrderReturnIndex.lean) identify the actual image size with the full cyclic gcd product, prove the canonical lcm exponent, classify every local shortened-period ratio, and derive d_l=l^r_l. Includes prime-two coordinates, arbitrary natural power exponents and c=1. The leaf, Carmichael grouping, public probability-profile import and saved paper compile. Claim98 now proves finite Carmichael-seed attainment. External seed existence and the final RH transfer remain separate open targets. |
| 98 | Separated seeds attain the native return floor (`thm:carmichael-separated-return-attainment`) | **Fully matched** | Four theorems in [CarmichaelReturnAttainment.lean](../PrimeFactorOscillations/Helpers/CarmichaelReturnAttainment.lean) retain the shared even factor, prove d_l=l at the canonical exponent, establish every binary return pattern, and combine the full negative-one seed with its Korselt certificate. Prime-two and empty packets are included. The leaf, Carmichael grouping, public probability-profile import and saved paper compile. This is finite attainment under the complete arithmetic seed hypotheses; existence for every packet and the Nicolas RH transfer are not yet formalized. |
| 99 | Quantitative rigidity of native vacancy minimizers (`thm:prime-return-vacancy-rigidity`) | **Fully matched** | Fourteen theorems and two definitions in [PrimeOrderReturnRigidity.lean](../PrimeFactorOscillations/Helpers/PrimeOrderReturnRigidity.lean) prove the exact relative-product identity, reciprocal-prime redundancy budget, positive floor, equality classification and 1/Y stability for every positive squarefree modulus and canonical prime packet. Prime-two and empty packets are included; the unique factor may depend on the label. The leaf, Carmichael grouping, public probability-profile import and saved paper compile. This gives finite arithmetic rigidity, not a new zero-free exponent. |
| 100 | Profile-preserving Carmichael extensions (`thm:carmichael-profile-extension`) | **Fully matched** | Seventeen theorems and one definition in [CarmichaelProfileExtension.lean](../PrimeFactorOscillations/Helpers/CarmichaelProfileExtension.lean) prove the coprime canonical-exponent multiplier, exact old-label image comparison, every binary-pattern probability and the full Korselt extension under the complete seed hypotheses. If four divides the old exponent, every original packet law is preserved. If two exactly divides it, the even image grows by 2^omega(B) and all odd images are preserved. The leaf, Carmichael grouping, public probability-profile import and saved paper compile. External seed existence and infinitude are not part of this finite claim. |
| 101 | Pointwise Carmichael profile lifts and exact fibers (`thm:carmichael-profile-lift-fibers`) | **Fully matched** | Sixteen theorems and five definitions in [CarmichaelProfileLifts.lean](../PrimeFactorOscillations/Helpers/CarmichaelProfileLifts.lean) identify the actual reduction maps, complete fibers of size phi(B), and an injective homomorphic canonical lift preserving every original prime-label success/failure bit, including two. For safe packets, every fiber either wholly matches or wholly fails, with the exact phi(B)-or-zero count. The exceptional even cofactor event is retained. The leaf, public grouping, probability-profile import and saved paper compile. No external infinitude or new RH estimate is asserted. |
| 102 | Exact conditional even thinning in Carmichael fibers (`thm:carmichael-conditional-even-thinning`) | **Fully matched** | Ten theorems and two definitions in [CarmichaelEvenThinning.lean](../PrimeFactorOscillations/Helpers/CarmichaelEvenThinning.lean) prove the native conditional probability over every complete reduction fiber. When two exactly divides the old exponent, a successful old even return survives in exactly a 2^(-omega(B)) fraction of lifts, while an old nonreturn never becomes a return. All prescribed odd success/failure bits remain coupled, including empty packets. The leaf, grouping, public probability-profile import and saved paper compile without leaf warnings. External infinitude and the RH transfer remain separate. |
| 103 | Exact criterion for pointwise profile preservation (`thm:carmichael-pointwise-profile-criterion`) | **Fully matched** | Eight theorems in [CarmichaelProfileCriterion.lean](../PrimeFactorOscillations/Helpers/CarmichaelProfileCriterion.lean) prove, for arbitrary coprime nonzero moduli, that every lift preserves an old prime-label return bit if and only if lambda(B) divides E/l. Includes arbitrary finite old-label packets, the exact canonical-exponent lcm identity and a nonpreservation witness over the old identity whenever the criterion fails. No squarefreeness or Carmichael seed assumption is needed. The leaf, grouping, public probability-profile import and saved paper compile without leaf warnings. |
| 104 | Full conditional profile kernel for coprime extensions (`thm:carmichael-full-profile-kernel`) | **Fully matched** | Nine theorems and five definitions in [PrimeOrderReturnKernel.lean](../PrimeFactorOscillations/Helpers/PrimeOrderReturnKernel.lean) and [CarmichaelProfileKernel.lean](../PrimeFactorOscillations/Helpers/CarmichaelProfileKernel.lean) prove the exact conditional joint law over every complete reduction fiber for arbitrary coprime nonzero moduli. The packet may contain every prime label of the new exponent, including new and even labels. Exponent-growth gates, all successes and failures, impossible patterns and empty packets are retained. Both leaves, the grouping, public probability-profile import and saved paper compile without leaf warnings. |
| 105 | Maximal-order lifts: exact density and existence (`thm:carmichael-maximal-order-lifts`) | **Fully matched** | Six theorems and two definitions in [CarmichaelMaximalOrderLifts.lean](../PrimeFactorOscillations/Helpers/CarmichaelMaximalOrderLifts.lean) identify the complete nonreturn event with full multiplicative order, give its exact conditional density over every actual reduction fiber, and prove existence of a maximal-order lift exactly when lcm(order(a),lambda(B)) equals lambda(m*B). Includes the canonical complete prime packet and the cases m=1, B=1 and exponent=1. The leaf, grouping, public probability-profile import and saved paper compile without leaf warnings. |
| 106 | Conditional rigidity of maximal-order lift profiles (`thm:carmichael-conditional-profile-rigidity`) | **Fully matched** | Twenty-two theorems and six definitions in [PrimeOrderGatedRigidity.lean](../PrimeFactorOscillations/Helpers/PrimeOrderGatedRigidity.lean) and [CarmichaelConditionalRigidity.lean](../PrimeFactorOscillations/Helpers/CarmichaelConditionalRigidity.lean) prove the exact normalized defect product and a joint penalty budget on every feasible fixed-base fiber with squarefree auxiliary modulus. Closed gates cost 1/(l-1); repeated open auxiliary ranks cost at least 1/l. Includes the zero-or-prime-product-floor dichotomy, equality classification, and the conclusion that excess below 1/Y forces every label l<=Y open with rank one. Both leaves, grouping, public probability-profile import and saved paper compile; three nonfatal lint suggestions remain. |
| 107 | Intrinsic additive carrier readout (`thm:carmichael-intrinsic-carrier-readout`) | **Fully matched** | The intrinsic signed observable uses only the modulus, tested power, actual unit count and actual return count. Its additive Fourier zeros are precisely the multiples of the unique physical prime whose local unit period does not divide that power. Includes the first positive zero, the full rational CRT-tensor zero classification and the near-minimal conditional-profile consumer. Thirty-six theorems and seventeen definitions in [PrimeCarrierFourier.lean](../PrimeFactorOscillations/Helpers/PrimeCarrierFourier.lean), [ModularReturnFourier.lean](../PrimeFactorOscillations/Helpers/ModularReturnFourier.lean) and [CarmichaelCarrierReadout.lean](../PrimeFactorOscillations/Helpers/CarmichaelCarrierReadout.lean). All three leaves, grouping, public probability-profile import and saved paper compile. Classical prime-field nonvanishing is reused; no analytic zero-free exponent gain is asserted. |
| 108 | All-carrier intrinsic readout (`thm:carmichael-all-carrier-readout`) | **Fully matched** | For every positive squarefree modulus and every natural power, the zero frequencies of the intrinsic globally centered return transform are exactly the multiples of the product of all physical primes whose local unit period does not divide that power. Includes both directions, the first positive zero, empty support and the actual CRT coprime-dilation argument retaining both full centering products. Maintained in [RationalFourierOrbit.lean](../PrimeFactorOscillations/Helpers/RationalFourierOrbit.lean), [PrimeReturnFourier.lean](../PrimeFactorOscillations/Helpers/PrimeReturnFourier.lean) and [CarmichaelAllCarrierReadout.lean](../PrimeFactorOscillations/Helpers/CarmichaelAllCarrierReadout.lean). All three leaves, grouping, public import and saved paper compile. The rank-one and near-minimal-density restrictions are removed; the RH boundary remains unchanged. |
| 109 | Prime-square intrinsic conductor shell (`thm:prime-square-intrinsic-shell`) | **Fully matched** | Exact full signed formula and zero/nonzero classification for the original intrinsic observable at modulus p squared and power p, for every prime and every natural frequency. The nonzero shell is p divides h but p squared does not, with the explicit exception p=2 where the whole centered transform is zero. Actual power-kernel enumeration, all Ramanujan compensation terms, and the general unit-to-residue bridge are maintained in [PrimePowerIntrinsicBridge.lean](../PrimeFactorOscillations/Helpers/PrimePowerIntrinsicBridge.lean), [PrimeSquareConductorShell.lean](../PrimeFactorOscillations/Helpers/PrimeSquareConductorShell.lean), and [PrimeSquareIntrinsicShell.lean](../PrimeFactorOscillations/Helpers/PrimeSquareIntrinsicShell.lean). Publication priority is unestablished; the full odd-modulus extension and RH transfer remain open. |

| 110 | Exact subgroup conductor reduction and zero shells (`thm:subgroup-conductor-shell`) | **Fully matched** | Every odd prime, all natural conductor parameters, every actual multiplicative subgroup, and every frequency prime to the remaining conductor. Exact kernel mass p^a, image mass r/gcd(r,p^a), full complex trace pushforward, and zero iff the prime divides that image mass. Includes the prime-conductor boundary, a=0, b=0, and the exact value at all frequencies divisible by the modulus. The complete assembled declaration is `conductor_trace_and_zero_shell`. Maintained in [CyclicConductorReduction.lean](../PrimeFactorOscillations/Helpers/CyclicConductorReduction.lean), [PrimePowerConductorReduction.lean](../PrimeFactorOscillations/Helpers/PrimePowerConductorReduction.lean), and [PrimePowerConductorShell.lean](../PrimeFactorOscillations/Helpers/PrimePowerConductorShell.lean). The complete globally centered odd-modulus inverse theorem remains open; no RH equivalence or exponent improvement is claimed. |

| 111 | Full compensated conductor reduction (`thm:compensated-conductor-reduction`) | **Fully matched** | For every positive N=m*B and all natural powers and frequencies, the explicit actual root-lifting hypothesis gives the complete centered identity C_N(m*j)=q*r*C_B(j), with both positive kernel masses and both signed traces retained. Includes native and original intrinsic zero equivalence. For every odd prime p, all s,k,h, the original intrinsic transform at p^(s+1), frequency p^s*h, equals p^s*gcd(k,p^s) times the transform at the actual prime modulus p. The same original exponent k is preserved. Includes k=0 and zero frequency. Maintained in [PrimePowerTameImage.lean](../PrimeFactorOscillations/Helpers/PrimePowerTameImage.lean) and [CompensatedConductorReduction.lean](../PrimeFactorOscillations/Helpers/CompensatedConductorReduction.lean), including the named dependent normalization. Full odd-modulus two-clock classification and Carmichael-sequence RH attainment/transfer remain open. |
| 112 | Quadratic cancellation with a retained principal coefficient (`thm:odd-return-character-support`) | **Fully matched** | 9 matched declarations. Exact signed cancellation for every function of an odd return packet; the actual vacancy indicator, its positive canonical principal coefficient and every modular-unit specialization are included. Maintained in [OddReturnCharacterSupport.lean](../PrimeFactorOscillations/Helpers/OddReturnCharacterSupport.lean). No RH or zero-free exponent improvement. |
| 113 | Root-trace support at every odd prime-power frequency (`thm:exact-primary-root-clock`) | **Fully matched** | 3 matched declarations. For every odd prime p and all natural s,k,h, the root trace is zero exactly when gcd(k,p^s) does not divide h. Includes k=0, h=0 and s=0. Maintained in [PrimePowerRootClock.lean](../PrimeFactorOscillations/Helpers/PrimePowerRootClock.lean). Full odd-composite assembly remains open. |
| 114 | Uniform stability from a single vacancy probability (`thm:carmichael-profile-stability`) | **Fully matched** | 10 matched declarations. For every finite abelian group and canonical prime packet, every event is dominated by the minimal law times V/V0; full total variation is at most 1-V0/V and full Hellinger energy is at most twice that quantity. Both normalized masses are retained and cancel exactly in the signed repair ledger. Includes 2 and empty support. Maintained in [CarmichaelProfileStability.lean](../PrimeFactorOscillations/Assembly/CarmichaelProfileStability.lean). No new RH exponent or growing-modulus prime-base estimate. |
| 115 | Conditional full-profile stability for coprime extensions (`thm:carmichael-conditional-stability`) | **Fully matched** | 15 matched declarations. For every coprime positive m,B, feasibility alone forces each open auxiliary image index to be at least its prime label. This removes the squarefree restriction from the vacancy floor. The entire conditional fiber law obeys event domination by V/V0, total variation at most 1-V0/V and Hellinger energy at most twice that amount. Exact feasibility and zero vacancy are separated before normalization; powers of 2 and empty packets are included. Maintained in [CarmichaelConditionalStability.lean](../PrimeFactorOscillations/Assembly/CarmichaelConditionalStability.lean). No new zero-free exponent. |
| 116 | Exact overlap of conditional return profiles (`thm:carmichael-fiber-geometry`) | **Fully matched** | 21 matched declarations. For any two old units of any coprime positive extension, the two directed gate-mismatch products A,B give exact full total variation 1-min(A,B) and Hellinger energy 2(1-sqrt(A*B)). A deterministic auxiliary return at a mismatched gate gives exact singularity, TV=1 and energy=2. No vacancy is divided out and no squarefree or feasibility assumption is used. Maintained in [CarmichaelFiberGeometry.lean](../PrimeFactorOscillations/Assembly/CarmichaelFiberGeometry.lean). No infinite-product equivalence or new zero-free exponent is claimed. |
| 117 | Uniform information bound for redundant prime labels (`thm:carmichael-redundant-tail`) | **Fully matched** | 18 newly checked declarations plus the existing prime-tail asymptotic. The actual reciprocal mismatch cost C controls full TV and gives -C^2/2 <= energy-C <= C^2. If gates agree through Y and all remaining mismatch indices are at least prime squared, TV<=T(Y), energy<=Phi(Y), with both majorants asymptotic to 1/(Y log Y), uniformly in both moduli and the whole packet. For squarefree auxiliary moduli, two actual carriers per mismatch suffice. Maintained in [CarmichaelRedundantTail.lean](../PrimeFactorOscillations/Assembly/CarmichaelRedundantTail.lean). No growing-modulus prime-base sampling transfer or new zero-free exponent. |
| 118 | Uniform projection of the actual return law (`thm:carmichael-tail-projection`) | **Fully matched** | 24 checked declarations in [CarmichaelProfileProjection.lean](../PrimeFactorOscillations/Assembly/CarmichaelProfileProjection.lean) and [CarmichaelTailProjection.lean](../PrimeFactorOscillations/Assembly/CarmichaelTailProjection.lean). Actual zero-padded marginals of arbitrary fibers have distance distortion <=T(Y),Phi(Y), without low-gate agreement. Both directed products and the negative Hellinger cross term remain exact. The principal multiplier R is strictly positive at every cutoff, lies in [1-T(Y),1], and has floor 1-2/Y>0 for Y>=3; zero and positive vacancy branches are preserved. Squarefree retention is exactly label<=Y or auxiliary rank<=1. Prime 2 and nonsquarefree moduli included. Existing tail asymptotics are reused. No prime-base sampling transfer or new zero-free exponent. |
| 119 | Uniformly positive, quadratic-free return correlation (`thm:carmichael-return-correlation`) | **Fully matched** | 45 checked declarations in [CarmichaelCorrelation.lean](../PrimeFactorOscillations/Assembly/CarmichaelCorrelation.lean), [CarmichaelCorrelationLocal.lean](../PrimeFactorOscillations/Assembly/CarmichaelCorrelationLocal.lean), [CarmichaelCorrelationSpectrum.lean](../PrimeFactorOscillations/Assembly/CarmichaelCorrelationSpectrum.lean) and [CarmichaelCorrelationFloor.lean](../PrimeFactorOscillations/Assembly/CarmichaelCorrelationFloor.lean). Exact same-base local products retain every overlap. Uniform K>=1/2 for every unit and odd packet; mean one, upper bound and identity value 1/delta. Nonnegative complete Dirichlet spectrum has principal coefficient one, total mass 1/delta and zero nonprincipal real/quadratic modes. Finite sample and common positive-excursion lower bounds follow. Label 2 exception explicit; empty packet included. Growing-modulus ascent equivalence and new analytic exponent are not claimed. |
| 120 | Moving-modulus Carmichael ascent criteria (`thm:carmichael-moving-ascent`) | **Fully matched** | 17 checked declarations in [AscentModulusBudget.lean](../PrimeFactorOscillations/Helpers/AscentModulusBudget.lean), [LocalizedAscentPointwise.lean](../PrimeFactorOscillations/Helpers/LocalizedAscentPointwise.lean), [WeightedLocalizedAscentCriterion.lean](../PrimeFactorOscillations/Helpers/WeightedLocalizedAscentCriterion.lean) and [CarmichaelAscentCriterion.lean](../PrimeFactorOscillations/Assembly/CarmichaelAscentCriterion.lean). Under exactly the old LocalAscentSampling premise, arbitrary varying odd packets and positive moduli c_X<=X^floor(m_X/2) preserve both RH criteria. Actual nonunits are zero weighted; at most half the distinct witness primes are excluded, total weight is >=m_X/4, and the common positive signed excursion survives with the full grid rounding loss. Both native eventual-sign and X^(7/10) upper-bound equivalences and false-RH unboundedness are compiled. No formalization of the external short-interval source and no new independent upper estimate or zero-free exponent are claimed. |
| 121 | Unrestricted smooth-conductor Carmichael ascent criteria (`thm:carmichael-smooth-ascent`) | **Fully matched** | 16 checked declarations in [UniformWeightedAscentCriterion.lean](../PrimeFactorOscillations/Helpers/UniformWeightedAscentCriterion.lean), [CarmichaelSmoothAscent.lean](../PrimeFactorOscillations/Assembly/CarmichaelSmoothAscent.lean) and [CarmichaelPastPrimeModuli.lean](../PrimeFactorOscillations/Assembly/CarmichaelPastPrimeModuli.lean). Under exactly LocalAscentSampling, positive c_X with largestPrimeFactor(c_X)<=X eventually and arbitrary odd return packets retain every witness, actual weight >=1/2, and D_K>=m_X*B_X/2. Both RH criteria and false-RH unboundedness are compiled. Arbitrary factorial/primorial power schedules, including exponent zero, are covered with no conductor-size bound. This replaces a size hypothesis by a support hypothesis; neither domain contains the other in general. No independent RH upper bound or zero-free improvement. |
| 122 | Single-pair bounded-error ascent criteria (`thm:carmichael-single-ascent`) | **Fully matched** | 13 checked declarations in [SinglePairAscentWindow.lean](../PrimeFactorOscillations/Helpers/SinglePairAscentWindow.lean), [SinglePairAscentCriterion.lean](../PrimeFactorOscillations/Helpers/SinglePairAscentCriterion.lean) and [CarmichaelSingleAscent.lean](../PrimeFactorOscillations/Assembly/CarmichaelSingleAscent.lean). One genuine bounded-gap pair with prefix in [X,X+X^(3/4)] per cutoff suffices; no quantitative pair count or cross-cutoff injectivity. At the same growing rank and square-root grid, RH iff eventual weighted excess<=0 iff an eventual real constant upper bound, for every weight schedule eventually >=1/2. False RH gives arbitrarily late excess above every real constant. The original Carmichael weight is covered at arbitrary smooth conductor with arbitrary odd return packets. Full rounding and signed product retained. The arithmetic upper bound itself and improved zero-free boundary remain unproved. |
| 123 | Prime-order spectral filters and native RH probes (`thm:carmichael-prime-packet`) | **Fully matched** | 39 checked declarations in [ReturnPacketPowerSupport.lean](../PrimeFactorOscillations/Helpers/ReturnPacketPowerSupport.lean), [CarmichaelPacketSpectrum.lean](../PrimeFactorOscillations/Assembly/CarmichaelPacketSpectrum.lean), [CarmichaelPrimePacket.lean](../PrimeFactorOscillations/Assembly/CarmichaelPrimePacket.lean), [CarmichaelPrimePacketSpectrum.lean](../PrimeFactorOscillations/Assembly/CarmichaelPrimePacketSpectrum.lean) and [CarmichaelPrimePacketAscent.lean](../PrimeFactorOscillations/Assembly/CarmichaelPrimePacketAscent.lean). Exact full-packet character-power and actual-kernel filters; singleton principal coefficient1, flat surviving nonprincipal coefficient1/(D-1)^2 and total mass1/(D-1), with a survivor proved to exist. At D>=3 every unit weight lies in [3/4,3/2]; D=2 forces label2 and genuine zero masks. Cutoff-varying labels, including2, and arbitrary positive smooth conductors preserve both one-pair RH criteria under eventual divisibility and index>=3. Original signs, phases, rank and rounding retained. No independent arithmetic upper bound or improved zero-free boundary. |
| 124 | Exact tame conductor compression (`thm:carmichael-tame-conductor`) | **Fully matched** | 11 checked declarations in [PrimePowerCharacterConductor.lean](../PrimeFactorOscillations/Helpers/PrimePowerCharacterConductor.lean) and [CarmichaelPrimeConductor.lean](../PrimeFactorOscillations/Assembly/CarmichaelPrimeConductor.lean). For q=p^(a+1), unit characters killed by m coprime to p factor through p; every nonprincipal one has conductor exactlyp. Every surviving native tame mode has that conductor; the full original kernel descends along prime reduction, and a nonprincipal mode with the original flat coefficient survives. All phases and coefficients retained. Includes a0 and residue prime2; wild labels excluded. No new signed arithmetic upper bound or zero-free exponent. |
| 125 | Exact primitive QRH transfer for native tame modes (`thm:carmichael-tame-chebyshev`) | **Fully matched** | 3 checked declarations in [CarmichaelTameChebyshev.lean](../PrimeFactorOscillations/Assembly/CarmichaelTameChebyshev.lean). Conductorp at levelp^(a+1) gives equality with the primitive character at every natural input, including0 and nonunits, then exact equality of Chebyshev sums. For every nonprincipal surviving native tame mode, one universal A>0 gives A*x^(7/8)*(1+log(p)+log(x+2))^2, uniformly in unbounded a and all naturalx>=2. The Euler correction is exactly zero. A is not numerically specified; principal RH wave and certified exponent7/8 unchanged. |
| 126 | Odd-wild native prime-square conductor classification (`thm:carmichael-wild-conductor`) | **Fully matched** | 14 checked declarations in [PrimePowerWildCharacterConductor.lean](../PrimeFactorOscillations/Helpers/PrimePowerWildCharacterConductor.lean) and [CarmichaelWildConductor.lean](../PrimeFactorOscillations/Assembly/CarmichaelWildConductor.lean). At q=p^(a+2), p divides the actual exponent for every primep. For oddp, the native index is exactlyp, every nonprincipal survivor has conductor exactlyp^2, and a survivor has coefficient1/(p-1)^2. Exact original kernel1+(p*1_H-1)/(p-1)^2, full descent to p^2, and unit bounds[3/4,3/2], uniformly in a. No remaining admissibility/index premise. Wild analytic transfer and two-power classification are proved in claims127 and128; certified7/8 unchanged. |
| 127 | Conductor-exact prime-power character waves (`thm:carmichael-prime-power-chebyshev`) | **Fully matched** | Four checked declarations in [CarmichaelPrimePowerChebyshev.lean](../PrimeFactorOscillations/Assembly/CarmichaelPrimePowerChebyshev.lean). Exact values on all natural inputs, including zero and nonunits, and exact Chebyshev equality at level p^(a+b+1), conductor p^(b+1). Universal bound A*x^(7/8)*(1+(b+1)*log(p)+log(x+2))^2 independent of a. Every odd-wild native nonprincipal survivor has the b=1 specialization. Universal positive A is not numerically specified; no signed principal bound or exponent gain. |
| 128 | Complete native two-power spectrum (`thm:carmichael-two-power-spectrum`) | **Fully matched** | 35 checked declarations in [TwoPowerCharacterConductor.lean](../PrimeFactorOscillations/Helpers/TwoPowerCharacterConductor.lean) and [CarmichaelTwoPowerConductor.lean](../PrimeFactorOscillations/Assembly/CarmichaelTwoPowerConductor.lean). Every2^e,e>=4: actual index2, unique even quadratic nonprincipal mode, conductor8, coefficient1, exact original kernel1+chi(u^(-1)) and0/2 masks. q2 inadmissible; q4 index2/conductor4/zero masks; q8 index4/conductors4or8/positive weights4/3and8/9. Exact reduction kernel generated by25 and actual unit exponent. Universal QRH logarithm3*log2 independent of level inflation; positive A not numerically specified. No zero-mask ascent-witness retention, full CRT compression or independent principal estimate; certified7/8 unchanged. |
| 129 | Dual carriers and least actual reduction modulus (`thm:carmichael-dual-carrier`) | **Fully matched** | 17 checked declarations in [CarmichaelDualCarrier.lean](../PrimeFactorOscillations/Assembly/CarmichaelDualCarrier.lean). Every positive squarefree B and prime label ell dividing lambda(B): original kernel depends exactly on primes p with p-1 not dividing lambda(B)/ell. A selected coordinate set suffices iff it contains them. Their product R is positive, divides B, and is the attained least actual unit reduction modulus: descent to d is equivalent to R dividing d. The same R is the first positive zero frequency of the full signed centered additive spectrum. Original global period, normalization and masks retained. No canonical compressed-kernel identity, prime-power CRT conductor claim or independent signed principal estimate; certified7/8 unchanged. |
| 130 | Exact original-kernel spectral conductor (`thm:carmichael-spectral-conductor`) | **Fully matched** | 11 checked declarations in [CarmichaelSpectralConductor.lean](../PrimeFactorOscillations/Assembly/CarmichaelSpectralConductor.lean). For every positive q and native prime label, original kernel descent to a positive divisor d is equivalent to descent of every actual surviving character, to their conductors dividing d, and to their conductor lcm M dividing d. M is positive, divides q and is the attained least actual kernel modulus. For squarefree B it equals the intrinsic active-prime product and the full signed additive zero spacing. Attainment is of kernel descent, not an individual character of conductor M. No canonical compressed-kernel substitution or independent signed principal bound; certified7/8 unchanged. |
| 131 | Sharp active-divisor native character assembly (`thm:carmichael-conductor-assembly`) | **Fully matched** | 15 checked declarations in [CarmichaelConductorAssembly.lean](../PrimeFactorOscillations/Assembly/CarmichaelConductorAssembly.lean). Every positive q and native prime label: actual activity E_d not dividing lambda(q)/ell automatically supplies local admissibility and coprime period inflation. Local survivors lift; arbitrary finite products with pairwise coprime true conductors remain alive with exact product conductor F dividing the least spectral conductor. For F not1, coefficient is the original global1/(D-1)^2, never multiplied local coefficients. Empty support included. Every nonprincipal mode at8 has coefficient1/9 and a genuine conductor8 survivor exists. Full arbitrary-modulus upper carrier classification and independent signed principal bound remain open; certified7/8 unchanged. |
| 132 | Native CRT conductor product and maximal actual mode (`thm:carmichael-maximal-conductor`) | **Fully matched** | 17 checked declarations in [CarmichaelCRTKernel.lean](../PrimeFactorOscillations/Assembly/CarmichaelCRTKernel.lean), [CarmichaelLocalSharpness.lean](../PrimeFactorOscillations/Assembly/CarmichaelLocalSharpness.lean) and [CarmichaelMaximalConductor.lean](../PrimeFactorOscillations/Assembly/CarmichaelMaximalConductor.lean). Every positive q and native prime label: least spectral conductor equals the product of local least conductors over exactly the active original prime-power coordinates. A genuine nonprincipal global survivor attains that entire conductor with exact original coefficient1/(D-1)^2. Complete actual CRT upper reduction matches the mixed-character lower construction; every tame, odd-wild and2/4/8/large two-power case is included. Original period, subgroup, phases and masks retained. No canonical reduced-kernel substitution or independent signed principal bound; certified7/8 unchanged. |
| 133 | Complementary native zero masks retain ascent RH witnesses (`thm:carmichael-complementary-ascent`) | **Fully matched** | 20 checked declarations in [CarmichaelComplementaryAscent.lean](../PrimeFactorOscillations/Assembly/CarmichaelComplementaryAscent.lean). The original kernel at every2^(r+4) and its actual residue translate by5 form an exact0/2 cover. For every localized bounded-gap prime-pair locator and arbitrary varying r, their full signed excesses are eventually(0,2B)or(2B,0), sum to2B, and are jointly eventually bounded iff RH. Failure of RH makes one fixed channel unbounded at arbitrarily large cutoffs. Phase0 is exactly the original Carmichael single-pair observable. Neither individual weight has a positive floor; no assertion that5p is prime, no individual-channel equivalence, and no independent signed upper bound or exponent gain. Certified7/8 unchanged. |
| 134 | Fixed prime residue supports and joint ascent RH criterion (`thm:carmichael-residue-ascent`) | **Fully matched** | 12 checked declarations in [CarmichaelResidueAscent.lean](../PrimeFactorOscillations/Assembly/CarmichaelResidueAscent.lean). Every original native kernel at2^(r+4) reduces through the actual unit map to2 on plus/minus1mod8 and0 otherwise. For odd p, the complementary channels select exactly{1,7}and{3,5}mod8. Every arbitrary varying-conductor ascent observable equals its fixed-class observable eventually. Joint boundedness and joint nonpositivity are RH-equivalent for each supplied localized bounded-gap pair locator; failure of RH makes one fixed class-union excess unbounded. Canonical reconstruction at8 is disproved by identity values2versus4/3. No individual-class RH criterion, independent signed upper bound or exponent gain; certified7/8 unchanged. |
| 135 | Sharp native progression mask covers and balanced prime-cycle RH transport (`thm:carmichael-progression-masks`) | **Fully matched** | 18 checked declarations in [CarmichaelProgressionMasks.lean](../PrimeFactorOscillations/Assembly/CarmichaelProgressionMasks.lean). Every original large two-power level and both channels: odd-start APs of even step not divisible by8 have three-term weight2or4 and exact four-term weight4; the entire signed common signal is4B. Step4mod8 balances in two terms. Two terms may be blind; steps divisible by8 have blind prime starts at every length, proving the exact three-term cover criterion. The actual full four-prime-cycle canonical transport is RH AND shape-recurrence equivalent with all recurring witness cycles balanced at every level and phase. Same canonical probability law, moving rank and displacement3d retained. No recurrence supplied by RH or independent principal estimate; certified7/8 unchanged. |
| 136 | Native coarse uniformity and odd-wild progression balance (`thm:carmichael-wild-averages`) | **Fully matched** | 24 checked declarations in CarmichaelKernelCoset, PrimeSquareProgressionFiber and [CarmichaelWildAverages.lean](../PrimeFactorOscillations/Assembly/CarmichaelWildAverages.lean). At every original native p^(a+2), each coarse unit fiber has average1 and probability mass1/(p-1), includingp2. At every oddp, p actual positions n+jpt with p coprime n,t have exact kernel sum p at all native depths and every unit phase; full common signed signal is pB. Actual original-kernel p² descent and p^a multiplicity retained. No assumption that those positions are prime, no recurrence or independent principal upper bound supplied; certified7/8 unchanged. |
| 137 | Balanced odd-wild full prime-cycle RH transport (`thm:carmichael-wild-prime-cycles`) | **Fully matched** | 4 checked declarations in [CarmichaelWildPrimeCycles.lean](../PrimeFactorOscillations/Assembly/CarmichaelWildPrimeCycles.lean). For every oddp,t coprime p,alpha>0, the original RH AND full-shape recurrence equivalence for j*p*t has actual full p-prime witness cycles balanced at all original native depths and unit phases. Exact displacement(p-1)*p*t and same canonical law, moving rank and strict upper comparison retained. Selecting q>=p+1 supplies actual unit positions. No recurrence from RH or upper q(N) supply, no independent principal estimate; certified7/8 unchanged. |
| 138 | Full native packet zero-support rigidity and uniform nonzero gap (`thm:carmichael-support-rigidity`) | **Fully matched** | 15 checked declarations in [CarmichaelSupportRigidity.lean](../PrimeFactorOscillations/Assembly/CarmichaelSupportRigidity.lean). Every finite abelian group and active finite packet: K=0 exactly when2is present,the2-return index is2,and the unit does not return. Odd decorations preserve the singleton2 zero set at the same group/native period; every nonzero value>=3/8,while old all-odd floor1/2 remains. Actual zero-extended prime weights preserve this common zero set for all natural arguments,including nonunits. Finite supported indices R inside T obey(3/8)*cardR<=full weighted mass; prime-index sets give actual retained-prime counts. Full odd spectra and L-quotients retained; no reverse constant bound,independent principal estimate or exponent gain.7/8 unchanged. |
| 139 | Uniform phase completion and mean-one ascent RH criterion (`thm:carmichael-binary-probability`) | **Fully matched** | 24 checked declarations in [CarmichaelBinaryCompletion.lean](../PrimeFactorOscillations/Assembly/CarmichaelBinaryCompletion.lean) and [CarmichaelBinaryProbability.lean](../PrimeFactorOscillations/Assembly/CarmichaelBinaryProbability.lean). One phase per modulus covers all active mixed packets; pair sum>=3/8,mean-one density>=3/16,probability mass=density/unit-group size. Full signed consumer>=3mB/32 under unit-count/common-lower hypotheses. Under original LocalAscentSampling and NAT qbudget,RH iff eventual nonpositivity iff C X^(7/10) upper bound,with NotRH excursions. No sampler construction,new prime progression,independent arithmetic upper estimate or exponent gain;7/8 unchanged. |
| 140 | Exact native label erasure, quadratic filtering and ascent RH criteria (`thm:carmichael-label-average`) | **Fully matched** | 19 checked declarations in [CarmichaelLabelAverage.lean](../PrimeFactorOscillations/Assembly/CarmichaelLabelAverage.lean) and [CarmichaelLabelAscent.lean](../PrimeFactorOscillations/Assembly/CarmichaelLabelAscent.lean). Full return-image phase section erases any active label exactly at the original group/period. Mean1 retained; binary projected kernel>=1/2 and every nonprincipal quadratic signed kernel sum0. Complete finite signed sums and zero-extended actual prime weights transfer exactly. Actual projected ascent excess equals old odd-packet excess at every cutoff; both RH criteria and NotRH excursions under original LocalAscentSampling and NAT qbudget. Phase sections exist; sampler existence and independent principal bound remain open. No nonlinear quotient simplification or exponent gain;7/8 unchanged. |
| 141 | Integral native permutation kernel (`thm:carmichael-permutation-kernel`) | **Fully matched** | 13 checked theorems in [CarmichaelPermutationKernel.lean](../PrimeFactorOscillations/Assembly/CarmichaelPermutationKernel.lean),plus an axiom check of the actual group-action definition. Every active native packet on every finite abelian group has concrete state product Fin(D(D-2)) disjoint-union returnImage. PositiveM=prod(D-1)^2,full fixedpointcard=M*K,normalizedkernel=card/M,and fixedpointmean=M. Original group/period and all local factors retained. Emptypacket andindex2 handled. Analytic Dirichlet/Artin factorization and independent signed upper estimates remain open;7/8 unchanged. |
| 142 | Integral native Dirichlet spectrum (`thm:carmichael-integral-spectrum`) | **Fully matched** | 16 checked theorems in [CarmichaelIntegralSpectrum.lean](../PrimeFactorOscillations/Assembly/CarmichaelIntegralSpectrum.lean). Explicit nonnegative integer character multiplicities from every subset,original-kernel coefficient=mu/M,principalmu=M,odd nonprincipal quadraticmu=0,and nonzerocoefficient>=1/M. Original actual all-natural weight and Mangoldt coefficients have exact integer Dirichlet expansions,including nonunits and every prime power; arbitrary finite signed complex sums retained. Empty/binary packets andq1 included. Analytic finite-L-product and independent arithmetic upper estimate remain open;7/8 unchanged. |
| 143 | Native L-products and shared-zero orders (`thm:carmichael-dirichlet-product`) | **Fully matched** | 12 checked theorems in [CarmichaelDirichletProduct.lean](../PrimeFactorOscillations/Assembly/CarmichaelDirichletProduct.lean). Full finite product L_chi^mu_chi analytic off1,nonzeroat2,finite local orders,sum of every weighted character order,and principalorder lowerboundM*ordL1. Exact supportedzero union. Negative logarithmic derivative plus arbitrary analytic error has order-1 iff a supportedzero exists,including shared/multiple zeros. Odd packet product omits nonprincipal quadratic factors exactly. No RH,GRH orstrip hypothesis. Actual ascent-character consumer,Mellin transfer and independent arithmetic upper estimate remain open;7/8 unchanged. |
| 144 | Complete signed ascent-character criterion (`thm:carmichael-ascent-spectrum`) | **Fully matched** | 8 checked theorems in [CarmichaelAscentSpectrum.lean](../PrimeFactorOscillations/Assembly/CarmichaelAscentSpectrum.lean). Original actual-prime and complete actual-minus-reference signed counts resolved exactly asP=M*E. Packetreal,normalizedpacket=originalexcess,principalrow coefficientM retained with every nonprincipal phase. Odd packets use exactly the quadratic-free character set of the full L-product. Both existing RH criteria and quantifiedNotRH excursions preserve the exact sampler,activity,oddness and eventual NAT qbudget. No sampler existence,new arithmetic cancellation bound or zero-free gain. Criterion complete; next work is joint character estimates;7/8 unchanged. |
| 145 | Signed ramified comparison (`thm:ramified-gram-comparison`) | **Fully matched** | 6 checked theorems in [RamifiedGramComparison.lean](../PrimeFactorOscillations/Assembly/DetectorPackets/RamifiedGramComparison.lean). Common-unit dilation, exact signed nonprincipal factor and q^(c-1) nonresonant bound, including degenerate numerator arguments; finite indexed products. Local nonprincipality and prime2 qualification explicit,goodLambda excluded. C=1 and full inverse/compensation estimates remain unchanged; no zero-free gain;7/8 unchanged. |
| 146 | Native signed profile estimate (`thm:carmichael-ascent-estimate`) | **Fully matched** | 2 checked theorems in [CarmichaelAscentEstimate.lean](../PrimeFactorOscillations/Assembly/CarmichaelAscentEstimate.lean). Actual normalized signed packet differs from mesh times the full signed probability-profile sum by at most its native weight mass,eventually under original sampling/activity/oddness. Exact full native character expansion of that profile main. Only finite-grid error bounded in absolute value; main signs,principal coefficient and previous quadratic cancellation retained. No RH or qbudget needed for this estimate; no new bound on the signed main;7/8 unchanged. |
| 147 | Complete signed native clock bound (`thm:carmichael-clock-estimate`) | **Fully matched** | 3 checked theorems in [CarmichaelClockEstimate.lean](../PrimeFactorOscillations/Assembly/CarmichaelClockEstimate.lean). Existing unconditional coefficient comparison applied to actual native profile/main packet. Positive and negative Nicolas terms carry r+K and r-K;eventualr>=2K preserves the negative contribution. Reciprocal allowance and actual native gridmass retained through J<=mesh*U+W. No RH or qbudget used in these bounds. Main signed arithmetic sum remains independently unestimated;7/8 unchanged. |

Reconciled cross-claim dependencies: claim 37 no longer lists the completed claim 36 law as missing. Claims 37, 50 and 57 no longer describe its proofs as held or unpromoted. Claims 50 and 57 still require their distinct progression and conditional-localization statements; the unshifted law does not establish those statements.

Prime-power supporting formalization (not a new labelled paper claim): [PrimePowerReturnSpectrum.lean](../PrimeFactorOscillations/Helpers/PrimePowerReturnSpectrum.lean), [PrimePowerReturnTrace.lean](../PrimeFactorOscillations/Helpers/PrimePowerReturnTrace.lean), and [PrimePowerReturnAllPrimes.lean](../PrimeFactorOscillations/Helpers/PrimePowerReturnAllPrimes.lean) prove the exact primitive-frequency classification for every proper prime power: the full centered return transform vanishes if and only if the conductor prime divides the power exponent. This includes prime 2, all odd small primes, and exponent zero. The proof keeps every last-layer orbit and the complete unit-mask subtraction. Claim 109 now resolves every frequency for modulus p squared and power p, including the original residue observable and prime2. The general odd-modulus two-clock classification remains unproved; claim 108 retains its squarefree scope and the RH boundary is unchanged.

Additional supporting formalization: [PrimePowerSubgroupTrace.lean](../PrimeFactorOscillations/Helpers/PrimePowerSubgroupTrace.lean) proves that at every primitive frequency of an odd proper prime-power conductor, the complete additive trace of any multiplicative subgroup vanishes exactly when the conductor prime divides its cardinality. This uses the actual subgroup, including all last-layer multiplication orbits. It is a classical supporting input for quotient images, not a completed arbitrary-conductor inverse theorem or a new RH equivalence.

All-frequency supporting input: [PrimePowerRootGrid.lean](../PrimeFactorOscillations/Helpers/PrimePowerRootGrid.lean) proves that the actual root trace at an odd prime power p^(s+1) is nonzero at every frequency divisible by gcd(k,p^s), including zero, for all natural s,k,h. The subgroup input has no frequency-coprimality hypothesis: a subgroup mass prime to p gives a nonzero trace at every frequency. The off-grid zero direction and the full globally centered odd-modulus classification remain unproved.

The dated sections below retain their historical theorem scopes and verification counts. Those historical counts are not current totals for this reconciliation.


## Maintained research results — 20 October 2026

The [reconciliation inventory](completed-research-inventory.json) identifies
301 maintained owners; the complete project build checks 1,139 owned modules
and the public axiom audit checks 4,843 selected declarations. Every audited
closure uses standard foundations only. The [verification record](VERIFICATION.md)
separates these totals from the historical audits below.

The research paper now includes the RH-conditional bilinear second moment and
weighted multiplicity defect, the prime-coordinate inverse theorem, sharp
cubic camouflage by infinitely many prime swaps, the residue-rational inverse
classification, and the exact compensated coprime and all-prime identities.
The inverse classifications and infinite construction have ordinary proofs;
the public Lean library contains their completed spectral, signed-logarithmic,
translation and finite-coordinate components, not a claimed full formalization.

The dynamics paper retains the early finite ranges (primes through 22 at
generation 4, and through 432 at generation 6), the general explicit divisor
constant, and the recovered short-mean source budget with its original
quantifiers. None supplies the open dense entry assumption.

The signed arithmetic estimate on the full compensated packet remains open.
The certified unconditional zero-free boundary is **7/8**; neither promotion,
detector precision nor the conditional scalar exponent calculations improves it.
Private proved nodes now have maintained owners, and failed attempts have an
explicit disposition rather than being counted as completed mathematics.

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

## Cubic pair windows and the signed native packet: maintained status, 28 October 2026

| Claim | Status and maintained owner |
|---|---|
| Weighted C1 scale estimate and uniform normalized-radius difference | Proved in [CubicPairRadius](../PrimeFactorOscillations/Helpers/CubicPairRadius.lean), with explicit finite Schwartz seminorm constants. |
| General pair reflection and conditional self-dual vanishing | Proved in [CubicPairReflection](../PrimeFactorOscillations/Helpers/CubicPairReflection.lean). Its original phase and symmetry premises are discharged for actual inert prime rows below. |
| Finite physical Mellin transfer, including the full quartic reference | Proved in [CarmichaelPhysicalPacket](../PrimeFactorOscillations/Assembly/CarmichaelPhysicalPacket.lean): each reference retains its shifted window multiplier and the factor $1/4$. Fixed finite support and positive sampled indices are explicit. |
| Physical affine reference and inverse-multiplicity symmetry | Proved in [CarmichaelWindowTransfer](../PrimeFactorOscillations/Assembly/CarmichaelWindowTransfer.lean), including $m_S(\chi^{-1})=m_S(\chi)$. |
| Explicit compensated Gaussian polynomial window | Proved in [CubicCompensatedWindow](../PrimeFactorOscillations/Helpers/CubicCompensatedWindow.lean): Mellin transform $\tfrac12P_d(s)\Gamma(s/2)$, convergence, moments at 1 and 2, affine scaling, and polynomial nonvanishing in $1/2<\Re s<1$. |
| Native principal Dirichlet character | Proved: `native_principal_separation`. The normalized coefficient is exactly one on the actual finite unit support. |
| Input conjugation and native pair-kernel symmetry | Proved in [CubicRationalRows](../PrimeFactorOscillations/Helpers/CubicRationalRows.lean). No reality assumption on the window is needed. |
| Inert-prime and twin-starter qualification | Proved in [CubicInertArithmetic](../PrimeFactorOscillations/Helpers/CubicInertArithmetic.lean): maximality, avoidance of lambda and actual row symmetry for primes $p\equiv2\bmod3$; twin starters other than 3 satisfy that congruence. |
| Actual normalized Gauss phase | Proved in [CubicInertPhase](../PrimeFactorOscillations/Helpers/CubicInertPhase.lean): the primary generator is $-p$ and the exact native `gaussTwo` has cube one. Its character, primitive trace and normalization are identified with the canonical Gauss theorem. |
| Actual inert-pair self-dual cancellation and $XH$ bound | Proved: `inert_selfdual_zero`, `inert_near_selfdual_uniform`, and `twin_near_selfdual_uniform`. No assumed phase, symmetry, maximality, admissibility or coprimality remains; distinct primes and the anti-Fourier window condition remain explicit. The pair scale is $pq$. |
| Exceptional small primes | Proved domains include inert prime 2. The exceptional twin starter 3 is excluded explicitly, and is absent from frames $X>3$. The two indices are twin starters, not both members of one twin pair. |
| Unit lattice row and all four compensation terms | Proved in [CubicUnitWindow](../PrimeFactorOscillations/Helpers/CubicUnitWindow.lean): $K_M(1,1)=-MW(0)+R_W(M)$, $|R_W(M)|\le C_W/M$ for $M\ge1$, and the full signed four-scale zero-mode identity. This is separate from the principal Dirichlet character and the arithmetic Abel-endpoint unit. |
| Anti-Fourier realization of the explicit Gaussian profile | Unfinished. Its polynomial reflection identity and zero moments do not alone establish this Fourier assertion or its Schwartz extension. |
| Infinite/growing-support physical transfer, prime-carrier insertion and full Abel limit | Unfinished. The finite physical transfer is not promoted to these stronger statements. |
| Full signed arithmetic saving | Unproved: $I_{D,G}\ll_\varepsilon D^{3/2+\varepsilon}$ uniformly in the stated packet domain. Both reciprocal L-factors, the derivative terms, physical mask and compensation cross terms remain in the target. |
| New zero-free boundary | None. Installed unconditional $7/8$ remains unchanged; target remains at most $3/4$. The $XH$ carrier estimate is a component estimate, not an assembled exponent gain. |

The [earlier kernel receipt](verification/cubic-pair-window.json),
[finite physical-transfer receipt](verification/carmichael-physical-window.json),
and [actual inert and unit-row receipt](verification/cubic-inert-unit-window.json)
record the corresponding focused theorem closures. Unchanged theorem files
were not re-audited. Paper labels include
`thm:carmichael-physical-window`, `thm:compensated-gaussian-window`,
`thm:rational-cubic-row-conjugation`, `prop:native-principal-window`,
`thm:actual-inert-cubic-window`, and `thm:cubic-unit-zero-mode`.

## Reciprocal Gaussian and norm-coordinate transfer (2026-10-28)

The alternative four-Gaussian window has 26 compiled declarations with focused
foundational checks. The saved paper compiles. The exact claim ledger is:

| Claim / owner | Status |
| --- | --- |
| Actual integrable plane Fourier anti-invariance and zero origin / `Helpers/CubicReciprocalGaussian.lean` | Proved and audited: 9 declarations. |
| Convergent four-scale radius Mellin transform / `Helpers/CubicReciprocalMellin.lean` | Proved and audited: 5 declarations. |
| Exact scale factorization and radius nonvanishing / `Helpers/CubicReciprocalNonzero.lean` | Proved and audited: 5 declarations, in namespace `CubicReciprocalMellin`. |
| Norm-coordinate Mellin transform and nonvanishing / `Helpers/CubicCarrierMellin.lean` | Proved and audited: 4 declarations. Multiplier is $M_V(s)=2M_W(2s)$ and is nonzero on $1/2<\Re s<1$. |
| Arbitrary signed finite Eisenstein carrier transfer, full quartic reference, both multipliers nonzero / `Assembly/CarmichaelCarrierWindow.lean` | Proved and audited: 3 declarations. The input is the positive integer norm of each nonzero carrier. |
| Actual Gaussian lattice and unit Poisson transfer | Proved below, without a negative-axis Schwartz-profile premise. The general paired-coset adapter remains unfinished. |
| Infinite prime selector, growing support and full Abel passage | Unfinished. Neither finite support nor an all-lattice identity supplies this transfer. |
| Restored arithmetic unit $C_G$ and full signed estimate | Unproved. Every quotient, derivative term, physical mask and compensation term remains. |
| Zero-free boundary | $7/8$ unchanged; target remains at most $3/4$. |

A split Eisenstein prime above $p$ has norm $p$ and contributes $p^{-s}$.
The rational carrier $p$ has norm $p^2$ and contributes $p^{-2s}$.
The [focused receipt](verification/reciprocal-gaussian-carrier-window.json)
records every declaration and its actual namespace.
Paper label: `thm:reciprocal-gaussian-carrier`.

## Actual Gaussian unit and multiplier holomorphy (2026-10-28)

These 21 additional claims are maintained, exported and individually focused-audited.
The previous 26 claims are unchanged and retain their earlier audit evidence.

Owner: `Helpers/CubicCarrierAnalytic.lean`, namespace `CubicCarrierAnalytic`.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `const_cpow_analyticAt` | Positive-base complex power is analytic at every complex point. | Proved; focused axiom audit passed. |
| `gamma_analyticAt_of_re_pos` | Native gamma function is analytic when Re(s)>0. | Proved; focused axiom audit passed. |
| `baseMultiplier_analyticAt` | Actual radius base multiplier is analytic when Re(s)>0. | Proved; focused axiom audit passed. |
| `scaleMultiplier_analyticAt` | Actual finite scale multiplier is entire. | Proved; focused axiom audit passed. |
| `carrierMultiplier_analyticAt` | Actual norm-coordinate carrier multiplier is analytic when Re(s)>0. | Proved; focused axiom audit passed. |

Owner: `Helpers/CubicGaussianUnit.lean`, namespace `CubicGaussianUnit`.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `exp_weight_bound` | Quadratic exponential envelope with constant 5. | Proved; focused axiom audit passed. |
| `gaussian_lattice_summable` | Absolute convergence of the actual scaled Gaussian lattice sum. | Proved; focused axiom audit passed. |
| `poisson_prefactor` | Exact positive-base binary Poisson prefactor. | Proved; focused axiom audit passed. |
| `gaussian_coordinates` | Actual integer-coordinate Gaussian identity. | Proved; focused axiom audit passed. |
| `gaussian_theta_poisson` | Actual Gaussian theta reciprocity. | Proved; focused axiom audit passed. |
| `window_lattice_hasSum` | Convergent four-scale lattice sum with its signed coefficients. | Proved; focused axiom audit passed. |
| `unitPacket_eq_theta` | Actual window lattice sum equals its four theta terms. | Proved; focused axiom audit passed. |
| `unitPacket_anti_reflection` | Actual window reciprocal-scale anti-reflection. | Proved; focused axiom audit passed. |
| `exp_weight3_bound` | Cubic exponential envelope with constant 16. | Proved; focused axiom audit passed. |
| `scaled_exp_weight3_bound` | Scaled cubic exponential envelope. | Proved; focused axiom audit passed. |
| `windowConstant_nonneg` | Explicit fixed window constant is nonnegative. | Proved; focused axiom audit passed. |
| `carrierProfile_weight3` | Actual positive-axis window has the explicit cubic envelope. | Proved; focused axiom audit passed. |
| `nonzero_tail_bound` | Actual nonzero lattice tail is O(M^(-2)), M>=1. | Proved; focused axiom audit passed. |
| `unit_zero_mode` | Actual unit row equals -M times its nonzero dual tail. | Proved; focused axiom audit passed. |
| `unitPacket_bound` | Actual unit row is O(M^(-1)), M>=1. | Proved; focused axiom audit passed. |
| `compensated_unit_identity` | All four compensation tails, including both mixed terms, with exact signs. | Proved; focused axiom audit passed. |

The unit estimate uses the actual four-Gaussian profile and has no negative-axis
Schwartz-profile premise. It does not bound the arithmetic Abel coefficient
$C_G$. The general paired-coset adapter, infinite prime selector and full Abel
passage are unfinished. The full signed target remains
$I_{D,G}(\lceil D^2\rceil)\ll D^{3/2+\varepsilon}$; the installed exponent is
$7/4$ and the zero-free boundary remains $7/8$, with target at most $3/4$.
Paper label: `thm:actual-gaussian-unit`.
Receipt: [actual Gaussian unit and holomorphy](verification/actual-gaussian-unit-window.json).


## Actual norm phase and centered Carmichael packet (2026-10-28)

Owner: `Assembly/CarmichaelNormPacket.lean`; namespace `CarmichaelNormPacket`.
All26 declarations below are compiled, exported and individually focused-audited.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `normPhase_principal` | Native norm phase has principal value1. | Proved; focused axiom audit passed. |
| `normPhase_norm` | Primitive additive character gives unit modulus for every native phase. | Proved; focused axiom audit passed. |
| `normPhase_inverse` | Native phase is conjugated by character inversion. | Proved; focused axiom audit passed. |
| `normPhase_cubic` | Nonprincipal cubic phase is chi(3)*tau^2/q. | Proved; focused axiom audit passed. |
| `cubic_norm_fourier` | Actual nonprincipal cubic norm transform with its squared Gauss phase. | Proved; focused axiom audit passed. |
| `filterPhase_principal` | Conjugate native filter retains principal value1. | Proved; focused axiom audit passed. |
| `filterPhase_norm` | Actual conjugate filter has unit modulus. | Proved; focused axiom audit passed. |
| `filterPhase_inverse` | Actual conjugate filter satisfies inverse conjugacy. | Proved; focused axiom audit passed. |
| `native_coefficient_balance` | Actual coefficient obeys k*G=conj(k). | Proved; focused axiom audit passed. |
| `native_coefficient_re_nonneg` | Actual filtered coefficients have nonnegative real parts. | Proved; focused axiom audit passed. |
| `native_kernel_ge_half` | Actual probability kernel has floor1/2 at index>=3. | Proved; focused axiom audit passed. |
| `coefficient_cubic_support` | Original nonzero coefficient forces chi^3=1 on the full field. | Proved; focused axiom audit passed. |
| `native_coefficient_inverse` | Actual filtered coefficients satisfy inverse conjugacy. | Proved; focused axiom audit passed. |
| `native_profile_real` | Complete norm profile is real, including the isotropic locus. | Proved; focused axiom audit passed. |
| `native_profile_transform_sum` | Full finite transform commutes with the character expansion. | Proved; focused axiom audit passed. |
| `native_nonprincipal_transform` | Every nonprincipal weighted summand has exact phase cancellation. | Proved; focused axiom audit passed. |
| `native_profile_transform` | Full transform is q*f+(q-1)*(q*delta0-1). | Proved; focused axiom audit passed. |
| `constant_trace_transform` | Constant profile transforms to q^2*delta0. | Proved; focused axiom audit passed. |
| `centered_profile_transform_split` | Centering retains the complete constant Fourier correction. | Proved; focused axiom audit passed. |
| `centered_profile_transform` | Centered native profile is an exact eigenfunction with eigenvalueq. | Proved; focused axiom audit passed. |
| `centered_coefficient_principal` | Signal-normalized centered coefficient has principal value1. | Proved; focused axiom audit passed. |
| `centered_coefficient_re_nonneg` | Signal-normalized centered coefficients retain nonnegative real parts. | Proved; focused axiom audit passed. |
| `centered_coefficient_formula` | Exact coefficient normalization and principal subtraction. | Proved; focused axiom audit passed. |
| `normalized_profile_split` | Full normalized character sum with its principal correction. | Proved; focused axiom audit passed. |
| `centered_profile_normalization` | q*fcentered equals normalized sum minus(q-1)*1_(N=0). | Proved; focused axiom audit passed. |
| `centered_principal_zero_not_analytic` | Actual normalized coefficients detect every principal zero away from1. | Proved; focused axiom audit passed. |

The actual filter is the conjugate of G=chi(3)*tau^2/q. The principal finite
correction and both isotropic lines are retained. Centering gives an exact
Fourier eigenfunction; restoring principal coefficient1 costs the factorq and
retains -(q-1)*1_(N=0). Shared-zero multiplicities cannot erase its signal.
The native Eisenstein quotient/trace specialization and physical lift are
proved below. Full inducing Euler factors and infinite Abel passage remain
unfinished. The arithmetic
I exponent7/4 and zero-free boundary7/8 are unchanged; required I exponent3/2
and target boundary at most3/4 remain live. No new arithmetic saving is claimed.
Paper label: `sec:carmichael-native-norm-packet`.
Receipt: [native norm packet](verification/carmichael-norm-packet.json).


## Native physical Carmichael norm packet (2026-10-28)

Owner: `Assembly/CarmichaelNormPhysical.lean`; namespace `CarmichaelNormPhysical`.
All27 public claims below are compiled, exported and individually focused-audited.
Two private convergence lemmas are included in those checked proof closures.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `coords_eval` | Native integer coordinates recover both coefficients of eval(a,b). | Proved; focused axiom audit passed. |
| `eval_sub` | Exact subtraction in the native Eisenstein basis. | Proved; focused axiom audit passed. |
| `eval_nat_mul` | Exact rational-integer dilation of both native coordinates. | Proved; focused axiom audit passed. |
| `omega_conj` | Actual complex conjugation of the native cubic root. | Proved; focused axiom audit passed. |
| `lambda_conj` | Actual conjugation reverses the native trace denominator. | Proved; focused axiom audit passed. |
| `trace_coordinate_fraction` | The native complex trace of (a+b*omega)/(q*lambda) is b/q. | Proved; focused axiom audit passed. |
| `trace_coordinate_character` | Actual exponential trace equals canonical stdAddChar(b modq). | Proved; focused axiom audit passed. |
| `trace_quotient_eval` | Actual quotient trace on every integer-coordinate representative. | Proved; focused axiom audit passed. |
| `quotient_eval_eq_iff` | Quotient equality is equivalent to congruence of both coordinates. | Proved; focused axiom audit passed. |
| `pairResidue_injective` | All field-coordinate pairs have distinct quotient classes. | Proved; focused axiom audit passed. |
| `pairResidue_surjective` | Every native quotient class is represented by a field-coordinate pair. | Proved; focused axiom audit passed. |
| `trace_pairResidue` | Actual product trace is exactly ad+bc-bd moduloq. | Proved; focused axiom audit passed. |
| `quotientProfile_pairResidue` | Transported profile agrees with the complete centered finite profile. | Proved; focused axiom audit passed. |
| `quotient_profile_transform` | Full native quotient Fourier transform has exact eigenvalueq. | Proved; focused axiom audit passed. |
| `gaussian_poisson` | Actual Gaussian Poisson transfer at dual rate1/(a*q^2). | Proved; focused axiom audit passed. |
| `compensated_gaussian_poisson` | All four arbitrary Gaussian scales and compensation cross terms. | Proved; focused axiom audit passed. |
| `physical_eq_gaussian_sum` | Actual infinite signed window equals its convergent four Gaussian sums. | Proved; focused axiom audit passed. |
| `physical_anti_reflection` | Actual four-Gaussian window satisfies K(M)=-M/q*K(q^2/M). | Proved; focused axiom audit passed. |
| `physical_selfdual_zero` | Exact cancellation at M=q for the native centered theta window. | Proved; focused axiom audit passed. |
| `compensated_physical_reflection` | Complete signed physical reflection at four arbitrary positive scales. | Proved; focused axiom audit passed. |
| `quotient_profile_unit_normalization` | Full spatial normalization includes the entire isotropic correction. | Proved; focused axiom audit passed. |
| `physical_unit_normalization` | Entire isotropic correction retained after actual infinite summation. | Proved; focused axiom audit passed. |
| `compensated_unit_normalization` | Unit normalization retains both mixed terms and all four scales. | Proved; focused axiom audit passed. |
| `split_roots_of_three_dvd` | Cubic exponent divisibility itself supplies both distinct split roots. | Proved; focused axiom audit passed. |
| `native_gaussian_poisson` | Actual Gaussian transfer without an extra root, phase or symmetry premise. | Proved; focused axiom audit passed. |
| `native_physical_anti_reflection` | Actual infinite window reflection under original cubic divisibility only. | Proved; focused axiom audit passed. |
| `native_compensated_physical_reflection` | Full compensated physical transfer with no extra matching hypotheses. | Proved; focused axiom audit passed. |

The original3-divides-exponent hypothesis now supplies the split roots.
The actual Eisenstein quotient, canonical trace, squared conductor, Gauss phase,
conjugation and complete infinite four-Gaussian transfer are proved. All four
AA-barcAB-cBA+|c|^2BB scales and the entire isotropic unit correction remain.
Marked-row inversion and the complete finite divisor packet are proved below.
Full inducing-mask identification, prime-weighted reciprocal-L transfer and
complete Abel passage remain unfinished. K(q)=0 is the native
geometric theta cancellation, not a vanishing arithmetic C_G or zero signal.
The installed I exponent7/4 and boundary7/8 are unchanged; the target remains
I exponent3/2 and zero-free boundary at most3/4.
Paper label: `sec:carmichael-native-physical`.
Receipt: [native physical window](verification/carmichael-norm-physical.json).

## Marked physical and full finite divisor packet (2026-10-28)

Owner: `Assembly/CarmichaelMarkedWindow.lean`; namespace `CarmichaelMarkedWindow`.
All26 claims below, plus two new generic APIs in `CarmichaelNormPhysical`,
are compiled and individually focused-audited. Earlier27 physical proofs are
unchanged and were not re-audited for these API additions.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `CarmichaelNormPhysical.windowPacket_hasSum` | Generic periodic window HasSum API. | Proved; focused axiom audit passed. |
| `CarmichaelNormPhysical.windowPacket_eq_gaussian_sum` | Generic periodic four-Gaussian expansion API. | Proved; focused axiom audit passed. |
| `markedProfile_one` | Identity mark recovers the original quotient profile. | Proved; focused axiom audit passed. |
| `markedProfile_mul` | Unit marks compose by actual quotient-ring multiplication. | Proved; focused axiom audit passed. |
| `marked_quotient_transform` | Actual native finite transform inverts every unit mark. | Proved; focused axiom audit passed. |
| `theta_one` | Identity mark recovers the native Gaussian theta sum. | Proved; focused axiom audit passed. |
| `gaussian_poisson` | Actual marked Gaussian transfer with inverse mark and conductor square. | Proved; focused axiom audit passed. |
| `physical_one` | Identity mark recovers the native physical window. | Proved; focused axiom audit passed. |
| `physical_eq_gaussian_sum` | Actual marked infinite window equals its convergent four Gaussian sums. | Proved; focused axiom audit passed. |
| `physical_reflection` | Full physical reflection carries A to inverse A with factor -M/q. | Proved; focused axiom audit passed. |
| `compensated_reflection` | All four marks, scales and complex compensation cross terms retained. | Proved; focused axiom audit passed. |
| `finitePacket_reflection` | Exact reflection on the entire arbitrary finite signed support. | Proved; focused axiom audit passed. |
| `finitePacket_hasSum` | Entire finite signed packet equals its actual convergent lattice sum. | Proved; focused axiom audit passed. |
| `marked_profile_normalization` | Marked spatial normalization retains the whole isotropic subtraction. | Proved; focused axiom audit passed. |
| `physical_unit_normalization` | Marked infinite window retains complete principal/isotropic normalization. | Proved; focused axiom audit passed. |
| `finitePacket_unit_normalization` | Every weighted finite row retains its isotropic unit correction. | Proved; focused axiom audit passed. |
| `compensated_unit_normalization` | All four compensation terms retained in both normalized and isotropic parts. | Proved; focused axiom audit passed. |
| `seed_auxiliary_inert` | Actual seed p+1 divisibility implies p mod3 equals2. | Proved; focused axiom audit passed. |
| `seed_auxiliary_lower_bound` | Actual seed p+1 divisibility implies p at least q-2. | Proved; focused axiom audit passed. |
| `seed_auxiliary_mod_twelve` | Actual cubic and fourfold seed conditions imply p mod12 equals11. | Proved; focused axiom audit passed. |
| `scalar_cast_q_zero` | The actual quotient kills the rational period q. | Proved; focused axiom audit passed. |
| `scalarUnit_val` | Bezout constructs each coprime rational mark with its actual scalar value. | Proved; focused axiom audit passed. |
| `rational_finite_reflection` | All rational dilations retain inverse marks, d^-2 and dual q^2*d^2/M. | Proved; focused axiom audit passed. |
| `depleted_reflection` | Full mu-weighted divisor packet has exact signed dual transfer. | Proved; focused axiom audit passed. |
| `depleted_hasSum` | Full mu-weighted divisor packet equals its actual convergent lattice sum. | Proved; focused axiom audit passed. |
| `depleted_unit_normalization` | Every divisor retains its complete normalized/isotropic correction. | Proved; focused axiom audit passed. |
| `depleted_compensated_reflection` | All divisors and all four compensation terms remain in the dual packet. | Proved; focused axiom audit passed. |
| `depleted_split_unit` | Explicit d=1 row and exactly the finite support of remaining divisors. | Proved; focused axiom audit passed. |

The actual unit marks need no phase or symmetry matching premise. Fourier
reflection inverts each mark. Every finite signed support, all divisors of B,
mu signs, d^-2 factors, four scales, both mixed terms and the full isotropic
subtraction survive. The d=1 divisor is explicitly retained. These are actual
convergent native window identities, with no RH premise. Identification of the
full inducing-modulus coprime mask and infinite norm L-series, the prime-weighted
full reciprocal-L packet, and the unbounded Abel limit remain unfinished.
Individual marked weights need not satisfy nonnegative-real-part positivity.
The installed arithmetic I exponent7/4 and certified boundary7/8 are unchanged;
required I exponent3/2 and target boundary at most3/4 remain active.
Paper label: `sec:carmichael-marked-window`.
Receipt: [marked and complete divisor packet](verification/carmichael-marked-window.json).

## Complete moving compensated physical packet (2026-10-28)

Owners: `Assembly/CarmichaelBalancedMask.lean` and
`Assembly/CarmichaelMovingWindow.lean`. All30 public claims compile in their
maintained owners and have individual focused standard-only axiom checks.
The earlier21 new proofs were not re-audited for the final9 additions.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `CarmichaelBalancedMask.origin_transform` | Finite trace transform of the spatial origin indicator. | Proved; focused axiom audit passed. |
| `CarmichaelBalancedMask.constant_transform` | Finite trace transform of the constant profile. | Proved; focused axiom audit passed. |
| `CarmichaelBalancedMask.balanced_pair_transform` | Full local profile 1-p*delta_0 has eigenvalue -p. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.idealRowSum_compensation` | Exact native row equals RA-c*RB before any norm. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.compensated_mobius_packet` | Full supported common-prime Mobius overlap with compensated weights. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.compensation_cross_terms` | Both complex mixed terms and c*bar(c) term retained. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.periodic_gaussian_summable` | Actual arbitrary-period profile Gaussian series converges. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.periodic_window_hasSum` | Actual infinite four-Gaussian carrier HasSum. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.periodic_window_gaussian_expansion` | Window equals its four convergent Gaussian sums. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.periodic_gaussian_transfer` | Native trace transfer for every nonzero Eisenstein period. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.periodic_window_transfer` | Full arbitrary-profile moving-window transfer, all Fourier terms retained. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.fullModulus_ne_zero` | Union-product period is nonzero under proved local maximality. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.fullModulus_mem` | Union generator belongs to every supported local ideal. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.fullModulus_norm_sq` | Exact period norm equals norm of the union ideal product. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.residueFactor_mk` | Actual quotient maps send native z to its local residue. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.pairProfile_mk` | Full quotient profile equals the actual two squarefree rows, including overlaps. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.full_pair_window_hasSum` | Actual overlapping native pair carrier HasSum. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.full_pair_window_transfer` | Actual overlapping pair transfer with no phase/symmetry/even-row exclusion. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.finiteRowSum_norm_square` | Exact complex double expansion of the entire finite row. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.finite_packet_window_hasSum` | Entire signed finite packet converges with all cross terms. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.finite_packet_window_transfer` | Entire signed finite packet transfers at each exact union period. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.pairWindow_unit` | Empty-support physical row is the actual unit packet. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.dualPairWindow_unit` | Dual empty-support row is the same actual unit packet. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.dualPairWindow_unit_bound` | Explicit O(1/M) geometric unit bound, every M>=1. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.native_compensated_window_hasSum` | Actual native idealRowSum compensated packet HasSum, original hypotheses only. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.native_compensated_window_transfer` | Actual native compensated ideal packet, every phase and cross term retained. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.idealSupport_one` | Actual ideal1 has empty normalized-factor support. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.native_unit_window` | Native ideal1 dual diagonal equals actual unit packet. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.native_unit_window_bound` | Native ideal1 diagonal has explicit cutoff-independent O(1/M) bound. | Proved; focused axiom audit passed. |
| `CarmichaelMovingWindow.native_compensated_unit_split` | Full native packet splits into unit diagonal, both mixed sums and exact nonunit support. | Proved; focused axiom audit passed. |

The native compensated HasSum and window transfer now use the actual moving
union-product period. No new phase-one, transpose-symmetry, primitive-row,
characteristic-two exclusion or real-line Schwartz hypothesis is present.
Every overlap, ideal Mobius sign, inert prime-power norm and all four
compensation terms remain. The full finite Fourier transform is retained;
individual scalar phases are not asserted to equal one.

The native ideal1 row is identified and bounded by B_V/M for M>=1. Its exact
split retains both mixed rows and the entire finite complement F.erase(1).
This geometric unit is distinct from arithmetic Abel C_G. No new estimate of
that arithmetic term, the prime-weighted reciprocal-L packet, or its uniform
unbounded Abel passage has been proved. I7/4 and the certified boundary7/8 are
unchanged. I3/2 and boundary at most3/4 remain the active target.
Paper label: `sec:carmichael-moving-window`.
Receipt: [complete moving window](verification/carmichael-moving-window.json).

## Arithmetic unit and finite native companion reconstruction (2026-10-28)

Owner: `Assembly/CarmichaelArithmeticUnit.lean`.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `compensated_native_unit_value` | Actual spatial u=1 row is the full compensated ideal-Mobius coefficient sum. | Proved; focused axiom audit passed. |
| `normFiber_companion_recovery` | Finite convolution of actual norm-fiber inverse-pair coefficients with the plain companion recovers rational mu*chi, including n=0. | Proved; focused axiom audit passed. |
| `compensated_coprime_unit` | Exact signed rational coprime unit form becomes the full Mobius-weighted sum of native companion amplitudes; all four compensation terms retained. | Proved; focused axiom audit passed. |

This closes the finite arithmetic-unit coefficient dictionary with no RH,
zero-free-strip or primitivity assumption. Ideal and rational Mobius functions
are related by the proved convolution, and rational coprimality remains
explicit. The existing norm-fiber Euler identity for Re(s)>1 retains both
inverse L factors. The spatial unit u=1 is distinct from the ideal1 theta bound.
No new I power or zero-free exponent is proved: the full signed amplitude sum,
prime-weighted frequency transfer and uniform Abel estimates remain open.
Installed I7/4 and boundary7/8 are unchanged; I3/2 and boundary<=3/4 remain active.
Paper label: `sec:carmichael-arithmetic-unit`.
Receipt: [arithmetic unit reconstruction](verification/carmichael-arithmetic-unit.json).

## Signed plain-companion character cancellation (2026-10-29)

Owner: `Assembly/CarmichaelCompanionCancellation.lean`.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `nonprincipal_prefix_bound` | Every positive prefix of a nonprincipal Dirichlet character is bounded by its modulus. | Proved; focused axiom audit passed. |
| `progression_eq` | Exact multiplier parametrization, including k=0 and every prime power. | Proved; focused axiom audit passed. |
| `progression_bound` | Uniform complete-period cancellation on every divisibility progression. | Proved; focused axiom audit passed. |
| `masked_progression_identity` | All coprimality Mobius corrections become exact lcm progressions. | Proved; focused axiom audit passed. |
| `masked_progression_bound` | The whole progression remainder is bounded by q*tau(H). | Proved; focused axiom audit passed. |
| `coprime_companion_identity` | Exact rectangular signed Mobius bilinear assembly. | Proved; focused axiom audit passed. |
| `coprime_companion_bound_left` | Joint unweighted character remainder is at most (B+1)*q^2*tau(H)*tau(K). | Proved; focused axiom audit passed. |
| `companionPacket_star` | Complex conjugation exchanges both supports and both masks. | Proved; focused axiom audit passed. |
| `coprime_companion_bound` | Symmetric joint remainder uses min(B,C)+1. | Proved; focused axiom audit passed. |
| `weighted_masked_progression_bound` | The actual combined complex window enters through its finite variation. | Proved; focused axiom audit passed. |
| `weighted_coprime_companion_identity` | All weighted coprimality rows remain in one exact signed sum. | Proved; focused axiom audit passed. |
| `weighted_companion_bound_left` | Joint weighted companion estimate, with both variations charged. | Proved; focused axiom audit passed. |
| `weightedCompanionPacket_star` | Weighted support and phase symmetry is proved. | Proved; focused axiom audit passed. |
| `weighted_coprime_companion_bound` | Full weighted joint estimate uses min(B,C)+1 and explicit conductor q^2. | Proved; focused axiom audit passed. |
| `cubic_companion_ne_one` | Every actual cubic companion is odd and nonprincipal; no additional phase hypothesis. | Proved; focused axiom audit passed. |
| `compensated_companion_expansion` | Both mixed terms and c*conj(c)*BB remain exactly. | Proved; focused axiom audit passed. |
| `pair_inverse_coeff_divisor_bound` | Actual inverse-pair coefficients are bounded by tau(n), including n=0. | Proved; focused axiom audit passed. |

The arbitrary-window bound retains the full signed coprimality expression
before complete-period cancellation. Its cost is
`(min(B,C)+1)*q^2*tau(H)*tau(K)*V(w,B)*V(v,C)`.
The variation uses the combined compensated windows. No prime-power norm
is discarded. For chi^3=1 the actual base-change companion is odd, so the
nonprincipal hypothesis is discharged; a principal companion remains an
explicit exceptional case outside this cancellation estimate.

This is an independent character estimate. Its complete native reindexing,
growing-parameter costs and the remaining long
native sector still need their signed consumer. No I3/2 or improved global
zero-free boundary is claimed. Installed I7/4 and boundary7/8 remain;
the active endpoint remains at most3/4.
Paper label: `sec:carmichael-companion-cancellation`.
Receipt: [signed companion estimate](verification/carmichael-companion-cancellation.json).

## Uniform prime-mask companion transfer (2026-10-29)

Owner: `Assembly/CarmichaelCompanionMasks.lean`.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `progression_divisor_window` | A divisibility window becomes the exact lcm progression, including zero indices. | Proved; focused axiom audit passed. |
| `progression_divisor_sum` | Every finite divisor coefficient is retained in the progression identity. | Proved; focused axiom audit passed. |
| `divisor_sum_progression_bound` | Weighted progression cancellation pays coefficient mass and the original window variation. | Proved; focused axiom audit passed. |
| `divisor_sum_packet_bound` | Both finite divisor masks are retained in the full coprime packet bound. | Proved; focused axiom audit passed. |
| `tag_product_pos` | Every finite prime-tag product is positive. | Proved; focused axiom audit passed. |
| `tag_product_dvd_iff` | Prime-tag divisibility is equivalent to all its individual prime conditions. | Proved; focused axiom audit passed. |
| `amplifier_product_split` | Exact A_G(ab) splitting requires no coprimality of a,b. | Proved; focused axiom audit passed. |
| `amplifier_tag_expansion` | Exact nonnegative squarefree-tag expansion of the amplifier. | Proved; focused axiom audit passed. |
| `tag_coefficient_nonneg` | All prime-tag expansion coefficients are nonnegative. | Proved; focused axiom audit passed. |
| `tag_coefficient_identity` | d times its tag coefficient equals its exact amplifier. | Proved; focused axiom audit passed. |
| `tag_coefficient_le` | Each coefficient is at most tau(d)/d. | Proved; focused axiom audit passed. |
| `tag_mass_le_divisor_harmonic` | Truncated tag mass is at most the divisor harmonic prefix, uniformly in G. | Proved; focused axiom audit passed. |
| `divisor_harmonic_le_square` | The divisor harmonic prefix is at most the square of the harmonic prefix. | Proved; focused axiom audit passed. |
| `amplifier_truncated_tag_expansion` | The exact product amplifier uses only tags below the companion cutoff. | Proved; focused axiom audit passed. |
| `progression_tag_window` | All tags become lcm progression conditions before variation. | Proved; focused axiom audit passed. |
| `tag_window_progression_bound` | Character cancellation estimates the actual truncated tag window. | Proved; focused axiom audit passed. |
| `amplified_window_eq` | Exact finite tag expansion of A_G(a*b) times the smooth window. | Proved; focused axiom audit passed. |
| `amplified_progression_identity` | The original amplified progression equals its full tag progression sum. | Proved; focused axiom audit passed. |
| `amplified_progression_bound` | Progression bound uniform in every finite prime mask, with explicit harmonic and conductor costs. | Proved; focused axiom audit passed. |
| `amplified_packet_bound` | Complete amplified packet bound with min(B,C)+1 and all q/divisor/harmonic/window costs. | Proved; focused axiom audit passed. |
| `amplified_compensation_expansion` | Exact AA, both mixed terms, and z*conj(z)*BB after amplification. | Proved; focused axiom audit passed. |

For every finite set G of primes, including 2, the full amplified packet is at most
`(min(B,C)+1)*q^2*tau(a)*tau(c)*tau(H)*tau(K)*h_B^2*h_C^2*V(w,B)*V(v,C)`.
The exact amplifier is A_G(a*b). Its mask conditions enter the progression
before variation; no coprimality within a column is imposed. All prime powers,
all supported tag conditions and all four compensation terms remain.
The estimate is uniform in the size and product of G.

The sampled-window and low-product estimates are proved below.
The full native hyperbola reindexing, remaining signed high-product sector
and uniform reciprocal-L/Abel consumer are still open.
No bound for the complete arithmetic unit or I3/2 is claimed.
Installed global I7/4 and boundary7/8 are unchanged; the target remains <=3/4.
Paper label: `sec:carmichael-companion-masks`.
Receipt: [uniform amplified companion](verification/carmichael-companion-masks.json).

## Target-sized low native product sector (2026-10-29)

Owner: `Assembly/CarmichaelNativeLowSector.lean`.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `harmonic_prefix_mono` | The positive harmonic prefix is monotone in its actual inclusive cutoff. | Proved; focused axiom audit passed. |
| `product_region_kernel_bound` | The full ac<=T reciprocal-maximum kernel has a square-root product cost. | Proved; focused axiom audit passed. |
| `companion_cutoff_cost` | The exact two companion cutoffs cost at most 2N/max(a,c). | Proved; focused axiom audit passed. |
| `low_companion_cost_bound` | Aggregate every retained companion cutoff on the full low-product region. | Proved; focused axiom audit passed. |
| `native_term_bound` | Apply the proved companion cancellation to the actual native coefficients and both cross masks. | Proved; focused axiom audit passed. |
| `low_native_packet_bound` | A complete finite bound for the signed low native packet with explicit divisor and variation caps. | Proved; focused axiom audit passed. |
| `low_native_packet_subpower` | Discharge all divisor and harmonic growth costs uniformly in q,H,N,T and finite prime masks. | Proved; focused axiom audit passed. |
| `scaled_window_variation` | The actual sampled fixed window has a variation bound independent of its native index and scale. | Proved; focused axiom audit passed. |
| `scaled_low_native_packet_subpower` | Apply the low-product estimate at N=4D,T=D with the sampled-window variation discharged. | Proved; focused axiom audit passed. |
| `schwartz_lipschitz` | The first Schwartz seminorm supplies the required global Lipschitz constant. | Proved; focused axiom audit passed. |
| `schwartz_low_native_packet_subpower` | An unconditional target-sized bound for the actual Schwartz-window low native sector, uniform in G. | Proved; focused axiom audit passed. |

The defined low native sector is bounded by
`C_eps*(3q)^2*V^2*(H*N)^eps*N*floor(sqrt(T))`, uniformly over all finite G.
All divisor and harmonic growth costs are discharged. For N=4D,T=D and a
Schwartz combined window f, its actual variation is at most
`S(f)=norm(f(0))+8*seminorm_Real_0_1(f)`, independently of a,D.
The compiled specialization is at most
`C_eps*(3q)^2*S(f)^2*(4*H*D)^eps*(4*D)*floor(sqrt(D))`.
This gives unconditional D^(3/2+eps) for this defined low sector with fixed
q,H,f and uniformly in G. It retains every native prime-power norm, both
cross masks, rational outer coprimality and the combined compensated window.

The complete hyperbola equality is proved in the following section.
The high-product sector ac>D remains signed,
including b=d=1. The complete unit packet, reciprocal-L assembly and uniform
Abel limit are not bounded here. Global I7/4 and boundary7/8 are unchanged;
the active complete target remains <=3/4.
Paper label: `sec:carmichael-native-low-sector`.
Receipt: [low native product bound](verification/carmichael-native-low-sector.json).

## Full rational unit and target-sized high-core remainder (2026-10-29)

Owner: `Assembly/CarmichaelNativeHyperbola.lean`.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `native_weighted_hyperbola` | Exact one-column native reconstruction with every norm prime power and the true floor cutoff. | Proved; focused axiom audit passed. |
| `native_weighted_hyperbola_star` | The conjugated column reconstructs with its full character phase. | Proved; focused axiom audit passed. |
| `native_bilinear_hyperbola` | Reconstruct both columns for an arbitrary complex kernel without a symmetry hypothesis. | Proved; focused axiom audit passed. |
| `coprime_product_kernel` | Rational product coprimality is exactly the outer conditions and both inner cross masks. | Proved; focused axiom audit passed. |
| `rational_unit_actual_weights` | The factored unit is the original compensated coefficient form with the full product amplifier. | Proved; focused axiom audit passed. |
| `rational_unit_native_packet` | The entire finite rational unit equals the complete signed native packet. | Proved; focused axiom audit passed. |
| `full_native_low_high_split` | Partition the native packet exactly at ac<=T, preserving every supported term. | Proved; focused axiom audit passed. |
| `rational_unit_high_core_remainder` | The actual rational unit differs from its retained high native core by the proved target-sized low remainder. | Proved; focused axiom audit passed. |

The full finite rational unit equals the complete signed native packet.
For N=4D,T=D, subtracting the retained high core ac>D leaves exactly the
proved low native sector. The compiled remainder is at most
`C_eps*(3q)^2*S(f)^2*(4*H*D)^eps*(4*D)*floor(sqrt(D))`, every positive
q,H,D, cubicchi, Schwartzf and finite primeG. All phases, norm prime powers,
original amplifiers A_G(a*b), masksH*c,H*a and four compensation terms remain.
The exact reconstruction holds for every character, arbitrary complex
kernel and finite cutoff, including the empty cutoff; no symmetry premise.

The finite hyperbola edge is closed. No estimate of the signed high main
term ac>D is claimed. Its joint Gauss cancellation, original reciprocal-L
prime-sampled consumer and uniform unbounded Abel passage remain open.
Global I7/4 and boundary7/8 are unchanged; the target remains <=3/4.
Paper label: `sec:carmichael-native-hyperbola`.
Receipt: [full unit reconstruction](verification/carmichael-native-hyperbola.json).

## Uniform square-part cancellation and physical windows (2026-10-29)

Owner: `Assembly/CarmichaelSquarepartCancellation.lean`.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `squarefree_progression_expansion` | Exact finite square-divisor expansion of an amplified squarefree progression. | Proved; focused axiom audit passed. |
| `squarefree_amplified_progression_bound` | Nonprincipal complete-period cancellation with the full finite prime amplifier. | Proved; focused axiom audit passed. |
| `squarefree_progression_rescale` | Exact shortened progression with both mask H*k and amplifier base a*k. | Proved; focused axiom audit passed. |
| `squarefree_amplified_rescaled_bound` | Cancellation on the actual shortened cutoff, including empty cutoffs. | Proved; focused axiom audit passed. |
| `squarefree_coprime_identity` | Full signed common-divisor identity, retaining k=1. | Proved; focused axiom audit passed. |
| `squarefree_coprime_row_bound` | Coupled row estimate after both column progression cancellations. | Proved; focused axiom audit passed. |
| `cubic_squarepart_row_bound` | Square-part specialization with the stated nonprincipal companion. | Proved; focused axiom audit passed. |
| `squarefree_divisor_cost_bound` | The complete supported square-root row cost is at most sqrt(B*C)*H_B. | Proved; focused axiom audit passed. |
| `squarefree_coprime_harmonic_bound` | Aggregate every supported row with explicit cap bounds. | Proved; focused axiom audit passed. |
| `squared_window_variation` | Physical squared Schwartz windows have a scale-independent seminorm budget. | Proved; focused axiom audit passed. |
| `squared_window_dilate` | Dilation changes A to A*k^2 exactly, with positive-index conventions preserved. | Proved; focused axiom audit passed. |
| `squared_window_rescaled_variation` | Discharge variation at every true floor cutoff B/k. | Proved; focused axiom audit passed. |
| `squarepart_companion_ne_one` | For every Dirichlet character, chi^2*chi_-3 is odd and nonprincipal. | Proved; focused axiom audit passed. |
| `squared_squarepart_subpower` | Uniform unconditional physical square-part mean with all caps discharged. | Proved; focused axiom audit passed. |

Supporting exports from `Assembly/CarmichaelNativeLowSector.lean`:
`cap_bound` and `harmonic_subpower`. Their existing proofs are unchanged and now
reusable publicly; both focused axiom checks passed. The six new public
definitions are tracked separately from the fourteen new theorem proofs.

For every eps>0 the final estimate is
`C_eps*(3q)^2*S2(f)*S2(g)*X^eps*sqrt(B*C)`,
where `X=(H+K+a+c+1)*(B+C+1)` and
`S2(f)=seminorm_Real_0_0(f)+8*seminorm_Real_0_1(f)`.
It holds for positive q,H,K,a,c,D, natural A,E,B,C with
A*B^2<=4D and E*C^2<=4D, all Dirichlet chi and Schwartz f,g.
B or C may be zero. C_eps is independent of every displayed parameter
and every finite prime G. Conductor, mask growth and seminorm costs
remain explicit. No RH hypothesis or installed 7/8 estimate is used.

The phase and physical variation hypotheses of this square-part estimate
are discharged. The exact signed common-divisor row k=1 and combined
compensated window remain. This is an auxiliary square-part packet:
its native coefficient and full finite-unit reindexing are proved in the
following section. The rectangular inner-mean and physical-row transfer is
proved below. The remaining signed small-square native core, prime-sampled
reciprocal-L consumer and uniform Abel passage remain open.
No bound for the complete native high core or I_{D,G} is asserted.
Global boundary7/8 is unchanged; the active complete target remains <=3/4.
Paper label: `sec:carmichael-squarepart-cancellation`.
Receipt: [uniform square-part estimate](verification/carmichael-squarepart-cancellation.json).

## Exact native square-part dictionary and full unit (2026-10-29)

Owner: `Assembly/CarmichaelNativeSquarepart.lean`.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `native_square_coeff` | Every positive rational square norm has coefficient mu(n)^2*(chi^2*chi_-3)(n), including all exceptional local factors. | Proved; focused axiom audit passed. |
| `native_coprime_squarepart` | Extract a coprime square part with its complete character phase. | Proved; focused axiom audit passed. |
| `native_zero_of_cube_dvd` | A prime cube divisor annihilates the native coefficient. | Proved; focused axiom audit passed. |
| `native_squarepart_formula` | The full pointwise formula treats every noncoprime overlap as an exact zero. | Proved; focused axiom audit passed. |
| `native_squarepart_sum` | Exact finite square-part transfer for every complex weight, including N=0. | Proved; focused axiom audit passed. |
| `native_squarepart_bilinear` | Transfer both columns for arbitrary complex kernels without a symmetry premise. | Proved; focused axiom audit passed. |
| `full_native_squarepart_packet` | Reconstruct the entire native packet with all companion rows and cross masks. | Proved; focused axiom audit passed. |
| `rational_unit_squarepart_packet` | The original full rational unit equals the complete square-part packet. | Proved; focused axiom audit passed. |

Shared export from `Assembly/CarmichaelSquarepartCancellation.lean`:
`square_dvd_square_mul_squarefree_iff`. Its existing proof is unchanged
and its focused axiom audit passed. Three new public definitions are
counted separately from the eight new theorem proofs.

The exact domain consists of positive pairs (r,s) with squarefree r,
r<=N, s<=floor(sqrt(N)), and r*s^2<=N. The map to r*s^2 is bijective.
Only r is filtered in this domain; mu(s)^2 retains the exact second-column
squarefree support. The pointwise coefficient formula itself requires only
r,s>0 and handles all overlaps by cube vanishing. It has no RH, cubic-order,
symmetry or extra phase hypothesis.

The full rational unit, every native norm prime power, the full amplifiers,
both masks H*c,H*a, the actual floors N/a,N/c, companion b=d=1,
square-part s=t=1 and all four compensation terms remain. No signed main
term was replaced by an unsigned coefficient mass or a Gram estimate.

The native coefficient and finite full-unit dictionary obligations are closed.
The rectangular regrouping and its uniform physical-row estimate are proved
below. The later aggregate section also proves the finite large-square
remainder bound. The signed small-square core, prime-sampled full reciprocal-L
consumer and uniform unbounded Abel passage remain open.

Benchmark status: exact structural transfer to the original finite unit.
Old complete I exponent: 7/4. New complete I exponent: 7/4.
Target complete I exponent: 3/2. No numerical diagnostics used.
Certified global boundary: 7/8. Active target: <=3/4.
Paper label: `sec:carmichael-native-squarepart`.
Receipt: [native square-part transfer](verification/carmichael-native-squarepart.json).

## Physical windows and full signed square-part rows (2026-10-29)

Owner: `Assembly/CarmichaelSquarepartPhysical.lean`.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `native_companion_range_swap` | Permute every supported companion/square-part pair at its exact product cutoff. | Proved; focused axiom audit passed. |
| `squarefree_rectangle_identity` | Express an arbitrary lower rectangle as its four signed prefix packets. | Proved; focused axiom audit passed. |
| `squared_rectangle_subpower` | Transfer the uniform squared-window mean to every positive lower rectangle. | Proved; focused axiom audit passed. |
| `native_squarepart_hyperbola` | Write the native finite sum with its exact hyperbola cutoff. | Proved; focused axiom audit passed. |
| `rational_column_squarepart_rows` | Reorder the original rational convolution into physical square-part rows. | Proved; focused axiom audit passed. |
| `amplifier_square_argument` | Retain the full amplifier under its exact square-support identity. | Proved; focused axiom audit passed. |
| `unit_good_squarepart_masks` | Derive both complete cross masks, including every column overlap. | Proved; focused axiom audit passed. |
| `physical_squarepart_rectangle` | Identify the actual coupled physical row with the squarefree rectangle. | Proved; focused axiom audit passed. |
| `physical_squarepart_rectangle_bound` | Bound that physical row uniformly with explicit conductor and seminorm costs. | Proved; focused axiom audit passed. |
| `rational_bilinear_squarepart_rows` | Transfer both columns for arbitrary complex kernels without a symmetry premise. | Proved; focused axiom audit passed. |
| `rational_unit_physical_squarepart_rows` | Identify the full original rational unit with all signed physical rows. | Proved; focused axiom audit passed. |
| `physical_rows_actual_cutoff_bound` | Discharge both window support premises at the actual square-root cutoffs. | Proved; focused axiom audit passed. |

The twelve new public theorem proofs and two definitions are maintained in the
owner and exported through RHAnalysis. The first seven focused axiom results
are retained; only the five subsequent declarations were newly audited.
No unchanged earlier theorem was reaudited.

For every eps>0, positive q,H,r,u,b,d,D,R,T, any Dirichlet chi modulo q,
any finite prime G and Schwartz f, set m=r*b,n=u*d,
B=floor(sqrt(4D/m)), C=floor(sqrt(4D/n)),
X=(H*r*n+H*u*m+m+n+1)*(B+C+1). The actual physical rectangle is bounded by
`|a_chi(r)|*|a_chi(u)|*C_eps*(3q)^2*S2(f)^2*X^eps*sqrt(B*C)`.
C_eps is independent of all displayed parameters and G. B or C may be zero.
The constant is four times the proved prefix constant. The actual phase
chi^2*chi_-3 is nonprincipal for every chi; no symmetry, RH or cubic-order
premise is introduced. The exact row uses masks H*r*n and H*u*m.

The full rational unit is the finite signed outer sum of these physical rows.
The common-divisor unit k=1, square parts s=t=1 and companions b=d=1 all
remain, as do AA-bar(z)*AB-z*BA+|z|^2*BB and every original character phase.
The complete signed native core has not been replaced by unsigned mass.

Closed: exact physical range transfer, both cross-mask hypotheses, arbitrary
lower rectangles, the actual window-support premises, and full two-column
finite-unit reordering without a symmetry assumption.
The later aggregate section proves the finite large-square sector bound.
Open: the retained signed small-square core, summation over every moving
prime frequency with its full conductor and window costs, the full
reciprocal-L consumer, and a uniform unbounded Abel passage.

Benchmark status: uniform row cancellation transferred to the actual finite
unit; no complete exponent gain claimed. Old complete I exponent: 7/4.
New complete I exponent: 7/4. Target: 3/2. No numerical diagnostics used.
Certified global boundary: 7/8. Active target: <=3/4.
Paper label: `sec:carmichael-squarepart-physical`.
Receipt: [physical square-part transfer](verification/carmichael-squarepart-physical.json).

## Complete large-square sector estimate (2026-10-29)

Owner: `Assembly/CarmichaelLargeSquareRemainder.lean`.

| Lean declaration | Claim | Status |
| --- | --- | --- |
| `hyperbola_mass_cap` | The weighted native hyperbola has exact cap A*M^(3/4)*H_M^2. | Proved; focused axiom audit passed. |
| `hyperbola_mass_subpower` | The positive outer cost is O_eps(M^(3/4+eps)), uniformly in the modulus and character. | Proved; focused axiom audit passed. |
| `physical_row_outer_cost` | The full cancelled row factors into two explicit three-quarter outer weights. | Proved; focused axiom audit passed. |
| `large_square_packet_subpower` | The restricted large-square aggregate has its complete conductor, mask and seminorm bound. | Proved; focused axiom audit passed. |
| `physical_row_zero_outside_square_cutoffs` | Every omitted product row is exactly zero because an inner interval is empty. | Proved; focused axiom audit passed. |
| `large_square_packet_full_support` | The restricted aggregate equals the full original large-square sector, with every nonzero row. | Proved; focused axiom audit passed. |
| `full_large_square_packet_subpower` | The full large-square sector has the same uniform power estimate. | Proved; focused axiom audit passed. |
| `rational_unit_full_sector` | At R=T=1 the full sector is exactly the original full signed rational unit. | Proved; focused axiom audit passed. |

All eight new public theorem proofs and three definitions are maintained and
exported through RHAnalysis. The focused audit covers only these eight;
no unchanged theorem was reaudited.

For every eps>0, positive q,H,D,R,T, every Dirichlet chi modulo q, finite
prime G and Schwartz f, put N=4D, M_R=floor(N/R^2), M_T=floor(N/T^2),
Xcal=(2*H*N^2+2*N+1)*(2*N+1). The complete large-square sector satisfies
`|P_(R,T)| <= C_eps*(3q)^2*S2(f)^2*Xcal^eps*N^(1/2)*M_R^(3/4+eps)*M_T^(3/4+eps)`.
C_eps is independent of all displayed parameters and G. Either M may be
zero. Both support truncations are proved identities: each removed row is
zero. The full sector includes all originally supported outer products.
R=T=1 recovers the entire original rational unit exactly.

The proof applies the actual character-cancelled rectangle bound first,
then estimates only the extracted remainder by positive hyperbola costs.
The retained small-square core is not assigned an unsigned mass bound.
All cross masks, actual floor cutoffs, all character phases and combined
compensation remain in the exact finite packet. The cost (3q)^2 and the
actual S2(f)^2 are explicit and must be charged for growing families.

Closed: the finite native large-square remainder estimate, including every
nonzero supported row and both actual outer cutoffs. Open: the retained
signed small-square estimate, the complete moving prime-frequency/full
reciprocal-L assembly and uniform unbounded Abel passage.

Benchmark status: a new uniform analytic estimate for the extracted sector;
the complete signed bound is not yet improved. Old complete I exponent: 7/4.
New complete I exponent: 7/4. Target: 3/2. No numerical diagnostics used.
Certified global boundary: 7/8. Active target: <=3/4.
Paper label: `sec:carmichael-large-square-remainder`.
Receipt: [complete large-square estimate](verification/carmichael-large-square-remainder.json).

## Actual carrier window and cubic phase transfer (October29)

Each declaration below is maintained in the named public namespace under
`PrimeFactorOscillations`. Definitions are excluded from the theorem count.

| Namespace | Claim | Mathematical content | Status |
| --- | --- | --- | --- |
| `CarmichaelCubicResonance` | `cubic_squarepart_conjugacy` | The cubic square-part companion is the conjugate plain companion, including nonunits. | Proved; focused axiom audit passed. |
| `CarmichaelCubicResonance` | `cubic_phase_product` | The two characters multiply to the actual principal character. | Proved; focused axiom audit passed. |
| `CarmichaelCubicResonance` | `cubic_companion_resonance` | The resonant phase cancels exactly against the square-part companion. | Proved; focused axiom audit passed. |
| `CarmichaelCubicResonance` | `cubic_resonance_pair` | Both resonant columns retain the arbitrary complex coupled kernel. | Proved; focused axiom audit passed. |
| `CarmichaelCubicResonance` | `cubic_companion_ratio` | Every congruence ratio retains its complete character coefficient. | Proved; focused axiom audit passed. |
| `CarmichaelCubicResonance` | `cubic_ratio_pair` | The two ratio classes retain both phases and every kernel term. | Proved; focused axiom audit passed. |
| `CarmichaelCubicResonance` | `shifted_cubic_input` | The exact physical input is cubic plus its signed quadratic shift. | Proved; focused axiom audit passed. |
| `CarmichaelCubicResonance` | `shifted_cubic_companion` | The shifted input has the same exact companion-phase coefficient. | Proved; focused axiom audit passed. |
| `CarmichaelCubicResonance` | `shifted_cubic_parameters_exist` | Every unit square-part index has residue and signed integer shift parameters. | Proved; focused axiom audit passed. |
| `CarmichaelCubicResonance` | `shifted_cubic_parameters_unique` | Those parameters are unique with the residue in [0,3q). | Proved; focused axiom audit passed. |
| `CarmichaelSquarepartCancellation` | `squarefree_packet_subpower_of_variation` | The uniform prefix mean needs only the actual dilation-variation budgets. | Proved; focused axiom audit passed. |
| `CarmichaelSquarepartPhysical` | `rectangle_subpower_of_variation` | All four exact prefixes give the same rectangle bound with arbitrary budgeted windows. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `antitone_positive_variation` | A positive decreasing sequence has exactly its initial-value endpoint variation. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `variation_finite_linear` | Finite complex window compensation has the explicit coefficient-weighted variation bound. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `gaussian_positive_clock_variation` | Every increasing positive Gaussian clock has variation at most one. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `carrier_positive_clock_variation` | The unchanged four-Gaussian carrier has uniform budget21/8. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `compensated_carrier_clock_variation` | The actual two-window compensation has budget(21/8)*(1+|z|). | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `carrier_rescaled_variation` | Every square-part dilation retains budget21/8 without a growing support condition. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `quartic_compensation_norm_le_one` | The exact D^(-3) physical coefficient has modulus at most one for D>=1. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `quartic_carrier_rescaled_variation` | Every actual compensated square-part dilation has uniform budget21/4. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `quartic_carrier_rectangle_subpower` | The actual carrier satisfies the squarefree rectangle mean with explicit(21/4)^2 cost. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `quartic_window_norm_coordinate` | The normalized window is exactly V(n/D)-D^(-3)V(n/D^4). | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `quartic_physical_packet_transfer` | The fixed finite physical carrier transfers to that exact compensated window. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `rational_kernel_star_swap` | The full coprimality-masked kernel is Hermitian for every complex window. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `physical_rectangle_star_swap` | Every return and compensation cross term obeys the exact row-exchange symmetry. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `phased_physical_rectangle_star_swap` | The actual plain-companion phase preserves symmetry without character-order exceptions. | Proved; focused axiom audit passed. |
| `CarmichaelCarrierVariation` | `quartic_carrier_physical_row_bound` | The actual compensated physical row has the uniform conductor-squared square-root mean, including unit indices. | Proved; focused axiom audit passed. |

The existing `squared_squarepart_subpower` and `squared_rectangle_subpower`
statements are unchanged. Their proofs now consume the more general
variation-budget providers; both changed proofs were freshly compiled and
axiom checked. The focused new check covers17 new and2 changed proofs.
The successful earlier check for the10 cubic phase proofs was reused;
no unchanged proof was reaudited.

Closed: the actual four-Gaussian carrier's physical-row qualification,
its exact fixed-support quartic transfer, the finite masked-kernel
symmetry, and the plain-companion phase symmetry. The cubic normal form
retains every residue ratio, nonunit zero and negative integer shift.
The actual profile is not asserted to be Schwartz on the negative
half-line. The proved positive-clock budget replaces that unnecessary
qualification. The physical coefficient is D^(-3), the reference scale
is D^4, and1/4 belongs only to the Mellin change of variables.

Open: the independent signed small-square core estimate; the original
moving sextic Hecke phase/norm-cube adapter; the complete prime-frequency
sum with both reciprocal L-factors; and the uniform unbounded Abel limit.
The fixed-support Mellin formula does not justify a simultaneous moving
carrier cutoff. The full rational unit is not reduced to its outer
r=u=b=d=1 subrow or claimed to satisfy the target bound.

Benchmark status: structural and actual-window transfer completed;
no complete exponent improvement. Old complete I exponent:7/4.
New complete I exponent:7/4. Target:3/2. No numerical diagnostics used.
Certified boundary:7/8. Active boundary target:<=3/4.
Paper label:`sec:carmichael-actual-carrier-transfer`.
Receipt:[actual carrier and phase transfer](verification/carmichael-actual-carrier-transfer.json).


## Sextic phases and signed unit means (2026-10-29)

Maintained owners: `CarmichaelSexticTransfer.lean` and
`CarmichaelEisensteinUnitMean.lean`. All19 declarations below compiled;
the14 earlier focused axiom outputs were reused unchanged and the5 new
proofs received fresh standard-only axiom checks.

| Owner namespace | Declaration | Exact claim scope | Status |
| --- | --- | --- | --- |
| `CarmichaelSexticTransfer` | `residual_as_cube` | The complete residual character is the level change of the cube. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `sextic_residual_quadratic` | Every sextic base character has quadratic residual, including the principal case. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `sextic_residual_real` | The quadratic residual equals its conjugate, including nonunit zeros. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `general_companion_ratio` | Every residue ratio retains the exact residual coefficient. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `general_ratio_pair` | Both phase rows and every complex kernel stay coupled in the exact ratio identity. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `shifted_norm_clock_monotone` | The positive-part norm clock is monotone for every signed integer shift. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `shifted_norm_clock_input` | Each admissible affine input gives the exact cubic norm clock. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `shifted_norm_clock_nonpositive` | Every invalid affine input has zero extended clock. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `shifted_carrier_zero_nonpositive` | The actual compensated carrier vanishes on the invalid-input extension. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `shifted_carrier_rescaled_variation` | The actual shifted/dilated carrier has uniform variation at most 21/4. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `residual_nonprincipal_of_odd` | Odd base characters have nonprincipal residual without an added phase assumption. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `neutral_exponents` | The squarefree preliminary neutral classification is exact under both bit bounds. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `neutral_factorization` | The preliminary all-prime squarefree valuation classification retains finite support. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `neutral_mask_support` | Even neutral rows retain their exact nonunit-mask support. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `gauss_neutral_exponents` | The unrestricted Gauss row permits sixth powers under the actual local support conditions. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `gauss_neutral_factorization` | All prime valuations have s=c*v^6, n=h^2 and the required disjointness. | Proved; focused axiom audit passed. |
| `CarmichaelSexticTransfer` | `gauss_neutral_mask_support` | The abstract neutral character product retains sixth-power prime support; full Gauss support has separate Ramanujan terms. | Proved; focused axiom audit passed. |
| `CarmichaelEisensteinUnitMean` | `periodic_zero_mean_uniform` | The full zero mode cancels before a scale-uniform signed Eisenstein frequency bound. | Proved; focused axiom audit passed. |
| `CarmichaelEisensteinUnitMean` | `nonprincipal_character_uniform` | Nonprincipal residue characters discharge mean zero without reality or primitivity. | Proved; focused axiom audit passed. |

The full Gauss classification assumes the displayed frequency-support
and character zero-mask conditions; it does not assert that they suffice
for a nonzero Gauss sum. Only the coefficient index c is squarefree.
The modulus index s is unrestricted. The character-product support is
c+v+h; the full imprimitive Gauss summand instead keeps the original
c*h coprimality mask and the separate Ramanujan divisibilities on v^6.
No v-coprimality mask is imposed on those nonunit frequency terms.
The signed frequency bound is uniform at every positive physical scale;
its conductor cost is the explicit sum of absolute residue weights.
Nonprincipality, rather than a reality or primitivity assumption,
discharges the zero mean. The cubic residual itself is principal and
is not passed to the nonprincipal theorem without the separate source
twist.

Open consumers: the full masked dilation, imprimitive Ramanujan pairs,
source-unit summation, moving Hecke/norm adapter, independent signed
small-square core estimate, and unbounded uniform Abel limit. The
fixed-support physical transfer and all compensation cross terms remain
in force. No source-unit or rational C_G estimate is inferred solely
from the frequency-row bound.

Benchmark status: exact phase/window qualifications and a signed uniform
frequency estimate proved; complete I exponent unchanged at7/4 (target3/2).
Certified zero-free boundary unchanged at7/8 (target<=3/4).
No finite numerical diagnostics were used.
Paper label:`sec:carmichael-sextic-unit-mean`.
Receipt:[sextic phases and signed unit means](verification/carmichael-sextic-unit-mean.json).


## Full masked and forced-ideal frequency estimates (2026-10-29)

Maintained owner: `CarmichaelEisensteinMaskedMean.lean`.
All7 declarations compiled. Four unchanged proof audits were reused;
the norm lemma and both strengthened signed bounds received fresh
standard-only axiom checks.

| Declaration | Exact scope | Status |
| --- | --- | --- |
| `ideal_moebius_norm_le_one` | Every exact ideal Mobius coefficient has modulus at most one. | Proved; focused axiom audit passed. |
| `residue_character_norm_le_one` | Every finite residue character has modulus at most one, including nonunit zeros. | Proved; focused axiom audit passed. |
| `masked_nonprincipal_character_uniform` | The full masked signed mean is bounded by C*p(W)*B_xi*2^card(S) at every positive scale. | Proved; focused axiom audit passed. |
| `row_mask_norm_le_one` | The actual complete prime-ideal mask has modulus at most one. | Proved; focused axiom audit passed. |
| `row_mask_multiplicative` | Prime-mask multiplicativity is exact, including every nonunit. | Proved; focused axiom audit passed. |
| `ideal_masked_frequency_dilation` | Every nonzero forced frequency ideal transfers with its actual mask scalar, character phase and rescaled norm argument. | Proved; focused axiom audit passed. |
| `ideal_divisible_masked_character_bound` | The same linear residue-mass bound holds uniformly for every nonzero forced ideal and every positive scale. | Proved; focused axiom audit passed. |

The exact dilation keeps M_S(g_D)*xi(g_D) and applies to every nonzero
ideal D, including all overlaps with the mask. Both signed estimates
are uniform for K>0 with explicit cost B_xi*2^card(S); neither an extra
residue-mass power nor an unstated conductor constant is introduced.
The character-product support c+v+h is distinct from the original
imprimitive Gauss mask c*h and the Ramanujan divisibilities on v^6.
The earlier paper, ledger and receipt now explicitly record this distinction;
no Lean theorem statement was invalidated by the wording correction.

Open: full source Gauss-to-Ramanujan identification and general-frequency
unit transport, all source-row sums and height bounds, moving Hecke/norm
adapter, independent signed small-square estimate, and the uniform Abel
limit with every compensation term. This is a proved signed frequency
estimate, not a complete source-unit or rational C_G estimate.

Benchmark status: full finite mask and all forced ideals handled at the
frequency-row level. Complete I exponent remains7/4 (target3/2); certified
boundary remains7/8 (target<=3/4). No finite numerical diagnostics used.
Paper label:`sec:carmichael-masked-frequency-dilation`.
Receipt:[full masked and forced-ideal means](verification/carmichael-masked-frequency-dilation.json).


## Primitive conductor saving in the signed frequency row (2026-10-29)

Maintained owner: `CarmichaelEisensteinPrimeMean.lean`.
All5 declarations compiled and received fresh standard-only axiom checks.

| Declaration | Exact scope | Status |
| --- | --- | --- |
| `primitive_conductor_signed_mean` | All nonzero primitive conductors; actual trace primitivity discharged; signed mean bounded by C*p(W)*sqrt(q). | Proved; focused axiom audit passed. |
| `primitive_conductor_masked_mean` | All finite distinct maximal-ideal masks; explicit factor 2^card(S), every K>0. | Proved; focused axiom audit passed. |
| `primitive_conductor_forced_ideal_mean` | Every nonzero forced frequency ideal; all mask overlaps and dilation phases retained. | Proved; focused axiom audit passed. |
| `primitive_source_unit_forced_ideal_mean` | Exact source normalizer sqrt(q*X*Y); conductor cancels, with every positive denominator proved. | Proved; focused axiom audit passed. |
| `prime_conductor_signed_mean` | At maximal conductors, nonprincipality discharges multiplicative primitivity. | Proved; focused axiom audit passed. |

The conductor may be composite when the multiplicative character is
primitive on ideals. The actual additive trace is primitive for every
nonzero conductor, by the existing general trace provider. No RH
hypothesis is used. At maximal conductors only nonprincipality is needed.

The earlier residue-mass cost B_xi is replaced by sqrt(q). With source
Q=q*X*Y, its normalizer cancels this conductor cost exactly. The remaining
frequency-row bound is C*p(W)*2^card(S)/sqrt(X*Y), uniform in all K>0
and all nonzero forced ideals. Constants/seminorms are existential;
mask and window-height costs remain explicit.

Open consumers: exact full imprimitive Gauss-to-Ramanujan source transfer,
general-frequency unit transport, source outer sums and height seminorms,
moving Hecke/norm adapter, independent signed small-square core, and the
uniform Abel limit with every compensation term. No complete source-unit
or rational C_G bound is inferred from this frequency-row improvement.

Benchmark status: certified frequency coefficient cap improves from B_xi
to sqrt(q); complete I exponent remains7/4 (target3/2), and certified
zero-free boundary remains7/8 (target<=3/4). No finite numerical diagnostics.
Paper label:`sec:carmichael-primitive-frequency-mean`.
Receipt:[primitive conductor frequency estimate](verification/carmichael-primitive-frequency-mean.json).


## General-frequency principal Gauss and signed Ramanujan transfer (2026-10-29)

Maintained owner: `CarmichaelRamanujanFrequency.lean`.
All5 declarations compiled and received fresh standard-only axiom checks.

| Declaration | Exact scope | Status |
| --- | --- | --- |
| `prime_power_frequency_lift` | Every character and divisible frequency; exact norm fiber count at modulus p^(n+1). | Proved; focused axiom audit passed. |
| `prime_power_zero_eq_prime` | Level n=0 is the actual base Gauss sum. | Proved; focused axiom audit passed. |
| `principal_prime_gauss_general` | All frequencies, including zero; actual nontrivial trace condition discharged. | Proved; focused axiom audit passed. |
| `principal_prime_power_ramanujan` | Both neighboring divisibility indicators at every frequency; no prime-over2/3 exclusion needed for this principal identity. | Proved; focused axiom audit passed. |
| `ramanujan_weighted_tsum` | Every summable complex weight; full infinite sum transferred with both signs and without a norm inequality. | Proved; focused axiom audit passed. |

The Gauss modulus is p^(n+1). The exact principal factor is
N((p^n))*(N((p))*1_(p^(n+1)|H)-1_(p^n|H)); neither term is dropped.
The actual trace is nontrivial at every prime maximal modulus. This
principal statement does not assume good-lambda or residue characteristic
not2; separate nonprincipal sextic qualifications remain separate.
The infinite identity retains arbitrary complex weights and so does not
require a positivity or reality premise on compensation terms.

The full source unit frequency domain m=a^6*u (u=1 for the unit row)
is distinct from the local neutral-character sector. If xi^6=1 then
xi(a^6) is principal on units, even when xi itself is nonprincipal.
The previously compiled all-element nonprincipal mean is not applied to
that restricted row without the actual power-character qualification.
Any higher-order auxiliary twist must preserve the complete Euler quotient
and a nonzero zero-signal normalizer before an exponent is claimed.

Open: full supported CRT/ray collection, source outer signed sums and
height costs, the moving Hecke/norm adapter, independent signed low core,
and uniform unbounded Abel passage with all AA-AB-BA+BB terms.

Benchmark status: exact general-frequency and summable signed transfers
proved; no new complete I estimate. I exponent7/4 remains (target3/2),
and boundary7/8 remains (target<=3/4). No numerical diagnostics used.
Paper label:`sec:carmichael-ramanujan-frequency`.
Receipt:[general-frequency Ramanujan transfer](verification/carmichael-ramanujan-frequency.json).


## Signed coprime Euler coordinates and damped negative phases (2026-10-29)

Maintained owner: `CarmichaelCoprimeSignedWave.lean`.
All16 declarations compiled and received fresh standard-only axiom checks.

| Declaration | Exact scope | Status |
| --- | --- | --- |
| `local_signed_factorization` | Exact local factor, with uv, both reciprocal factors and amplifier correction retained. | Proved; focused axiom audit passed. |
| `numerator_norm_square` | Exact real and imaginary phase-square identity. | Proved; focused axiom audit passed. |
| `local_gap_square` | Exact squared gap with both denominators. | Proved; focused axiom audit passed. |
| `local_reverse_comparison` | Weak comparison of a nonnegative diagonal and the off-diagonal modulus. | Proved; focused axiom audit passed. |
| `local_reverse_comparison_strict` | Strict gap at a nonzero local phase. | Proved; focused axiom audit passed. |
| `localDiagonal_pos_of_bounds` | Positive diagonal for 0<=a<=5/4 and norm(z)<=3/10. | Proved; focused axiom audit passed. |
| `finite_product_reverse_comparison` | Every finite supported product with nonnegative diagonals. | Proved; focused axiom audit passed. |
| `finite_product_reverse_comparison_strict` | Strict full finite product, retaining every coordinate. | Proved; focused axiom audit passed. |
| `cancellingPhase_properties` | Exact unit phase -conj(c)/norm(c) and real value -norm(c). | Proved; focused axiom audit passed. |
| `norm_one_sub_square` | Exact diagonal damping identity. | Proved; focused axiom audit passed. |
| `compensatedResponse_expand` | All AA, AB, BA and BB terms before estimation. | Proved; focused axiom audit passed. |
| `compensatedResponse_zero` | Exact undamped response. | Proved; focused axiom audit passed. |
| `damping_remainder_bound` | Norm estimate only on the explicit quadratic damping remainder. | Proved; focused axiom audit passed. |
| `compensatedResponse_upper_remainder` | Complete signed response with an explicit upper error. | Proved; focused axiom audit passed. |
| `compensatedResponse_negative` | Negative phase survives norm(w)<=1 and 6*(d+norm(c))*norm(w)<=norm(c)-d. | Proved; focused axiom audit passed. |
| `finite_product_compensated_negative` | Complete finite signed-product theorem with every compensation term. | Proved; focused axiom audit passed. |

The off-diagonal Euler correction has modulus strictly larger than the
positive diagonal product when one retained local phase is nonreal.
Choosing its opposite unit phase gives a negative response. The full
AA-AB-BA+BB expression remains negative under the stated explicit damping
condition. A norm is applied only to this separate damping remainder.

The finite Euler-coordinate products are not identified with the physical
Abel C_G. Infinite-product nonvanishing, the zero-isolating test-window
transfer, the actual prime-sampled adapter and the independent signed
high-native estimate remain open. This theorem alone does not establish
negative excursions of the full arithmetic packet.

Benchmark status: finite signed sign-control proved; no complete arithmetic
power improvement. Complete I exponent7/4 remains (target3/2), and
boundary7/8 remains (target<=3/4). No numerical diagnostics used.
Paper label:`sec:carmichael-coprime-signed-wave`.
Receipt:[signed Euler-coordinate comparison](verification/carmichael-coprime-signed-wave.json).

## Target-sized nonsquarefree rational high remainder (2026-10-29)

Maintained owner: `CarmichaelSquarefreeHighRemainder.lean`.
All10 public declarations compiled and received fresh standard-only axiom checks.

| Declaration | Exact scope | Status |
| --- | --- | --- |
| `rational_unit_squarefree_native` | Exact reconstruction with squarefree full rational inputs; all original Mobius weights retained. | Proved; focused axiom audit passed. |
| `squarefree_low_high_split` | Complete supported partition at ac<=T. | Proved; focused axiom audit passed. |
| `nonsquarefree_high_cancellation` | High minus projected high equals projected low minus original low, with signs intact. | Proved; focused axiom audit passed. |
| `squarefree_native_term_factorization` | Exact squarefree companion row with both full H*a*c masks. | Proved; focused axiom audit passed. |
| `squarefree_native_term_bound` | Actual cubic companion cancellation with explicit divisor and rescaled-variation caps. | Proved; focused axiom audit passed. |
| `low_squarefree_native_packet_bound` | Complete low projected region bounded by 2*(3q)^2*M^6*V^2*H_N^6*N*sqrt(T). | Proved; focused axiom audit passed. |
| `low_squarefree_native_packet_subpower` | Uniform subpower mask dependence; no divisor cap remains. | Proved; focused axiom audit passed. |
| `schwartz_low_squarefree_native_packet_subpower` | Physical N=4D,T=D; all rescaled variations discharged, including empty prefixes. | Proved; focused axiom audit passed. |
| `rational_unit_squarefree_high_remainder` | Rational unit minus signed squarefree high core is O_eps((3q)^2*S(f)^2*(4HD)^eps*D^(3/2)). | Proved; focused axiom audit passed. |
| `nonsquarefree_high_subpower` | Entire nonsquarefree rational high contribution has the same target-sized bound. | Proved; focused axiom audit passed. |

The arithmetic estimates are unconditional, for every nonzero modulus q,
chi^3=1, finite prime amplifier G, positive H,D and complex Schwartz f.
No primitivity assumption or exclusion of 2 or 3 is made.
The exact coefficient, amplifier, both masks and compensation cross terms
are retained. S(f) is seminorm(0,0)(f)+8*schwartzLipschitzConstant(f).
For changing compensated windows, S(f_D)^2 remains an explicit cost.

The projection concerns rational inputs a*b,c*d. It does not make the
separate dual Gauss frequency m=a^6 squarefree or nonprincipal.
The signed projected high core, actual prime-sampled quotient transfer
and uniform unbounded Abel passage remain open.

Benchmark status: new unconditional component estimate at exponent3/2;
complete I exponent stays7/4 and certified boundary stays7/8.
Previously no separate maintained target-sized nonsquarefree-high bound
was available. The surviving squarefree high core remains unestimated.
No numerical diagnostics or completed unknown sums are used; no new
complete-bound failure domain can be asserted.
Paper label:`sec:carmichael-squarefree-high-remainder`.
Receipt:[squarefree high remainder](verification/carmichael-squarefree-high-remainder.json).

## Power compensation in complete compact character portfolios (2026-10-29)

Maintained owner: `CarmichaelPowerCompensation.lean`.
All four public declarations compiled and received focused standard-only axiom checks.

| Declaration | Exact scope | Status |
| --- | --- | --- |
| `character_power_compensation_bound` | Complete reference/cross remainder for one actual depleted smooth character row; uniform in every power d, divisor cutoff N and D>0. | Proved; focused axiom audit passed. |
| `portfolio_power_compensation_bound` | Same estimate for the full complex finite character portfolio; all mixed-character terms retained. | Proved; focused axiom audit passed. |
| `portfolio_quartic_compensation_subpower` | Complete AB+BA+BB remainder is O(D^(11/8+eps)), uniformly in N and D>=1. | Proved; focused axiom audit passed. |
| `portfolio_octic_compensation_subpower` | Complete eighth-power reference remainder is O(D^(7/8+eps)), uniformly in N and D>=1. | Proved; focused axiom audit passed. |

Rows retain mu(h*m), chi(h*m), the fixed coprimality mask and the actual
complex window. Every positive divisor h<=N is included. The portfolio is
combined before compensation and squaring. Only the exact reference
remainder is bounded; AA remains signed and unestimated at the target.

Constants depend on the fixed modulus, characters, complex weights,
depletion mask, smooth compact window and exponent slack, independently
of d,N,D. The statement includes q=1, all nonunits and N=0. It assumes
q,r>0 and smooth support in [lo,hi] with lo>0 and hi>=0.
No noncompact-carrier, product-amplifier, growing-conductor or full
prime-sampled/Abel adapter is asserted.

Benchmark status: new unconditional complete reference-remainder estimate
on this specified compact-window packet. Quartic exponent11/8 and
octic exponent7/8 are proved; full I exponent7/4 and boundary7/8 remain
unchanged. No numerical experiments or completions of unknown sums.
No complete improved-bound failure domain is available.
Paper label:`sec:carmichael-power-compensation`.
Receipt:[power-compensation estimates](verification/carmichael-power-compensation.json).


## Unit Euler remainder after exact angular-factor extraction (2026-10-29)

Maintained owner: `CarmichaelUnitEulerRenormalization.lean`.
All ten public declarations compiled and received focused standard-only axiom checks.

| Declaration | Exact scope | Status |
| --- | --- | --- |
| `rational_slice_factorization` | Exact signed rational factorization at v=w=1; every denominator hypothesis explicit. | Proved; focused axiom audit passed. |
| `unramified_slice_factorization` | Factorization of the actual unramifiedClosed coordinates; angular A retained. | Proved; focused axiom audit passed. |
| `local_remainder_defect` | Uniform remainder defect <=4 Q^(-3/2) for Q>=4, Re(s)>=3/4 and Re(s+z)>=3/4. | Proved; focused axiom audit passed. |
| `local_remainder_lower` | Uniform local remainder norm >=1/2 on the same full domain. | Proved; focused axiom audit passed. |
| `local_remainder_analyticAt` | Analyticity along analytic s,z paths; actual denominator nonvanishing discharged. | Proved; focused axiom audit passed. |
| `remainderProduct_ne_zero` | Nonvanishing infinite remainder product from summable defects and inverse defects. | Proved; focused axiom audit passed. |
| `analyticOnNhd_remainderProduct` | Analytic infinite product along every admissible analytic path, by normal convergence. | Proved; focused axiom audit passed. |
| `finite_slice_factorization` | Exact factorization at every finite cutoff, with extracted factors retained. | Proved; focused axiom audit passed. |
| `source_remainderProduct_ne_zero` | Nonvanishing for actual source angular/character phases outside arbitrary finite S and norm<exp(2). | Proved; focused axiom audit passed. |
| `analyticOnNhd_sourceRemainderProduct` | Analyticity for that actual-source remainder product on the enlarged path region. | Proved; focused axiom audit passed. |

The exact factor is F=(1-Q^(-1)*V)/(1-R)*J, with
J=1+Q^(-1)*(D-R)/(1-D), D=eta*Q^(-s), V=Q^(-6*z),
and R=A*Q^(4-6*s-6*z). The actual A retains the angular sixth-power
phase and the source character. It is not set to one.

The local defect/lower bounds require Q>=4 and |A|,|eta|<=1.
The generic infinite-product results require sum Q^(-3/2)<infinity.
That summability is discharged for the actual source prime ideals with
norm>=exp(2), outside any finite S. Smaller norms and ramified factors
remain explicit outside this product. No independent restriction Re(z)>0
is needed for J when Re(s)>=3/4 and Re(s+z)>=3/4.

Benchmark status: new proved estimate and nonvanishing for the explicitly
renormalized remainder; the extracted angular Euler block and full source
reciprocal L factor remain. This is not a bound for the unextracted factor,
the complete exceptional-frequency row, or its physical/Abel consumer.
Full I exponent7/4 and certified boundary7/8 remain unchanged; required
exponents are3/2 and at most3/4. No finite diagnostics or completed unknown
signed sums are used. A complete improved-bound failure domain is unavailable.
Paper label:`sec:carmichael-unit-euler-renormalization`.
Receipt:[unit Euler renormalization](verification/carmichael-unit-euler-renormalization.json).


## Convex noncancellation in the critical Euler wedge (2026-10-29)

Maintained owner: `CarmichaelEulerCriticalWedge.lean`.
All thirteen public declarations compiled and received focused standard-only axiom checks.

| Declaration | Exact scope | Status |
| --- | --- | --- |
| `convex_numerator_re_lower` | Exact lower bound for the real part of the complete convex numerator, retaining both coordinates. | Proved; focused axiom audit passed. |
| `convex_numerator_re_pos` | Strict positive real part when both coordinates lie in the open unit disk. | Proved; focused axiom audit passed. |
| `local_remainder_lower_wedge` | Uniform norm(J)>=c_delta/2 for Q>=2 on the full fixed-margin wedge. | Proved; focused axiom audit passed. |
| `local_remainder_defect_wedge` | Uniform norm(J-1)<=(2/c_delta) Q^(-1-delta), with all constants explicit. | Proved; focused axiom audit passed. |
| `local_remainder_analyticAt_wedge` | Analyticity of the actual local remainder along admissible analytic paths. | Proved; focused axiom audit passed. |
| `remainderProduct_ne_zero_wedge` | Nonzero infinite product from summable defects and inverse defects on that wedge. | Proved; focused axiom audit passed. |
| `analyticOnNhd_remainderProduct_wedge` | Normal convergence and analytic infinite product on each fixed-margin open path region. | Proved; focused axiom audit passed. |
| `source_remainderProduct_ne_zero_wedge` | Actual-source remainder product nonzero for Re(s)>0 and Re(s+z)>2/3. | Proved; focused axiom audit passed. |
| `analyticOnNhd_sourceRemainderProduct_wedge` | Actual-source analytic product along fixed-margin analytic paths. | Proved; focused axiom audit passed. |
| `source_principal_remainder_analytic` | Principal-residue actual-source remainder analytic on the full half-plane Re(s)>1/2. | Proved; focused axiom audit passed. |
| `source_principal_remainder_ne_zero` | Principal-residue actual-source remainder nonzero on that same full half-plane. | Proved; focused axiom audit passed. |
| `principal_factor_ne_zero_critical` | Full rational principal local factor nonzero for every Q>=2, Re(s)>1/2 and unit-bounded phases. | Proved; focused axiom audit passed. |
| `source_principal_factor_ne_zero_critical` | Every actual idealClosedCorrection local principal factor nonzero for Re(s)>1/2; small norms included. | Proved; focused axiom audit passed. |

Here c_delta=1-2^(-delta)>0 and delta is any positive real with
delta<=Re(s) and delta<=6*Re(s+z)-4. Bounds include Q=2 and all
unit-bounded phases. The positive-real-part claim is for
N=1-(1-t)D-tR; it is not a positivity claim about J or the readout.
The generic product requires sum Q^(-1-delta)<infinity; this is
discharged for actual high source prime ideals and every delta>0.
That product uses the existing norm>=exp(2) family outside arbitrary
finite S. The separate local correction theorem covers every source
prime norm>=2, without adding any small-prime deletion.

Benchmark status: the same actual source remainder is now analytic and
nonzero throughout the principal half-plane Re(s)>1/2, extending the
former fixed3/4 remainder region. Constants depend on the positive
margin and are not uniform as delta tends to zero. The extracted angular
block and reciprocal L function remain. No nonvanishing of their full
infinite product below its proved convergence region, signed high AA
estimate, physical-window transfer or Abel estimate is asserted.
Full I exponent7/4 and boundary7/8 remain unchanged; required3/2 and
at most3/4 remain open. No finite diagnostics or unknown-sum completions
are used; an improved complete-bound failure domain is unavailable.
Paper label:`sec:carmichael-euler-critical-wedge`.
Receipt:[critical Euler wedge](verification/carmichael-euler-critical-wedge.json).


## Native integer CRT mass and complete divisor coverage (2026-10-30)

Maintained owners: `Assembly/PeriodicPairAffinity.lean`,
`Assembly/FiniteFieldPairSubperiodMass.lean`, and
`Assembly/FiniteFieldPairIntegerCRT.lean`.
All 31 theorem proofs compiled. Their 31 closures and the 11 new definitions
received a fresh audit: only `propext`, `Classical.choice`, and `Quot.sound`.
Previously checked unchanged providers were not re-audited.

The first 7 rows belong to PeriodicPairAffinity, the next 7 to
FiniteFieldPairSubperiodMass, and the final 17 to FiniteFieldPairIntegerCRT.

| Declaration | Exact scope | Status |
| --- | --- | --- |
| `shifted_period_mass` | Every shifted complete period has the original full-period sum. | Proved; compiled; new-only axiom audit passed. |
| `whole_period_mass` | Exact mass on any integer number of periods. | Proved; compiled; new-only axiom audit passed. |
| `partial_period_mass` | Nonnegative residual segment is bounded by one full period. | Proved; compiled; new-only axiom audit passed. |
| `interval_mass_bounds` | Floor-period lower and upper mass bounds at every integer origin. | Proved; compiled; new-only axiom audit passed. |
| `interval_mass_positive` | Positive interval mass for N>=M and positive full mean. | Proved; compiled; new-only axiom audit passed. |
| `period_affinity_nonneg` | Nonnegative complete-period affinity. | Proved; compiled; new-only axiom audit passed. |
| `interval_affinity_le_twice` | Both normalization masses positive and normalized interval affinity <=2 times complete affinity for N>=M. | Proved; compiled; new-only axiom audit passed. |
| `mass_deficit_square_bound` | Exact complement deficit squared <= missingCount times full second moment. | Proved; compiled; new-only axiom audit passed. |
| `subset_mass_lower` | Full mean minus square-root complement energy bounds every finite subset mass. | Proved; compiled; new-only axiom audit passed. |
| `subset_mass_positive` | Strict positive mass under the explicit complement-energy condition. | Proved; compiled; new-only axiom audit passed. |
| `raw_packet_mean` | Exact full-product mean for odd fields, nonzero shifts and q>=16. | Proved; compiled; new-only axiom audit passed. |
| `raw_packet_square_sum` | Exact full raw joint energy from the existing normalized product-moment provider. | Proved; compiled; new-only axiom audit passed. |
| `raw_subset_mass_lower` | Finite-subset lower bound retaining the exact raw product energy. | Proved; compiled; new-only axiom audit passed. |
| `raw_subset_mass_positive` | Positive raw subset mass when missingCount*rawEnergy<M. | Proved; compiled; new-only axiom audit passed. |
| `zmod_sum_range` | Canonical natural representatives enumerate ZMod M exactly. | Proved; compiled; new-only axiom audit passed. |
| `crt_natCast` | Canonical ring CRT sends n to the actual tuple of n modulo each modulus. | Proved; compiled; new-only axiom audit passed. |
| `crt_period_sum` | Exact integer complete-period sum equals the finite product-space sum. | Proved; compiled; new-only axiom audit passed. |
| `sampled_periodic` | Actual integer evaluation is periodic with product modulus. | Proved; compiled; new-only axiom audit passed. |
| `window_injective` | Every consecutive window of length N<=M has injective CRT encoding. | Proved; compiled; new-only axiom audit passed. |
| `window_image_card` | Its finite image has cardinality exactly N. | Proved; compiled; new-only axiom audit passed. |
| `window_image_sum` | Its subset sum equals the consecutive integer interval mass. | Proved; compiled; new-only axiom audit passed. |
| `residue_space_card` | The complete residue product has cardinality M. | Proved; compiled; new-only axiom audit passed. |
| `missing_window_count` | The omitted residue set has cardinality exactly M-N. | Proved; compiled; new-only axiom audit passed. |
| `integer_subperiod_mass_lower` | For N<=M, interval mass >=M-sqrt((M-N)*M*E), at every integer origin. | Proved; compiled; new-only axiom audit passed. |
| `integer_subperiod_mass_positive` | Strict positive integer mass when (M-N)*E<M. | Proved; compiled; new-only axiom audit passed. |
| `integer_long_interval_affinity` | Native integer normalized comparison with factor2 and both positive masses, N>=M. | Proved; compiled; new-only axiom audit passed. |
| `raw_integer_subperiod_mass_lower` | Actual raw prime-field product evaluated at the same integer shift h; exact known energy. | Proved; compiled; new-only axiom audit passed. |
| `raw_integer_subperiod_mass_positive` | Same actual raw integer product and explicit strict positivity condition. | Proved; compiled; new-only axiom audit passed. |
| `prime_pair_of_nonzero_packet` | All primes p<=Y covered, all forbidden rows zero, and Y<n,n+h<=Y^2 imply both endpoints prime. | Proved; compiled; new-only axiom audit passed. |
| `prime_pair_of_positive_integer_mass` | Positive native interval mass with complete divisor coverage produces an actual integer prime pair. | Proved; compiled; new-only axiom audit passed. |
| `prime_pair_of_subperiod_energy` | Complete signed mean/energy bound composed with coverage produces an actual integer prime pair under (M-N)*E<M. | Proved; compiled; new-only axiom audit passed. |

The generic CRT moduli are positive and pairwise coprime; the same native
integer is used in every coordinate. The two raw specializations additionally
require prime moduli, odd characteristic, p>=16 and h nonzero modulo each p.
Those specializations alone omit small primes and p dividing h. The independent
coverage consumer explicitly requires every prime through Y and both forbidden
rows for every modulus. It does not silently infer coverage from product size.
All sums and complements are over the named complete finite residue space.

Benchmark status: proved finite-window transfer and a sufficient integer
prime-pair consumer; no new unbounded positive-mass estimate.
Old bound: nonnegative raw mass >=0. New bound: raw mass >=
M-sqrt((M-N)*M*E), with the old zero bound still available.
Components: full signed mean M; exact missing cardinality M-N; full raw
product energy E=prod(1+(3p+d)/(p*(p-d))), with each raw d in {1,3,5}.
Actuals: no numerical experiments or unknown-sum completions.
First nonpositive domain of this sufficient lower bound: (M-N)*E>=M.
That is not a statement that actual mass vanishes there. The required natural
height range is Y<A and A+N-1+h<=Y^2 for N>0, whereas this test proves
positivity only for N>M*(1-1/E). No estimate reaching the former range on
unbounded cutoffs is claimed. No new H1 or RH/QRH boundary follows.

The generic periodic and complement inequalities are elementary and are not
claimed as independently novel classical theorems. Their role is an exact
consumer for the specific raw pair moments and probability-law comparisons.
Paper label: `sec:integer-crt-pair-mass`.

## Exact optimal quadratic-character approximation (2026-10-30)

Maintained owners: `Assembly/FiniteFieldCharacterProjection.lean` and
`Assembly/FiniteFieldOptimalCharacterLaw.lean`. All 26 theorem proofs
compiled; a new-only audit of their closures and the 4 definitions found
only `propext`, `Classical.choice`, and `Quot.sound`.

The common raw-law domain is an odd finite field K, q=card K>=16,
chi(-1)=-1, and h nonzero. The first 13 structural identities have the
weaker hypotheses printed in their declarations. Every sum is over the
complete finite field, including the two explicitly completed singular rows.
The first 17 rows belong to FiniteFieldCharacterProjection, the final 9
to FiniteFieldOptimalCharacterLaw.

| Declaration | Exact scope | Status |
| --- | --- | --- |
| `masked_trace_good` | Trace completion equals the actual trace on both nonexceptional rows. | Proved; compiled; new-only axiom audit passed. |
| `masked_trace_zero` | Completion is exactly zero on c=0. | Proved; compiled; new-only axiom audit passed. |
| `masked_trace_neg_shift` | Completion is exactly zero on c=-h. | Proved; compiled; new-only axiom audit passed. |
| `masked_trace_pairing` | Full signed pairing retains both actual singular corrections. | Proved; compiled; new-only axiom audit passed. |
| `trace_reflection` | Actual trace reverses under c maps to -h-c when chi(-1)=-1. | Proved; compiled; new-only axiom audit passed. |
| `trace_two_character_sum` | Exact trace pairing with the product of the two quadratic characters is zero. | Proved; compiled; new-only axiom audit passed. |
| `masked_trace_sum` | Completed trace has total sum zero. | Proved; compiled; new-only axiom audit passed. |
| `masked_trace_left_character_sum` | Completed trace is orthogonal to chi(c), including both removed rows. | Proved; compiled; new-only axiom audit passed. |
| `masked_trace_right_character_sum` | Completed trace is orthogonal to chi(c+h), including both removed rows. | Proved; compiled; new-only axiom audit passed. |
| `masked_trace_two_character_sum` | Completed trace is orthogonal to chi(c)*chi(c+h). | Proved; compiled; new-only axiom audit passed. |
| `masked_trace_square_sum` | Exact completed square sum is (q-3)*(q+1), without Hasse. | Proved; compiled; new-only axiom audit passed. |
| `masked_trace_polynomial_sum` | Orthogonality to every real bilinear polynomial in the two signs. | Proved; compiled; new-only axiom audit passed. |
| `masked_trace_table_sum` | Orthogonality to every arbitrary real function of both signs; no positivity or boundedness hypothesis. | Proved; compiled; new-only axiom audit passed. |
| `raw_density_decomposition` | Raw density equals optimalDensity minus the completed trace divided by q-3. | Proved; compiled; new-only axiom audit passed. |
| `raw_projection_pythagoras` | Exact universal Pythagorean identity, with residual (q+1)/(q*(q-3)). | Proved; compiled; new-only axiom audit passed. |
| `character_only_error_lower` | Sharp lower squared error for every two-sign surrogate. | Proved; compiled; new-only axiom audit passed. |
| `optimal_density_error` | The explicit optimal density attains that exact minimum. | Proved; compiled; new-only axiom audit passed. |
| `raw_optimal_sign_statistics` | Every two-sign statistic has identical expectations under raw and optimal laws. | Proved; compiled; new-only axiom audit passed. |
| `sum_optimal_density` | The explicit optimal density has total sum q. | Proved; compiled; new-only axiom audit passed. |
| `optimal_density_good_bounds` | Optimal density lies in [1,2] on admissible rows. | Proved; compiled; new-only axiom audit passed. |
| `optimal_density_bounds` | Optimal density is nonnegative and at most2 everywhere. | Proved; compiled; new-only axiom audit passed. |
| `optimal_density_square_shift` | On admissible rows, square shift gives the correction using chi(c) alone. | Proved; compiled; new-only axiom audit passed. |
| `optimal_density_nonsquare_shift` | On admissible rows, nonsquare shift gives the correction using chi(c+h) alone. | Proved; compiled; new-only axiom audit passed. |
| `character_only_error_reciprocal` | Every arbitrary two-sign surrogate has mean-square error at least1/q. | Proved; compiled; new-only axiom audit passed. |
| `character_only_affinity_upper` | Every two-sign density with meanq and range[0,2] has raw affinity at most1-1/(32q). | Proved; compiled; new-only axiom audit passed. |
| `raw_optimal_affinity_upper` | The normalized optimal density satisfies the same reciprocal affinity loss. | Proved; compiled; new-only axiom audit passed. |

For every real tableg of (chi(c),chi(c+h)), the exact squared-distance
minimum is b_q=(q+1)/(q*(q-3)), attained by the explicit masked optimal
law. Pythagoras reads D(raw,g)=b_q+D(optimal,g). No positivity, mean or
coefficient restriction on g is required for this minimum. The additional
affinity theorem requires 0<=g<=2 and sum g=q. Its bound applies to this
entire class, not just one preselected flat or twist-averaged model.
The optimal law retains both zero masks; its correction on admissible rows
uses chi(c) when chi(h)=1, and chi(c+h) when chi(h)=-1.

Benchmark status: exact finite-field approximation optimum proved.
Old bound: comparisons with named flat and averaged laws; no installed
universal optimum over arbitrary nonlinear two-sign models.
New bound: inf_g D(raw,g)=b_q>=1/q; bounded normalized two-sign models
have affinity<=1-1/(32q).
Components: the exact signed first moments -1, both singular corrections,
trace-reflection cancellation, and completed square sum (q-3)*(q+1).
Actuals: the initial nonzero cell-mean candidate failed at p7,h1,cell--;
the corrected zero means and square identity passed 128 nonzero-shift
frames in prime fields7,11,19,23,31,43. These were falsification checks;
the uniform theorem is supplied by the real compiled proofs.
First nonpositive domain: none within q>=16 for b_q; this does not give
a positive natural-height integer packet mass. Its previous lower bound0
and the unbounded prime-pair recurrence problem remain unchanged.

Scope: the observable algebra is generated by the two named quadratic
characters, not by all Dirichlet characters or all arithmetic observables.
The result prevents replacing the raw elliptic fluctuations by an arbitrary
nonlinear function of those two signs with mean-square error o(1/q). It is
a complete-field theorem, not an incomplete integer-window estimate.
Classical Legendre sign symmetry and orthogonal projection are credited.
The model-specific optimum was not found in the checked public and live
private target records or the targeted primary literature search; general
priority remains unestablished. The matched Carmichael label-erasure owner
has different group-phase objects and is a completed input, not this target.
Paper label: `sec:optimal-character-pair-law`.

## Optimal joint character projection (2026-10-31)

Maintained owners: `Mathlib/Algebra/BigOperators/WeightedFiberProduct.lean`
and `Assembly/FiniteFieldJointCharacterProjection.lean`. All 19 theorem
proofs compile; a new-only audit of 27 declarations found only `propext`,
`Classical.choice`, and `Quot.sound`. No unchanged proof was re-audited.

The finite-field domain is any finite family of odd fields, each q>=16,
chi(-1)=-1, with a nonzero shift in each field. The complete uniform product
measure is essential. Competitors are arbitrary real functions of the full
vector of two-sign profiles; positivity, normalization and independence
are not assumed. The two generic transport declarations hold over any
commutative semiring and arbitrary finite coordinate and label types.

| Declaration | Exact scope | Status |
| --- | --- | --- |
| `Fintype.sum_prod_mul_comp_eq` | Exact finite weighted pushforward with the complete joint statistic retained. | Proved; compiled; new-only axiom audit passed. |
| `Fintype.sum_prod_mul_comp_eq_of_fiber_sums` | Coordinate fiber-mass equality gives equality for every coupled joint statistic. | Proved; compiled; new-only axiom audit passed. |
| `character_label_eq` | Finite observed-label equality agrees exactly with equality of both quadratic signs. | Proved; compiled; new-only axiom audit passed. |
| `raw_optimal_label_mass` | Every actual sign fiber has identical raw and projected mass, including singular rows. | Proved; compiled; new-only axiom audit passed. |
| `raw_second_moment_exact` | Raw second moment equals (q^2+3)/(q*(q-3)) when chi(-1)=-1. | Proved; compiled; new-only axiom audit passed. |
| `optimal_second_moment_exact` | Projected second moment equals (q^2-q+2)/(q*(q-3)). | Proved; compiled; new-only axiom audit passed. |
| `raw_joint_character_statistics` | Every arbitrary coupled function of all two-sign profiles has equal raw and projected expectation. | Proved; compiled; new-only axiom audit passed. |
| `raw_joint_second_moment` | Exact product of the raw one-field second moments. | Proved; compiled; new-only axiom audit passed. |
| `optimal_joint_second_moment` | Exact product of the visible one-field second moments. | Proved; compiled; new-only axiom audit passed. |
| `joint_projection_pythagoras` | Full coupled error identity, retaining and canceling the exact mixed-statistic term. | Proved; compiled; new-only axiom audit passed. |
| `joint_character_error_lower` | Sharp universal error floor prod rawMoment minus prod visibleMoment. | Proved; compiled; new-only axiom audit passed. |
| `raw_moment_pos` | Positive raw energy factor throughout q>=16. | Proved; compiled; new-only axiom audit passed. |
| `moment_fraction_identity` | Exact visibleMoment=retainedFraction*rawMoment with all denominators checked. | Proved; compiled; new-only axiom audit passed. |
| `retained_fraction_bounds` | The exact retained fraction lies in (0,1-1/q] on q>=16. | Proved; compiled; new-only axiom audit passed. |
| `joint_relative_error_identity` | Exact relative-error numerator identity for every arbitrary joint character model. | Proved; compiled; new-only axiom audit passed. |
| `joint_relative_error_lower` | Universal normalized error floor (1-prod retainedFraction)*prod rawMoment. | Proved; compiled; new-only axiom audit passed. |
| `optimal_joint_table_comp` | The explicit joint sign table evaluates to the product projection. | Proved; compiled; new-only axiom audit passed. |
| `joint_projection_error_exact` | The product projection attains the complete coupled error floor. | Proved; compiled; new-only axiom audit passed. |
| `raw_joint_energy_pos` | Strict positivity of the raw product energy, including the empty-family case. | Proved; compiled; new-only axiom audit passed. |

The 8 audited definitions are `characterLabels`, `CharacterLabel`,
`characterLabel`, `rawMoment`, `visibleMoment`, `retainedFraction`,
`jointTable`, and `optimalJointTable`. The field-specific theorem names
above are in `PrimeFactorOscillations.FiniteFieldJointCharacterProjection`.

Benchmark status: exact complete-product approximation optimum proved.
Old bound: a one-field universal optimum and comparisons with named product
models; no installed exact optimum against every coupled sign statistic.
New bound: min_B E[(U-B)^2]/E[U^2] =
1-prod((q^2-q+2)/(q^2+3)), attained by the explicit product projection.
Components: exact local weighted sign-fiber masses; unrestricted joint
pushforward; raw moment (q^2+3)/(q*(q-3)); projected moment
(q^2-q+2)/(q*(q-3)); full mixed term E[UB-GB]=0.
Actuals: finite falsification passed 70 local nonzero-shift frames in
fields19,23,31 and 12 coupled frames in fields19 and23. These checks do
not certify the universal result; the maintained Lean proofs do.
First nonpositive domain: the empty index set has exact minimum0;
every nonempty admissible family has a positive error fraction because
0<retainedFraction<=1-1/q<1. This is an approximation error, not a lower
bound on integer prime-pair mass. The natural-height mass estimate,
integer recurrence, H1, and the installed QRH boundary7/8 are unchanged.

The earlier coupled twist-count theorem optimizes a different class:
mixtures of scaled pair counts. It does not establish this optimum over
the full joint two-sign algebra. General finite conditional expectation
and tensorization are classical; the specific raw-law Euler factor and
its application were not found in the checked target records or targeted
primary-source search. General literature priority remains unconfirmed.
Paper label: `sec:joint-character-projection`.

## Full raw pair covariance and signed window kernels (October 31)

All 21 theorem proofs and 3 definitions below are maintained and compiled.
The new-only axiom audit covers exactly these 24 declarations and reports
only propext, Classical.choice and Quot.sound. No unchanged declarations
were re-audited.

Candidate owner:
`PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairCovariance.lean`.
The following theorem names are in namespace `FiniteField`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `splitCubicPointTrace_reflection_neg_one` | proved and audited | odd field; chi(-1)=-1; arbitrary h,c |
| `splitCubicPointTrace_arithmetic_progression_zero` | proved and audited | odd field; chi(-1)=-1; arbitrary h |
| `sum_splitCubicPointTrace_shift_mul_char` | proved and audited | odd field; h nonzero; arbitrary k,v |
| `splitCubicPointTrace_shift_correlation` | proved and audited | odd field; h nonzero; arbitrary lag |
| `quadraticPairCorrelationKernel_zero` | proved and audited | any finite field; h nonzero |
| `quadraticPairCorrelationKernel_even` | proved and audited | any finite field; arbitrary h,k |
| `quadraticPairCorrelationKernel_adjacent` | proved and audited | odd field; chi(-1)=-1; h nonzero |
| `splitCubicPointTrace_adjacent_correlation` | proved and audited | odd field; chi(-1)=-1; h nonzero |
| `quadraticPairCount_first_order_completion` | proved and audited | odd field; h nonzero; both forbidden rows |
| `quadraticPair_linearized_shift_correlation` | proved and audited | odd field; h nonzero; arbitrary A,j,k |
| `completedQuadraticPairNumerator_shift_correlation` | proved and audited | odd field; chi(-1)=-1; h nonzero; every lag |
| `completedQuadraticPairNumerator_reflection` | proved and audited | odd field; chi(-1)=-1; arbitrary h,c |
| `quadraticPairCount_shift_completion` | proved and audited | odd field; h nonzero; every boundary intersection |
| `completedQuadraticPairNumerator_boundary_correction` | proved and audited | odd field; chi(-1)=-1; arbitrary h,k |
| `monicQuadraticPairCount_shift_correlation` | proved and audited | odd field; chi(-1)=-1; h nonzero; every lag |
| `monicQuadraticPairCount_adjacent_correlation` | proved and audited | odd field; chi(-1)=-1; h nonzero; exact chi(2) formula |

Assembly owner:
`PrimeFactorOscillations/Assembly/FiniteFieldRawPairCovariance.lean`.
The following names are in namespace
`PrimeFactorOscillations.FiniteFieldRawPairCovariance`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `covariance_count` | proved and audited | odd field; chi(-1)=-1; h nonzero; q>=16 |
| `covariance_adjacent` | proved and audited | same normalized domain; shared-endpoint lag |
| `covariance_shifted` | proved and audited | any finite field; arbitrary h,a,b |
| `packet_cross_moment` | proved and audited | arbitrary finite product; arbitrary shifts |
| `signed_window_second_moment` | proved and audited | arbitrary finite product and finite signed window; every cross term |

Definitions: `FiniteField.quadraticPairCorrelationKernel`,
`PrimeFactorOscillations.FiniteFieldRawPairCovariance.covariance` and
`PrimeFactorOscillations.FiniteFieldRawPairCovariance.shiftedPacket`.
Here covariance is explicitly the uncentered raw cross moment;
the centered covariance is that value minus 1 when the mean is 1.

benchmark_status: exact signed complete-product identities proved;
no improved integer-window bound claimed.
old_bound: the raw diagonal second moment was exact; general lag and
signed window off-diagonal terms had no installed explicit raw count formula.
new_bound: the full all-lag count formula is exact, and at lag h,
16*sum_c w(c)*w(c+h)=q^3-5*q^2+(5-4*chi(2))*q-9.
The normalized shared-endpoint value divides this by q*(q-3)^2.
components: quartic character kernel, both signed trace-character mixed
products, both singular-row subtractions, all boundary intersections,
and every signed product-window cross term.
actuals: falsification passed 156 local frames and 4444 all-lag frames
in the stated finite test domain, including the genuine extension field F27;
these are diagnostics, not the universal proof.
first_nonpositive_domain: unavailable for the unresolved integer-window
mass; no finite or infinite integer positivity range is asserted.

The required integer input remains a positive sum of the full prime
avoidance mask V_Y(n) on Y<n<=Y^2-h along unbounded Y, for fixed positive
even h. CRT complete-period support and a modulus larger than Y^2 do
not discharge this input. The previous natural-height mass estimate,
integer recurrence, H1 and certified QRH boundary 7/8 are unchanged.
All-lag exactness is currently specialized to chi(-1)=-1; the generic
product-window identity retains arbitrary finite fields without that
hypothesis. Literature priority beyond the targeted primary comparison
is unconfirmed. Paper label: `sec:raw-pair-covariance`.

## All-character raw covariance and exact twist compensation (October 31)

All 15 theorem proofs and 2 definitions below are maintained and compiled.
The affected candidate, assembly, public facade and full project closure compile.
The new-only audit covers exactly these 17 declarations and reports only
propext, Classical.choice and Quot.sound. Unchanged declarations were not
re-audited. This removes the preceding covariance theorem's chi(-1)=-1
restriction; it does not establish positive mass in an integer interval.

Candidate owner:
`PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairGeneralCovariance.lean`.
Names in the first table are in namespace `FiniteField`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `splitCubicPointTrace_reflection` | proved and audited | odd field; arbitrary h,c; exact chi(-1) factor |
| `quadraticPairCorrelationKernel_adjacent_general` | proved and audited | odd field; h nonzero; exact kernel -1-chi(-1) |
| `completed_trace_numerator_shift_correlation` | proved and audited | odd field; h nonzero; every lag; all signed mixed terms |
| `completedQuadraticPairNumerator_shift_correlation_general` | proved and audited | odd field; h nonzero; every lag and both character signs |
| `completedQuadraticPairNumerator_reflection_general` | proved and audited | odd field; arbitrary h,c; exact trace reflection |
| `completedQuadraticPairNumerator_boundary_correction_general` | proved and audited | odd field; arbitrary h,k; both singular-row subtractions |
| `monicQuadraticPairCount_shift_correlation_general` | proved and audited | odd field; h nonzero; every lag, including 0,h,-h; all intersections |
| `monicQuadraticPairCount_adjacent_correlation_general` | proved and audited | odd field; h nonzero; exact character and CM trace terms |
| `monicQuadraticPairCount_twist_compensated_adjacent` | proved and audited | odd field; h nonzero; every nonsquare dilation a |
| `compensatedQuadraticPairCrossMoment_gt_one` | proved and audited | real q>=16; both real character parameters in [-1,1] |
| `compensatedQuadraticPairCrossMoment_error` | proved and audited | same scalar domain; explicit error <=12/q^2 |

Assembly owner:
`PrimeFactorOscillations/Assembly/FiniteFieldRawPairCovariance.lean`.
Names in the next table are in namespace
`PrimeFactorOscillations.FiniteFieldRawPairCovariance`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `covariance_count_general` | proved and audited | odd field; h nonzero; every lag; q>=16 |
| `twistCompensatedCovariance_eq_model` | proved and audited | odd field; h nonzero; chi(a)=-1; q>=16; actual normalized counts |
| `twistCompensatedCovariance_gt_one` | proved and audited | same actual-law domain; strict positive excess over 1 |
| `twistCompensatedCovariance_error` | proved and audited | same actual-law domain; absolute error <=12/q^2 from 1+1/q |

Definitions:
`FiniteField.compensatedQuadraticPairCrossMoment` and
`PrimeFactorOscillations.FiniteFieldRawPairCovariance.twistCompensatedCovariance`.

Write q=#K, sigma=chi(-1), eta=chi(2), D_b=q-3+chi(b)+chi(-b),
and C_b(k)=q^(-1)*sum_c u_b(c)*u_b(c+k), where
u_b(c)=4*w_b(c)/D_b is the existing normalized raw pair law.
The exact compensated correlation is
(D_h^2*C_h(h)+D_(a*h)^2*C_(a*h)(a*h))/(D_h^2+D_(a*h)^2)
= [q^3-5*q^2+(5-4*eta)*q-11-2*sigma]/
[q*((q-3)^2+2*(1+sigma))].
The class label is shared inside each product. This is a weighted average
of correlations, not the autocorrelation of an averaged density.

benchmark_status: uniform actual compensated overlap law proved.
old_bound: exact adjacent/raw correlation was specialized to chi(-1)=-1;
no all-character balanced overlap estimate was installed.
new_bound: for every odd finite field with q>=16, every h nonzero and
every chi(a)=-1, the displayed correlation exceeds 1 and differs from
1+1/q by at most 12/q^2, independently of h and the nonsquare choice.
components: full quartic trace kernel; signed trace-character products;
singular masks and every boundary intersection; exact paired CM trace
cancellation; both distinct positive normalizers.
actuals: finite falsification passed 178 local, 3758 all-lag and 1790
linked-twist frames, including genuine extension fields F9,F25,F27.
These diagnostics are not the uniform proof.
first_nonpositive_domain: none in the proved q>=16 domain, by the
universal theorem, not by a finite scan. Outside that domain no positivity
is asserted. The integer-window mass bound is unavailable.

Unnormalized identities hold over all odd fields, including characteristic3
and q=3,5,7,9,11,13. Integer divisor coverage separately retains the p=2
parity mask, each small odd prime mask, and the coincident-residue masks for
all primes dividing the fixed integer gap h. The nonzero-gap formulas do
not replace those exceptional masks.

The available correlation identity is over the complete residue period
M=product_(prime p<=Y) p. The required integer range remains
Y<n<=Y^2-h for fixed positive even h, along unbounded Y. The open estimate is
sum_(Y<n<=Y^2-h) product_(prime p<=Y) 1_(p does not divide n*(n+h)) > 0.
The fixed-gap alignment is proved in the follow-up below; positive mass
throughout the required short integer range remains open. Integer
recurrence, H1 and the installed QRH boundary 7/8 are unchanged.

The new exact count formula and compensated normalized law are distinct from
the preceding specialized theorem. Classical trace symmetries are proved
inputs; literature priority beyond the targeted primary comparison remains
unconfirmed. Paper label: `sec:all-character-compensation`.

## Fixed-gap pullback of the compensated law (October 31)

All three following theorems are maintained, compiled and audited in
`PrimeFactorOscillations/Assembly/FiniteFieldRawPairCovariance.lean`,
namespace `PrimeFactorOscillations.FiniteFieldRawPairCovariance`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `covariance_dilation_pullback` | proved and audited | any finite field; arbitrary h,k; a nonzero |
| `twistCompensatedCovariance_same_gap` | proved and audited | any finite field; arbitrary h; a nonzero; exact shared-coordinate weighted correlation |
| `dilation_pair_avoidance_iff` | proved and audited | any field; arbitrary h,c; a nonzero; both forbidden residues retained |

The new-only audit checks exactly these three declarations, with only
propext, Classical.choice and Quot.sound. No previous theorem is re-audited.
These are the coordinate-transfer corollaries of the compensated theorem,
not a separately claimed original analytic estimate.

For v_0(c)=u_h(c) and v_1(c)=u_(a*h)(a*c), multiplication by a permutes
the field and gives E[v_1(c)*v_1(c+k)]=C_(a*h)(a*k). Therefore
Cbar_(h,a)=E[D_h^2*v_0(c)*v_0(c+h)+D_(a*h)^2*v_1(c)*v_1(c+h)]/
(D_h^2+D_(a*h)^2). Both slots now use the same original shift h.
The conditions a*c nonzero and a*(c+h) nonzero are exactly c nonzero
and c+h nonzero. The class label remains shared within each product;
this expression does not pretend to be an averaged density's autocorrelation.

benchmark_status: exact fixed-gap coordinate consumer proved.
old_bound: Cbar>1 and abs(Cbar-(1+1/q))<=12/q^2 were proved for the
two linked local gaps, without an installed same-coordinate representation.
new_bound: the identical bounds now apply to the displayed same-gap
weighted correlation over every odd field q>=16, h nonzero, chi(a)=-1.
components: bijective scaling of the complete finite sum, both squared
normalizers, both product slots, and the exact forbidden-residue equivalence.
actuals: no new numerical data; these universal algebraic identities are
proved directly in Lean.
first_nonpositive_domain: none in the inherited quantitative domain;
the positive integer-window bound remains unavailable.

Field-by-field pullback can use the residues of a single fixed integer gap.
The available exact moment is still over the complete CRT period M;
the required sum remains positive full prime-avoidance mass on
Y<n<=Y^2-h for unbounded Y. Alignment alone supplies no bound for that
short sum. Integer pair recurrence, H1 and QRH7/8 are unchanged.
Paper theorem: `thm:fixed-gap-pullback`.

## Full compensated lag kernel and one-third persistence (October 31)

All 15 theorem proofs and 5 definitions below are maintained and compiled.
The new-only audit covers exactly these 20 declarations and reports only
propext, Classical.choice and Quot.sound. No unchanged declarations were
re-audited. The full proof and probabilistic interpretation are in paper
section `sec:compensated-persistence`; the editor source compiles.

Candidate owner:
`PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairCompensatedKernel.lean`.
The theorem names in this table are in namespace `FiniteField`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `quadraticPairCorrelationKernel_scale` | proved and audited | any finite field; arbitrary h,k; unit dilation |
| `monicQuadraticPairCount_twist_compensated_correlation` | proved and audited | odd field; h nonzero; every k; chi(a)=-1; all singular intersections |
| `twistCompensatedPairKernel_zero` | proved and audited | any finite field; h nonzero; exact zero-lag numerator |
| `compensatedQuadraticPairPersistence_denominator_pos` | proved and audited | real q>=16; t<=1; explicit positive denominator |
| `compensatedQuadraticPairPersistence_bounds` | proved and audited | real q>=16; t,u in [-1,1]; strict bounds 0<rho<1/2 |
| `compensatedQuadraticPairPersistence_error` | proved and audited | same scalar domain; absolute error from 1/3 <=5/q |

Candidate definitions: `FiniteField.twistCompensatedPairKernel` and
`FiniteField.compensatedQuadraticPairPersistence`.

Assembly owner:
`PrimeFactorOscillations/Assembly/FiniteFieldCompensatedKernel.lean`.
The next names are in namespace
`PrimeFactorOscillations.FiniteFieldCompensatedKernel`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `kernel_eq_covariances` | proved and audited | any finite field; arbitrary h,k; a nonzero; physical pullback retained |
| `normalization_pair` | proved and audited | finite field; h nonzero; chi(a)=-1; both squared normalizers |
| `kernel_eq_model` | proved and audited | odd field; q>=16; h nonzero; chi(a)=-1; every lag |
| `kernel_zero_eq_model` | proved and audited | same qualified domain; exact diagonal model |
| `kernel_adjacent` | proved and audited | finite field; a nonzero; matches preceding shared-endpoint law |
| `centeredPersistence_eq_model` | proved and audited | qualified domain; actual centered correlation equals rational model |
| `centeredPersistence_law` | proved and audited | qualified domain; 0<rho<1/2 and abs(rho-1/3)<=5/q |
| `kernel_shifted` | proved and audited | any finite field; arbitrary h,a,x,y; exact displacement y-x |
| `signed_window_kernel` | proved and audited | any finite field; arbitrary finite signed weights and shifts; every mixed term |

Assembly definitions: `moment`, `kernel`, and `centeredPersistence`.
Their probability interpretation requires the qualified positive-denominator
domain above; the purely algebraic translation/window identities have a
larger domain and do not assert normalization outside it.

Writing sigma=chi(-1), eta=chi(2), R=(q-3)^2+2*(1+sigma), the actual
zero-lag moment is [q^3-3*q^2+(5+2*sigma)*q-11-2*sigma]/(q*R).
The centered shared-endpoint coefficient is exactly
rho=[q^2-(6+4*eta+2*sigma)*q-11-2*sigma]/
[3*q^2-6*q-11-2*sigma]. The denominator is positive throughout the
qualified domain. Both class densities have mean1 by the existing
`sum_raw_density` and the unit pullback, so this is an actual correlation
coefficient with a shared class label, not a ratio of uncentered moments.

benchmark_status: uniform actual centered persistence law and full signed
one-field window consumer proved.
old_bound: exact single-class every-lag identities and compensated adjacent
moment were installed; no compensated every-lag kernel or uniform centered
persistence estimate was installed.
new_bound: exact compensated every-lag count model; 0<rho<1/2 and
abs(rho-1/3)<=5/q for every odd field q>=16, h nonzero, chi(a)=-1.
components: retained quartic kernel; all signed character corrections;
exact cancellation of both cubic boundary traces; all three singular
intersection masks; distinct positive normalizers; every signed window
cross term.
actuals: falsification passed 43042 full compensated frames and 3758
gap-ratio diagnostic frames in F3,F5,F7,F9,F11,F13,F17,F19,F23,F25,F27,F31.
These tests are not the uniform proof. The separate numerical 4/q envelope
and ratio-homogeneity checks are diagnostics, not promoted bound claims.
first_nonpositive_domain: none for rho in the proved qualified domain,
by the universal theorem. The positive integer-window mass remains
unavailable; no finite or cofinal integer positivity range is asserted.

The one-third fair-Bernoulli benchmark is classical. The result proved here
is the explicit actual-count compensated law with a uniform 5/q error.
It was not found in the checked unfinished-target records or targeted
primary comparison; literature priority remains unconfirmed.

The available signed window identity averages the complete field.
Its insertion into a complete product does not estimate the actual integer
origin on Y<n<=Y^2-h. The cofinal positive-mass estimate is still open.
Integer recurrence, H1 and the installed QRH boundary7/8 are unchanged.

## Tensorized compensated persistence and exact small-prime masks (2026-10-31)

Paper claims: `thm:tensor-persistence`, `prop:tensor-exceptional-mask`.
Every advertised theorem below compiled from its maintained owner; only the
new declarations were recursively audited. The allowed foundational axioms
are `propext`, `Classical.choice`, and `Quot.sound`.

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/EulerProduct/ShiftedBounds.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `Finset.eulerShiftRatio_bounds` | proved and audited | c>=0; n>c+1; ratio in (0,1] |
| `Finset.eulerShiftRatio_Icc` | proved and audited | integers N>=m>c+1, c>=0; exact consecutive product |
| `Finset.eulerShiftRatio_Icc_lower` | proved and audited | same consecutive domain; positive endpoint lower constant |
| `Finset.eulerShiftRatio_subset_lower` | proved and audited | any finite distinct integer support n>=m>c+1; c>=0 |
| `Finset.shiftedEulerProduct_bounds` | proved and audited | same arbitrary finite support; shifted and ordinary products with exact lower constant |

Definitions (compiled and audited): `Finset.shiftedEulerFactor`, `Finset.eulerShiftRatio`.

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairProductFactors.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.compensatedQuadraticPairBase_pos` | proved and audited | real q>=16, t>=-1 |
| `FiniteField.compensatedQuadraticPairDiagonalNumerator_pos` | proved and audited | real q>=16, t>=-1 |
| `FiniteField.compensatedQuadraticPairMomentRatio_eq` | proved and audited | real q>=16, t>=-1; arbitrary u; full ratio identity |
| `FiniteField.compensatedQuadraticPairCrossMoment_lower` | proved and audited | q>=16, t,u in [-1,1]; C>=1+1/(4q) |
| `FiniteField.compensatedQuadraticPairMomentRatio_bounds` | proved and audited | same local domain; both shifted Euler squares |
| `FiniteField.compensatedQuadraticPairDiagonalMoment_bounds` | proved and audited | q>=16, t in [-1,1]; both inverse Euler cubes |

Definitions (compiled and audited): `FiniteField.compensatedQuadraticPairDiagonalMoment`, `FiniteField.compensatedQuadraticPairMomentRatio`.

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairTensorPersistence.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.compensatedQuadraticPairDiagonalProduct_pos` | proved and audited | finite distinct integer q>=17; t_q>=-1 |
| `FiniteField.compensatedQuadraticPairCrossProduct_lower` | proved and audited | q>=17, t_q,u_q in [-1,1]; B>=1+L/4; empty support included |
| `FiniteField.compensatedQuadraticPairRatioProduct_bounds` | proved and audited | same finite domain; (81/256)E^2<=B/A<=E^2 |
| `FiniteField.compensatedQuadraticPairInverseDiagonalProduct_bounds` | proved and audited | q>=17, t_q in [-1,1]; (343/512)E^3<=1/A<=E^3 |
| `FiniteField.compensatedQuadraticPairTensorPersistence_compatible` | proved and audited | full finite domain; a>=2, 1<=b<=a; signed centered Euler-square bounds |
| `FiniteField.compensatedQuadraticPairTensorPersistence_obstructed` | proved and audited | q>=17, t_q in [-1,1], a>=2, b=0; signed centered negative Euler-cube bounds |

Definitions (compiled and audited): `FiniteField.compensatedQuadraticPairDiagonalProduct`, `FiniteField.compensatedQuadraticPairCrossProduct`, `FiniteField.compensatedQuadraticPairTensorPersistence`.

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairMaskOverlap.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.QuadraticPairTwistLikelihood.mask_nonneg` | proved and audited | any field with decidable equality; every c,h |
| `FiniteField.QuadraticPairTwistLikelihood.mask_adjacent_indicator` | proved and audited | finite odd field; h nonzero; all three distinct forbidden residues retained |
| `FiniteField.QuadraticPairTwistLikelihood.sum_mask_adjacent` | proved and audited | finite odd field; h nonzero; exact sum q-3 |
| `FiniteField.QuadraticPairTwistLikelihood.sum_mask_zero` | proved and audited | any finite field; exact zero-gap mask sum q-1 |
| `FiniteField.QuadraticPairTwistLikelihood.maskMoments_zero` | proved and audited | any finite field q>=2; both moments q/(q-1) |
| `FiniteField.QuadraticPairTwistLikelihood.maskMoments_nonzero` | proved and audited | odd finite field q>=3, h nonzero; exact normalized diagonal and shared moments |
| `FiniteField.QuadraticPairTwistLikelihood.maskSharedMoment_card_three` | proved and audited | odd field of cardinality3; h nonzero; shared moment zero |
| `FiniteField.QuadraticPairTwistLikelihood.mask_adjacent_vanish_card_three` | proved and audited | same card-three domain; every residue has zero shared mask product |
| `FiniteField.QuadraticPairTwistLikelihood.maskMoments_compatible` | proved and audited | odd field q>=5, h nonzero; 1<=shared<=diagonal |

Definitions (compiled and audited): `FiniteField.QuadraticPairTwistLikelihood.maskDiagonalMoment`, `FiniteField.QuadraticPairTwistLikelihood.maskSharedMoment`.

Owner: `PrimeFactorOscillations/Assembly/FiniteFieldTensorPersistence.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.atomic_sum` | proved and audited | any finite field; arbitrary h,a and two functions; exact shared-label average |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.atom_weight_nonneg` | proved and audited | any finite field; every class and coordinate |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.atom_weight_one` | proved and audited | q>=16; h nonzero; arbitrary multiplier |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.atom_value_mean` | proved and audited | odd field q>=16; h and multiplier nonzero; every lag |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.atomic_kernel` | proved and audited | any finite field; exact shared-label physical kernel |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.packet_kernel` | proved and audited | arbitrary finite field family and support; exact full-product moment |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.packet_shifted_kernel` | proved and audited | same family; arbitrary two dependent shift families; every mixed coordinate retained |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.packet_shifted_diagonal` | proved and audited | same family; shift-invariance of the product diagonal |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.packet_weight_one` | proved and audited | q>=16 and nonzero gaps on support; actual product weights normalized |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.packet_value_mean` | proved and audited | odd q>=16; nonzero gaps and multipliers on support; every shift |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.packet_diagonal_model` | proved and audited | distinct supported field sizes q>=17; odd fields, nonzero gaps, nonsquare multipliers |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.packet_adjacent_model` | proved and audited | same qualified actual field domain; full shared-endpoint moment |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.centered_packet_compatible` | proved and audited | qualified actual field domain; a>=2, 1<=b<=a; actual centered Euler-square comparison |
| `PrimeFactorOscillations.FiniteFieldTensorPersistence.centered_packet_obstructed` | proved and audited | qualified actual field domain; a>=2, b=0; actual centered negative Euler-cube comparison |

Definitions (compiled and audited): `PrimeFactorOscillations.FiniteFieldTensorPersistence.atomWeight`, `PrimeFactorOscillations.FiniteFieldTensorPersistence.atomValue`, `PrimeFactorOscillations.FiniteFieldTensorPersistence.packetKernel`, `PrimeFactorOscillations.FiniteFieldTensorPersistence.centeredPacketPersistence`.

benchmark_status: universal finite-product comparison and its actual
shared-label probability consumer proved; integer-window mass remains open.
old_bound: the one-field centered coefficient was controlled by 1/3+O(1/q);
no uniform centered product comparison with exceptional-prime sign was installed.
new_bound: (81/256)*(b/a)*(L/(L+4))*E^2<=rho<=(b/a)*E^2 for
a>=2 and 1<=b<=a. For b=0, z/(a-z)<=-rho<=E^3/(a-E^3),
where z=(343/512)*E^3 and E=product_(q in S)(1-1/q).
components: exact C>=1+1/(4q) supply; positive diagonal; uniform shifted
Euler telescoping; both subtractions of1; shared class labels; distinct
squared normalizers; every product-coordinate cross term; parity,
card-three and gap-divisor masks.
actuals: retained falsification records cover4036 local scalar corner
cases and348 finite-product/prefix cases. These are diagnostics, not the
uniform proof or integer pair counts. The actual law is identified by
compiled finite-sum equalities and normalization.
first_nonpositive_domain: compatible nonempty S has positive lower bound;
empty S has rho=(b-1)/(a-1), including zero when b=1. The obstructed
b=0 regime is negative for every S. No finite or cofinal positivity
domain is asserted for the integer-window count.

The elementary telescoping and tensorization are classical inputs.
Priority of the explicit compensated square/cube comparison remains
unconfirmed beyond the targeted comparison. The independent-field
product does not give a positive survivor in Y<n<=Y^2-h. Integer
recurrence, H1 and QRH7/8 are unchanged; QRH exponent work stays paused.

## Trace-free actual-count covariance and signed windows (2026-10-31)

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairTraceFreeKernel.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.sum_twistPairNumerator_shift_correlation` | proved and audited | finite odd field; nonzero h; every lag; unmasked exact character kernel |
| `FiniteField.twistPairNumerator_boundary_sum` | proved and audited | any finite field; arbitrary h,k; exact four-boundary evaluation |
| `FiniteField.sum_traceFreePairNumerator_shift_correlation` | proved and audited | finite odd field; nonzero h; every lag; unnormalized formula includes q=3 |
| `FiniteField.monicQuadraticPairCount_full_twist_correlation` | proved and audited | finite odd field; nonzero h; nonsquare multiplier; all four actual count products retained |

Definitions (compiled and audited): `FiniteField.traceFreePairLagNumerator`.

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairTraceFreeSigns.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.traceFreePairKernel_eq_model` | proved and audited | finite odd field q>=5; nonzero h; every lag |
| `FiniteField.traceFreePairCovariance_zero` | proved and audited | same qualified domain; exact diagonal including chi(-1) correction |
| `FiniteField.traceFreePairCovariance_nonoverlap` | proved and audited | same qualified domain; lag outside {0,h,-h}; exact signed character formula |
| `FiniteField.traceFreePairCovariance_neg` | proved and audited | any finite field; arbitrary h,k; exact evenness |
| `FiniteField.traceFreePairCovariance_nonpos_nonoverlap` | proved and audited | finite odd field q>=5; nonzero h; chi(-1)=-1; all nonoverlap lags |
| `FiniteField.traceFreePairCovariance_adjacent_neg_one` | proved and audited | same negative-character domain; exact adjacent covariance including chi(2) |
| `FiniteField.traceFreePairCovariance_adjacent_le` | proved and audited | same negative-character domain; adjacent covariance <=1/(q-3) |
| `FiniteField.traceFreePairCovariance_graph_upper` | proved and audited | same negative-character domain; every lag; diagonal and both overlap rows retained |
| `FiniteField.traceFreePairCovariance_positive_iff` | proved and audited | finite odd field q>=5; nonzero h; chi(-1)=1; nonoverlap covariance positive iff all three displayed character products are -1 |

Definitions (compiled and audited): `FiniteField.traceFreePairKernel`, `FiniteField.traceFreePairCovariance`.

Owner: `PrimeFactorOscillations/Assembly/FiniteFieldTraceFreeWave.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `PrimeFactorOscillations.FiniteFieldTraceFreeWave.centered_shift_kernel` | proved and audited | finite odd field q>=5; nonzero h; arbitrary two shifts; exact centered covariance |
| `PrimeFactorOscillations.FiniteFieldTraceFreeWave.windowEnergy_eq_covariance` | proved and audited | same qualified field domain; arbitrary finite index set, signed real coefficients and shifts |
| `PrimeFactorOscillations.FiniteFieldTraceFreeWave.edgeEnergy_le_square_sum` | proved and audited | any field; finite index set; arbitrary signed real coefficients and injective shifts; every edge displacement |
| `PrimeFactorOscillations.FiniteFieldTraceFreeWave.windowEnergy_le_graph` | proved and audited | finite odd field q>=5; nonzero h; chi(-1)=-1; nonnegative weights and injective shifts; full two-edge graph bound |
| `PrimeFactorOscillations.FiniteFieldTraceFreeWave.windowEnergy_le_four_square_sum` | proved and audited | same qualified window domain; uniform 4*sum b_i^2/(q-3) bound |

Definitions (compiled and audited): `PrimeFactorOscillations.FiniteFieldTraceFreeWave.windowEnergy`, `PrimeFactorOscillations.FiniteFieldTraceFreeWave.edgeEnergy`.

benchmark_status: universal complete-field signed covariance identity and
nonnegative-window variance estimate proved and audited; all23 public
declarations exported. Integer-origin mass remains open.
old_bound: for chi(-1)=-1 and N unit-weight shifts, the elementary
diagonal envelope is2N^2/(q-3).
new_bound: for distinct shifts and nonnegative coefficients,
V<=[2*sum b_i^2+E_h+E_(-h)]/(q-3)<=4*sum b_i^2/(q-3).
Unit weights give4N/(q-3), strictly improving the displayed envelope
when N>2.
components: exact canonical weight; all four mixed count products;
both endpoint masks; diagonal, both overlap rows and every nonoverlap
sign; signed square expansion before the nonnegative-weight inequality.
actuals: retained diagnostics cover10698 exact kernels,9672 nonoverlap
sign checks,187470 actual nonsquare twist constants and340 signed-window
checks over the stated16 prime and extension fields. These do not prove
the universal theorem or any integer supply.
first_nonpositive_domain: unavailable for the integer-origin prime-pair
count; no positive integer-window domain is certified by this field bound.

The unnormalized kernel includes cardinality3. Normalized claims require
q>=5. The negative-character branch has first actual cardinality7;
cardinality5 lies in the positive-character classification.
Characteristic2 and h=0 remain the existing separately qualified packet
fallbacks. Arbitrary signed weights are permitted in the exact identity;
the graph upper bound requires nonnegative weights and injective shifts.

The paper gives the complete proof and distinguishes the classical
triple-character pattern ingredient from this covariance application.
Priority remains under review. No integer prime-pair recurrence, H1
improvement or change to the accepted QRH7/8 boundary is claimed.
QRH exponent research stays paused.


## Cubic actual-count transport and native prime masks (2026-10-31)

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/Primes/TwinCubic.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `Nat.TwinCubic.step_add_two` | proved and audited | all natural n; simultaneous square factorization of the second endpoint |
| `Nat.TwinCubic.step_chebyshev` | proved and audited | all natural n; exact cubic Chebyshev identity without natural subtraction |
| `Nat.TwinCubic.block_eq` | proved and audited | all natural n; B(n)=3+4*n*(n+2) |
| `Nat.TwinCubic.endpointProduct_step` | proved and audited | all natural n; exact endpoint product multiplication by B(n)^2 |
| `Nat.TwinCubic.orbit_eq_left_square` | proved and audited | all natural seeds and indices; first endpoint accumulated square |
| `Nat.TwinCubic.orbit_add_two_eq_right_square` | proved and audited | all natural seeds and indices; second endpoint accumulated square |
| `Nat.TwinCubic.step_pos` | proved and audited | positive natural n; positive next iterate |
| `Nat.TwinCubic.orbit_pos` | proved and audited | positive seed; every orbit index |
| `Nat.TwinCubic.lt_step` | proved and audited | positive natural n; strictly larger next iterate |
| `Nat.TwinCubic.orbit_strictMono` | proved and audited | positive seed; strictly increasing full orbit |
| `Nat.TwinCubic.seed_add_le_orbit` | proved and audited | positive seed; explicit seed+k lower bound for every k |
| `Nat.TwinCubic.step_composite_pair` | proved and audited | positive natural n; both next endpoints are nonprime |
| `Nat.TwinCubic.exists_large_composite_pair` | proved and audited | positive seed; every natural X; a later composite pair above X |
| `Nat.TwinCubic.step_mod_three` | proved and audited | n mod 3=2; next iterate has the same residue |
| `Nat.TwinCubic.orbit_mod_three` | proved and audited | seed mod 3=2; all orbit indices |
| `Nat.TwinCubic.orbit_mod_six` | proved and audited | seed mod 6=5; all orbit indices |
| `Nat.TwinCubic.affine_factors_coprime` | proved and audited | every natural n; the two odd affine factors are coprime |
| `Nat.TwinCubic.block_coprime_endpointProduct` | proved and audited | n mod 3=2; new block coprime to both old endpoints jointly |
| `Nat.TwinCubic.endpointProduct_dvd_next` | proved and audited | every natural n; old endpoint product divides the next |
| `Nat.TwinCubic.endpointProduct_orbit_dvd` | proved and audited | all seeds; i<=j; full endpoint-product divisibility |
| `Nat.TwinCubic.block_dvd_next` | proved and audited | every natural n; new block divides the next endpoint product |
| `Nat.TwinCubic.earlier_block_dvd` | proved and audited | all seeds; i<j; earlier block divides later endpoint product |
| `Nat.TwinCubic.blocks_coprime_of_lt` | proved and audited | seed mod 3=2; i<j; corresponding new blocks coprime |
| `Nat.TwinCubic.blocks_pairwise_coprime` | proved and audited | seed mod 3=2; all distinct orbit indices |
| `Nat.TwinCubic.new_prime_divisor` | proved and audited | n mod 3=2; every prime divisor of B(n) absent from the old endpoint product |

Definitions (compiled and audited): `Nat.TwinCubic.step`, `Nat.TwinCubic.endpointProduct`, `Nat.TwinCubic.block`, `Nat.TwinCubic.orbit`, `Nat.TwinCubic.leftScale`, `Nat.TwinCubic.rightScale`.

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairCubicLift.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.cubicPairLift_add_two` | proved and audited | all fields; arbitrary c; exact second-endpoint factorization |
| `FiniteField.cast_twinCubic_step` | proved and audited | all fields; every natural n; integer lift agrees with field polynomial |
| `FiniteField.traceFreePairNumerator_square_transport` | proved and audited | finite field; two nonzero simultaneous square multipliers; both endpoint masks retained |
| `FiniteField.traceFreePairWeight_square_transport` | proved and audited | same finite-field square-transport hypotheses; canonical weight unchanged |
| `FiniteField.traceFreePairNumerator_cubic_lift` | proved and audited | every finite field and c; exact new-factor mask, including singular endpoints |
| `FiniteField.traceFreePairWeight_cubic_lift` | proved and audited | every finite field and c; algebraic masked weight identity; probability normalization retains its existing qualified domain |
| `FiniteField.monicQuadraticPairCount_cubic_lift` | proved and audited | finite odd field; any nonsquare multiplier; exact actual two-class count sum including cardinality three |
| `FiniteField.traceFreePairWeight_twinCubic_orbit` | proved and audited | finite field; arbitrary seed and index; both accumulated square multipliers nonzero |
| `FiniteField.quadraticChar_twinCubic_rows` | proved and audited | same unramified orbit domain; both signed quadratic-character rows preserved |

Definitions (compiled and audited): `FiniteField.cubicPairLift`.

Owner: `PrimeFactorOscillations/Assembly/FiniteFieldCubicLift.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `PrimeFactorOscillations.FiniteFieldCubicLift.integer_mask_product` | proved and audited | every bounded prime modulus; arbitrary residue; exact product opening mask |
| `PrimeFactorOscillations.FiniteFieldCubicLift.block_cast_zero_iff` | proved and audited | every bounded modulus and natural n; affine field-product zero iff integer block divisibility |
| `PrimeFactorOscillations.FiniteFieldCubicLift.integer_mask_cubic_lift` | proved and audited | every bounded prime modulus, including two and three; exact new-prime opening mask |
| `PrimeFactorOscillations.FiniteFieldCubicLift.actual_local_cubic_lift` | proved and audited | all bounded moduli and natural n; full canonical local row, including fallback and composite unit rows |
| `PrimeFactorOscillations.FiniteFieldCubicLift.actual_packet_cubic_lift` | proved and audited | every natural cutoff and n; exact full actual packet times the complete new-prime mask |
| `PrimeFactorOscillations.FiniteFieldCubicLift.block_mask_eq_one` | proved and audited | every cutoff and n; no supported prime divides the new block |
| `PrimeFactorOscillations.FiniteFieldCubicLift.block_mask_eq_zero` | proved and audited | every cutoff and n; any named prime divisor at or below cutoff |
| `PrimeFactorOscillations.FiniteFieldCubicLift.actual_packet_eq_of_no_new_prime` | proved and audited | every cutoff and n; full actual packet unchanged under complete supported avoidance |
| `PrimeFactorOscillations.FiniteFieldCubicLift.actual_packet_zero_of_new_prime` | proved and audited | every cutoff and n; full actual packet zero when a supported new prime is present |

Definitions (compiled and audited): `PrimeFactorOscillations.FiniteFieldCubicLift.primeBlockMask`, `PrimeFactorOscillations.FiniteFieldCubicLift.blockMask`.

benchmark_status: exact universal cubic transport proved; all52 new public declarations compiled and foundational-axiom audited. Public closure and final staged validation accompany promotion.
old_bound: no maintained exact cubic transport for the complete canonical actual packet.
new_bound: P_Q(T(n))=P_Q(n)*product_(prime p<=Q)1_(p does not divide (2n+1)(2n+3)), for all natural Q,n. Both unramified character rows and the actual two-class sum are preserved exactly.
components: simultaneous endpoint square factors; both zero-discriminant masks; every prime row including two and three; coprime new blocks and every supported prime-factor mask; no discarded count class or compensation term.
actuals: pre-formalization falsification covered5349 actual two-class sums,5346 normalized weights,42 integer-orbit frames and189 coprime-block comparisons in the recorded finite domain. These are diagnostics, not universal proofs or integer prime-pair counts.
first_nonpositive_domain: unavailable for integer-origin mass; no positive window or cofinal prime-pair supply is certified. A visible new factor makes the transported packet exactly zero, including when it was already zero.

The cubic Chebyshev identity and elementary coprime-orbit arithmetic are classical ingredients. Priority of the actual-count and complete-mask application remains unconfirmed. The paper contains its complete ordinary proof and preserves all normalization and unramified hypotheses. No integer prime-pair recurrence, H1 improvement, RH proof or change to the accepted QRH7/8 boundary is claimed; QRH exponent research stays paused.


## Exact cubic mass loss and uniform probability survival (2026-10-31)

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairCubicLift.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.traceFreePairNumerator_cubic_root` | proved and audited | finite field; three nonzero; every root of (2c+1)(2c+3); exact numerator q+chi(3) |
| `FiniteField.traceFreePairWeight_cubic_root` | proved and audited | same root domain; exact algebraic weight (q+chi(3))/(q-3); probability use retains odd q>=5 |
| `FiniteField.cubic_pair_mask_zero_iff` | proved and audited | arbitrary field with two nonzero; exact two-root classification; no finiteness assumption |
| `FiniteField.sum_traceFreePairWeight_cubic_lift_deletion` | proved and audited | finite odd field; exact complete sum minus the two exceptional-root weights; includes algebraic cardinality-three case |
| `FiniteField.traceFreePairWeight_cubic_lift_mean` | proved and audited | finite odd field q>=5; three nonzero; exact one-step normalized mean |
| `FiniteField.traceFreePairNumerator_cubic_lift_char_three` | proved and audited | finite odd field; three zero; pointwise numerator preservation, including cardinality three |
| `FiniteField.traceFreePairWeight_cubic_lift_char_three` | proved and audited | same field domain; pointwise algebraic weight preservation |
| `FiniteField.traceFreePairWeight_cubic_iterate_char_three` | proved and audited | same field domain; every natural iteration count and every initial field element |
| `FiniteField.traceFreePairWeight_cubic_iterate_mean_char_three` | proved and audited | finite odd field q>=5; three zero; normalized mean one for every iteration count |

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairCubicSurvival.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.quadraticChar_cubic_root` | proved and audited | finite odd field; every exceptional root; discriminant character equals chi(-3), including characteristic three |
| `FiniteField.cubicSafeSector_step` | proved and audited | finite odd field; three nonzero; chi(c(c+2))=-chi(-3); both sector and canonical weight preserved |
| `FiniteField.cubicSafeSector_iterate` | proved and audited | same protected-sector domain; every natural iteration count |
| `FiniteField.sum_traceFreePairNumerator_quadratic_character` | proved and audited | finite odd field; exact full signed moment -q+1-2*chi(-1), with both endpoint corrections |
| `FiniteField.sum_traceFreePairNumerator_safe_sector` | proved and audited | finite odd field; three nonzero; exact denominator-free weighted character projector |
| `FiniteField.traceFreePairWeight_safe_sector_mass` | proved and audited | finite odd field q>=5; three nonzero; exact initial protected-sector probability |
| `FiniteField.traceFreePairWeight_cubic_iterate_mean_ge_safe_sector` | proved and audited | same qualified probability domain; every iteration count; full mean at least the exact protected-sector mass |
| `FiniteField.traceFreePairWeight_cubic_iterate_mean_lower` | proved and audited | every finite odd field q>=5; every natural iteration count; full mean >=(q-3)/(2q), including characteristic three |

benchmark_status: universal finite-field first-step and all-iterate survival theorems compiled, exported and new-declaration audited; all17 declarations have real proofs.
old_bound: the trivial nonnegative lower envelope 0 for an arbitrary iterate followed from the existing masked good-point bounds; no uniform positive all-iterate reserve was installed.
new_bound: E_0 W_2(T^k(c))>=(q-3)/(2q) for every odd q>=5 and every k>=0. Outside characteristic three, the stronger lower bound is 1/2+chi(-3)*(q-1+2*chi(-1))/(2q(q-3)); characteristic three has exact mean1 at every iterate.
components: invariant discriminant-character sector; both exceptional roots; signed numerator moment -q+1-2*chi(-1); exact projector and endpoint masks; nonnegative complementary mass; positive denominator domain; no discarded class or character cross term.
actuals: diagnostics retained135 exact-rational means,120 weighted first-death rows,13 protected-sector masses and1647 pointwise invariance checks over15 stated prime and extension fields with iteration counts0..8. These are falsification evidence, not the universal proof or integer prime counts.
first_nonpositive_domain: none in the qualified finite-field theorem domain q>=5 and k>=0. No positive integer-window domain is certified; sum_(Y<n<=Y^2-2)P_Y(n)>0 along unbounded Y remains unproved.

The full finer absorption profile involving v3(q^2-1) is still an unproved target and is not advertised as formalized. Classical Chebyshev graph theory is prior work; priority of this compensated count-law application remains under review. No integer prime-pair recurrence, H1 improvement or change to the accepted QRH7/8 boundary is claimed; QRH exponent research stays paused.

## Complete square-transport profiles and attained mass (2026-10-31)

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairSquareTransport.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.squarePairReach_refl` | proved and audited | every field; identity square transport; no finiteness hypothesis |
| `FiniteField.traceFreePairNumerator_square_transport_gap` | proved and audited | every finite field and gap; both multipliers nonzero; both endpoint masks and character rows preserved |
| `FiniteField.traceFreePairWeight_square_transport_gap` | proved and audited | same domain; exact algebraic canonical weight equality, before probability qualification |
| `FiniteField.squarePairReach_zero_iff` | proved and audited | finite field; nonzero gap; endpoint zero reachable exactly when chi(h(c+h))=1; square-root witness included |
| `FiniteField.squarePairReach_neg_shift_iff` | proved and audited | finite field; nonzero gap; endpoint -h reachable exactly when chi(-hc)=1; square-root witness included |
| `FiniteField.squarePairCore_good` | proved and audited | every finite field; double-negative core excludes both endpoints |
| `FiniteField.squarePairCore_of_no_positive` | proved and audited | finite field; nonzero gap; absence of both positive characters forces the double-negative core |
| `FiniteField.traceFreePairWeight_core` | proved and audited | finite field q>=5; exact core weight one |
| `FiniteField.squarePairCollapse_reachable` | proved and audited | finite field; every nonzero gap and point; explicit piecewise collapse is compatible |
| `FiniteField.squarePairCollapse_profile` | proved and audited | finite field q>=5; nonzero gap; collapse pullback equals the complete core indicator |
| `FiniteField.traceFreePairWeight_square_reach_cases` | proved and audited | finite field; every compatible point pair; transported weight is zero or its original value |
| `FiniteField.traceFreePairWeight_square_core` | proved and audited | finite field q>=5; nonzero gap; every compatible image of a core point has weight one |
| `FiniteField.traceFreePairWeight_nonneg_all` | proved and audited | finite field q>=5; nonzero gap; global nonnegativity including both zero endpoints |

Definitions (compiled and audited): `FiniteField.squarePairReach`, `FiniteField.squarePairCore`, `FiniteField.squarePairCollapse`.

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairSquareExtremal.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.squarePairCollapse_zero` | proved and audited | finite field; nonzero gap; collapse fixes zero |
| `FiniteField.squarePairCollapse_neg_shift` | proved and audited | finite field; nonzero gap; collapse fixes -h |
| `FiniteField.squarePairCollapse_idempotent` | proved and audited | finite field; nonzero gap; pointwise idempotence |
| `FiniteField.squarePair_mask_attainment` | proved and audited | finite field q>=5; nonzero gap; every predicate containing the core has a compatible map realizing exactly its masked law |
| `FiniteField.squarePair_profiles_iff` | proved and audited | same domain; arbitrary real-valued function; both directions of the complete attainable-profile classification |
| `FiniteField.squarePairCore_indicator` | proved and audited | finite field; nonzero gap; exact integer two-character projector with both endpoint corrections zero |
| `FiniteField.sum_squarePairCore_indicator` | proved and audited | finite odd field; nonzero gap; four times the core count equals q-chi(-1), retaining the signed cross term |
| `FiniteField.squarePairCore_mass` | proved and audited | finite odd field q>=5; nonzero gap; exact normalized core mass (q-chi(-1))/(4q) |
| `FiniteField.traceFreePairWeight_square_extremal` | proved and audited | finite odd field q>=5; every nonzero gap and every compatible map; complete sharp mean interval |
| `FiniteField.traceFreePairWeight_square_minimum_attained` | proved and audited | same field/gap domain; explicit compatible idempotent collapse attains the exact lower endpoint |

benchmark_status: exact universal attainable-profile and attained-extremum theorems;23 real theorems and3 definitions, with new-only foundational-axiom audit. Export and final staged checks accompany promotion.
old_bound: the nonnegative lower envelope0 for general simultaneous-square pullbacks; prior cubic survival applies to a strictly smaller map family.
new_bound: (q-chi(-1))/(4q) <= E_0 W_h(Phi(c)) <=1, for every odd finite field q>=5, every nonzero gap and every compatible map, with zero multipliers allowed. Both endpoints attained; the minimum witness is idempotent. Every attainable profile is exactly W_h*1_A for some A containing the double-negative core, and conversely every such mask is attained.
components: exact square-root endpoint witnesses; both forbidden endpoints; all character classes; signed cross term sum(alpha*beta)=-chi(-1); count4|core|=q-chi(-1); positive normalization q-3; no discarded compensation term.
actuals: falsification checked all nonzero shifts in15 prime and extension fields,340 field/shift frames and96660 compatible point transitions; these checks are not the universal proof or integer-origin pair counts.
first_nonpositive_domain: none in the proved finite-field domain q>=5. No positive integer-window domain is certified; unbounded-cutoff positivity in Y<n<=Y^2-h remains open.

The projector and correlation ingredients are classical. The complete arbitrary-map weighted-profile classification is the application proved here; historical priority remains unconfirmed. This does not improve the stronger cubic-specific reserve, prove integer prime-pair recurrence or change H1, RH or the accepted QRH7/8 boundary. QRH exponent research stays paused.

## Complete low-degree square-transport rigidity and sequence survival (2026-10-31)

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticCharacterPolynomial.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.quadraticChar_affine_sum` | proved and audited | finite odd field; nonzero slope; exact zero full character sum |
| `FiniteField.affine_zero_indicator_sum` | proved and audited | every finite field; nonzero slope; exact root count one |
| `FiniteField.quadraticChar_quadratic_sum` | proved and audited | finite odd field; nonzero quadratic coefficient; exact discriminant split, including repeated roots |
| `FiniteField.quadratic_zero_indicator_sum` | proved and audited | same domain; exact root-indicator sum 1+chi(discriminant) |

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticCharacterOneException.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.square_off_one_character_sum` | proved and audited | arbitrary function on a finite field; square away from one named input; exact signed correction and full zero count |
| `FiniteField.affine_square_off_one_constant` | proved and audited | finite odd q>=5; square away from one input forces zero slope |
| `FiniteField.quadratic_square_off_one_dichotomy` | proved and audited | finite odd q>=5; nonzero leading coefficient; square polynomial or exact five-element exceptional character data |

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairCubicRigidity.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.cubic_squarePairReach_constant_zero` | proved and audited | every field; all-input compatibility of a polynomial of degree at most three forces constant term zero |
| `FiniteField.cubic_squarePairReach_endpoint` | proved and audited | every field; nonzero shift; exact second-anchor coefficient relation |
| `FiniteField.cubic_squarePairReach_quotient_squares` | proved and audited | every field; exact anchor relation and compatibility; both quotient square conditions retain their exceptional inputs |
| `FiniteField.cubic_squarePairReach_rigidity` | proved and audited | every finite odd q>=5 and nonzero h; full coefficient dichotomy; five-element exception excluded jointly; characteristic three retained |
| `FiniteField.cubic_squarePairReach_iff` | proved and audited | same domain; both directions of the complete classification, with explicit converse square witnesses |

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairLowDegreeSurvival.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.cubicPair_map_dichotomy` | proved and audited | finite odd q>=5; normalized shift two; the entire polynomial map is identity or the cubic lift |
| `FiniteField.polynomialPairWalk_is_cubic_iterate` | proved and audited | every field; any sequence of identity/cubic maps; its n-stage composite is a cubic iterate with exponent at most n |
| `FiniteField.low_degree_square_transport_survival` | proved and audited | every finite odd q>=5; any globally compatible sequence of degree-at-most-three polynomial maps at shift two; every finite composition has mean >=(q-3)/(2q) |

Definition (compiled and audited): `FiniteField.polynomialPairWalk`.

benchmark_status: universal exact map classification, both directions, and all-sequence finite-field survival;15 real theorems and1 definition, with new-only foundational-axiom audit.
old_bound: arbitrary compatible maps have mean >=(q-chi(-1))/(4q); the half-scale theorem was available only for the selected cubic and its iterates.
new_bound: every compatible polynomial of degree at most three is identity or X*(4X/h+3)^2. At shift two, every finite sequence of such maps has mean >=(q-3)/(2q), independently of its length and coefficients. This matches the general bound at q=5,7 and is strictly stronger for every admissible q>=9.
components: exact one-input signed compensation; quadratic discriminant sum and full zero count; both quotient rows; common leading character; disjoint three-root sets in q=5; nonzero two and nonzero gap; complete coefficient cancellation; existing all-iterate cubic survival with all masks retained.
actuals: the pre-formalization classification test covered385620 coefficient rows across all340 nonzero-shift frames in15 prime and extension fields, finding exactly680 compatible polynomials. The earlier135 exact-rational cubic-iterate means are retained as diagnostics. These finite evaluations do not replace the universal proof or count integer prime pairs.
first_nonpositive_domain: none in the qualified finite-field survival domain q>=5 and every finite sequence length. No positive integer-origin window or unbounded-cutoff prime-pair supply is certified.

The classical character-sum ingredients are not claimed new. The two-anchor low-degree classification differs from all-secant subgroup conditions and from the earlier open exact cubic absorption profile. Historical priority remains unconfirmed after the recorded portfolio and primary-literature comparison. These are completed finite-field results, not an integer short-window estimate, H1 improvement, RH proof or QRH exponent gain. QRH research remains paused and7/8 unchanged.

## Exact-minimum transport profiles and linear polynomial degree (2026-10-31)

Owner: `PrimeFactorOscillations/Mathlib/Algebra/Field/FieldFunctionPolynomial.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `Polynomial.fieldFunctionPolynomial_eval` | proved and audited | every finite field of cardinality at least two; every function and every input; explicit Fermat-indicator polynomial represents that function |
| `Polynomial.fieldFunctionPolynomial_natDegree_le` | proved and audited | every finite field; explicit function polynomial has natural degree at most q-1 |
| `Polynomial.card_eval_zero_le_natDegree` | proved and audited | every finite field; nonzero polynomial; all field inputs whose evaluation vanishes counted against natural degree |

Definition (compiled and audited): `Polynomial.fieldFunctionPolynomial`.

Owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairPolynomialDegree.lean`.

| Claim | Status | Exact scope |
| --- | --- | --- |
| `FiniteField.square_transport_minimum_profile_iff` | proved and audited | every finite odd q>=5 and nonzero h; every globally compatible map; exact minimum mean iff its entire profile is the core indicator |
| `FiniteField.square_transport_minimum_iff_endpoints` | proved and audited | same domain; minimum mean iff every noncore image is one of the two endpoints |
| `FiniteField.square_transport_extremizer_degree_lower` | proved and audited | every finite odd q>=5 and nonzero h; every attaining compatible polynomial; 8*degree>=3q+chi(-1) |
| `FiniteField.square_transport_extremizer_polynomial_exists` | proved and audited | same domain; an attaining compatible polynomial exists of degree at most q-1 |
| `FiniteField.square_transport_minimum_degree` | proved and audited | same domain; one attaining polynomial simultaneously satisfies both degree bounds and has least degree among every attaining polynomial |

Definition (compiled and audited): `FiniteField.SquareTransportMinimizer`.

benchmark_status: universal complete equality cases and attained minimum-degree growth;8 real theorems and2 definitions, with new-only foundational-axiom audit.
old_bound: the arbitrary-map quarter-scale minimum and classification through degree three were proved; no field-uniform linear lower degree bound or bounded-degree attaining polynomial package was installed.
new_bound: every exact-minimum compatible polynomial satisfies 8*degree>=3q+chi(-1). The minimum degree exists and is attained between ceil((3q+chi(-1))/8) and q-1, uniformly in every nonzero shift.
components: nonnegative complete profile minus the forced core; exact equality case; all noncore images in the two endpoints; nonzero polynomial P*(P+h); full distinct-root count; signed core count 4|core|=q-chi(-1); explicit Fermat interpolation and natural least-degree selection.
actuals: diagnostics covered all340 nonzero-shift frames in15 prime and extension fields,10692 point evaluations and1006 high-coefficient checks. They verified the explicit upper witness, not the actual minimum degree; its least degree was not numerically computed. The sharper characteristic-dependent degree of the canonical collapse remains unproved and is not promoted here.
first_nonpositive_domain: not a signed-mass benchmark; the degree lower bound is positive throughout q>=5. Positive integer-window mass remains unavailable.

The root-count and interpolation tools are classical, including the polynomial-evaluation framework of Reed and Solomon. The proposed new application is the full equality case and uniform polynomial-complexity consequence for this compensated probability law; historical priority remains unconfirmed. The earlier unfinished integer polynomial-plus-prime degree-budget extremality problem has different objects and conclusions and was not reopened. No H1, RH or QRH exponent gain is claimed; QRH remains paused and7/8 unchanged.


## All-index odd Pell endpoint identities

Owner: PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPell.lean

Definitions: FiniteField.oddPellPair and FiniteField.oddPellMap.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| FiniteField.oddPell_pair_invariant | proved and audited | Every commutative ring, every x and k; complete coupled quadratic invariant. |
| FiniteField.oddPell_shifted_square | proved and audited | Every commutative ring; both endpoint square factors, including zero multipliers. |
| FiniteField.oddPell_map_reachable | proved and audited | Every field and k; the map is globally compatible for shift2. |
| FiniteField.oddPell_pair_trace | proved and audited | Every field with2 nonzero, z nonzero and every k; both exact trace coordinates. |
| FiniteField.oddPell_map_trace_scaled | proved and audited | Same domain; 2*z^(2*k+1)*Phi=(z^(2*k+1)-1)^2. |
| FiniteField.oddPell_map_shift_trace_scaled | proved and audited | Same domain; shifted scaled identity with the positive endpoint. |
| FiniteField.oddPell_map_eq_zero_iff | proved and audited | Same domain; Phi=0 iff z^(2*k+1)=1. |
| FiniteField.oddPell_map_eq_neg_two_iff | proved and audited | Same domain; Phi=-2 iff z^(2*k+1)=-1. |

No assumption excludes odd indices divisible by the characteristic. This module is the algebraic input to the selected odd-semigroup mass problem. The subsequent maintained owner QuadraticPairOddPellSectors now proves its exact native split/nonsplit endpoint input counts. QuadraticPairOddPellMean now proves the full weighted probability formula at every nonzero shift. QuadraticPairOddPellMinimum now proves the full2-primary minimum and modulo-eight attainment classification.

benchmark_status: structural input formalization;8 real theorems and2 definitions, with new-only foundational-axiom audit.
old_bound: the cubic transport and its uniform3-power survival were installed; no all-index native Pell trace and endpoint package was exported.
new_bound: the integer-window mass and certified QRH boundary are unchanged. The new exact endpoint equivalences hold for every nonnegative k over every field with2 nonzero.
components: coupled recurrence, conserved quadratic form, both square multipliers, joint trace induction, scaled map identities, nonzero scalar cancellation and both endpoint iff directions.
actuals: finite falsification for the still-unproved mass candidate covered2758 odd-index profiles,99078 point checks and10692 all-shift affine checks across15 fields, including extensions and characteristic-divisible indices. These are finite diagnostics, not proof of the proposed mass or minimum formula.
first_nonpositive_domain: no signed-mass bound is claimed. The trace hypotheses require2*z nonzero. The full finite-field weighted profile and natural-height integer pair mass remain open.

## Native trace fibers and torus kernel counts (2026-10-31)

Owner: PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairTraceTori.lean

Definition: FiniteField.oddTraceInput z=(z-1)^2/(2*z).

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| FiniteField.pow_card_eq_self_iff_mem_range | proved and audited | Any extension K/F of a finite field, including infinite K: y^card(F)=y iff y is in the embedded base field. |
| FiniteField.oddTraceInput_map | proved and audited | Every field homomorphism; exact compatibility with the normalized trace coordinate. |
| FiniteField.oddTraceInput_sub_scaled | proved and audited | Nonzero z,w and 2; the full scaled trace difference factors as (z-w)*(z*w-1). |
| FiniteField.oddTraceInput_eq_iff | proved and audited | Same domain; equal trace inputs iff z=w or z*w=1. |
| FiniteField.oddTraceInput_eq_zero_iff | proved and audited | Nonzero z and 2; the zero input has exactly the endpoint z=1. |
| FiniteField.oddTraceInput_eq_neg_two_iff | proved and audited | Same domain; the negative endpoint input has exactly z=-1. |
| FiniteField.exists_oddTraceInput | proved and audited | Algebraically closed K with 2 nonzero; every input has a nonzero trace representative. |
| FiniteField.oddTraceInput_mem_base_iff | proved and audited | K/F as above with 2 nonzero; trace input lies in F iff z^(q-1)=1 or z^(q+1)=1. |
| FiniteField.card_oddTraceInput_image | proved and audited | Any finite inverse-closed nonzero set S containing 1 and -1, with 2 nonzero: card(S)+2=2*card(trace image). |
| FiniteField.exists_torus_power_kernel | proved and audited | Every n>=1 and d>=0 in a field with enough n-th roots of unity; a finite set of all joint n-th and d-th roots has cardinal gcd(n,d). |
| FiniteField.exists_torus_trace_kernel_image | proved and audited | Same root hypothesis, (-1)^n=1 and 2 nonzero; simultaneous n-th and (2*m)-th roots have trace-image count satisfying 2*card(image)=gcd(n,2*m)+2, for every m>=0. |

These are classical geometric and group-theoretic inputs to the selected odd-semigroup mass problem. No characteristic-coprimality condition is imposed on d or m. The subsequent owner QuadraticPairOddPellSectors now proves the actual split/nonsplit input cardinalities; QuadraticPairOddPellMean now proves their weighted mean at every nonzero shift. QuadraticPairOddPellMinimum now proves the full2-primary minimum and modulo-eight attainment consumer.

benchmark_status: exact input formalization;11 real theorems and1 definition, with new-only foundational-axiom audit.
old_bound: all-index Pell endpoint recovery was exported, but the native trace-fiber and finite torus cardinality bridge was not.
new_bound: the generic joint-root count is exactly gcd(n,d), and the joint endpoint trace image satisfies 2*card(image)=gcd(n,2*m)+2. Integer-window positive mass and the certified QRH boundary remain unchanged.
components: polynomial root bound, extension-field Frobenius, exact scaled trace factorization, reciprocal fibers, both singleton endpoints, fiberwise finite sums and the cyclic power-kernel cardinal theorem.
actuals: universal symbolic proofs; no new finite diagnostic is used as evidence for the weighted mean or minimum formula.
first_nonpositive_domain: no signed integer-mass lower bound is installed. The trace count requires 2 nonzero and both endpoint roots; the full finite-field weighted profile and natural-height integer pair mass remain open.

## Native split/nonsplit Pell endpoint counts (2026-10-31)

Owner: PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellSectors.lean

Definition: FiniteField.oddPellEndpointSector P k is the finite set of c outside {0,-2} satisfying P c and oddPellMap c k in {0,-2}. The input precedes the index in oddPellMap.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| FiniteField.oddTraceInput_discriminant_square | proved and audited | Every field with2 nonzero and z nonzero: (z-(t(z)+1))^2=t(z)*(t(z)+2). |
| FiniteField.oddTraceInput_discriminant_isSquare_iff_mem_base | proved and audited | Any field extension K/F with2 nonzero, t(z)=c in F: c*(c+2) square in F iff z belongs to embedded F; includes both endpoints. |
| FiniteField.pow_card_sub_one_eq_one_iff_mem_range | proved and audited | Any extension of a finite field, z nonzero: z^(q-1)=1 iff z belongs to embedded F. |
| FiniteField.oddPell_map_endpoint_union_iff | proved and audited | Every field with2 nonzero: Phi_k(t(z)) is0 or-2 iff z^(2*(2*k+1))=1. |
| FiniteField.oddPell_pair_map | proved and audited | Every homomorphism of commutative rings; both coordinates of the all-index recurrence commute with the map. |
| FiniteField.oddPell_map_map | proved and audited | Same domain; the actual Pell map commutes with the ring homomorphism. |
| FiniteField.exists_base_torus_trace_kernel | proved and audited | Enough n-th roots and the explicit trace-descent condition; a native finite set C of all trace inputs has 2*card(C)=gcd(n,2*m)+2. |
| FiniteField.card_oddPell_endpoint_sector | proved and audited | Algebraically closed extension, enough n-th roots, both endpoint roots and an explicit nonendpoint sector criterion; gives2*card(sector)+2=gcd(n,2*m). |
| FiniteField.oddPell_endpoint_split_nonsplit_counts | proved and audited | All odd finite fields, all k>=0: both sector criteria and enough-roots conditions are discharged at n=q-1 and q+1. The two actual nonendpoint collapsed-input counts satisfy2*N+2=gcd(q-1,2*m) and2*N+2=gcd(q+1,2*m), m=2*k+1. |

The last theorem is unconditional on the field and index apart from2 nonzero. In particular q=3 and characteristic-divisible indices are included. The normalized probability law requires q>=5; the weighted mean is now proved in QuadraticPairOddPellMean, and QuadraticPairOddPellMinimum now proves the2-primary semigroup optimum.

benchmark_status: exact native cardinality bridge;9 real theorems and1 definition, with new-only foundational-axiom audit.
old_bound: only generic trace-involution image and power-kernel counts were public; the actual base-field Pell endpoint sectors were uncounted.
new_bound: the full nonendpoint split and nonsplit counts are exactly specified by2*N+2=gcd(q-1,2*m) and gcd(q+1,2*m), with every endpoint correction retained.
components: native square-discriminant equivalence, finite-field fixed points, ring-homomorphism transport, joint endpoint kernel, trace descent, both erased endpoints and the concrete q-1/q+1 sector criteria.
actuals: universal symbolic proofs; no finite diagnostic substitutes for a count. The subsequent QuadraticPairOddPellMean promotion proves the exact probability formula.
first_nonpositive_domain: the integer-window positive-mass problem and certified QRH boundary are unchanged. The generic sector theorem has stated root/descent hypotheses, all discharged in the concrete joint count. The later Mean owner proves the weighted mean; QuadraticPairOddPellMinimum now proves the exact optimized semigroup minimum.

The Pell and Chebyshev identities are classical inputs. Historical priority of the proposed weighted odd-semigroup extremal application remains unconfirmed. This input promotion neither rebrands the existing finer cubic absorption problem as new nor changes H1, RH or QRH. QRH stays paused and7/8 unchanged.

## Exact odd-Pell means at every nonzero shift (2026-10-31)

The maintained owner `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellMean.lean` proves the complete trace-free mean at every nonzero shift h, for every odd finite field q>=5 and every k>=0, with m=2*k+1 and t=chi(-1):

`mean = 1 - ((q+t)*(gcd(q-1,m)-1) + (q-t)*(gcd(q+1,m)-1))/(q*(q-3))`.

Its definition `FiniteField.oddPellShiftMap h c k` is `(h/2)*oddPellMap ((2/h)*c) k`. The argument order is input c followed by index k. The actual endpoint masks, collapsed source weights and both split/nonsplit sectors are retained; no characteristic-coprimality hypothesis is introduced.

| Maintained declaration | Status and exact scope |
| --- | --- |
| `FiniteField.oddPell_collapsed_numerator` | Lean proved in QuadraticPairOddPellMean; exact intermediate identity with the source theorem's stated hypotheses; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPell_collapsed_weight` | Lean proved in QuadraticPairOddPellMean; exact intermediate identity with the source theorem's stated hypotheses; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPell_weight_loss_pointwise` | Lean proved in QuadraticPairOddPellMean; exact intermediate identity with the source theorem's stated hypotheses; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPell_weight_loss_sectors` | Lean proved in QuadraticPairOddPellMean; exact intermediate identity with the source theorem's stated hypotheses; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPell_weight_sum` | Lean proved in QuadraticPairOddPellMean; exact intermediate identity with the source theorem's stated hypotheses; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPell_gcd_twice_index` | Lean proved in QuadraticPairOddPellMean; exact intermediate identity with the source theorem's stated hypotheses; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPell_mean` | Lean proved in QuadraticPairOddPellMean; exact shift-two expectation, q>=5, every k; maintained compilation and new-only axiom audit. |
| `FiniteField.traceFreePairNumerator_common_scale` | Lean proved in QuadraticPairOddPellMean; exact intermediate identity with the source theorem's stated hypotheses; maintained compilation and new-only axiom audit. |
| `FiniteField.traceFreePairWeight_common_scale` | Lean proved in QuadraticPairOddPellMean; exact intermediate identity with the source theorem's stated hypotheses; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPellShiftMap_reachable` | Lean proved in QuadraticPairOddPellMean; scaled square reach over every field with 2 and h nonzero; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPellShiftMap_two` | Lean proved in QuadraticPairOddPellMean; shift-two specialization over every field with 2 nonzero; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPell_shift_mean` | Lean proved in QuadraticPairOddPellMean; full all-nonzero-shift expectation, q>=5, every k; maintained compilation and new-only axiom audit. |

The supporting owner `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellArithmetic.lean` supplies the following distinct optimization inputs.

| Maintained declaration | Status and exact scope |
| --- | --- |
| `FiniteField.oddPell_exists_two_part` | Lean proved in QuadraticPairOddPellArithmetic; every positive natural has a power-of-two times odd decomposition; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPell_gcd_odd_bound` | Lean proved in QuadraticPairOddPellArithmetic; the gcd with an odd index is at most the stated odd part; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPell_gcd_odd_product_left` | Lean proved in QuadraticPairOddPellArithmetic; the same odd product attains the corresponding gcd maximum; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPell_gcd_odd_product_right` | Lean proved in QuadraticPairOddPellArithmetic; the same odd product attains the corresponding gcd maximum; maintained compilation and new-only axiom audit. |
| `FiniteField.oddPell_character_mod_four` | Lean proved in QuadraticPairOddPellArithmetic; quadratic phase is +1 at q=1 mod4 and -1 at q=3 mod4, for every odd finite field; maintained compilation and new-only axiom audit. |

The full weighted minimum and its2-primary/modulo-eight attainment classification are now proved in QuadraticPairOddPellMinimum. The mean, all-shift adapter and extremal consumer are all maintained Lean proofs.

benchmark_status: exact all-shift probability formula,12 mean/transport theorems,5 arithmetic theorems and1 definition; new-only foundational-axiom audit.
old_bound: native endpoint-sector cardinalities were proved, but the full trace-free expectation and all-shift transfer were pending.
new_bound: the exact displayed expectation holds uniformly for every odd q>=5, every h nonzero and every odd degree m=2*k+1, including characteristic-divisible m.
components: collapsed-row signed numerator, pointwise two-sector loss, exact native counts, odd gcd simplification, mean-one normalization, common scaling with both masks and a field bijection.
actuals: universal symbolic proofs; no numerical completion of the optimized minimum or integer-window survivor count.
first_nonpositive_domain: the exact optimized semigroup minimum is now proved in QuadraticPairOddPellMinimum; positive joint mass in an integer primality window remains open. H1, RH and the paused7/8 QRH boundary are unchanged.

The trace and torus ingredients are classical. Priority of the weighted odd-semigroup extremal application remains unconfirmed.


## Exact odd-Pell semigroup minimum and modulo-eight attainment (2026-10-31)

Maintained owner: `PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellMinimum.lean`.

For every odd finite field F of order q>=5, every nonzero h and every k>=0, the actual expectation is bounded below by `C/q+(q+1)*(C-u)/(q*(q-3))`, where `C=oddPellCoreCard(F)`, `4*C=q-chi(-1)` and `C=2^s*u` with u odd. There exists an index attaining this value. Some index attains the unrestricted square-transport minimum C/q iff q mod8 is3 or5.

| Maintained declaration | Status and exact scope |
| --- | --- |
| `FiniteField.oddPell_minimum_odd_parts` | Lean proved: uniform lower bound and actual attainment from both odd parts; same odd product attains both gcd maxima. Maintained source compilation and new-only foundational-axiom audit. |
| `FiniteField.oddPell_core_count` | Lean proved: exact integer identity 4*C=q-chi(-1), for every odd finite field. Maintained source compilation and new-only foundational-axiom audit. |
| `FiniteField.oddPell_core_pos` | Lean proved: mandatory core cardinality is positive for q>=5. Maintained source compilation and new-only foundational-axiom audit. |
| `FiniteField.oddPell_core_odd_iff` | Lean proved: core cardinality is odd iff q mod8 is3 or5; every odd finite field. Maintained source compilation and new-only foundational-axiom audit. |
| `FiniteField.oddPell_minimum_core_parts` | Lean proved: exact lower bound C/q+(q+1)*(C-u)/(q*(q-3)) and attainment, for each odd decomposition C=2^s*u. Maintained source compilation and new-only foundational-axiom audit. |
| `FiniteField.oddPell_minimum` | Lean proved: unconditional existence of the odd decomposition and the attained exact minimum, all odd q>=5 and all nonzero shifts. Maintained source compilation and new-only foundational-axiom audit. |
| `FiniteField.oddPell_attains_core_iff` | Lean proved: some odd-Pell index reaches C/q iff C is odd, in both directions. Maintained source compilation and new-only foundational-axiom audit. |
| `FiniteField.oddPell_attains_minimum_iff` | Lean proved: some odd-Pell index reaches the unrestricted minimum C/q iff q mod8 is3 or5, in both directions. Maintained source compilation and new-only foundational-axiom audit. |

The four maintained definitions are `FiniteField.oddPellExpectedWeight` (the actual normalized expectation), `FiniteField.oddPellGcdMass` (the exact odd-part expression), `FiniteField.oddPellCoreCard` (the finite mandatory-core count) and `FiniteField.oddPellCoreMass` (the displayed exact minimum expression). The full target is proved, rather than only its mean, cardinality or gcd inputs.

benchmark_status: exact attained finite-field minimum and complete modulo-eight criterion,8 real theorems and4 definitions.
old_bound: the all-shift mean and simultaneous odd gcd maxima were public; their full weighted optimum and residue-class attainment were pending.
new_bound: exact attained minimum C/q+(q+1)*(C-u)/(q*(q-3)), with C=2^s*u and u odd; attainment of C/q iff q mod8 in{3,5}.
components: retained two-sector mean, simultaneous odd product, both quadratic phase cases, exact core count, positive denominators, positive divisor comparison and both parity directions.
actuals: universal symbolic Lean proofs over every stated field, shift and index; no finite diagnostic substitutes for a bound.
first_nonpositive_domain: the normalized theorem excludes q=3 because q-3 vanishes; the core-count and parity results include it. The integer-window joint survivor estimate remains open. H1, RH and the paused7/8 QRH boundary are unchanged.

The classical trace and torus inputs are not novelty claims. Priority of this weighted odd-semigroup optimization remains unconfirmed.


## Full odd-Pell joint defects and signed energy (2026-10-31)

Owners: PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellOverlap.lean and QuadraticPairOddPellEnergy.lean.
Export: QuadraticPairOddPellLaws through the existing CorrelationLaws and root Mathlib facade.

The following entries are real maintained Lean proofs. The final focused owner and public consumer builds, new-only foundational-axiom audit, staged fast checks and paper compilation accompany the promotion.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| FiniteField.oddPell_gcdIndex_degree | proved | The defined gcd index has degree gcd(2*k+1,2*l+1). |
| FiniteField.oddPell_trace_common_endpoints | proved | Joint trace endpoint condition equals the gcd-degree condition. |
| FiniteField.oddPell_common_endpoints | proved | Every field with 2 nonzero; common native endpoints equal the gcd-degree endpoints. |
| FiniteField.oddPell_endpoint_sector_inter | proved | Exact finite sector intersection, for any fixed sector predicate. |
| FiniteField.oddPell_common_sector_counts | proved | Both native common-sector counts with the doubled gcd exponents. |
| FiniteField.oddPell_common_sector_sizes | proved | Counts plus one equal gcd(q-1,gcd(m_k,m_l)) and gcd(q+1,gcd(m_k,m_l)). |
| FiniteField.oddPell_totient_gcd_kernel | proved | Every positive N and every k,l; exact finite odd-divisor kernel. |
| FiniteField.oddPell_gcd_energy_diagonal | proved | Every positive N, finite index support and arbitrary real signed coefficients. |
| FiniteField.oddPell_defect_two_mask | proved | Exact normalized-shift defect including both endpoint exclusions. |
| FiniteField.oddPell_defect_meet_two | proved | Pointwise product is the squared gcd-index defect at shift 2. |
| FiniteField.oddPell_defect_normalize | proved | The same nonzero-shift scaling transports every index. |
| FiniteField.oddPell_defect_meet | proved | Pointwise gcd meet at every nonzero shift. |
| FiniteField.oddPell_defect_square_sectors | proved | Both squared sector weights; opposite-sector cross terms vanish by disjointness. |
| FiniteField.oddPell_defect_square_sum | proved | Exact split and nonsplit second moments. |
| FiniteField.oddPell_defect_inner_two | proved | Complete normalized bilinear gcd kernel at shift 2. |
| FiniteField.oddPell_defect_inner | proved | Complete normalized bilinear kernel at every nonzero shift. |
| FiniteField.oddPell_defect_energy | proved | Every odd finite field q>=5, every nonzero shift, finite support S and arbitrary real coefficients; full totient diagonalization with every signed cross term retained. |
| FiniteField.oddPell_defect_zero | proved | Degree one has identically zero defect at every admissible shift. |
| FiniteField.oddPell_defect_coprime | proved | Coprime odd degrees have pointwise disjoint defects; no independence claim. |

The five definitions are FiniteField.oddPellGcdIndex, FiniteField.oddPellPrimitiveDivisors, FiniteField.oddPellDefect, FiniteField.oddPellSplitWeight and FiniteField.oddPellNonsplitWeight. Algebraic bilinear identities include q=3 as degenerate zero-quotient identities; normalized probability interpretation requires q>=5. Degrees divisible by the characteristic remain allowed.

benchmark_status: exact universal finite signed-energy theorem;19 real theorems and5 definitions, with no nonnegative-coefficient restriction.
old_bound: exact one-point means and attained minimum were available; joint defects and signed combinations had no exported complete kernel.
new_bound: exact all-shift bilinear gcd law and full odd-divisor totient diagonalization; no integer-window lower bound or QRH exponent improvement is claimed.
components: algebraic-closure trace representatives, multiplicative-order gcd meet, native sector intersections and counts, both compensated weights, one common shift bijection and the classical sum-of-totients identity.
actuals: universal symbolic Lean proofs for the stated fields, indices, shifts and signed coefficients; no finite completion or experiment supplies an unresolved estimate.
first_nonpositive_domain: q=3 is excluded from probability normalization. The growing-cutoff integer joint-survivor count remains open; H1, RH and the paused7/8 QRH boundary are unchanged.

Classical trace and totient identities are supporting inputs, not novelty claims. Priority of the masked probability joint-energy theorem remains unconfirmed.


## Primitive odd-Pell atoms: localization inputs (2026-10-31)

Owners: PrimeFactorOscillations/Mathlib/NumberTheory/ArithmeticFunction/DivisorKernelAtoms.lean and PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellConductor.lean.
Export: QuadraticPairOddPellLaws, then the existing correlation and root facades.

These inputs are proved. The following sections prove the arbitrary-test-function law, complete finite signed-span converse, exact support spectrum and attained sharp minimum. The selected localization theorem is complete, including the stated characteristic3 and q3 treatment.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| Finset.mem_divisorKernelAtom | proved | Exact least-active-label atom definition. |
| Finset.divisorKernelAtom_subset | proved | Each atom is contained in its original kernel set. |
| Finset.divisorKernelAtom_disjoint | proved | Distinct admissible least labels give disjoint atoms. |
| Finset.divisorKernel_subset_of_dvd | proved | Divisibility gives inclusion for an exact gcd-intersection family. |
| Finset.divisorKernelAtom_dvd_of_mem | proved | In a finite positive divisor ideal, the primitive label divides every active label. |
| Finset.exists_divisorKernelAtom_of_mem | proved | Every kernel point belongs to an atom labelled by a divisor. |
| Finset.divisorKernel_eq_biUnion_atoms | proved | Exact disjoint divisor cover of each kernel. |
| Finset.divisorKernel_card_sum_atoms | proved | Full finite sum of primitive cardinalities. |
| Finset.divisorKernelAtom_one_card | proved | Under card(E_d)+1=d, the degree-one atom is empty. |
| Finset.divisorKernelAtom_card | proved | Under the same exact cardinalities, every admissible d>1 has primitive cardinality phi(d). |
| FiniteField.oddPell_sectorDivisors_pos | proved | Every odd-divisor label is positive; uses only the finite field cardinal parameter. |
| FiniteField.oddPell_sectorDivisors_down | proved | Full divisor closure of the odd label set. |
| FiniteField.oddPell_degree_sector_card | proved | Every odd m: card(E_(sigma,m))+1=gcd(q-1,m) or gcd(q+1,m). |
| FiniteField.oddPell_degree_sector_inter | proved | Every pair of odd degrees: sector intersection equals the gcd-degree sector. |
| FiniteField.oddPell_degree_sector_gcd | proved | Pointwise equality E_(sigma,m)=E_(sigma,gcd(N_sigma,m)); not merely equal cardinality. |
| FiniteField.oddPell_primitiveSector_card | proved | Every odd d>1 dividing its native modulus: primitive sector cardinality phi(d). |
| FiniteField.oddPell_primitiveSector_disjoint | proved | Different primitive labels in one sector are disjoint. |
| FiniteField.oddPell_primitiveSector_mem_degree | proved | At a primitive d-point, every odd degree m responds iff d divides m. |
| FiniteField.oddPell_degree_sector_eq_biUnion_atoms | proved | Every q>=5 and odd m: complete divisor-atom endpoint cover. |
| FiniteField.oddPell_primitiveSector_opposite_disjoint | proved | Every split primitive atom is disjoint from every nonsplit primitive atom. |

The five definitions are Finset.divisorKernelAtom, FiniteField.oddPellSectorModulus, FiniteField.oddPellSectorDivisors, FiniteField.oddPellDegreeSector and FiniteField.oddPellPrimitiveSector. The label set includes1; its atom has cardinal0. Positive primitive counts require d>1. All field assertions use 2 nonzero when stated, and arbitrary odd degrees remain allowed.

benchmark_status: exact localization inputs proved;20 maintained theorems and5 definitions in these owners. The complete selected localization theorem is proved in the following owners.
old_bound: complete quadratic signed energy, with no exported native primitive-atom partition.
new_bound: disjoint primitive atoms have exact size phi(d), and membership at any odd degree is exactly divisor membership. No new integer-window lower bound or analytic exponent is claimed.
components: least-label gcd rigidity, finite disjoint union, strong divisor induction, sum of totients, native sector gcd intersections, equality from inclusion and cardinality, and both opposite-sector masks.
actuals: universal Lean proofs for the stated divisor ideals, fields and degrees; no finite numerical completion supplies an estimate.
first_nonpositive_domain: degree1 has an empty atom; q3 is outside normalized probability interpretation. The nonlinear law, finite signed-span converse, sharp support spectrum/minimum and q3 quotient degeneracy are proved below. The integer joint-survivor problem, H1/RH and the paused7/8 boundary are unchanged.

The primitive order/totient data are classical inputs, not the proposed novelty claim. The full signed-probe localization spectrum is now proved; historical priority remains unconfirmed.

## Full finite signed odd-Pell distribution (2026-10-31)

Owner: PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellDistribution.lean.
Export: QuadraticPairOddPellLaws, then the existing correlation and root facades.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| FiniteField.oddPell_atomLabels_left | proved | Split labels are exactly the odd divisors d>1 of q-1. |
| FiniteField.oddPell_atomLabels_right | proved | Nonsplit labels are exactly the odd divisors d>1 of q+1. |
| FiniteField.oddPell_atom_card | proved | Every tagged primitive atom has cardinality phi(d). |
| FiniteField.oddPell_atom_disjoint | proved | All distinct tagged atoms are disjoint, including opposite sectors. |
| FiniteField.oddPell_defect_degree_sectors | proved | Exact two-sector pointwise defect, with both weights retained. |
| FiniteField.oddPell_defect_on_atom | proved | A degree-m defect at a primitive d-point is its sector weight iff d divides m. |
| FiniteField.oddPell_probe_on_atom | proved | Arbitrary finite signed coefficients give the exact divisor-filtered probe value. |
| FiniteField.oddPell_exists_atom_of_sector | proved | Every endpoint-sector point belongs to a nonempty-label primitive class. |
| FiniteField.oddPell_defect_off_atoms | proved | Every defect vanishes outside the union of all primitive classes. |
| FiniteField.oddPell_probe_off_atoms | proved | Every finite signed probe vanishes outside that same union. |
| FiniteField.oddPell_probe_distribution_two | proved | Arbitrary real test-function pushforward at shift2, with zero compensation. |
| FiniteField.oddPell_probe_normalize | proved | Every nonzero shift transports the whole signed probe by c maps to (2/h)c. |
| FiniteField.oddPell_probe_distribution | proved | Full arbitrary-test-function distribution, every nonzero shift, q>=5 and 2 nonzero. |

The five definitions are FiniteField.oddPellSignedProbe, FiniteField.oddPellAtomLabels, FiniteField.oddPellAtom, FiniteField.oddPellAtomDegree and FiniteField.oddPellAtomWeight. The law averages uniformly over the q input points; it does not sample inputs with density W. No continuity of the test function, RH hypothesis or restriction on characteristic-divisible odd degrees is used.

benchmark_status: exact full pushforward proved;13 maintained theorems and5 definitions in this owner, bringing the localization candidate to33 theorems at this stage. The finite signed-span converse, exact support spectrum and sharp minimum are proved in the following sections.
old_bound: exact signed quadratic energy and native atom partition.
new_bound: complete finite distribution of every signed probe, with atom masses phi(d)/q and an explicitly retained zero-value correction.
components: exact disjoint atom cover, divisor-filtered signed values, compensation f(value)-f(0), finite sum interchange and nonzero-shift bijection.
actuals: universal Lean proofs over the stated full domain; no numerical estimate is substituted.
first_nonpositive_domain: signed divisor sums may vanish, so a probe can erase an atom. This is included exactly in the law. Arbitrary atom isolation is proved below; integer-window survivor positivity, H1/RH and the paused7/8 boundary remain unchanged.

## Complete finite signed odd-Pell span (2026-10-31)

Owner: PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellLocalization.lean.
Export: QuadraticPairOddPellLaws, then the existing correlation and root facades.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| FiniteField.oddPell_splitWeight_pos | proved | q>=5 makes the split weight strictly positive. |
| FiniteField.oddPell_nonsplitWeight_pos | proved | q>=5 makes the nonsplit weight strictly positive. |
| FiniteField.oddPell_atomWeight_pos | proved | Every tagged primitive weight is strictly positive. |
| FiniteField.oddPell_atomDegree_pos | proved | Every admissible primitive degree is positive. |
| FiniteField.oddPell_atomDegree_odd | proved | Every admissible primitive degree is odd. |
| FiniteField.oddPell_atomDegree_injective | proved | At q>=5, equal primitive degrees force equal tagged labels, including across sectors. |
| FiniteField.oddPell_probe_add | proved | Exact finite union and zero-extension construction for addition of signed probes. |
| FiniteField.oddPell_mem_probeSpace | proved | Membership means an actual finite index set and real coefficient function represent the input function. |
| FiniteField.oddPell_defect_mem_probeSpace | proved | Every individual defect is a singleton finite signed probe. |
| FiniteField.oddPell_probe_atom_expansion | proved | Complete pointwise primitive-indicator expansion of every signed probe at every nonzero shift. |
| FiniteField.oddPell_defect_atom_expansion | proved | Exact divisor-triangular primitive-indicator expansion of every individual defect. |
| FiniteField.oddPell_atomIndicator_mem_probeSpace | proved | Each primitive indicator has a finite signed Pell representation, by strong divisor induction and positive-weight inversion. |
| FiniteField.oddPell_probeSpace_iff_atom_expansion | proved | Complete converse: finite signed probes are exactly arbitrary real combinations of the finitely many primitive indicators. |

The two definitions are FiniteField.oddPellAtomIndicator and FiniteField.oddPellProbeSpace. The latter's carrier explicitly requires a finite index set and coefficient function; no abstract or infinite representability assumption replaces a finite probe. Every field-level converse holds for every nonzero h, q>=5 and 2 nonzero.

benchmark_status: full finite signed-span converse proved;13 maintained theorems and2 definitions in this owner,46 candidate theorems and12 definitions through this stage. The next owner completes A5 sharp support/minimum and A6 integration.
old_bound: full forward distribution with exact signed values on primitive classes, without converse finite representability.
new_bound: every primitive indicator and every finite real combination of them is an actual finite signed probe; this characterizes the entire probe space.
components: positive native weights, no equal primitive degrees across sectors, finite union coefficient construction, full pointwise expansion and strict proper-divisor induction with signed subtraction.
actuals: universal Lean proofs over the full stated field and shift domain; no finite computations or unproved analytic inputs.
first_nonpositive_domain: every sector weight is positive at q>=5. The q3 quotient degeneracy and sharp support-cardinality/minimum theorem are proved below. No new integer-window positivity or RH/QRH gain is claimed. Historical priority remains unconfirmed.

## Exact signed odd-Pell support spectrum and minimum (2026-10-31)

Owner: PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellSpectrum.lean.
Export: QuadraticPairOddPellLaws, then the existing correlation and root facades.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| FiniteField.oddPell_mem_shiftAtom | proved | Exact inverse-scaling membership for every nonzero shift and 2 nonzero. |
| FiniteField.oddPell_shiftAtom_card | proved | Every transported primitive class has cardinality phi(d). |
| FiniteField.oddPell_shiftAtom_disjoint | proved | Distinct primitive classes remain disjoint under every nonzero shift. |
| FiniteField.oddPell_mem_functionSupport | proved | Exact finite support is the set of inputs with nonzero real value. |
| FiniteField.oddPell_atomIndicator_eq_shiftAtom | proved | Each normalized primitive indicator is the indicator of its transported class. |
| FiniteField.oddPell_atom_sum_on_shiftAtom | proved | A finite primitive-indicator sum has precisely its assigned coefficient on each class. |
| FiniteField.oddPell_atom_sum_support | proved | Exact support is the disjoint union of classes with nonzero coefficients, including every signed cancellation. |
| FiniteField.oddPell_shiftAtom_union_card | proved | Every selected class union has cardinality equal to its exact totient sum. |
| FiniteField.oddPell_probe_support_iff_union | proved | A finite set is an actual finite signed probe support iff it is a union of primitive classes. |
| FiniteField.oddPell_support_card_spectrum | proved | All attainable support sizes are exactly all totient subset sums, including zero. |
| FiniteField.oddPell_atomLabels_nonempty | proved | The primitive label set is nonempty at every q>=5. |
| FiniteField.oddPell_minSupport_spec | proved | The explicit finite minimum is attained by a primitive label and is no larger than any primitive class size. |
| FiniteField.oddPell_atom_totient_two_le | proved | Every nonempty-label primitive class has at least two points. |
| FiniteField.oddPell_minSupport_two_le | proved | The exact minimum is at least two for every q>=5. |
| FiniteField.oddPell_functionSupport_nonempty_iff | proved | A function has nonempty finite support iff it is not the zero function. |
| FiniteField.oddPell_sharp_support_minimum | proved | Every nonzero finite signed probe has support at least m(q), and an actual finite probe attains m(q), every nonzero shift and odd q>=5. |
| FiniteField.oddPell_minSupport_eq_two_of_not_three_dvd | proved | The exact minimum is2 whenever3 does not divide q. |
| FiniteField.oddPell_card_three_probe_zero | proved | At q3 every quotient-defined finite signed probe vanishes, for every nonzero shift. |
| FiniteField.oddPell_minSupport_card_three | proved | The empty-label minimum convention at q3 is0. |
| FiniteField.oddPell_minSupport_card_nine | proved | The exact minimum at q9 is4. |
| FiniteField.oddPell_minSupport_card_twentyseven | proved | The exact minimum at q27 is6. |
| FiniteField.oddPell_minSupport_card_twofortythree | proved | The exact minimum at q243 is10. |

The three definitions are FiniteField.oddPellShiftAtom, FiniteField.oddPellFunctionSupport and FiniteField.oddPellMinSupport. The last is the minimum of the finite primitive totient set, with0 for an empty set. At q>=5 the set is proved nonempty. Actual finite signed representability comes from the maintained probe-space carrier and the completed converse; no completion or unproved inverse hypothesis is used.

benchmark_status: complete selected localization theorem proved;22 new maintained theorems and3 definitions,68 candidate theorems and15 definitions cumulatively. A0-A6 are complete after the recorded promotion checks.
old_bound: forward distribution and finite signed-span classification, without an exported support spectrum or sharp minimum.
new_bound: exact support sets and cardinalities; attained m(q)=min phi(d) over all tagged odd d>1 dividing q-1 or q+1, m(q)>=2 and m(q)=2 if3 does not divide q. At q9,27,243 the exact minima are4,6,10; q3 probes vanish.
components: shift bijection, disjoint native classes, exact signed coefficient values, finite-probe converse, full subset-sum spectrum, explicit ordinary-order finite minimum and both lower-bound and attainment proofs.
actuals: universal Lean proofs for the full domain; the four fixed-cardinality formulas are additional kernel-checked consequences, not evidence for the universal statement.
first_nonpositive_domain: support0 is attained by the zero probe. Nonzero normalized probes use odd q>=5; q3 is explicitly degenerate and is not a normalized mean-one probability law. No integer-window positivity or RH/QRH gain is claimed. Historical priority remains unconfirmed.

## Prime-extension signed support lattice and Sophie Germain endpoint (2026-10-31)

Owners: PrimeFactorOscillations/Mathlib/NumberTheory/ArithmeticFunction/PrimeExtensionTotient.lean and PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellPrimeExtension.lean.
Export: QuadraticPairOddPellLaws, then the existing correlation and root facades.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| Nat.primeExtension_primeFactor_progression | proved | For odd prime ell, every odd prime divisor p of 3^ell-1 or 3^ell+1 satisfies 2*ell dividing p-1. |
| Nat.primeExtension_totient_dvd | proved | Every prime ell, including2, and every admissible odd d>1 have 2*ell dividing phi(d); ell2 is handled explicitly. |
| Nat.primeExtension_safePrime_factor | proved | For every ell>=2, primality of 2*ell+1 supplies its divisibility into 3^ell-1 or 3^ell+1. |
| Nat.primeExtension_endpoint_prime | proved | An admissible d with phi(d)=2*ell forces 2*ell+1 prime. |
| FiniteField.oddPell_primeExtension_atom_totient_dvd | proved | Every primitive class at q=3^ell has size divisible by 2*ell. |
| FiniteField.oddPell_primeExtension_minSupport_dvd | proved | The attained sharp minimum is divisible by 2*ell. |
| FiniteField.oddPell_primeExtension_minSupport_lower | proved | The sharp minimum is at least 2*ell. |
| FiniteField.oddPell_primeExtension_support_dvd | proved | Every actual finite real signed probe has support size divisible by 2*ell, including the zero probe. |
| FiniteField.oddPell_primeExtension_minSupport_eq_iff_prime | proved | The sharp minimum equals 2*ell iff 2*ell+1 is prime. |
| FiniteField.oddPell_primeExtension_minSupport_composite_gap | proved | If 2*ell+1 is not prime, the sharp minimum is at least 4*ell. |
| FiniteField.oddPell_primeExtension_endpoint_iff_prime | proved | For every nonzero shift, an actual nonzero finite signed probe of support 2*ell exists iff 2*ell+1 is prime. |

The extension degree ell is prime and includes2. It is independent of the polynomial index k, whose odd-Pell degree is2*k+1. Native support statements retain a finite field of cardinality 3^ell, h nonzero, 2 nonzero, arbitrary finite index support and arbitrary real signed coefficients. Scalar minimum statements use only the cardinality and the finite primitive-label formula. No new definitions, infinite completion, RH hypothesis, conditional zero detector or integer-window positivity assumption is used.

benchmark_status: full selected prime-extension theorem proved;11 new maintained public theorems and0 definitions. The earlier completed localization package remains68 theorems and15 definitions.
old_bound: exact support subset-sum spectrum and attained minimum m(q)>=2 for general odd q>=5.
new_bound: at q=3^ell for every prime ell, all support sizes are multiples of2*ell, m(q)>=2*ell, m(q)=2*ell iff 2*ell+1 is prime, and otherwise m(q)>=4*ell.
components: exact full signed support spectrum; multiplicative order of9 modulo every admissible odd prime; totient divisibility; explicit degree2 case; safe-prime Fermat supply; attained primitive minimum and actual finite representability.
actuals: universal kernel-checked proofs over the full prime-ell domain; the finite degree2 exception is justified after the symbolic split. No numerical experiment or unresolved analytic completion supplies the bound.
first_nonpositive_domain: zero support is attained by the zero probe; every nonzero probe has the stated positive minimum. The theorem does not prove infinitely many Sophie Germain primes, integer prime pairs, RH or a QRH improvement. The order and totient ingredients are classical; historical priority of the signed-probe support conclusion remains unconfirmed.

## Extension-degree roughness and the tower obstruction (2026-10-31)

Owners: PrimeFactorOscillations/Mathlib/NumberTheory/ArithmeticFunction/TernaryExtensionOrder.lean and PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellRoughness.lean.
Export: QuadraticPairOddPellLaws, then the existing correlation and root facades.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| Nat.ternaryExtension_primeFactor_iff | proved | For every prime p, divisibility into3^n-1 or3^n+1 is equivalent to9^n=1 in ZMod p. |
| Nat.ternaryExtension_primeFactor_lift | proved | Every such prime factor lifts from degree d to degree n whenever d divides n. |
| Nat.ternaryExtension_primeFactor_lower | proved | Every n>=2 and admissible odd prime p satisfy2*minFac(n)<=p-1, using the full square-order half exponent. |
| Nat.ternaryExtension_totient_lower | proved | Every admissible odd d>1 has phi(d)>=2*minFac(n). |
| Nat.ternaryExtension_endpoint_prime | proved | An admissible totient equal to2*minFac(n) forces2*minFac(n)+1 prime. |
| FiniteField.oddPell_ternary_atom_totient_lower | proved | Every primitive class at3^n has at least2*minFac(n) points, all n>=2. |
| FiniteField.oddPell_ternary_minSupport_lower | proved | The attained sharp support minimum is at least2*minFac(n). |
| FiniteField.oddPell_ternary_support_lower | proved | Every nonzero actual finite signed probe has support at least2*minFac(n), every nonzero shift and2 nonzero. |
| FiniteField.oddPell_ternary_minSupport_eq_iff_prime | proved | The attained minimum equals2*minFac(n) iff2*minFac(n)+1 is prime. |
| FiniteField.oddPell_ternary_endpoint_iff_prime | proved | Actual nonzero finite support2*minFac(n) exists iff, every nonzero shift. |
| FiniteField.oddPell_ternary_minSupport_bound_of_degree_dvd | proved | If d>=2 divides n>=2, the minimum at3^n is at most3^d+1. |
| FiniteField.oddPell_ternary_minSupport_upper | proved | The minimum is at most3^minFac(n)+1. |
| FiniteField.oddPell_ternary_minSupport_bounds | proved | Both uniform scalar bounds for the explicitly defined ternary minimum. |
| FiniteField.oddPell_ternary_minSupport_tendsto_iff | proved | For every sequence of degrees a(j)>=2, the minimum tends to infinity iff minFac(a(j)) does. |
| FiniteField.oddPell_ternary_tower_bounded | proved | A fixed d>=2 dividing every degree gives the uniform minimum bound3^d+1. |
| FiniteField.oddPell_ternary_tower_not_tendsto | proved | The minimum cannot tend to infinity along such a fixed-divisor tower. |

The one definition is FiniteField.oddPellTernaryMinSupport n, the existing scalar minimum evaluated at cardinality3^n using Fin(3^n). It records a number; no field structure on Fin(3^n) is assumed. Actual field/probe statements retain the finite field, nonzero shift,2 nonzero, finite polynomial-index support and arbitrary real signed coefficients. All composite and even degrees n>=2 are included. No divisibility of all support sizes by2*minFac(n), or composite-case4*minFac(n) gap, is claimed for composite n.

benchmark_status: complete all-extension classification proved;16 new maintained public theorems and1 definition. The prior completed68-theorem localization and11-theorem prime-extension candidates are preserved.
old_bound: exact finite totient minimum for general fields; explicit2*ell lower bound and endpoint iff only for prime extension degrees.
new_bound: for every n>=2 and r=minFac(n),2*r<=m(3^n)<=3^r+1 and m(3^n)=2*r iff2*r+1 is prime; divergence along every degree sequence is equivalent to divergence of r, with a uniform fixed-divisor tower bound.
components: order_p(9)>1 dividing both n and(p-1)/2, least-prime-factor lower bound, all admissible totients, exact full signed minimum and actual finite attainment, divisor-degree prime-factor lift, and the two explicit scalar bounds.
actuals: universal kernel-checked proofs over the full stated domains; no numerical or unresolved analytic completion is used.
first_nonpositive_domain: zero probes have support0, and n=1 is the earlier q3 degeneracy; all nonzero bounds here require n>=2. Fixed-divisor towers have bounded minima despite growing field size. This proves no integer-window positivity, H1, RH, QRH improvement or Sophie Germain infinitude. Classical arithmetic and Chebyshev geometry are inputs; historical priority of the signed-probe classification remains unconfirmed.

## Forbidden second signed support level and sharp non-Sophie gap (2026-10-31)

Owners: PrimeFactorOscillations/Mathlib/NumberTheory/ArithmeticFunction/PrimeExtensionTotientGap.lean and PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellSupportGap.lean.
Export: QuadraticPairOddPellLaws, then the existing correlation and root facades.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| Nat.primeExtension_composite_totient_lower | proved | Every admissible composite odd d>1 at a prime degree ell has phi(d)>=(2*ell)^2. |
| Nat.primeExtension_small_weight_prime | proved | An admissible degree of weight at most4*ell is prime, all prime ell including2. |
| Nat.primeExtension_first_weight_degree | proved | Weight2*ell forces degree2*ell+1, not merely an unspecified prime factor. |
| Nat.primeExtension_primeFactor_ne_four | proved | An admissible prime p cannot equal4*ell+1 when ell is prime and ell is not3; exact quadratic reciprocity obstruction. |
| Nat.primeExtension_second_weight_iff | proved | Admissible weight4*ell occurs iff ell=3 and d=13. |
| FiniteField.oddPell_primeExtension_first_atom_degree | proved | Every primitive label of weight2*ell has degree2*ell+1. |
| FiniteField.oddPell_primeExtension_second_atom_iff | proved | A primitive label has weight4*ell iff ell=3 and its degree is13. |
| FiniteField.oddPell_primeExtension_support_ne_four | proved | No actual finite real signed probe has support4*ell for prime ell other than3; unique first-weight label excludes a two-atom reconstruction. |
| FiniteField.oddPell_primeExtension_support_four_iff | proved | At every nonzero shift, actual finite signed support4*ell exists iff ell=3, with split degree13 attaining the exception. |
| FiniteField.oddPell_primeExtension_support_gap | proved | For ell not3, every full finite signed support is0,2*ell,or at least6*ell. |
| FiniteField.oddPell_primeExtension_minSupport_nonSophie_gap | proved | If2*ell+1 is not prime, the attained sharp minimum is at least6*ell, every prime ell. |
| FiniteField.oddPell_primeExtension_minSupport_seventeen | proved | The sharp scalar minimum at3^17 is102=6*17, using the nonsplit degree103 class. |
| FiniteField.oddPell_primeExtension_seventeen_attained | proved | At every nonzero shift in a field of cardinality3^17, an actual nonzero finite signed probe has support102. |

All support consumers retain arbitrary finite polynomial-index support, arbitrary real signed coefficients, a finite field of cardinality3^ell, nonzero shift and2 nonzero. The polynomial index is independent of ell. The scalar statements need only the existing cardinality-dependent minimum. Degree2 is included in the universal arithmetic and signed statements; degree3 is the unique exception to the missing second level. No infinite completion, RH assumption or integer-window positivity hypothesis is introduced.

benchmark_status: full selected forbidden-level theorem proved;13 new maintained public theorems and0 definitions. The completed68-theorem localization,11-theorem prime-extension and16-theorem roughness candidates are preserved.
old_bound: nonprime2*ell+1 gave minimum at least4*ell; all supports were known to be multiples of2*ell.
new_bound: nonprime2*ell+1 gives minimum at least6*ell; for ell not3 all full signed supports are0,2*ell,or at least6*ell; support4*ell exists exactly at ell3. The coefficient6 is sharp on the stated domain, attained at ell17.
components: composite totient bound(2*ell)^2; exact quadratic reciprocity exclusion of prime4*ell+1; unique degree2*ell+1 for a first-weight atom; injectivity of primitive labels; exact full signed support subset sum; previous endpoint iff and actual finite attained minimum.
actuals: universal kernel-checked proofs over every prime ell, not finite prime sampling; the degree3 and degree17 witnesses use exact finite representability and integer arithmetic, with no field enumeration.
first_nonpositive_domain: zero probes have support0. Degree3 genuinely attains the excluded level12 and is explicitly retained; degree2 is included and the non-Sophie hypothesis is false there. No composite-degree6*minFac bound, integer prime-pair positivity, H1, RH, QRH improvement or Sophie Germain infinitude is claimed. Classical arithmetic is input; historical priority of the signed-support conclusion remains unconfirmed.

## Sharp prime-conductor window and rational-prime alphabet (2026-10-31)

Owners: PrimeFactorOscillations/Mathlib/NumberTheory/ArithmeticFunction/PrimeExtensionCompositeBarrier.lean and PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellPrimeWindow.lean.
Export: QuadraticPairOddPellLaws, then the existing correlation and root facades.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| Nat.primeExtension_composite_totient_barrier | proved | For every prime ell and admissible composite odd d>1, phi(d)>=2*ell*(2*ell+1); both coprime factors cannot have the first weight. |
| Nat.primeExtension_below_barrier_prime | proved | Every admissible degree with totient below that sharp barrier is prime. |
| Nat.mem_primeExtensionPrimeAlphabet | proved | Exact membership: an odd prime p with p-1<L divides3^ell-1 or3^ell+1. |
| Nat.mem_primeExtensionPrimeAlphabet_power | proved | Exact alternative membership using the complete identity9^ell=1 in ZMod p. |
| Nat.primeExtensionPrimeAlphabet_five | proved | The finite alphabet at ell5 is exactly11,61. |
| Nat.primeExtensionPrimeAlphabet_five_no_boundary_sum | proved | No subset of that alphabet has weight sum110. |
| FiniteField.oddPell_primeWindow_support_iff_union | proved | Every support set of cardinality below L=2*ell*(2*ell+1) is attainable iff it is a union of prime-degree primitive shifted classes, with actual finite converse. |
| FiniteField.oddPell_primeWindow_support_card_iff | proved | For every n<L, actual finite signed support n exists iff n is a subset sum of p-1 over the rational-prime alphabet; degree injectivity preserves multiplicity one. |
| FiniteField.oddPell_primeWindow_nonzero_iff | proved | At every nonzero shift, a nonzero actual finite signed probe below L exists iff the rational-prime alphabet is nonempty. |
| FiniteField.oddPell_primeWindow_five_boundary_attained | proved | At q=3^5, every nonzero shift has an actual nonzero finite signed probe with support110, from the composite degree121 class. |

The definition Nat.primeExtensionPrimeAlphabet ell is a computable finite range filtered by primality, oddness and the exact divisibility disjunction. It tests small rational primes and does not require factoring3^ell-1 or3^ell+1. The theorem gives the full signed-support window, not an assumed count of primes in an integer window. Every prime ell including2 and3, n0, arbitrary finite polynomial-index support and arbitrary real signed coefficients remain in scope. Field support statements retain cardinality3^ell, h nonzero and2 nonzero.

benchmark_status: complete selected sharp-window theorem proved;10 new maintained public theorems and1 definition. The completed68/11/16/13-theorem candidates are preserved.
old_bound: composite atom totients were bounded below by(2*ell)^2; the exact full support spectrum still ranged over all primitive divisors.
new_bound: composite atoms have size at least L=2*ell*(2*ell+1); the whole support spectrum below L is exactly the subset sums of p-1 over the bounded rational-prime alphabet, with both actual finite converse directions. The strict cutoff is sharp at ell5, where L110 is attainable but no alphabet subset sum110 exists.
components: first-weight degree uniqueness, coupled coprime-factor totient product, repeated-prime square contribution, exact signed support union, primitive degree injectivity, full finite-span converse and the complete modular-power adapter.
actuals: universal kernel-checked proofs over every prime degree and every n<L. The fixed ell5 alphabet and boundary witness are exact consequences after the universal argument; no field enumeration or numerical completion supplies it.
first_nonpositive_domain: zero support is included; the alphabet may be empty and no unconditional nonempty claim is made. The boundary n=L genuinely fails at ell5. No composite-degree lift, integer prime-pair positivity, H1, RH, QRH improvement or prime infinitude is claimed. Classical arithmetic is input; historical priority of the full signed-window statement remains unconfirmed.

## Complete stable signed-support spectrum in odd characteristic (2026-10-31)

The characteristic p, extension degree m, tower stage j, primitive degree d, polynomial probe index k and actual support size N are distinct. At every nonzero shift and with2 nonzero, the full actual finite real signed-probe spectrum stabilizes to all even N, except2/8 in characteristic3 and4 in characteristic5. The explicit tower degrees are720*5^j,720*3^j,12*3^j, respectively. Every allowed N occurs at every j>=N, with a finite-index, real-coefficient witness supported entirely on split primitive classes. The quantitative horizons are310*5^j-6,186*3^j+2,21*3^j-1, respectively, with the same permanent holes. Global exclusions apply to arbitrary signed probes, not just the constructive degree families.

Owner: PrimeFactorOscillations/Mathlib/NumberTheory/ArithmeticFunction/TotientSubsetSumIntervals.lean.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| Finset.subset_sum_interval_insert | proved | Adding a new indexed weight w extends [A,S-A] to [A,S+w-A] when w+2A<=S+1. |
| Finset.subset_sum_interval_insert_block | proved | Ordered distinct new indices extend a subset-sum interval with every prefix weight retained. |
| Nat.oddTotient_base_three_interval | proved | Exact finite base certificate for degrees5,7,11,13,17,19 with normalized interval center exclusion A=5. |
| Nat.oddTotient_base_five_interval | proved | Exact finite base certificate for degrees3,7,9,11,13,17,19 with normalized interval center exclusion A=3. |
| Nat.oddTotient_base_other_interval | proved | Exact finite base certificate for degrees3,5 with normalized interval center exclusion A=0. |

Supporting definitions: Finset.subsetSumInterval, Finset.subsetSumAdmissibleBlock.

Owner: PrimeFactorOscillations/Mathlib/NumberTheory/ArithmeticFunction/OddTotientFamilies.lean.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| Nat.oddTotient_auxiliary_data | proved | The five auxiliary primes are odd, lie in [7,19], avoid3/5, and have totients dividing720. |
| Nat.oddTotient_prime_power_unit_injective | proved | For prime r and positive units avoiding r, equality u*r^a=v*r^b forces u=v and a=b. |
| Nat.oddTotient_scaled_three_weight | proved | The exact normalized weight of e*3^(i+1) is phi(e)*3^i when e is coprime to3. |
| Nat.oddTotient_scaled_five_weight | proved | The exact normalized weight of e*5^(i+1) is2*phi(e)*5^i when e is coprime to5. |
| Nat.oddTotient_scaled_blocks_disjoint | proved | Every two distinct stages of a unit-prime scaled degree family are disjoint. |
| Nat.oddTotient_base_scaled_block_disjoint | proved | A base bounded by19 is disjoint from every auxiliary-prime block scaled by r>=3. |
| Nat.oddTotient_scaled_five_block_sum | proved | Every five-scaled block has total normalized weight124*5^i. |
| Nat.oddTotient_scaled_three_block_sum | proved | Every three-scaled block has total normalized weight62*3^i. |
| Nat.oddTotient_base_weight_sums | proved | The three exact base totals are33,35,3. |
| Nat.oddTotient_three_mem_cases | proved | Every member of the characteristic3 family is a base degree or belongs to one block i<=j. |
| Nat.oddTotient_five_mem_cases | proved | Every member of the characteristic5 family is a base degree or belongs to one block i<=j. |
| Nat.oddTotient_other_mem_cases | proved | Every member of the other odd characteristics family is a base degree or belongs to one block i<=j. |
| Nat.oddTotient_other_blocks_disjoint | proved | The pure3-power and5-times3-power blocks are disjoint at different stages. |
| Nat.oddTotient_base_other_block_disjoint | proved | The base degrees3,5 are disjoint from every other-characteristic block. |
| Nat.oddTotient_other_block_sum | proved | Every other-characteristic block has total normalized weight7*3^i. |
| Nat.oddTotient_three_next_disjoint | proved | The next block is disjoint from the full preceding characteristic3 family. |
| Nat.oddTotient_five_next_disjoint | proved | The next block is disjoint from the full preceding characteristic5 family. |
| Nat.oddTotient_other_next_disjoint | proved | The next block is disjoint from the full preceding other odd characteristics family. |
| Nat.oddTotient_three_total | proved | Exact normalized total 31*5^(j+1)+2 for all stages. |
| Nat.oddTotient_five_total | proved | Exact normalized total 31*3^(j+1)+4 for all stages. |
| Nat.oddTotient_other_total | proved | Exact normalized total (7*3^(j+1)-1)/2 for all stages, stated as2*total+1=7*3^(j+1). |
| Nat.oddTotient_scaled_block_data | proved | Every selected scaled degree is odd, exceeds1, and retains the stated characteristic coprimality. |
| Nat.oddTotient_other_block_data | proved | Every degree3^(i+2) or5*3^(i+1) is odd, exceeds1, and avoids any characteristic coprime to3,5. |
| Nat.oddTotient_three_data | proved | Every degree in the characteristic3 family is odd, exceeds1, and avoids the stated characteristic. |
| Nat.oddTotient_five_data | proved | Every degree in the characteristic5 family is odd, exceeds1, and avoids the stated characteristic. |
| Nat.oddTotient_other_data | proved | Every degree in the other odd characteristics family is odd, exceeds1, and avoids the stated characteristic. |
| Nat.oddTotient_normalized_weight_double | proved | For every odd degree d>1, twice phi(d)/2 equals phi(d) exactly. |
| Nat.oddTotient_sum_normalized_double | proved | The finite totient sum equals twice the normalized indexed weight sum. |

Supporting definitions: Nat.oddTotientAuxiliaryPrimes, Nat.oddTotientBaseThree, Nat.oddTotientBaseFive, Nat.oddTotientBaseOther, Nat.oddTotientScaledBlock, Nat.oddTotientOtherBlock, Nat.oddTotientThreeDegrees, Nat.oddTotientFiveDegrees, Nat.oddTotientOtherDegrees.

Owner: PrimeFactorOscillations/Mathlib/NumberTheory/ArithmeticFunction/OddTotientCoverage.lean.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| Nat.oddTotient_three_interval_step | proved | The ordered characteristic3 block extends the covered interval under its exact first-weight reserve. |
| Nat.oddTotient_five_interval_step | proved | The ordered characteristic5 block extends the covered interval under its exact first-weight reserve. |
| Nat.oddTotient_other_interval_step | proved | The ordered other odd characteristics block extends the covered interval under its exact first-weight reserve. |
| Nat.oddTotient_three_coverage | proved | Universal coverage of every integer in [5,31*5^(j+1)-3] by distinct degree-indexed normalized weights. |
| Nat.oddTotient_five_coverage | proved | Universal coverage of every integer in [3,31*3^(j+1)+1] by distinct degree-indexed normalized weights. |
| Nat.oddTotient_other_coverage | proved | Universal coverage of every integer in [0,(7*3^(j+1)-1)/2] by distinct degree-indexed normalized weights. |
| Nat.oddTotient_stage_le_power | proved | For every r>=2 and every stage j, j+1<=r^j. |
| Nat.oddTotient_three_base_subset | proved | Every base degree5,7,11,13,17,19 remains available at every stage. |
| Nat.oddTotient_five_base_subset | proved | Every base degree3,7,9,11,13,17,19 remains available at every stage. |
| Nat.oddTotient_other_base_subset | proved | Every base degree3,5 remains available at every stage. |
| Nat.oddTotient_three_realize_interval | proved | Every normalized target in [5,31*5^(j+1)-3] gives an actual finite degree subset with total totient twice that target. |
| Nat.oddTotient_five_realize_interval | proved | Every normalized target in [3,31*3^(j+1)+1] gives an actual finite degree subset with total totient twice that target. |
| Nat.oddTotient_other_realize_interval | proved | Every normalized target in [0,(7*3^(j+1)-1)/2] gives an actual finite degree subset with total totient twice that target. |

Owner: PrimeFactorOscillations/Mathlib/NumberTheory/ArithmeticFunction/OddTotientSpectrum.lean.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| Nat.oddTotient_positive_even_lower | proved | Every odd d>1 has phi(d)>=2. |
| Nat.oddTotient_coprime_three_lower | proved | Every odd d>1 coprime to3 has phi(d)>=4. |
| Nat.oddTotient_composite_factor_bound | proved | If every nontrivial divisor of a composite d has totient at least B, then phi(d)>=B^2. |
| Nat.oddTotient_composite_lower_six | proved | Every odd composite degree has totient at least6. |
| Nat.oddTotient_three_small_degrees | proved | An odd degree coprime to3 with totient at most8 is5 or7. |
| Nat.oddTotient_five_small_degree | proved | An odd degree coprime to5 with totient at most4 is3. |
| Nat.oddTotient_three_forbidden | proved | No finite set of distinct admissible odd degrees coprime to3 has total totient2 or8. |
| Nat.oddTotient_five_forbidden | proved | No finite set of distinct admissible odd degrees coprime to5 has total totient4. |
| Nat.oddTotient_support_necessary | proved | Every admissible finite totient sum is even and satisfies the characteristic3/5 exclusions. |
| Nat.oddTotient_three_horizon_realize | proved | Every allowed support total satisfying N+6<=310*5^j is realized by a subset of the characteristic3 degree family. |
| Nat.oddTotient_three_eventual_realize | proved | Every allowed support total N is realized inside the characteristic3 degree family at every stage j>=N. |
| Nat.oddTotient_five_horizon_realize | proved | Every allowed support total satisfying N<=186*3^j+2 is realized by a subset of the characteristic5 degree family. |
| Nat.oddTotient_five_eventual_realize | proved | Every allowed support total N is realized inside the characteristic5 degree family at every stage j>=N. |
| Nat.oddTotient_other_horizon_realize | proved | Every allowed support total satisfying N+1<=21*3^j is realized by a subset of the other odd characteristics degree family. |
| Nat.oddTotient_other_eventual_realize | proved | Every allowed support total N is realized inside the other odd characteristics degree family at every stage j>=N. |
| Nat.oddTotient_support_spectrum | proved | Complete iff for all odd prime characteristics: every even total except2,8 at3 or4 at5 is an admissible finite totient sum. |

Supporting definitions: Nat.oddTotientSupportAllowed.

Owner: PrimeFactorOscillations/Mathlib/NumberTheory/ArithmeticFunction/OddTotientPowerTowers.lean.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| Nat.oddTotient_degree_period | proved | Coprimality and phi(d) dividing m imply d divides p^m-1. |
| Nat.oddTotient_coprime_product_period | proved | Separate Euler periods for coprime factors suffice to place their product in p^m-1. |
| Nat.oddTotient_scaled_block_period | proved | Every block through stage j divides p^(C*r^j)-1 under the displayed separate-factor periods. |
| Nat.oddTotient_three_family_period | proved | Every degree in the characteristic3 family divides3^(720*5^j)-1. |
| Nat.oddTotient_five_family_period | proved | Every degree in the characteristic5 family divides5^(720*3^j)-1. |
| Nat.oddTotient_other_block_period | proved | Every selected other-characteristic block through stage j divides p^(12*3^j)-1. |
| Nat.oddTotient_other_family_period | proved | The entire other-characteristic degree family divides p^(12*3^j)-1. |
| Nat.oddTotient_tower_degree_lower | proved | Every selected tower extension degree is at least12, including stage0. |
| Nat.oddTotient_prime_power_card_bounds | proved | For p>=3 and m>=2, p^m>=9 and p divides p^m. |
| Nat.oddTotient_tower_data | proved | Uniform all-characteristic family data: oddness, degree>1, characteristic coprimality, and split-sector divisibility. |
| Nat.oddTotient_tower_eventual_realize | proved | Every allowed N is a totient sum inside the corresponding explicit degree family at every j>=N. |

Supporting definitions: Nat.oddTotientTowerDegree, Nat.oddTotientTowerDegrees.

Owner: PrimeFactorOscillations/Mathlib/NumberTheory/LegendreSymbol/QuadraticPairOddPellStableSpectrum.lean.

| Lean declaration | Status | Exact scope |
| --- | --- | --- |
| FiniteField.oddPell_stable_support_necessary | proved | Every actual signed probe has even support, excluding2/8 if3 divides the field order and4 if5 divides it; all sectors retained. |
| FiniteField.oddPell_stable_split_realize | proved | Every admissible finite split-degree set is the exact support union of an actual finite signed probe, with cardinality its totient sum. |
| FiniteField.oddPell_stable_three_horizon | proved | At q=3^(720*5^j), every allowed N with N+6<=310*5^j has an actual finite split-support witness. |
| FiniteField.oddPell_stable_five_horizon | proved | At q=5^(720*3^j), every allowed N<=186*3^j+2 has an actual finite split-support witness. |
| FiniteField.oddPell_stable_other_horizon | proved | For prime p>=7 and q=p^(12*3^j), every even N with N+1<=21*3^j has an actual finite split-support witness. |
| FiniteField.oddPell_stable_tower_realize | proved | At every j>=N in every selected odd-characteristic tower, every allowed N has actual finite indices, real coefficients and an exact split-class support identity. |
| FiniteField.oddPell_stable_tower_spectrum | proved | Complete actual-finite-probe iff at every j>=N: support N exists precisely for the characteristic-dependent allowed even totals; every nonzero shift,2 nonzero. |

Supporting definitions: FiniteField.oddPellSplitSupportWitness.

The finite base certificates check all64/128/4 subsets of their respective fixed degree bases; every tower stage and target interval is handled by universal induction. Equal normalized weights at the distinct degrees7 and9 are retained. Euler periods are applied separately to coprime degree factors, so the displayed periods are preserved. The native witness predicate contains actual finite polynomial indices and real coefficients, the exact split-class support identity, and the exact support cardinality. The already proved q3 all-zero degeneracy remains outside the normalized q>=5 law.

benchmark_status: complete selected stable-spectrum theorem proved;80 new maintained public theorem declarations and15 supporting definitions across six owners.
old_bound: the complete fixed-field divisor/totient subset-sum spectrum and the bounded-minimum obstruction for fixed-divisor towers; no classification of every eventually attainable size.
new_bound: exact stable spectrum for every odd characteristic, exactly the permanent holes2/8 at3 and4 at5, the three explicit sufficient horizons, and actual finite split-support witnesses at every j>=N.
components: indexed interval insertion with all prefixes; distinct geometric degree blocks; all-stage totals and coverage; universal composite-degree exclusions; separate-factor Euler periods; exact full signed-span converse and primitive-class cardinalities.
actuals: universal kernel-checked proofs for every stage and admissible support total, with exact finite base certificates only. The new-only axiom audit covers all80 new theorem declarations and uses foundational axioms only.
first_nonpositive_domain: zero support is included; the listed small holes are genuine universal exclusions. Horizon and stage sufficiency are explicit, without an optimality claim. No integer prime-pair window positivity, H1, RH or QRH improvement is claimed. QRH remains paused at7/8; historical priority of the combined classification remains unconfirmed.


## Uniform integral odd-Pell probes across fields (2026-10-31)

The common code is an actual finite polynomial-index set with ordinary integer coefficients. It depends on the selected primitive degrees, and not on the field or shift. For each odd prime p and allowed N, it can be chosen once before every j>=N and every field of size p^(towerDegree p j). The existing stable spectrum is unchanged; integrality and the order of quantifiers are strengthened. The exact native weights and all repeated-index contributions are retained.

Owners: `ArithmeticFunction/OddDivisorProbe.lean` and `LegendreSymbol/QuadraticPairOddPellUniform.lean`, exported by `QuadraticPairOddPellLaws`.

| Declaration | Status | Exact scope |
| --- | --- | --- |
| UniversalOddDivisorProbe.sum_moebius | proved | Exact signed divisor sum for every positive integer; classical inversion input. |
| UniversalOddDivisorProbe.divisor_filter | proved | Exact supported quotient-divisibility filter, including the empty case. |
| UniversalOddDivisorProbe.filtered_moebius | proved | Signed quotient-filter sum equals the exact degree indicator. |
| UniversalOddDivisorProbe.mem_probeIndices | proved | Every retained divisor term has its actual polynomial index in the common finite set. |
| UniversalOddDivisorProbe.evaluate | proved | Exact finite pushforward over any ring, retaining all index collisions and integer signs. |
| UniversalOddDivisorProbe.index_identity | proved | For every odd divisor quotient,2*index+1 equals that quotient exactly. |
| UniversalOddDivisorProbe.amplitude | proved | One finite integer code has amplitude1 on D and0 at every other positive degree. |
| FiniteField.oddPell_universal_probe_expansion | proved | The actual common code retains native positive weights on exactly the selected degree labels; every nonzero shift. |
| FiniteField.oddPell_universal_probe_support | proved | Exact support union over selected native classes, uniformly for q>=5 and2 nonzero. |
| FiniteField.oddPell_universal_split_labels | proved | When every selected degree splits, the selected label set is exactly the left-tagged degree image. |
| FiniteField.oddPell_universal_split_support | proved | The actual fixed integral code has the exact split-class union and support cardinality sum_D phi(d). |
| Nat.oddTotient_tower_mono | proved | The explicit degree families are monotone in the stage; a degree set chosen once remains admissible. |
| FiniteField.oddPell_integral_stable_tower | proved | For every allowed N, exists one finite S and a:Nat->Int before all j>=N, all admitted fields and all nonzero shifts; support cardinality=N. |

Supporting definitions: UniversalOddDivisorProbe.probeIndex, UniversalOddDivisorProbe.probeIndices, UniversalOddDivisorProbe.probeCoefficients, and FiniteField.oddPellUniversalProbe.

Both maintained owners and the four public consumers compile. The new-only axiom audit covers all13 declarations and uses only propext, Classical.choice and Quot.sound. Its saved log SHA256 is `03AD999984A658316A4708A59BDC6071581CC9120DA02B8BEFFD69B9730C328A`. The canonical paper and watched source are byte-identical, and the desktop editor compiler confirms success.

benchmark_status: complete common-integral-code theorem proved;13 new maintained public theorem declarations and4 supporting definitions.
old_bound: for each j>=N, each admitted finite field and nonzero shift, there exist finite polynomial indices and real coefficients attaining N.
new_bound: there exist one finite polynomial-index set and one ordinary integer coefficient vector, chosen before all j>=N, admitted fields and nonzero shifts, attaining N everywhere; exact selected primitive classes and native weights are preserved.
components: signed filtered Mobius identity; finite divisor-to-index pushforward with all collisions; universal indicator amplitudes; native expansion and disjoint support; one degree subset at stage N and monotonic tower families.
actuals: universal kernel-checked proofs, including the explicit all-field quantifier in the main theorem; maintained owner and public closure compilation;13-declaration foundational-only audit; successful watched paper compilation. No finite field/stage sample stands in for these statements.
first_nonpositive_domain: N0 is allowed; the unchanged characteristic3 holes are2/8 and the characteristic5 hole is4. The native positive-weight formula requires q>=5; the existing q3 all-zero law remains separate. The sufficient j>=N threshold is not claimed optimal. No positive joint integer prime-pair window mass, H1, RH or QRH improvement follows; QRH remains paused at7/8. Mobius inversion is classical, and historical priority of the uniform native strengthening remains unconfirmed.

## One-field completeness for bounded odd-Pell signed relations (2026-10-31)

The full mathematical claim is proved in `QuadraticPairOddPellFiniteDetector.lean` and recorded in paper Section `sec:odd-pell-finite-detector`, Theorem `thm:odd-pell-finite-detector`, and Corollary `cor:odd-pell-finite-code-comparison`. The supporting characteristic restriction is an API exposure in the existing stable-spectrum owner. There are10 new maintained public theorem declarations and1 public API promotion; no new supporting definitions or completed private-only proofs.

| Declaration | Status | Exact scope |
| --- | --- | --- |
| FiniteField.oddPell_atom_characteristic_data | proved | Public API promotion of the existing atom-data proof: every visible degree is odd, >1 and coprime to any prime divisor p of the field cardinality. This is not a new mathematical proof. |
| FiniteField.oddPell_probe_zero_iff_amplitudes | proved | For q>=5 and nonzero h, the entire native probe is zero iff every visible signed divisibility amplitude is zero; all native weights retained. |
| FiniteField.oddPell_split_amplitude_zero | proved | Vanishing of a probe forces the amplitude of every positive split primitive degree e>1 to vanish. |
| FiniteField.oddPell_bounded_amplitudes_suffice | proved | For degrees 2*k+1<=M, vanishing of all odd characteristic-coprime amplitudes e in (1,M] forces the full native probe to vanish. |
| FiniteField.oddPell_factorial_zero_iff | proved | A field of size p^(M!), M>=2, tests exactly those finitely many amplitudes, for every bounded finite real coefficient code. |
| FiniteField.oddPell_factorial_vanishing_transfer | proved | Vanishing in the factorial witness transfers to every finite field whose cardinality is divisible by p, with nonzero shift and 2 nonzero; q=3 is included. |
| FiniteField.oddPell_factorial_all_fields_iff | proved | Universe-polymorphic equivalence between the single-field test and all admitted finite fields in that universe; no RH or asymptotic sampling hypothesis. |
| FiniteField.oddPell_probe_sub | proved | The native signed probe of a-b equals the difference of the probes on the same finite support. |
| FiniteField.oddPell_factorial_compare_iff | proved | Two bounded real coefficient codes agree in the factorial witness iff all stated signed divisibility sums agree. |
| FiniteField.oddPell_factorial_comparison_transfer | proved | Agreement of two bounded codes in the witness transfers to every admitted finite field and nonzero shift. |
| FiniteField.oddPell_galois_factorial_zero_iff | proved | Actual GaloisField p (M!) specialization at shift 1, with cardinality and 2 nonzero discharged from odd prime p and M>=2. |

Both maintained proof owners compile. The new-only audit covers these11 public declarations and uses only propext, Classical.choice and Quot.sound. The saved audit SHA256 is `DBB116137159BA8EF7BDA21A2D1BFB8C2A9B9E7BE39AF48C7872D0D5447286BE`. The canonical paper and watched source are byte-identical and the desktop editor compiler confirms success. Public-export and final staged checks are release gates recorded in the completion receipt; these do not replace the proof or axiom checks.

benchmark_status: complete single-field relation theorem proved;10 new maintained public theorem declarations and1 public API promotion.
old_bound: the existing exact vanishing test uses a field's varying primitive labels, determined by divisors of q-1 and q+1.
new_bound: for every odd prime p, M>=2 and finite real signed code supported on input degrees 2*k+1<=M, one actual field of size p^(M!) detects vanishing over every finite extension of characteristic p; the equivalent finite test is B_e=0 for every odd 1<e<=M coprime to p.
components: nonempty primitive classes and positive native weights; exact signed atom expansion; all characteristic-coprime degrees split in the factorial extension by Euler periods; empty amplitudes above M; the existing q3 all-zero law; exact subtraction for two-code comparison; the actual GaloisField specialization.
actuals: universal kernel-checked statements and foundational-only11-declaration audit, including all finite fields in the explicit universal theorem; successful watched paper compilation. No sample of fields, degrees or coefficients is used as proof of the universal claim.
first_nonpositive_domain: M2 includes the degree-one/empty-admissible-degree case; empty supports are allowed. Positive native weights require q>=5; q3 is handled by its separate proved zero law. The characteristic is an odd prime and shifts and2 are nonzero. The sufficient factorial exponent is not claimed minimal. No integer prime-pair native-window positivity, H1, RH or QRH improvement follows; QRH remains paused at7/8. Historical priority of the native relation classifier remains unconfirmed.


## Uniform small-prime signatures for actual integer pair returns (2026-10-31)

Paper: `finite-fields.tex`, Theorem `thm:integer-signature-return` and Corollary `cor:least-gap-signature-return`. All declarations below are in `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

Owners: `Assembly/FiniteFieldIntegerSignature.lean`, `Assembly/FiniteFieldIntegerSignatureWindow.lean`, and `Assembly/FiniteFieldIntegerSignatureReturn.lean`.

| Declaration | Status | Exact scope |
| --- | --- | --- |
| numerator_kernel_mul_numerators | proved | Exact multiplicativity of the full numerator Jacobi kernel. |
| exists_coprime_prime_factor_witness | proved | Constructive CRT nonprincipal witness with an arbitrary coprime coefficient. |
| numerator_character_ne_one_of_coprime_prime_factor | proved | Nonprincipality from the actual odd-valuation prime factor. |
| separation_score_identity | proved | Exact signed positive-supply-minus-correlation identity. |
| exists_uniform_separation_score_lower | proved | Uniform signed score lower bound, with conductor and prime cutoff retained. |
| endpoint_coefficient_coprime | proved | Coprimality of the endpoint prime with the full comparison coefficient. |
| positive_kernel_square_on_prime | proved | The actual endpoint kernel squares to one on the admissible band. |
| separation_score_zero_of_matching | proved | Exact coordinate agreement forces the full signed score to vanish. |
| exists_finite_endpoint_signature_separation | proved | Finite prime-band endpoint distinction under its explicit mass margin. |
| endpoint_cost_le_uniform | proved | Full conductor budget uniformly below the common pair height. |
| exists_finite_prime_pair_signature_rigidity | proved | Two-coordinate finite prime-pair rigidity with its explicit margin. |
| reciprocal_band_eq_sub | proved | Exact finite reciprocal-prime prefix subtraction. |
| reciprocal_square_band_lower | proved | For K>=2, square-band mass is at least log(2)-2E/log(K). |
| eventually_reciprocal_square_band_positive | proved | Eventual square-band mass at least log(2)/2. |
| precise_core_tendsto_atTop | proved | The existing integer polylogarithmic core tends to infinity. |
| eventually_precise_core_square_fits | proved | The full square band lies below Q eventually, including the ceiling. |
| signature_uniform_log_bound | proved | Uniform logarithmic conductor budget at bounded gap and height Q^2. |
| signature_uniform_cost_le | proved | Complete character allowance bounded by the existing vanishing relative error. |
| eventually_uniform_signature_margin | proved | The finite mass margin holds uniformly at every sufficiently large height. |
| eventually_prime_pair_signature_rigidity | proved | Full uniform positive-numerator two-coordinate rigidity for actual prime pairs. |
| numerator_kernel_neg_matching | proved | Explicit cancellation of the original negative-unit character phase. |
| original_signature_implies_positive | proved | Actual finite-field A/B coordinate agreement supplies both normalized signatures. |
| eventually_actual_pair_signature_rigidity | proved | Uniform rigidity for the original two finite-field carrier coordinates. |
| unbounded_least_gap_signature_rigid_frames | proved | Existing unbounded H1 positive frames admit only the identical signature-preserving actual prime-pair return. |

Supporting definitions: `reciprocalBand`, `separationScore`, and `originalSignatureMatch`. The existing `preciseCore` is reused.

The three maintained owners compile without warnings. All24 new theorem closures have only propext, Classical.choice and Quot.sound. The full prime-pair theorem includes the original A=-h*n phase, every prime in the complete band, positive bounded gaps, and all actual prime-pair endpoints in the stated height range. The H1 corollary retains the existing positive frame mass and actual consecutive endpoints. The onset is existential; no numerical onset or optimal cutoff exponent is claimed.

benchmark_status: complete uniform signature-return rigidity proved;24 maintained theorem declarations and3 supporting definitions.
old_bound: a finite prime-band certificate required an explicit reciprocal-mass margin; no uniform height discharge or actual A/B and H1-frame consumer.
new_bound: for every fixed H>=1, all sufficiently large Q and all actual prime pairs in (Q,Q^2] with positive gaps<=H, equality of both original coordinates on every prime K(Q)<p<=K(Q)^2 forces the same pair and gap, where K(Q)=ceil((10 log Q)^128).
components: constructive coprime-factor nonprincipality; exact signed score; installed uniform Dirichlet tail; Mertens mass >=log(2)-2E/log(K); full conductor <=4H^2Q^4; vanishing allowance <=C/(10 log Q)^2; ceiling-aware K^2<Q; explicit negative-unit phase; existing H1 positive frames.
actuals: universal maintained Lean proofs and new-only foundational-axiom audits; no numerical sample is used to establish the universal theorem.
first_nonpositive_domain: positive gaps and H>=1 are required; the band eventually excludes2 and every prime<=H and lies below all four endpoint primes. No new pair supply, numerical H1 bound, RH proof or zero-free exponent improvement follows. The general least-nonresidue mechanism is classical; priority of the two-coordinate integer-return application remains unconfirmed.


## The native probability weights determine the integer pair (2026-10-31)

Paper: `finite-fields.tex`, Lemma `lem:native-signed-energy`, Theorem `thm:native-integer-return`, and Corollary `cor:native-least-gap-return`. All declarations below are in `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

Owners: `Assembly/FiniteFieldIntegerNativeRigidity.lean` and `Assembly/FiniteFieldIntegerNativeReturn.lean`.

| Declaration | Status | Exact scope |
| --- | --- | --- |
| real_kernel_mul | proved | Exact real product formula, retaining the numerator kernel's original signs. |
| real_kernel_le_one | proved | Universal real kernel upper bound on every odd prime. |
| real_kernel_square_endpoint | proved | Both signed endpoint characters square to one on the admissible band. |
| prime_correlation_le_mass | proved | Possible principal correlation retains the entire reciprocal-prime mass. |
| exists_coprime_prime_correlation_bound | proved | Two-sided signed correlation bound for the full coprime-factor numerator character. |
| exists_endpoint_prime_correlation_bound | proved | Uniform full conductor budget for either sign and every distinct pair of endpoint primes. |
| native_trace_energy_identity | proved | Four diagonal and all six signed correlation terms in the exact native trace energy. |
| exists_native_trace_energy_lower | proved | Complete E>=2M-10epsilon bound for all distinct actual prime pairs, including every shared endpoint. |
| native_weight_trace_eq | proved | Actual scalar weight equality gives aggregate trace equality, with both opening masks and p-3 checked. |
| native_energy_zero_of_weight_match | proved | Equality of all actual local weights gives zero full energy on the supported band. |
| eventually_native_weight_pair_rigidity | proved | For each fixed positive gap bound, all large bounded-height prime pairs are determined by their native weight vector. |
| unbounded_least_gap_native_rigid_frames | proved | Existing unbounded positive H1 frames permit only the identical actual prime-pair return preserving the native weights. |

Supporting definitions: `primeCorrelation`, `nativeTrace`, `nativeTraceEnergy`, and `nativeWeightMatch`.

Both maintained owners compile without warnings. All12 new closures have only propext, Classical.choice and Quot.sound. The conclusion assumes equality only of the actual native scalar local weights. The original character phases, zero-mask checks, all four overlap cases, complete six-correlation energy and possible principal contribution are retained. It is not a theorem about equality of arbitrary unmarked products or normalized location distributions.

benchmark_status: complete native-weight integer-return theorem proved;12 new maintained theorem declarations and4 supporting definitions.
old_bound: uniform integer rigidity required equality of both labelled A/B characters at every prime in the band.
new_bound: equality of the actual scalar native weights suffices, uniformly for every fixed H>=1, all sufficiently large Q and all actual prime pairs in (Q,Q^2] with positive gaps<=H. The complete finite signed estimate is E>=2M-10epsilon, with epsilon=C*(3+log(4H^2T^2))^2*Y^(-1/32).
components: the exact native scalar law; four diagonal terms and six signed correlations; two internal and three cross nonprincipal bounds; at most one shared endpoint; full mass M for the remaining possible principal row; existing margin at5C; all original phases and opening masks; actual positive H1 recurrence frames.
actuals: universal maintained kernel proofs and12 new-only foundational-axiom audits. No finite character, field, height or pair sample is substituted for the universal bounds.
first_nonpositive_domain: identical pairs have zero energy and are excluded only in the separation contradiction. Positive gaps prevent two distinct shared endpoints. Actual scalar weights use primes>=5; the complete band is above H and below all endpoints. No numerical H1 bound, new prime recurrence, RH proof or QRH exponent improvement follows. The quantitative extension is recorded below; priority remains unconfirmed.

## Quantitative separation of the native probability weights (2026-10-31)

Paper: `finite-fields.tex`, Theorem `thm:native-metric-separation` and Corollary `cor:native-metric-least-gap`. Owner: `Assembly/FiniteFieldIntegerNativeMetric.lean`. Namespace: `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

| Declaration | Status | Exact scope |
| --- | --- | --- |
| native_weight_scaled_difference | proved | Exact (p-3) times the actual native-weight difference equals the aggregate trace difference; both masks and denominator checked. |
| native_weight_energy_eq_trace | proved | The scaled native squared discrepancy equals the full signed trace energy on the entire supported prime band. |
| native_metric_defect_tendsto_zero | proved | The explicit Mertens and full-conductor defect tends to zero. |
| exists_uniform_native_metric_lower | proved | One absolute C gives the eventual 2log2-d_C(Q) separation for every fixed positive gap bound and all distinct eligible actual prime pairs. |
| eventually_native_weight_metric_separation | proved | For every eta>0, all sufficiently large eligible distinct pairs have scaled native discrepancy at least 2log2-eta. |
| eventually_native_metric_pair_rigidity | proved | Scaled discrepancy below log2 eventually forces the identical integer pair and gap. |
| unbounded_least_gap_native_metric_frames | proved | Existing unbounded positive H1 frames retain the same pair and H1 under every eligible approximate return with discrepancy below log2. |

Supporting definitions: `integerNativeWeight`, `nativeWeightEnergy`, and `nativeMetricDefect`.

The maintained owner compiles without warnings. All seven new-only theorem closures use propext, Classical.choice and Quot.sound. This is a quantitative extension for the actual scalar local probability weights; it is distinct from the older optional labelled-coordinate distance target.

benchmark_status: universal quantitative native-profile separation and actual approximate-return consumer proved.
old_bound: exact native-weight equality forced equality of eligible bounded-height prime pairs; no positive mismatch allowance was stated.
new_bound: D_Q>=2log2-d_C(Q), where d_C(Q)=4B/logK(Q)+10relativeError(C,Q)->0. Consequently every fixed eta>0 gives the uniform eventual bound D_Q>=2log2-eta, and D_Q<log2 forces the identical pair.
components: exact (p-3) scalar scaling; the whole six-correlation energy; complete E>=2M-10epsilon; M>=log2-2B/logK; full-conductor epsilon<=relativeError(C,Q); both proved limits; existing actual positive H1 frames.
actuals: seven universal maintained kernel proofs and new-only foundational-axiom audits; no finite sample or numerical completion supplies any estimate.
first_nonpositive_domain: identical pairs have zero discrepancy. All eventual onsets may depend on H and eta; C is absolute. The finite support is exactly the primes K(Q)<p<=K(Q)^2. This is a scaled squared discrepancy, with no assertion of an unscaled positive distance, an optimal constant, new integer pair supply, a numerical H1 value, RH or priority.

## Global native-profile reconstruction with finite erasures (2026-10-31)

Paper: `finite-fields.tex`, Lemma `lem:native-endpoint-readout`, Theorem `thm:native-global-inverse` and Corollary `cor:native-global-least-gap`. Owners: `Assembly/FiniteFieldNativeEndpointReadout.lean` and `Assembly/FiniteFieldNativeGlobalReturn.lean`. Namespace: `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

| Declaration | Status | Exact scope |
| --- | --- | --- |
| real_kernel_square_of_nonzero | proved | A nonzero residue at an odd prime gives a real numerator-kernel square of one. |
| native_weight_large_prime_trace | proved | The exact centered scalar weight equals the aggregate trace above both endpoints, with both masks checked. |
| native_trace_endpoint_readout | proved | Squaring the aggregate trace cancels the gap square and recovers the negative endpoint-product character. |
| native_weight_endpoint_readout | proved | Exact endpoint-product readout from the actual native scalar probability weight for all positive integer pairs. |
| native_weight_match_product_one | proved | Equal actual native weights force the combined endpoint-product character to equal one at every admissible field prime. |
| distinct_prime_pairs_have_odd_carrier | proved | Distinct oriented prime pairs have an explicit odd unique endpoint carrier; integer endpoint two is included. |
| not_eventually_prime_kernel_one | proved | The existing full-conductor correlation estimate prevents a coprime odd-carrier character from being one at all sufficiently large primes. |
| cofinite_native_weight_pair_rigidity | proved | Every actual oriented prime pair is determined by its cofinite native-weight profile, without height ordering or a fixed gap bound. |
| unbounded_least_gap_global_native_frames | proved | Existing positive H1 frames admit only the identical cofinite-profile-preserving actual return, with no target-height or gap ceiling. |

Supporting definition: `cofiniteNativeWeightMatch`.

Both maintained owners compile without warnings. All nine new-only theorem closures use propext, Classical.choice and Quot.sound. The local readout does not require prime integer endpoints; primality is used in the global odd-carrier inverse.

benchmark_status: universal global inverse and its actual H1-frame consumer proved.
old_bound: exact and quantitative finite-band reconstruction applied to common (Q,Q^2] windows with a fixed positive gap bound.
new_bound: cofinite native-profile equality determines every actual positive-gap prime pair, with arbitrary integer heights and gaps. The observation hypothesis is cofinite prime fields; this does not enlarge the domain of the earlier finite-band quantitative theorem.
components: full centered native scalar law; every endpoint and gap mask; exact gap-square cancellation; negative endpoint-product characters; explicit odd unique endpoint including two; full4D conductor; existing universal correlation estimate and square-band margin; actual positive least-gap frames.
actuals: nine universal maintained kernel proofs and nine new-only foundational-axiom audits, without numerical substitute estimates.
first_nonpositive_domain: positive gaps and actual prime endpoints are retained. Field primes two, three, endpoint divisors and gap divisors lie in the allowed finite exceptional set. No positive-density erasure threshold, return existence, new pair supply, numerical H1 value, RH/QRH gain or established priority is claimed.

## Sharp adaptive half-mass native reconstruction (2026-10-31)

Paper: `finite-fields.tex`, Lemma `lem:native-half-signed`, Theorems `thm:native-half-inverse` and `thm:native-half-sharp`, Corollary `cor:native-half-least-gap`. Owners: `Assembly/FiniteFieldNativeAgreement.lean` and `Assembly/FiniteFieldNativeHalfSharpness.lean`. Namespace: `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

| Declaration | Status | Exact scope |
| --- | --- | --- |
| real_kernel_ge_neg_one | proved | The real numerator character at an odd prime is at least minus one, including its zero branch. |
| native_agreement_mass_le_character | proved | Above both endpoints and field prime three, the full finite agreement mass is at most one-half of mass plus the signed endpoint-product correlation. |
| exists_eventual_fixed_prime_correlation_bound | proved | Every fixed coprime odd-carrier numerator, of either sign, has its complete field-band correlation bounded by relativeError(B,U) for some fixed B>=0. |
| exists_eventual_native_agreement_upper | proved | Distinct actual positive-gap prime pairs have agreement mass at most M_U/2+relativeError(B,U)/2 eventually. |
| retained_mass_le_native_agreement | proved | Every finite supported set preserving actual native weights has reciprocal mass at most the entire agreement mass. |
| native_pair_rigidity_of_retained_mass | proved | Arbitrary adaptive sets retaining M_U/2+epsilon at unbounded scales recover any fixed actual prime pair, for epsilon>0. |
| native_pair_rigidity_of_retained_fraction | proved | Retained mass at least (1/2+delta)M_U at unbounded independent field scales forces both endpoints and gap to agree, for delta>0. |
| unbounded_least_gap_retained_native_frames | proved | Existing unbounded positive H1 frames admit only the identical fixed actual return under the adaptive retained-fraction hypothesis. |
| native_sharp_pair_match_iff | proved | For every prime p>13, pairs (5,7) and (5,13) have equal native weights exactly when chi_91(p)=1. |
| native_sharp_character_square | proved | The real chi_91 character squares to one at every prime p>13, with its two prime factors checked. |
| native_sharp_agreement_identity | proved | The complete finite agreement mass of the explicit distinct pairs equals (M+C_91)/2 above thirteen. |
| native_sharp_agreement_approx | proved | The explicit pair agreement mass minus half the complete square-band mass tends to zero. |
| native_sharp_retention_data | proved | The explicit finite chi_91=1 retained sets lie in the supported prime bands and preserve every actual native weight. |
| native_sharp_retention_mass_approx | proved | Reciprocal mass of those explicit retained sets minus M_U/2 tends to zero. |
| native_sharp_retention_above_subhalf | proved | For every fixed real c<1/2, the explicit retained mass eventually exceeds cM_U. |
| native_half_retention_is_sharp | proved | Actual distinct positive-gap prime pairs and finite retained sets satisfy every observation hypothesis while eventually exceeding every subhalf fraction. |

Supporting definitions: `nativeAgreementMass` and `nativeSharpRetentionSet`.

Both maintained owners compile without warnings. All sixteen new-only theorem closures use propext, Classical.choice and Quot.sound. Integer pairs are fixed before the independent field scale U tends to infinity. The H1-frame height Q is a separate parameter.

benchmark_status: universal adaptive reconstruction and exact sharpness for arbitrary actual prime pairs proved.
old_bound: arbitrary finite erasures of a cofinite native profile preserve the inverse, with no positive-fraction erasure theorem.
new_bound: agreementMass<=M_U/2+relativeError(B,U)/2 for every fixed distinct actual pair comparison, where relativeError(B,U)->0 and M_U>=log2/2 eventually. Arbitrary adaptive retained mass >=(1/2+delta)M_U along unbounded U therefore recovers the pair. The explicit distinct pairs have retained mass M_U/2+o(1), so no smaller universal threshold works.
components: full centered native scalar law; endpoint-product readout; exact signed indicator bound; explicit unique odd endpoint including integer two; full4D conductor; all field and endpoint mask onsets; complete fixed-character error; retained-set inclusion; actual positive least-gap frames; exact91 class with full modulus364.
actuals: sixteen universal maintained kernel proofs and sixteen new-only foundational-axiom audits; no finite sample or numerical completion supplies a bound.
first_nonpositive_domain: the theorem requires a fixed positive margin above half mass. It does not assert reconstruction at exactly half. Field exceptions disappear only after a pair-dependent onset. The witness (5,13) is not consecutive; no consecutive-pair or growing-endpoint sharpness is claimed. Reciprocal weights are not unweighted field counts. No return existence, new integer pair supply, numerical H1 value, RH/QRH gain, or established priority is claimed.

## Sharp three-eighths agreement for consecutive prime pairs (2026-10-31)

Paper: `finite-fields.tex`, Lemmas `lem:native-negative-row` and `lem:native-seven-agreement`, Theorems `thm:native-short-three-eighths` and `thm:native-consecutive-three-eighths`, Corollary `cor:native-consecutive-least-gap`. Owners: `Assembly/FiniteFieldNegativeNumerator.lean`, `Assembly/FiniteFieldNativeAgreementSpectrum.lean`, `Assembly/FiniteFieldNativeShortPairAgreement.lean`, `Assembly/FiniteFieldNativeConsecutiveAgreement.lean`.

`negative_numerator_character_ne_one` is in namespace `PrimeFactorOscillations.IntegerQuadraticCharacter`; all other declarations are in `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

| Declaration | Status | Exact scope |
| --- | --- | --- |
| negative_numerator_character_ne_one | proved | For every A>0, the full numerator character of -A modulo4A is nonprincipal, with explicit witness4A-1; negative squares are included. |
| exists_eventual_nonprincipal_correlation_bound | proved | Every fixed nonzero actual nonprincipal full numerator character has complete signed band correlation bounded eventually by relativeError(B,U). |
| fixed_nonprincipal_prime_correlation_tendsto_zero | proved | The same complete signed correlation tends to zero with its full modulus and nonunit mask. |
| native_agreement_indicator | proved | Above both positive integer endpoint pairs and field prime three, the actual scalar-weight equality indicator is exactly(3-ab-cd+ac+ad+bc+bd+3abcd)/8. |
| native_agreement_mass_eq_seven_correlations | proved | The entire finite supported reciprocal-prime agreement mass equals3M/8 plus the full seven-correlation signed remainder. |
| native_agreement_remainder_tendsto_zero_of_short_gaps | proved | For actual prime pairs with0<h<n,0<k<m and distinct lower/upper endpoints, all seven actual character rows tend to zero. |
| native_agreement_three_eighths_of_short_gaps | proved | For every fixed pair in that arithmetic class, native agreement mass minus3M_U/8 tends to zero. |
| native_indexed_gap_lt_lower | proved | Every actual indexed consecutive prime gap is smaller than its lower prime, including index zero, via Bertrand and the exact prime enumeration. |
| native_agreement_three_eighths_of_consecutive | proved | Every two distinct actual consecutive prime pairs have complete native agreement mass3M_U/8+o(1), with no character-independence assumption. |
| native_consecutive_pair_rigidity_of_retained_fraction | proved | Arbitrary adaptive supported observations of mass at least(3/8+delta)M_U at unbounded scales force the same actual consecutive prime index. |
| native_consecutive_three_eighths_is_sharp | proved | Every two distinct actual consecutive prime pairs admit explicit agreeing finite sets with mass3M_U/8+o(1), eventually above every fixed subthree-eighths fraction. |
| unbounded_least_gap_consecutive_native_frames | proved | Existing unbounded positive H1 frames admit only the identical actual consecutive return under the improved retained-mass hypothesis. |

Supporting definition: `nativeAgreementRemainder`. Both integer prime pairs are fixed before the independent field scale U. The H1-frame parameter Q is separate.

All four maintained owners compile without warnings. The twelve new-only theorem closures use propext, Classical.choice and Quot.sound. No unchanged older theorem closure was reaudited.

benchmark_status: exact complete agreement law, sharp adaptive consecutive-pair inverse and actual least-gap consumer proved.
old_bound: the maintained inverse on consecutive pairs required retained reciprocal mass at least(1/2+delta)M_U, inherited from the arbitrary-prime-pair theorem.
new_bound: every fixed distinct consecutive comparison satisfies A_U-3M_U/8->0. Retained mass at least(3/8+delta)M_U on unbounded independent scales recovers the same pair. Every distinct consecutive comparison supplies agreeing sets of mass3M_U/8+o(1), proving the universal constant optimal with a fixed positive margin.
components: exact centered native scalar law; full seven-character identity with weights-1,-1,+1,+1,+1,+1,+3; every opening mask and denominator; explicit negative Jacobi witness4A-1 including negative unit squareclasses; three actual positive odd-prime carriers with all factors; full4abs(D) character mean; Bertrand and exact prime enumeration including(2,3); complete retained-set inclusion and actual H1-frame data.
actuals: twelve universal maintained kernel proofs and twelve new-only foundational-axiom audits; no finite sample, independent-sign model or numerical completion supplies an estimate.
first_nonpositive_domain: no reconstruction assertion at exactly3/8 without a fixed positive surplus. The three-eighths law excludes identical pairs, whose agreement mass is M_U. All eventual onsets may depend on the fixed integer pairs and requested tolerance. This is reciprocal-prime mass, not an unweighted field count or a uniform theorem with growing integer endpoints. The arbitrary-pair half-mass theorem remains sharp in its larger class. No return existence, new pair supply, numerical H1, RH/QRH gain or established priority is claimed.

## Complete native agreement spectrum for arbitrary prime pairs (2026-10-31)

Both integer pairs are fixed before independent field scale U. For distinct actual positive-gap prime pairs, alpha=(3+e(hknm)+e(hk(n+h)(m+k)))/8, where e(D)=1 precisely when the actual full numerator character modulo4abs(D) is principal (and e(0)=0). Then A_U-alpha*M_U->0 and A_U/M_U->alpha, with alpha in{3/8,1/2}.

| Claim / declaration | Status | Maintained owner | Evidence and scope |
| --- | --- | --- | --- |
| `principal_prime_kernel_eventually` | proved | `PrimeFactorOscillations/Assembly/FiniteFieldNativePrincipalMean.lean` | Principal full numerator character evaluates to1 at every sufficiently large prime; all nonunit exceptions retained. |
| `principal_prime_correlation_eventually_eq_mass` | proved | `PrimeFactorOscillations/Assembly/FiniteFieldNativePrincipalMean.lean` | Principal reciprocal correlation is eventually exactly the observed band mass. |
| `prime_correlation_principal_centered_tendsto_zero` | proved | `PrimeFactorOscillations/Assembly/FiniteFieldNativePrincipalMean.lean` | Every fixed nonzero numerator is centered by its actual principal contribution. |
| `negative_prime_correlation_tendsto_zero` | proved | `PrimeFactorOscillations/Assembly/FiniteFieldNativePrincipalMean.lean` | Includes negative squares and the full4abs(D) modulus. |
| `prime_correlation_square_factor_eventually` | proved | `PrimeFactorOscillations/Assembly/FiniteFieldNativePrincipalMean.lean` | Removes a fixed nonzero square multiplier only after all its prime divisors leave the band. |
| `native_product_prime_correlation_tendsto_zero` | proved | `PrimeFactorOscillations/Assembly/FiniteFieldNativeAgreementClassification.lean` | Full four-coordinate product including both gap squares, arbitrary distinct actual prime pairs and endpoint2. |
| `native_agreement_centered_by_cross_characters` | proved | `PrimeFactorOscillations/Assembly/FiniteFieldNativeAgreementClassification.lean` | Complete seven-row signed assembly with both positive principal contributions retained. |
| `native_agreement_rate_dichotomy` | proved | `PrimeFactorOscillations/Assembly/FiniteFieldNativeAgreementClassification.lean` | Only3/8 or1/2; excludes5/8 using the proved half bound and positive band mass. |
| `native_agreement_ratio_tendsto_rate` | proved | `PrimeFactorOscillations/Assembly/FiniteFieldNativeAgreementClassification.lean` | Normalized agreement fraction converges to the explicit rate; denominator eventually at least log2/2. |

Namespace: `PrimeFactorOscillations.FiniteFieldIntegerSignature`. Supporting definitions: `numeratorPrincipalIndicator`, `nativeAgreementRate`. All nine declarations compile without warnings and pass new-only foundation audits containing only propext, Classical.choice and Quot.sound. No unchanged earlier closure was reaudited.

benchmark_status: complete exact two-value agreement law for arbitrary fixed actual prime pairs, proved.
old_bound: arbitrary distinct prime pairs had agreement mass at most M_U/2+o(1); exact3M_U/8 was proved on the short/consecutive subclass.
new_bound: every arbitrary distinct actual positive-gap prime pair comparison has A_U-alpha*M_U->0 and A_U/M_U->alpha, with explicit alpha in{3/8,1/2}. No universal arbitrary-pair threshold below1/2 is asserted.
components: full principal-character centering and nonunit masks; all four negative rows; unchanged actual endpoint carrier; entire gap-square multiplier and its finite exceptional primes; both positive cross rows; complete signed assembly; existing half upper bound; eventual positive reciprocal band; explicit denominator positivity before normalization.
actuals: nine universal maintained proofs and nine new-only foundation audits. No finite sample or independent-sign model is used.
first_nonpositive_domain: identical pairs are excluded. The theorem is not uniform for integer endpoints growing with U. The explicit full-character criterion has the proved arithmetic square refinement in the following section. No integer pair supply, H1 determination, return existence, RH/QRH exponent improvement or established priority is claimed.

## Arithmetic square classifier for native agreement (2026-10-31)

Paper: `finite-fields.tex`, Theorem `thm:native-arithmetic-spectrum`, identity `eq:native-principal-square`. Namespace: `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

| Claim / declaration | Status | Maintained owner | Evidence and scope |
| --- | --- | --- | --- |
| `numerator_character_square_mul_ne_one` | proved | `Assembly/FiniteFieldNativeSquareCharacter.lean` | A positive natural square multiplier preserves nonprincipality, using exact signed band means and the positive mass floor. |
| `squarefree_numerator_character_ne_one` | proved | `Assembly/FiniteFieldNativeSquareCharacter.lean` | Every squarefree d>1 has nonprincipal full numerator character; d=2 uses the exact unit witness3 modulo8. |
| `square_numerator_character_eq_one` | proved | `Assembly/FiniteFieldNativeSquareCharacter.lean` | Every nonzero natural square has principal full numerator character, including equality at all nonunit residues. |
| `numerator_character_nat_eq_one_iff_isSquare` | proved | `Assembly/FiniteFieldNativeSquareCharacter.lean` | For every positive natural N, full numerator principality iff Nat IsSquare N; arbitrary repeated factors and powers of2 included. |
| `numerator_principal_indicator_nat_eq_square` | proved | `Assembly/FiniteFieldNativeSquareCharacter.lean` | The actual principal indicator equals the elementary integer-square indicator on every positive natural numerator. |
| `native_agreement_rate_eq_square_test` | proved | `Assembly/FiniteFieldNativeArithmeticAgreement.lean` | Exact rate formula(3+1_square(hknm)+1_square(hk(n+h)(m+k)))/8 for all positive integer inputs. |
| `native_agreement_arithmetic_classification` | proved | `Assembly/FiniteFieldNativeArithmeticAgreement.lean` | Distinct actual positive-gap prime pairs have rate1/2 iff at least one cross integer is square, and3/8 iff neither is square. |
| `native_agreement_ratio_tendsto_square_rate` | proved | `Assembly/FiniteFieldNativeArithmeticAgreement.lean` | The actual reciprocal-band agreement fraction converges to that explicit square-test formula. |

All eight declarations compile warning-free and pass new-only foundational-axiom audits containing only propext, Classical.choice and Quot.sound. Unchanged older theorem closures were not reaudited. Both owners are exported through the maintained finite-field facade.

benchmark_status: complete arithmetic classification and actual normalized native agreement limit, proved.
old_bound: exact rate in{3/8,1/2} required two full-character principality tests.
new_bound: rate1/2 iff hknm or hk(n+h)(m+k) is an integer square; rate3/8 iff neither is a square. The exact agreement limit is the elementary square-indicator formula.
components: full4N numerator characters and nonunit masks; squarefree decomposition; exact d=2 unit witness; odd-prime carrier; complete square-factor correlation identity; positive reciprocal-band floor; unchanged seven-row signed assembly and dichotomy.
actuals: eight universal maintained proofs and eight new-only axiom audits; no finite experiment or independent-sign model supplies the theorem.
first_nonpositive_domain: N>0 is required for the supporting square criterion. Actual prime endpoints and positive gaps ensure both cross numerators are positive. Identical pairs are excluded from the rate classifier and normalized limit. Endpoints are fixed before U; no growing-endpoint uniformity, integer pair supply, H1 determination, RH/QRH gain or established priority is claimed.

## Square-root count of exceptional half-agreement pairs (2026-10-31)

Paper: `finite-fields.tex`, Theorem `thm:native-exception-count`, equation `eq:native-exception-count`. Owner: `Assembly/FiniteFieldNativeExceptionalAgreement.lean`. Namespace: `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

| Claim / declaration | Status | Exact verified scope |
| --- | --- | --- |
| `native_half_agreement_endpoint_localization` | proved | For fixed distinct actual positive-gap prime pairs with rate1/2, either m<=hn and h*n*k*m is square, or m+k<=h(n+h). Includes integer endpoint2 and arbitrary positive gaps. |
| `native_exceptional_agreement_count_bound` | proved | For every natural Y, the actual finite set of distinct candidate prime pairs(m,q),m<q<=Y, of rate1/2 has cardinality <=(A+1)*(Nat.sqrt(A^2*Y)+1)+(B+1)^2, where A=hn,B=h(n+h). Complete injective square-root count and both finite branches proved. |

Supporting definition: `nativeHalfAgreementPairs`, with its full finite product support, both primality tests, strict endpoint order, exclusion of the reference pair and exact native rate test. Both declarations compile warning-free and their new-only axiom audits contain only propext, Classical.choice and Quot.sound. No unchanged earlier theorem closure was reaudited. The square-root interpretation in real Y is the elementary consequence of this exact compiled Nat.sqrt bound, not a separate formal big-O declaration.

benchmark_status: complete universal finite exception count proved.
old_bound: fixed distinct candidate pairs had exact limiting agreement3/8 or1/2, with no count of the one-half exceptions as their heights vary.
new_bound: card(E_Y)<=(A+1)*(Nat.sqrt(A^2*Y)+1)+(B+1)^2 at every natural cutoffY. Every exception has either lower endpoint<=A with the actual square condition, or upper endpoint<=B.
components: full native arithmetic rate classifier; actual prime coprimality; full odd-prime carriers and principality iff square; explicit small-prime thresholds; exact root identity; injectivity by A*m>0; finite square-root rectangle; complete bounded upper-endpoint branch; union bound with overlaps retained.
actuals: two universal maintained real proofs and two new-only foundational-axiom audits. No finite numerical test supplies the count.
first_nonpositive_domain: reference endpoints are prime and h>0. Candidate pairs have m<q<=Y and differ from the reference. Each field-scale limit uses fixed compared pairs; the height count concerns those limiting rates. No growing-endpoint field uniformity, integer prime-pair supply, H1 value, RH/QRH improvement or established literature priority is claimed.

## Global rigidity of pairwise exceptional agreement (2026-10-31)

Paper: `finite-fields.tex`, Theorem `thm:native-agreement-geometry`. Owner: `Assembly/FiniteFieldNativeAgreementGeometry.lean`. Namespace: `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

| Claim / declaration | Status | Exact verified scope |
| --- | --- | --- |
| `native_half_agreement_family_rigidity` | proved | For every index type I and injective family of actual positive-gap prime pairs, all distinct native agreement rates equal1/2 iff either every lower-invariant product A_i*A_j is square or every upper-invariant product B_i*B_j is square, with A_i=h_i*n_i,B_i=h_i*(n_i+h_i). Empty, singleton, arbitrary finite and infinite families included. |

The full statement compiles warning-free. Its one new-only axiom audit contains only propext, Classical.choice and Quot.sound. No unchanged earlier proof closure was reaudited. The exclusion of mixed exceptional triangles is a mathematical consequence of this compiled arbitrary-family statement, rather than a separately compiled triangle declaration.

benchmark_status: complete global classification of pairwise exceptional families, proved.
old_bound: each distinct comparison had rate1/2 iff its lower or upper cross integer was square, with row choices treated pair by pair.
new_bound: every pairwise exceptional family has one globally shared lower squareclass or one globally shared upper squareclass; mixed exceptional triangles are excluded.
components: the actual native arithmetic classifier, its full square-indicator formula, exclusion of simultaneous matching rows for distinct pairs, exact positive-square cancellation, and global equivalence-relation propagation.
actuals: one universal maintained real proof and one new-only foundational-axiom audit; no finite experiment or independent-sign model supplies the theorem.
first_nonpositive_domain: actual prime endpoints, positive gaps and an injective pair family are required. Each compared pair is fixed before its field-scale limit; no common field cutoff for an infinite family, candidate-pair supply, H1 determination, RH/QRH gain or established literature priority is asserted.

## Prime-divisor support and unbounded exceptional families (2026-10-31)

Paper: `finite-fields.tex`, Theorems `thm:native-endpoint-divisors` and `thm:native-unbounded-lower-row`. Owner: `Assembly/FiniteFieldNativeEndpointDivisors.lean`. Namespace: `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

| Claim / declaration | Status | Exact verified scope |
| --- | --- | --- |
| `native_square_cross_rows_endpoint_divisors` | proved | For arbitrary natural n,h and actual candidate primes m,m+k with k>0, a lower cross square forces m dividing h*n, and an upper cross square forces m+k dividing h*(n+h). Includes endpoint2 without an odd-prime assumption. |
| `native_half_agreement_endpoint_divisor_cover` | proved | Every distinct actual positive-gap prime-pair comparison of native rate1/2 has m dividing h*n or m+k dividing h*(n+h), using the complete square-test classifier. |
| `native_half_agreement_unbounded_family_rigidity` | proved | For every injective family of actual positive-gap prime pairs with unbounded upper endpoints and all distinct rates1/2, every lower-invariant cross product is square, and every lower endpoint divides the lower invariant of every fixed reference. |

All three real declarations compile warning-free and pass exactly three new-only axiom audits containing only propext, Classical.choice and Quot.sound. The explicit finite prime-divisor-set interpretation is an elementary consequence of the compiled divisibility conclusion and positivity, rather than a separately compiled finite-set declaration. No unchanged previous closure was reaudited.

benchmark_status: exact arithmetic support and full unbounded-family restriction proved.
old_bound: exceptional endpoints satisfied m<=h*n or m+k<=h*(n+h); an arbitrary pairwise exceptional family could share either squareclass row.
new_bound: m divides h*n or m+k divides h*(n+h). An unbounded-upper-endpoint exceptional family must share the lower row, and every lower endpoint lies among the prime divisors of each fixed reference lower invariant.
components: exact native square classifier; coprimality of the two actual prime endpoints within each pair; prime divisibility of a square; cancellation of a positive prime; complete two-row family dichotomy; positive fixed upper invariant and the full unboundedness quantifier.
actuals: three universal maintained real proofs and three new-only foundational-axiom audits. No finite numerical test or assumed prime-producing polynomial supplies the theorem.
first_nonpositive_domain: candidate endpoints are prime with positive gap; the actual rate cover also requires distinct actual reference and candidate pairs with positive reference gap. The family theorem requires an injective pair map and unbounded upper endpoints. No new prime-pair supply, H1, RH/QRH gain, common field cutoff for an infinite family or established literature priority is claimed.

## Sharp collective native-agreement energy (2026-10-31)

Paper: `finite-fields.tex`, Theorem `thm:native-agreement-energy` and equations `eq:native-agreement-energy`, `eq:native-agreement-energy-kernel`. Owner: `Assembly/FiniteFieldNativeAgreementEnergy.lean`. Namespace: `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

| Claim / declaration | Status | Exact verified scope |
| --- | --- | --- |
| `native_agreement_form_lower_bound` | proved | Every finite index type, positive natural lower endpoints and gaps, and real coefficient vector satisfy Q >= (3/8)*((sum c)^2+sum c^2) for the explicitly defined kernel with diagonal1 and auxiliary native cross rates off the diagonal. Empty families and zero vectors included. |
| `native_agreement_mass_form_tendsto` | proved | For every fixed finite injective family of actual positive-gap prime pairs and every fixed real coefficient vector, the normalized physical agreement-mass quadratic form tends to the stated kernel form. Self mass equals the full reciprocal band mass; its normalized diagonal is eventually1. The codebook and coefficients are fixed before U tends to infinity. |
| `native_agreement_three_eighths_sharp` | proved | An actual injective four-pair prime codebook and coefficient vector have sum c=0, sum c^2=4, and Q=3/2. The proof constructs (11,43),(11,139),(41,43),(41,139) with c=(1,-1,-1,1). This witnesses optimality of the uniform Euclidean constant3/8. |

All three advertised theorems compile warning-free. Their three new-only axiom-closure audits contain only propext, Classical.choice and Quot.sound and cover the maintained private fixed-example lemmas used by the sharpness proof. No unchanged earlier closure was reaudited. The matrix/eigenvalue interpretation follows mathematically from the compiled quadratic inequality; a separate eigenvalue declaration is not advertised.

The complete paper proof retains the signed kernel K=(3/8)J+(1/8)L+(1/8)V+(3/8)Id. The positive squareclass relations partition the same finite support, so each row-kernel form is a sum of squared class totals. The diagonal correction is essential: the identical-pair auxiliary cross formula5/8 is not physical self-agreement1. The square/nonsquare certificates in the four-pair example are kernel-checked integer arithmetic. Finite diagnostic checks are separate evidence and do not prove the universal bound.

benchmark_status: sharp universal finite-family coercivity and actual physical limit proved.
old_bound: exact individual cross rates3/8 or1/2 and squareclass family rigidity; no installed uniform lower coefficient for all signed codebook forms.
new_bound: Q >= (3/8)*((sum c)^2+sum c^2) >= (3/8)*sum c^2, with the last coefficient optimal.
components: exact arithmetic cross-rate classifier; actual off-diagonal field-band limits; exact physical diagonal; positive-square cancellation and finite quotient partition; all signed products; maintained exact prime, square, nonsquare and rational sharpness certificates.
actuals: three maintained headline theorem proofs and their three foundational closure audits. A separate finite falsification check covered20686 signed small-codebook cases, including empty and singleton supports; those evaluations are not analytic inputs.
first_nonpositive_domain: every admissible nonzero coefficient vector has strictly positive limiting energy; empty families and the zero vector have energy0. The physical statement requires fixed finite injective actual prime-pair codebooks with positive gaps. No growing-codebook uniformity, new prime-pair supply, H1 value, RH/QRH exponent gain or established literature priority is asserted. Equality-kernel positivity is classical; the arithmetic application and actual sharpness witness are the new project result.

## Endpoint recovery in native squareclass rows (2026-10-31)

Paper: `finite-fields.tex`, Theorem `thm:native-row-fibres`. Owner: `Assembly/FiniteFieldNativeRowFibres.lean`. Namespace: `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

| Claim / declaration | Status | Exact verified scope |
| --- | --- | --- |
| `native_square_rows_recover_endpoints` | proved | For actual prime pairs n,n+h and m,m+k with positive gaps, a lower-row square match forces n=m when h<n and k<m; an upper-row square match always forces n+h=m+k. The prime2 is included. |

The maintained real proof compiled warning-free. Its one new-only axiom-closure audit contains only propext, Classical.choice and Quot.sound; no unchanged earlier closure was reaudited. This is a project-local supporting composition of the existing endpoint-divisor theorem and elementary prime divisibility. No independent novelty claim is made for the elementary argument.

benchmark_status: exact row-fibre endpoint constraints proved.
old_bound: a lower match gave m dividing h*n; an upper match gave m+k dividing h*(n+h).
new_bound: lower endpoints are equal under the two short-gap assumptions; upper endpoints are equal without short-gap assumptions.
components: the same endpoint-divisor implications applied in both directions; prime-divisor splitting; positive gaps and prime endpoints.
actuals: one universal maintained theorem and one new-only foundational-axiom audit; no numerical experiment.
first_nonpositive_domain: lower recovery requires h<n and k<m; upper recovery only requires actual prime endpoints and positive gaps. The full height-packing lower bound and matching capacity order are now proved in the final height-capacity section below. No RH/QRH exponent or H1 gain is asserted.

## Finite clean-gap native packing (2026-10-31)

Paper: `finite-fields.tex`, Theorem `thm:native-clean-packing` and equations `eq:native-clean-gap`, `eq:native-clean-packing`. Owner: `Assembly/FiniteFieldNativeCleanPacking.lean`. Namespace: `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

| Claim / declaration | Status | Exact verified scope |
| --- | --- | --- |
| `native_clean_gap_packing` | proved | For every finite set S of actual short prime pairs (n,n+h), 0<h<n, and natural T, if no gap has a square divisor u^2 with u>=T, some M subset S satisfies |S|<=2*(T-1)*|M| and every distinct selected native agreement rate is3/8. Natural subtraction includes T=0,1, when S is empty. Prime2 and empty supports are included. |

The complete maintained proof compiles warning-free. Its one new-only axiom closure contains only propext, Classical.choice and Quot.sound. Positive squarefree decomposition and finite maximization are existing Mathlib results; the real project-local argument combines them with the proved native endpoint recovery and exact rate classifier. No unchanged earlier closure was reaudited. No separate novelty is claimed for classical squarefree decomposition or finite matching.

benchmark_status: universal finite clean-support extraction bound proved.
old_bound: endpoint constraints alone, without an installed quantitative subfamily selection theorem.
new_bound: |S|<=2*(T-1)*|M|, with all distinct selected native rates3/8.
components: positive squarefree gap decomposition; exact square-factor cancellation; native endpoint recovery on both rows; root-index injection into {1,...,T-1}; maximum-cardinality two-row separation; the full finite neighborhood cover and overlap-safe union count; exact arithmetic native agreement classification.
actuals: one universal maintained Lean proof and one new-only foundational axiom closure. A separate diagnostic tested1937 full clean-support cases for consecutive heights2..150 and T=0..12, including prime2 and empty cases. Those computations are evidence only and do not supply the universal proof.
first_nonpositive_domain: a nonempty clean support forces T>=2 and a nonempty selected family. T=0,1 and empty supports have the stated zero case. The stronger Y^2/log(Y)^2 lower supply, matching upper order, PNT supply and complete physical capacity assembly are now proved in the final height-capacity sections below. Each finite family is fixed before its field limit. No RH/QRH or H1 gain is claimed.

## Exact integer square-divisor tail (2026-10-31)

Paper: `finite-fields.tex`, Theorem `thm:integer-square-tail`, equations `eq:integer-square-tail-step` and `eq:integer-square-tail`. Owner: `Mathlib/Data/Nat/DivSquareTail.lean`. Namespace: `Nat`.

| Claim / declaration | Status | Exact verified scope |
| --- | --- | --- |
| `Nat.div_sq_add_div_le_div_pred` | proved | Every natural Y and u>=2 satisfy Y/(u*u)+Y/u<=Y/(u-1), with natural division and no rounding remainder. Includes Y=0. |
| `Nat.sum_Ico_div_sq_le` | proved | Every natural Y,T,N with T>=2 satisfy sum over T<=u<N of Y/(u*u)<=Y/(T-1). The finite upper endpoint N is arbitrary; empty ranges and Y=0 are included. |

Both real proofs compile warning-free. Exactly two new-only closure audits were run: the step uses propext and Quot.sound; the finite tail also uses Classical.choice. These are standard classical arithmetic formalizations, maintained as a project-independent Mathlib candidate with sole import Mathlib.Algebra.BigOperators.Intervals, not standalone originality claims. The existing native packing construction is their consumer.

benchmark_status: exact universal integer floor-tail allowance proved.
old_bound: the proposed deletion argument had a real reciprocal-square tail and no installed natural-quotient telescoping bound.
new_bound: sum over T<=u<N of floor(Y/u^2)<=floor(Y/(T-1)), with no accumulated floor error.
components: associativity of natural division; u*floor(q/u)<=q; positive denominator u-1; complete finite induction retaining the terminal quotient; empty-interval case.
actuals: two maintained real proofs and two new-only closure audits. Separate diagnostics checked49599 one-step cases and14529 tail cases for Y=0..500; their restricted N=Y+1 tail domain is recorded and is not used as the universal proof.
first_nonpositive_domain: Y=0 or an empty summation interval gives the zero case. T>=2 ensures the displayed denominators are positive. The actual prime-pair deletion consumer is now proved in the next section; the stronger Y^2/log(Y)^2 lower bound and matching capacity order are now proved in the final height-capacity section below. No RH/QRH or H1 gain is asserted.

## Actual prime-product packing with the deletion allowance (2026-10-31)

Paper: `finite-fields.tex`, Theorem `thm:native-height-square-tail` and equation `eq:native-height-square-tail`. Owner: `Assembly/FiniteFieldNativeHeightPacking.lean`. Namespace: `PrimeFactorOscillations.FiniteFieldIntegerSignature`.

| Claim / declaration | Status | Exact verified scope |
| --- | --- | --- |
| `native_height_square_tail_packing` | proved | All finite prime sets A,B, every natural Y and natural T>=2 with Y<2*n on A, q<=Y on B and n<q on A x B admit a family M of actual short prime pairs with |A|*|B|<=2*(T-1)*|M|+|A|*floor(Y/(T-1)); all distinct selected native rates equal3/8. Empty sets and prime2 are included. |

The complete maintained real proof compiled warning-free. Its one new-only axiom closure contains only propext, Classical.choice and Quot.sound. No unchanged earlier closure was reaudited. Classical integer division, finite injections and the union estimate are inputs; the project-specific conclusion composes the exact divisor allowance with the native clean-support extraction theorem.

benchmark_status: exact finite prime-product supply and square-divisor loss assembled in one proved inequality.
old_bound: a clean-support extraction and a separate integer quotient tail, with no installed consumer on arbitrary actual prime endpoint products.
new_bound: |A|*|B|<=2*D*|M|+|A|*floor(Y/D), D=T-1>=1, with all distinct selected native rates3/8.
components: injective endpoint-to-gap coordinates; the quotient injection on every square-divisor fibre; every root T<=u<=Y; the complete overlap-safe finite union; exact natural quotient tail; native clean-support extraction.
actuals: one universal maintained proof and one new-only foundational axiom audit. A separate falsification check covered1419 full quarter-interval supports, every Y=0..128 and T=2..12, including lower prime2; no computation is an analytic input.
first_nonpositive_domain: the allowance can exhaust the displayed positive supply when floor(Y/D)>=|B|; no positivity is asserted there. The complete squarefree-gap route and full asymptotic height-capacity theorem are now proved in the final sections below. No integer H1 or RH/QRH exponent gain is asserted.

## Uniform actual prime-block collision estimate (2026-10-31)

Paper: `finite-fields.tex`, Theorem `thm:uniform-prime-block-collisions`, equations `eq:uniform-prime-block-collisions` and `eq:prime-block-signed-character-packet`. Owner: `Helpers/QRHPrimeBlockCollision.lean`. Namespace: `PrimeFactorOscillations.QRH`.

| Claim / declaration | Status | Exact verified scope |
| --- | --- | --- |
| `exists_primeBlockCollisionCount_le_seven_fourths` | proved | One C>0 precedes every positive modulus N and natural a,b,c,Y with N<=a<=b<=c<=Y. For actual prime blocks A=(a,b], B=(b,c], the congruent-pair count Q satisfies abs(Q-|A||B|/phi(N))<=C*Y^(7/4)*(1+log N+log(Y+2))^4. Includes modulus1, empty blocks and prime2 when admitted by the domain. |

The complete maintained proof compiles warning-free. Its one new-only closure audit contains only propext, Classical.choice and Quot.sound. No unchanged closure was reaudited. The analytic input is the already proved conductor-uniform 7/8 prime-character prefix bound, including imprimitive characters and every natural endpoint. Classical character orthogonality and the existing residue-count theorem provide the reconstruction. This application is supporting arithmetic for native packing, not a standalone priority claim or a new QRH exponent.

benchmark_status: actual two-block congruence discrepancy bounded uniformly without an extra totient or residue-class factor.
old_bound: the low-square-divisor route had no installed paired-prime congruence consumer; a separate-class product envelope would charge additional residue-class factors.
new_bound: abs(Q-|A||B|/phi(N))<=C*Y^(7/4)*(1+log N+log(Y+2))^4, with one universal C.
components: both interval prefix boundaries; inverse and direct nonprincipal characters; the full product support and repeated quotient outputs; exact principal unit mass |A||B|; the coupled character product; exact cancellation of the character-count denominator.
actuals: one universal maintained real proof and one new-only foundational axiom audit; no numerical experiment or assumed prime-count asymptotic.
first_nonpositive_domain: the error may exceed the principal supply on small or sparse blocks; no positivity is asserted in that regime. The complete finite squarefree-gap supply is now proved in the following section. The asymptotic native codebook order and optimal height capacity are now proved in the final section below. No H1 value or RH/QRH exponent gain is claimed.

## Complete finite squarefree prime-pair supply (2026-11-01)

Paper: `finite-fields.tex`, Theorem `thm:squarefree-prime-block-supply`, equations `eq:squarefree-prime-block-supply` and `eq:squarefree-full-union`. Maintained application owner: `Helpers/QRHSquarefreePrimePairs.lean`. The two reusable classical inputs are candidates under `Mathlib/Data/Finset/`.

| Claim / declaration | Status | Exact verified scope |
| --- | --- | --- |
| `Finset.card_filter_exists_sq_dvd_le` | proved | Every finite S of natural pairs (n,h) with n in a finite A and 0<h<=Y: the complete filtered union exists u>=T with u^2 dividing h has cardinal at most card(A)*floor(Y/(T-1)), for every natural Y and T>=2. Quotient-fibre injection, all overlaps, and the exact finite integer tail; no rounding loss. Extraction of the previously proved local high-root argument, not a new analytic saving. |
| `Finset.sum_inv_mul_pred_le_of_four_notMem` | proved | Every finite S of naturals n>=2 with 4 not in S satisfies sum_S 1/(n*(n-1))<=11/12 over the reals. Every denominator is positive. Classical finite telescoping with the excluded contribution 1/12; no numerical experiment or primality assumption. |
| `QRH.mem_primeBlockSet_iff` | proved | Membership in the actual block (a,b] is equivalent to primality together with a<p<=b, for all natural a,b,p, including empty and reversed endpoint ranges. |
| `QRH.exists_squarefreePrimeBlockGapSet_lower` | proved | One C>0 precedes all natural a,b,c,Y,R with R>=2 and R^2<=a<=b<=c<=Y. For the actual two blocks and their complete squarefree-gap support S_sf, card(A)*card(B)/12 <= card(S_sf)+C*R*Y^(7/4)*(1+2*log(Y+2))^4+card(A)*floor(Y/R). Empty blocks included. No RH premise. |

All three maintained owners compile warning-free in the pinned direct cached environment. The four new-only declaration closures contain exactly propext, Classical.choice and Quot.sound. Unchanged closures were not reaudited. The application retains the full product supply, every low prime-square divisor, the complete high-root union, repeated congruence outputs and the exact modulus range p^2<=R^2<=a. It consumes the already proved uniform 7/8 prime-character input; the certified zero-free boundary is unchanged. The classical candidate statements and block membership identity are supporting inputs, not standalone novelty claims.

benchmark_status: complete universal finite squarefree-gap lower bound installed; the asymptotic height-capacity theorem is still unproved.
old_bound: the full high-root union at cutoff T=2 supplies only the raw fallback card(S_sf)>=card(A)*card(B)-card(A)*Y; count nonnegativity also gives zero. This fallback is a mathematical consequence of the existing quotient-fibre and integer-tail inputs, not an advertised separately compiled comparison declaration.
new_bound: card(S_sf)>=card(A)*card(B)/12-C*R*Y^(7/4)*(1+2*log(Y+2))^4-card(A)*floor(Y/R), uniformly on the stated integer domain, with one existential C>0.
components: exact positive product supply; low principal reciprocal sum at most 11/12; all <=R prime-square collision errors with only the prime-root count <=R charged; full high-square-divisor allowance card(A)*floor(Y/R); no overlap or cutoff term discarded.
actuals: maintained real proofs and four new-only standard-foundation closures; no finite counts, numerical completions, or assumed prime-count asymptotics enter the bound.
first_nonpositive_domain: unavailable numerically because the inherited universal constant C has not been made explicit; no effective positivity cutoff is claimed. The quarter-block prime supplies are now formalized below. The rounded cutoff and native height cardinality are now formalized below; flat physical stability is proved below; matching capacity upper order and the assembled height consumer are now proved below.

## Uniform PNT prime-block supplies (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Exact theta increment is at most the prime-block cardinal times log Y | PrimeFactorOscillations.QRH.primeBlock_theta_sub_le_card_mul_log | Proved for all natural a<=b<=Y, including empty blocks. |
| Both adjacent quarter blocks have uniform PNT supply | PrimeFactorOscillations.QRH.eventually_primeQuarterBlock_supply | Proved: for all sufficiently large natural N and every Y>=4N, N<=2*card((2N,3N])*log Y and N<=2*card((3N,4N])*log Y. |

The maintained owner Helpers/PrimeBlockPackingSupply.lean compiles warning-free. Exactly the two new declaration closures were checked; each contains only propext, Classical.choice and Quot.sound. No RH premise is used. For N>=1 and Y>=4N the denominator 2*log Y is positive, yielding the displayed cardinal lower bounds in the paper. The finite theta comparison is exact, and the PNT threshold is uniform in Y.

benchmark_status: uniform lower supply installed in both actual prime blocks; full height-capacity theorem unproved.
old_bound: the complete finite squarefree-gap inequality retained its exact positive product supply without a formal asymptotic lower bound on that product.
new_bound: for the quarter blocks the positive product is at least N^2/(4*log(Y)^2), as a mathematical consequence of the compiled inequalities and positive denominator; the rounded-cutoff and native cardinality assembly are now proved below.
components: unconditional theta PNT bands 15n/16 and 17n/16; signed increments at least 11N/16 and 9N/16; exact finite prime sums; no sampled counts.
actuals: two maintained real proofs and two new-only standard-foundation closure checks, with no numerical completion.
first_nonpositive_domain: no effective numerical threshold is claimed because the inherited PNT convergence is existential.

## Asymptotic squarefree supply and native height codebooks (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Uniform squarefree prime-pair supply at every large height | PrimeFactorOscillations.QRH.eventually_squarefree_quarter_prime_pair_supply | Proved: with N=floor(Y/4), the actual squarefree-gap pairs from (2N,3N] and (3N,4N] have cardinality at least Y^2/(2000*log(Y)^2); also Y>=24 and log Y>=1. |
| Actual native codebooks with all distinct agreements three eighths | PrimeFactorOscillations.FiniteFieldIntegerSignature.eventually_native_prime_pair_height_packing | Proved: at every sufficiently large natural Y there is a finite set M of actual short prime pairs (n,n+h), with 0<h<n and n+h<=Y, cardinality at least Y^2/(4096*log(Y)^2), and all distinct native agreement rates 3/8. |

Helpers/NativeHeightSquarefreeSupply.lean and Assembly/FiniteFieldNativeAsymptoticPacking.lean compile warning-free. Exactly the two new public theorem closures were checked; both contain only propext, Classical.choice and Quot.sound. Their maintained proofs include every cutoff and integer-rounding condition. The arithmetic input is the existing unconditional uniform 7/8 character bound, with no new zero-free exponent claimed.

benchmark_status: complete positive squarefree supply and native codebook cardinality lower bound proved; flat physical stability is proved below; matching capacity upper order and the assembled height consumer are now proved below.
old_bound: the complete finite squarefree-gap inequality, supplemented by the two PNT block supplies, still retained a growing cutoff and both full error allowances.
new_bound: card(S_sf)>=Y^2/(2000*log(Y)^2), and an actual native codebook exists with card(M)>=Y^2/(4096*log(Y)^2), at every sufficiently large natural Y.
components: N=floor(Y/4), R=ceil(Y^(1/8)), 2<=R and R^2<=2N; exact positive product supply; complete low allowance at most 1250*C*Y^(15/8)*log(Y)^4; complete high allowance at most Y^(15/8); their sum at most Y^2/(2000*log(Y)^2); finite clean packing at T=2 costs a factor of two.
actuals: no numerical prime counts, diagnostic completions or finite checks enter the bound. The codebook contains actual integer prime pairs. Each codebook is fixed before the independent field-scale limit.
first_nonpositive_domain: no effective starting height is claimed because the inherited uniform constant C and PNT convergence thresholds remain existential. The theorem proves positivity for all sufficiently large heights.

## Exact flat native energy and optimal stability (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Exact full signed energy of every flat native kernel | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_flat_agreement_form | Proved for every finite I, arbitrary n,h:I->Nat, flat off-diagonal rates 3/8, and all real coefficient vectors: Q=(3/8)*(sum c)^2+(5/8)*sum(c^2). |
| Actual physical mass converges to the same exact form | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_flat_agreement_mass_form_tendsto | Proved with both endpoints prime, positive gaps, injective pair map and flat rates. The finite family and coefficients are fixed before U tends to infinity. |
| Flat native stability is at least five eighths | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_flat_agreement_stability | Proved for all finite flat kernels and all signed real coefficients, including the empty and one-entry cases. |
| No larger constant works on a nontrivial flat family | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_flat_agreement_stability_optimal | Proved when two specified distinct indices exist: every uniform lower constant kappa valid for all coefficient vectors is at most 5/8. |

Assembly/FiniteFieldNativeFlatEnergy.lean compiles warning-free. Exactly the four new public theorem closures were checked; each contains only propext, Classical.choice and Quot.sound. The physical diagonal is one, while the auxiliary cross-rate on identical labels is five eighths. No diagonal substitution is made. The matrix facts are classical supporting algebra for the actual native height-codebook construction; no standalone priority claim is made.

benchmark_status: exact flat physical energy and optimal five-eighths stability proved; matching height upper order and the assembled codebook consumer are now proved in the following section.
old_bound: arbitrary positive native families satisfy Q>=(3/8)*((sum c)^2+sum(c^2)); the general three-eighths sharpness theorem is unchanged.
new_bound: on the flat class Q=(3/8)*(sum c)^2+(5/8)*sum(c^2), and 5/8 is the largest uniform lower constant if at least two entries exist.
components: physical diagonal one; every off-diagonal exactly 3/8; all signed coefficient products retained; the proved finite-family physical mass limit; a two-coordinate vector with sum zero and squared norm two certifies optimality.
actuals: four maintained real proofs and four new-only standard-foundation closures; no numerical prime counts, character tables or diagnostic completions.
first_nonpositive_domain: the finite identity and lower bound are exact on the stated class. Optimality requires two distinct indices. No effective field-scale threshold is claimed.

## Optimal native height capacity and assembled physical stability (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Matching cardinality upper order for all actual prime-pair sets | PrimeFactorOscillations.FiniteFieldIntegerSignature.eventually_prime_pair_height_card_upper | Proved: for every sufficiently large natural Y, every finite V with prime endpoints and n+h<=Y has card(V)<=4*Y^2/log(Y)^2. Flat agreement and positive gaps are not needed for this upper bound. |
| Complete height-order codebook and sharp physical stability | PrimeFactorOscillations.FiniteFieldIntegerSignature.eventually_native_prime_pair_height_capacity | Proved: at every sufficiently large Y, an actual codebook M has short positive gaps, both prime endpoints, height<=Y, cardinality>=Y^2/(4096*log(Y)^2), at least two entries, and all distinct agreement rates 3/8. Its physical signed mass converges to (3/8)*(sum c)^2+(5/8)*sum(c^2), and a uniform stability constant works exactly when it is <=5/8. The same eventual statement includes the universal upper bound. |

Assembly/FiniteFieldNativeHeightCapacity.lean compiles warning-free. Exactly its two new public closures were checked; both contain only propext, Classical.choice and Quot.sound. The complete asymptotic height-capacity theorem is proved. The maximum-cardinality formulation follows mathematically from the displayed existential/universal bounds and the finite ambient pair set; no separate compiled maximum definition is advertised.

benchmark_status: full optimal height order and actual-codebook physical stability proved.
old_bound: the height lower codebook and separate flat-kernel energy were proved, without the matching upper order or assembled physical consumer.
new_bound: Y^2/(4096*log(Y)^2)<=card(M)<=4*Y^2/log(Y)^2 eventually, with at least two actual entries and optimal physical stability 5/8.
components: inject (n,h) into (n,n+h); apply the proved PNT bound pi(Y)<=2Y/log(Y); retain the complete squarefree-gap lower supply; use power-log decay to guarantee two entries; apply the exact physical limit with all signed cross products; prove both directions of the stability equivalence.
actuals: two maintained real proofs and two new-only standard-foundation closures; no finite prime counts or numerical completion.
first_nonpositive_domain: all conclusions hold for every sufficiently large natural height. The inherited constants and convergence cutoffs remain existential. Each finite codebook is fixed before the independent field-scale limit; no simultaneous growing-codebook limit, integer bounded-gap value or improved zero-free exponent is claimed.

## Exact weighted prime-pair collision sieve (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Weighted zero count over a finite field | Finset.card_nonzero_linear_sum_zero | Proved: over every finite field K and nonzero a,b, exactly card(K)-1 ordered pairs of nonzero coordinates satisfy a*x+b*y=0. |
| Exact finite weighted sieve in CRT coordinates | PrimeFactorOscillations.tendsto_prime_pair_weighted_sieve_pattern | Proved for every fixed finite pairwise-coprime prime family and natural coefficients nonzero modulo every selected prime: the actual ordered prime-pair residue event tends to the product of 1-1/(ell-1). |
| Direct sieve for actual integer weighted outputs | PrimeFactorOscillations.tendsto_prime_pair_weighted_nondivisibility_pattern | Proved on the complete ordered pairs of primes<=N, normalized by pi(N)^2, for the integer event ell does not divide a*p+b*q at every selected prime. The coefficients and finite prime family are fixed before N tends to infinity. |

The changed FiniteAffineRoots.lean candidate and new WeightedPrimePatterns.lean owner compile warning-free. Exactly these three new theorem closures were checked; all use only propext, Classical.choice and Quot.sound. Unequal coefficients are retained, and the whole integer weighted sum is typed before casting. The empty prime set and the permitted prime-two factor are included. These classical supporting facts do not independently settle the new density-one native retention target.

benchmark_status: finite weighted local and actual-input sieve factors proved; the completed native density-one assembly is recorded below.
old_bound: the proved height-capacity bounds remain Y^2/(4096*log(Y)^2) and 4*Y^2/log(Y)^2, with sharp physical stability 5/8 on the constructed codebooks.
new_bound: for every fixed permitted prime family, the exact limiting fraction is product(1-1/(ell-1)). The full native retention ratio is proved in the density-one section below.
components: nonzero field coefficients; one zero pair per nonzero first coordinate; positive local denominator ell-1; exact unit-pair CRT independence; both actual prime inputs retained; complete integer-output casting.
actuals: three maintained proofs and three new-only standard-foundation closure checks; no finite numerical prime experiments.
first_nonpositive_domain: the finite product is zero if an allowed sieve includes prime2 and is one for an empty sieve. Coefficient-zero primes are outside the hypothesis. This fixed-family component is consumed by the full density-one theorem below; no growing-sieve sampling limit is used.

## Vanishing weighted-prime-output density (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Vanishing sieve product outside a fixed prefix | PrimeFactorOscillations.tendsto_weighted_sieve_product_zero | Proved for every natural B>=2: the product over prime B<p<=n of 1-1/(p-1) tends to zero. |
| Zero density of positive weighted prime outputs | PrimeFactorOscillations.tendsto_weighted_prime_output_probability_zero | Proved for every fixed positive natural a,b,k: the probability on all ordered primes p,q<=N of existence of a prime r with a*p+b*q=k*r tends to zero. No cutoff on r is imposed. |

The maintained WeightedSieveDecay.lean owner compiles warning-free. Exactly these two new closures were checked; both use only propext, Classical.choice and Quot.sound. The proof preserves unequal coefficients, the small-output exception, and the order of limits: a finite sieve is fixed before N tends to infinity. These classical supporting estimates do not by themselves prove density-one native retention.

benchmark_status: weighted-prime-output decay proved and consumed by the completed native density-one theorem below.
old_bound: weighted-prime-output probability was bounded only by one; the committed native height-capacity and stability bounds remain unchanged.
new_bound: weighted-prime-output probability is o(1) for every fixed positive triple a,b,k. No effective cutoff or power rate is claimed.
components: exact weighted unit-pair CRT sieve; Mertens divergence of prime odds; nonnegative finite-product exponential bound; fixed small-first-prime exception; full finite probability union bound.
actuals: two maintained warning-free Lean proofs and two new-only standard-foundation closure checks; no numerical substitutions.
first_nonpositive_domain: not applicable to this nonnegative limit. The squarepart allowance, sparse native collision removal and final error absorption are all proved below. This component gives no RH exponent gain.

## Full large-squarepart deletion allowance (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Arbitrarily small principal squarepart deletion loss | PrimeFactorOscillations.QRH.exists_primeBlock_largeSquarepart_small_allowance | Proved: one universal C>0 works for every eps>0 after choosing T>=2, uniformly for every 2<=R and R^2<=a<=b<=c<=Y. The count of actual prime-block gaps with some integer u>=T satisfying u^2 divides the gap is at most eps*A.card*B.card + C*R*Y^(7/4)*(1+2*log(Y+2))^4 + A.card*floor(Y/R). |

The maintained NativeSquarepartTail.lean owner compiles warning-free. The one new theorem closure uses only propext, Classical.choice and Quot.sound. Every integer square root is included; T>R and the empty low interval are covered. The totient-tail summability consumes the already proved LPF uniform bound rather than introducing a new assumption. This is a supporting arithmetic estimate for the density-one native retention application.

benchmark_status: full finite squarepart deletion allowance proved and consumed by the completed native density-one theorem below.
old_bound: the earlier squarefree supply retained a fixed 1/12 fraction after a fixed 11/12 principal allowance.
new_bound: the principal mass of the full large-squarepart deletion set is at most eps times the actual block product, for every eps>0 and a suitable fixed T. Both finite errors remain explicit.
components: existing uniform collision estimate at every integer modulus u^2; summable 4/u^(3/2) majorant; complete low-root union T<=u<=R; complete high-root union u>=R+1; exact natural-quotient allowance.
actuals: one maintained warning-free proof and one new-only standard-foundation closure; no finite numerical prime experiments.
first_nonpositive_domain: not applicable to this upper bound. The theorem requires2<=R and R^2<=a; its explicit finite errors are absorbed in the density-one theorem below. No integer bounded-gap value or stronger zero-free exponent is claimed.

## Sparse removal of both native collision rows (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Exact finite collision deletion consumer | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_clean_sparse_collision_packing | Proved for every natural T,Y and finite S of short actual prime pairs with endpoints<=Y and no integer square root>=T dividing a gap: a subset M has all distinct native rates3/8 and S.card<=M.card+E_T(Y). E_T(Y) counts the actual ordered endpoint pairs<=Y satisfying either positive weighted-prime row event. |
| Vanishing full fixed-root event density | PrimeFactorOscillations.FiniteFieldIntegerSignature.tendsto_native_weighted_endpoint_output_probability_zero | Proved for every fixed natural T, including empty root ranges: E_T(Y)/pi(Y)^2 tends to zero. The finite root and row family is fixed before Y tends to infinity. |

The maintained FiniteFieldNativeSparseConflicts.lean owner compiles warning-free. Exactly these two new theorem closures use only propext, Classical.choice and Quot.sound. The proof retains both native rows, every squarefree core and all valid distinct root pairs. Equal roots are excluded by actual pair equality; the larger-root anchor produces one of the two positive weighted-prime equations. The probability predicate takes the two actual endpoints as separate inputs.

benchmark_status: full finite collision consumer and zero-density loss proved; the completed native density-one assembly is recorded below.
old_bound: the clean-set matching theorem gave S.card<=2*(T-1)*M.card.
new_bound: S.card<=M.card+E_T(Y), with E_T(Y)/pi(Y)^2 tending to zero for every fixed T. The complete lower bound is AB minus the D3 squarepart deletion bound minus E_T(Y).
components: both endpoint-recovery rows; squarefree-core cancellation; distinct-root orientation; both positive coefficient orders; complete supported finite union; actual endpoint injection.
actuals: two maintained warning-free proofs and two new-only standard-foundation closures; no numerical replacements for analytic estimates.
first_nonpositive_domain: not applicable to the finite loss inequality. T is fixed before the sampling limit; the uniform rounded-cutoff and error absorption are assembled in the following density-one theorem. No growing-root-family limit or improved zero-free exponent is claimed.

## Complete native density-one retention (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Almost all complete quarter-block actual prime pairs retained | PrimeFactorOscillations.FiniteFieldIntegerSignature.eventually_native_prime_pair_density_one | Proved: for every real eps>0, at every sufficiently large natural Y there is M contained in the full quarter-block prime-pair gap set S_Y with M.card>=(1-eps)*S_Y.card and every distinct native agreement rate exactly3/8. Every retained pair has prime endpoints, 0<h<n and n+h<=Y. |

The maintained FiniteFieldNativeDensityOne.lean owner compiles warning-free. The one new headline closure uses only propext, Classical.choice and Quot.sound. D1-D5 are now all proved. The complete signed consumer retains the actual block product and subtracts both the full large-squarepart loss and the full supported weighted-prime event count. The fixed root threshold is selected before the height tends to infinity.

benchmark_status: full density-one theorem proved.
old_bound: the height-order theorem gave Y^2/(4096*log(Y)^2) codewords; the clean-set matching consumer incurred the fixed factor2*(T-1).
new_bound: for every eps>0, all sufficiently large heights retain at least1-eps of every actual pair in the complete quarter-block candidate set. All distinct native rates remain exactly3/8.
components: D3 principal allowance eps/3; fixed-T probability threshold eps/972; arbitrary rounding reserve243/eps; exact PNT comparisons D<=81*AB and pi(Y)^2<=4*D; full retention AB-B_T-E_T with all errors retained.
actuals: one maintained warning-free full theorem and one new-only standard-foundation closure; no numerical substitutes for unresolved estimates.
first_nonpositive_domain: the conclusion holds for every sufficiently large natural height, with an existential cutoff depending on eps. No effective starting height or convergence rate is claimed. Density one is relative to the complete quarter-block candidate set; the certified integer zero-free boundary is unchanged.

## Sharp physical stability on density-one codebooks (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Same-witness density-one retention, physical energy and optimal stability | PrimeFactorOscillations.FiniteFieldIntegerSignature.eventually_native_density_one_physical_capacity | Proved: for every eps>0 and all sufficiently large natural heights, the same actual quarter-block codebook retains at least1-eps of all candidates, has at least two codewords and distinct rates3/8, has exact physical mass limit3/8*(sum c)^2+5/8*sum(c^2), and admits every uniform lower stability constant kappa exactly when kappa<=5/8. The finite codebook is fixed before the independent field-scale limit. |

The maintained FiniteFieldNativeDensityEnergy.lean owner compiles warning-free. Its one new closure uses only propext, Classical.choice and Quot.sound. This is a compiled corollary of density-one retention and the existing flat-energy theorems, with no separate priority claim. The at-least-two condition is proved using the smaller retention parameter min(eps,1/2) and the existing actual squarefree supply.

benchmark_status: full same-witness physical consumer proved; the density-one theorem remains complete.
old_bound: density-one retention and physical optimal stability were available in separate statements about constructed codebooks.
new_bound: the same almost-full codebooks satisfy the exact signed physical energy formula and optimal5/8 stability for every real coefficient vector. The retention fraction remains1-eps.
components: min(eps,1/2) selection; actual candidate count>=4; at least two retained codewords; injective endpoint labelling; exact physical diagonal and all signed cross terms; two-entry zero-sum sharpness witness.
actuals: one maintained warning-free combined theorem and one new-only standard-foundation closure; no numerical experiments or new arithmetic assumptions.
first_nonpositive_domain: all sufficiently large natural heights for each eps>0, with an existential threshold. Optimality includes an explicitly proved two-codeword witness. Each field-scale limit fixes the finite codebook; no simultaneous growing-family limit is claimed.

## Positive cross-output certificates without short gaps (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Unrestricted lower square row forces a positive three-prime equation | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_lower_square_cross_positive_output | Proved: for distinct lower primes n,m>2, positive gaps and prime upper endpoints, a square h*k*n*m gives positive a,b, h=m*a, k=n*b, a*b>1 and (a*b-1)*n+(n+h)=a*(m+k). No short-gap hypothesis. |
| Fixed lower endpoint cutoff bounds both output coefficients | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_lower_square_cross_bounded_positive_output | Proved: under the same hypotheses, endpoints<=Y and J*n,J*m>Y imply witnesses a,b<J, for arbitrary natural J,Y. |

The maintained FiniteFieldNativeCrossOutputs.lean owner compiles warning-free; exactly these two new closures use only propext, Classical.choice and Quot.sound. The prime2 exception is explicit: (n,h)=(2,3), (m,k)=(3,2) has square lower row and a*b=1. The coefficient triples (a*b-1,1,a) are positive and are admissible for the already proved arbitrary-positive weighted-prime output theorem, without requiring denominator=sum of coefficients.

benchmark_status: unrestricted finite collision certificate proved; full unrestricted density-one retention remains open.
old_bound: lower-row endpoint equality was available with both short-gap assumptions.
new_bound: without short gaps, every distinct-lower collision above the fixed lower cutoff maps to one of finitely many positive weighted-prime equations.
components: exact endpoint divisibility; distinct-prime coprimality; positive quotient witnesses; full parity exception; exact natural-subtraction identity; both coefficient cutoffs.
actuals: two maintained warning-free proofs and two new-only standard-foundation closures. The separate finite diagnostic checks 532 cross collisions among pairs with upper endpoint<=200 and is not an asymptotic input.
first_nonpositive_domain: lower prime2 is excluded by an explicit counterexample; empty coefficient ranges cause no exception. No new full retention fraction, effective cutoff, QRH exponent or integer prime-gap result is claimed.

## Arbitrary and identical prime-block collisions (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Uniform two-block congruence count without separation | PrimeFactorOscillations.QRH.exists_primeBlocksCollisionCount_le_seven_fourths | Proved: one C>0 before every nonzero modulus N and natural a,b,c,d,Y, with N<=a,c and a<=b<=Y,c<=d<=Y; absolute discrepancy from actual block-cardinality product/phi(N) is at most C*Y^(7/4)*(1+log N+log(Y+2))^4. Blocks may overlap or coincide. |
| Identical-block count including every diagonal pair | PrimeFactorOscillations.QRH.exists_primeBlockSelfCollisionCount_le_seven_fourths | Proved: N<=a<=b<=Y; principal mass is card(primes(a,b])^2/phi(N), with the same error form and a uniform existential constant. |
| Original adjacent-block statement preserved | PrimeFactorOscillations.QRH.exists_primeBlockCollisionCount_le_seven_fourths | Proved compatibility specialization with unchanged public statement. |

The maintained QRHPrimeBlockCollision.lean owner compiles warning-free. Exactly its two new closures and its changed compatibility-proof closure were checked; all use only propext, Classical.choice and Quot.sound. No unchanged theorem closures were re-audited. This generalizes the endpoint interface of the existing complete character-product proof and keeps its full principal mass and same-character product.

benchmark_status: uniform overlapping-block component proved; full unrestricted density-one consumer remains open.
old_bound: the public collision adapter required adjacent separated blocks (a,b] and (b,c].
new_bound: arbitrary two blocks, including the same block, with principal card(A)*card(B)/phi(N) and uniform error C*Y^(7/4)*L^4. The exponent and its constant provenance are unchanged.
components: existing all-modulus seven-eighths prime-character prefixes; both block boundaries; inverse character; complete character product before residue reconstruction; actual unit support; full diagonal.
actuals: two new maintained proofs and one changed compatibility proof, all warning-free and standard-foundation only. No numerical character tests are used.
first_nonpositive_domain: the modulus must not exceed either lower block endpoint; empty blocks and N=1 are included. For the planned square-modulus consumer require R^2<=floor(Y/J), with J fixed before Y. No new full retention fraction, effective threshold or zero-free exponent is claimed.

## Full squarepart allowance on arbitrary positive-gap supports (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Complete large-squarepart deletion bound on arbitrary supported prime pairs | PrimeFactorOscillations.QRH.exists_primeBlocksSupport_largeSquarepart_small_allowance | Proved: one C>0 before eps>0; choose fixed T>=2; all natural endpoints a<=b<=Y,c<=d<=Y, R>=2,R^2<=a,c, and every finite positive-gap support with lower endpoint in (a,b], upper endpoint in (c,d] and gap<=Y satisfy bad.card<=eps*card(A)*card(B)+C*R*Y^(7/4)*(1+2log(Y+2))^4+card(A)*floor(Y/R). |
| Adjacent-block full squarepart theorem preserved | PrimeFactorOscillations.QRH.exists_primeBlock_largeSquarepart_small_allowance | Proved compatibility specialization with unchanged statement. |

The maintained NativeSquarepartTail.lean owner compiles warning-free. Its one new theorem closure and one changed compatibility closure use only propext, Classical.choice and Quot.sound. The existing private summable totient-square allowance and exact high-root natural quotient are reused. The support may omit any candidates, but the principal allowance is against the actual endpoint-block product, not against its own potentially sparse cardinality.

benchmark_status: full-support uniform deletion component proved; unrestricted retention assembly remains open.
old_bound: the complete deletion estimate applied to the full adjacent-block gap image.
new_bound: the same complete allowance and errors apply to any positive-gap support in arbitrary endpoint blocks, including identical blocks.
components: sum over every integer square root; injective endpoint map; uniform complete same-character discrepancy; summable principal allowance; exact high-root floor(Y/R) term; full low/high union including T>R.
actuals: one new maintained proof and one changed compatibility proof, both warning-free and standard-foundation only; no numerical completion of unestimated terms.
first_nonpositive_domain: R>=2 and R^2<=both lower block endpoints are required. The threshold T is fixed before Y and no effective threshold is supplied. No density-one assertion for arbitrary sparse S or new zero-free exponent is claimed.

## Unrestricted finite collision extraction (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Full two-row flatness from clean gaps, root-event avoidance and lower-row recovery | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_clean_avoiding_weighted_outputs_flat_of_lower_recovery | Proved: finite actual prime-pair supports with positive gaps, no roots u>=T, avoidance of both root-output rows, and explicit square-lower-row endpoint recovery have every distinct agreement rate3/8. No short-gap assumption. |
| Fixed cross-output anchor class has zero prime-pair probability | PrimeFactorOscillations.FiniteFieldIntegerSignature.tendsto_native_cross_endpoint_output_probability_zero | Proved for every fixed natural J, including empty index ranges. The two arguments are actual endpoints; all positive triples (a*b-1,1,a), 1<=a,b<J,ab>1, are included. |
| Unrestricted finite extraction with both sparse losses | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_unrestricted_clean_sparse_collision_packing | Proved: all finite clean actual prime-pair supports with positive gaps, lower primes>2, upper endpoints<=Y and J*lower>Y admit M subset S with S.card<=M.card+E_T(Y)+C_J(Y), and every distinct native agreement rate3/8. J,T,Y are arbitrary naturals; no short-gap assumption. |
| Original short-gap sparse extraction preserved | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_clean_sparse_collision_packing | Proved compatibility consumer with unchanged public statement. The existing fixed-root probability theorem is unchanged and was not re-audited. |

Both maintained owners compile warning-free. Exactly the three new declarations and the changed compatibility proof use only propext, Classical.choice and Quot.sound. The full root-flatness proof is reused with an explicit lower-recovery hypothesis. The proved bounded positive-output certificate discharges it after cross-output deletion, with every upper-row and lower-row term retained.

benchmark_status: full unrestricted finite sparse consumer proved; its full-height density-one consumer is proved in the following section.
old_bound: clean sparse extraction required every gap to be shorter than its lower endpoint.
new_bound: without short gaps, S.card<=M.card+E_T(Y)+C_J(Y) above the fixed lower cutoff, and both fixed-parameter event probabilities tend to zero.
components: complete two-row root outputs; positive lower-row cross-output certificate; fixed finite coefficient union; exact actual-endpoint injection; both deletion classes and all squarefree cores.
actuals: three new maintained proofs and one changed compatibility proof across two owners, all warning-free and standard-foundation only. No finite numerical count replaces a limiting estimate.
first_nonpositive_domain: lower prime2 is excluded explicitly; J and T are fixed before the sampling limit. The clean support and lower cutoff are supplied in the full-height theorem below. No effective cutoff or new zero-free exponent is claimed.

## Full positive-gap density-one retention (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Full actual prime-pair candidate membership | PrimeFactorOscillations.FiniteFieldIntegerSignature.mem_nativeFullPrimePairGapSet_iff | Proved for every natural height and label: exactly prime n,n+h, positive h, upper endpoint<=Y. No short-gap condition. |
| Full candidate and low-prefix PNT supplies | PrimeFactorOscillations.FiniteFieldIntegerSignature.eventually_native_full_pair_supplies | Proved: for each fixed positive J, eventually D<=81 card(S_Y), pi(Y)^2<=4D, and pi(floor(Y/J))*pi(Y)<=(8/J)D, with D=Y^2/log(Y)^2. |
| Unrestricted density-one native codebooks | PrimeFactorOscillations.FiniteFieldIntegerSignature.eventually_native_full_prime_pair_density_one | Proved: for every real eps>0 and every sufficiently large natural Y, some M subset S_Y retains at least (1-eps) card(S_Y) and every distinct native agreement rate is3/8. All positive prime gaps with actual upper endpoint<=Y are admissible. |
| Completed quarter-block theorem preserved | PrimeFactorOscillations.FiniteFieldIntegerSignature.eventually_native_prime_pair_density_one | Proved with unchanged statement; its proof now specializes the private fixed-J cutoff at J=4. |

Maintained owners: Assembly/FiniteFieldNativeFullHeightSupply.lean and Assembly/FiniteFieldNativeDensityOne.lean. The three new declarations and the changed quarter-block proof compile warning-free, with exactly propext, Classical.choice and Quot.sound. The two unchanged supplier closures were reused from their existing successful audit rather than re-audited.

benchmark_status: full positive-gap retention proved; sharp full-height capacity and its same-witness physical specialization are proved in the following section.
old_bound: density-one retention was restricted to separated quarter blocks; arbitrary full-height labels had only constant-factor or finite clean-support results.
new_bound: card(M)>=(1-eps) card(S_Y), eventually for every natural Y and every fixed real eps>0; no short-gap restriction.
components: full positive supply D<=81 card(S_Y); low-prefix cost<=8D/J; complete squarepart principal and character/high-root remainder; both E_T and C_J; four allowances each<=eps D/324; total loss<=eps D/81.
actuals: three new maintained proofs and one changed compatibility proof. No finite numerical count is used in place of an analytic estimate.
first_nonpositive_domain: J>=4 with eps J>=2592 is fixed first, T second, then Y grows. The threshold is not effective. The sharp capacity and physical specialization are supplied below. No RH/QRH exponent or integer bounded-gap conclusion.

## Sharp full-height native capacity (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Two strict prime-pair triangles plus the full diagonal | PrimeFactorOscillations.FiniteFieldIntegerSignature.nativeFullPrimePairGapSet_card_twice | Proved for every natural Y: 2 card(S_Y)+pi(Y)=pi(Y)^2. Empty and singleton prime ranges are included. |
| Exact full positive-gap candidate cardinality | PrimeFactorOscillations.FiniteFieldIntegerSignature.nativeFullPrimePairGapSet_card | Proved for every natural Y: card(S_Y)=(pi(Y)^2-pi(Y))/2, with natural subtraction and division. |
| Sharp normalized full count | PrimeFactorOscillations.FiniteFieldIntegerSignature.tendsto_native_full_pair_count_ratio | Proved: card(S_Y)/(Y^2/log(Y)^2) tends to1/2 along natural heights, retaining the entire diagonal correction. |
| Sharp full capacity, relative retention, and same-witness physical stability | PrimeFactorOscillations.FiniteFieldIntegerSignature.eventually_native_full_pair_sharp_capacity | Proved for every fixed real eps>0: eventually every V subset S_Y has card(V)<=(1/2+eps)D, and the same constructed M retains at least1-eps of S_Y, has card(M)>=(1/2-eps)D and at least2 members, every distinct native rate3/8, the exact signed physical energy limit3/8(sum c)^2+5/8 sum c^2, and optimal lower stability constant5/8. |
| Largest flat codebook has leading constant1/2 | Direct mathematical squeeze consequence of the preceding compiled bracket | Established consequence; the maximal-size function itself is not a separate compiled declaration. |

Maintained owners: Assembly/FiniteFieldNativeFullCounting.lean and Assembly/FiniteFieldNativeFullCapacity.lean. Exactly these four new closures compile warning-free and use only propext, Classical.choice and Quot.sound. No earlier unchanged theorem closure was re-audited.

benchmark_status: full unrestricted native density-one and sharp-capacity programme proved.
old_bound: relative full-height retention was proved, with only constant-factor height supplies recorded.
new_bound: optimal full-height cardinality has leading constant1/2 on D=Y^2/log(Y)^2; for every eps>0 the compiled universal upper and constructed lower brackets are (1/2+eps)D and (1/2-eps)D.
components: exact upper/lower triangle bijection and diagonal; existing PNT ratio; log(Y)/Y decay; full retained coefficient(1-delta)(1/2-delta), delta=min(eps/8,1/8); all signed physical cross terms; same codebook with at least2 members.
actuals: four new maintained proofs across two focused owners. No finite numerical completion or assumed asymptotic is used.
first_nonpositive_domain: eps>0 fixed before Y; every sufficiently large natural height; positive normalized denominators and at least2 retained labels. Each finite codebook is fixed before the independent field-scale limit. No effective threshold, simultaneous growing-codebook limit, new zero-free exponent or integer bounded-gap claim.


## Sharp deletion deficit and every-maximal native capacity (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Positive square-product transitivity | Nat.isSquare_mul_trans_of_pos | Proved for natural a,b,c with b>0: square(a*b) and square(b*c) imply square(a*c). Classical supporting lemma extracted to the Mathlib candidate layer. |
| At most one conflict in each native row | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_flat_square_row_conflicts_card_le_one | Proved for every finite flat actual prime-pair family and every positive anchor; both complete row filters have cardinality at most1. |
| Complete two-row conflict bound | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_flat_square_conflicts_card_le_two | Proved: the full conflict union has cardinality at most2, including its intersection. |
| Full finite deletion comparison | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_dominating_selection_flat_deficit | Proved: for every finite actual support S, dominating G subset S, and flat M subset S, card(S minus G)<=2 card(S minus M). G need not be flat. All complements are relative to S. |
| Actual-prime sharpness certificate | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_dominating_selection_flat_deficit_sharp | Proved: labels(11,2),(11,8),(5,8), with middle singleton G and outer pair M, have actual prime endpoints, both required flatness properties, domination, and deletion deficits2 and1. The constant2 is optimal as a direct consequence. |
| Sharpness witness rates | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_maximal_packing_sharp_rates | Proved: the two middle conflicts have rate1/2 and the outer pair has rate3/8, using explicit roots and nonsquare intervals. |
| Insertion maximality implies full square-row domination | PrimeFactorOscillations.FiniteFieldIntegerSignature.native_insertion_maximal_flat_selection_dominates | Proved on every finite actual support. A selection is insertion-maximal when any flat single-label extension was already selected; inclusion maximality implies this condition. |
| Density-one retention uniformly over every dominating selection | PrimeFactorOscillations.FiniteFieldIntegerSignature.eventually_native_full_dominating_density_one | Proved: for every eps>0, eventually for every natural Y and every dominating G subset S_Y, card(G)>=(1-eps)card(S_Y). |
| Sharp capacity uniformly over every dominating selection | PrimeFactorOscillations.FiniteFieldIntegerSignature.eventually_native_full_dominating_sharp_capacity | Proved: the same universally quantified G has relative retention and bracket(1/2-eps)D<=card(G)<=(1/2+eps)D. |
| Every maximal family's same-witness physical limit and optimal stability | PrimeFactorOscillations.FiniteFieldIntegerSignature.eventually_native_full_maximal_physical_capacity | Proved: every insertion-maximal flat G at every sufficiently large height has relative retention, the sharp bracket, at least2 members, exact signed physical limit3/8(sum c)^2+5/8 sum c^2, and optimal lower stability constant5/8. |

All three maintained owners compile warning-free. Exactly these ten new theorem closures use only propext, Classical.choice and Quot.sound. Earlier unchanged closures are not re-audited.

benchmark_status: sharp finite deficit and every-maximal full-height capacity proved.
old_bound: the full-height theorem selected an existential density-one family separately for each height.
new_bound: every dominating family at the same sufficiently large height has density1 and leading capacity1/2; every maximal flat family also has the exact physical limit.
components: positive square-row transitivity; both full conflict rows; complete charge from M minus G to G minus M; exact finite deficit identities; full retention at eps/2; absolute lower bound2 card(M)-card(S_Y); delta=eps/4.
actuals: ten new maintained declarations across three focused owners; explicit actual-prime witness, no numerical completion of an analytic remainder.
first_nonpositive_domain: positive square-transitivity middle factor; actual prime endpoints and positive gaps; eps fixed before all sufficiently large natural heights; each finite family fixed before the field limit. The coherent single infinite computable family is proved in the following section. No new zero-free exponent or integer bounded-gap conclusion.


## One computable coherent infinite native family (2026-11-01)

| Claim | Maintained declaration | Status and scope |
| --- | --- | --- |
| Computable choices and global membership | Definitions.NativePrimePairGreedy: nativePrimePairGreedyInsert, nativePrimePairGreedyScan, nativePrimePairGreedyPrefix, nativePrimePairGreedyClass and decidability instances | Compiled computable definitions. Visit every lower endpoint below each upper endpoint, check both primes and both complete square rows; selected labels are never removed. No noncomputable declaration or choice-based construction. |
| Prefix geometry, flatness and monotonicity | nativePrimePairGreedyPrefix_geometry; nativePrimePairGreedyPrefix_flat; nativePrimePairGreedyPrefix_mono | Proved for every natural height, including0. Every selected label has actual prime endpoints, positive gap and upper endpoint at most the height. |
| Complete support is retained or blocked | nativePrimePairGreedyPrefix_retained_or_blocked; nativePrimePairGreedyPrefix_dominates | Proved for every label of S_Y; blockers are retained from the actual birth visit through every later prefix. Both square rows and long gaps are included. |
| Every prefix is maximal flat | nativePrimePairGreedyPrefix_agreement; nativePrimePairGreedyPrefix_maximal | Proved: all distinct selected rates are3/8, and every flat single-label extension was already selected. |
| Exact global coherence | nativePrimePairGreedyPrefix_mem_at_birth; nativePrimePairGreedyPrefix_mem_iff | Proved: prefix membership is equivalent to membership in the one fixed decidable class and in S_Y. |
| Global actual-prime geometry and flatness | nativePrimePairGreedyClass_geometry; nativePrimePairGreedyClass_agreement | Proved for every global class member and every distinct pair, by placing both in the prefix at their maximum birth height. |
| Uniform persistent capacity | eventually_nativePrimePairGreedyPrefix_capacity | Proved: every fixed eps>0 gives relative retention and the sharp(1/2+-eps)D bracket along all sufficiently large natural heights. |
| Prefix sizes are unbounded and the one class is infinite | eventually_nativePrimePairGreedyPrefix_card_ge; nativePrimePairGreedyClass_infinite | Proved: for every N, eventually card(G_Y)>=N; the decidable global class is infinite. |
| Actual retained fraction tends to1 | tendsto_nativePrimePairGreedyPrefix_retention_ratio | Proved along all natural heights, with denominators positive eventually. |
| Sharp normalized persistent size tends to1/2 | tendsto_nativePrimePairGreedyPrefix_count_ratio | Proved: card(G_Y)/(Y^2/log(Y)^2) tends to1/2. |
| Full constructive headline | native_computable_density_one_flat_prime_pair_family | Proved and compiled as one statement: the fixed class is infinite, consists of actual positive prime pairs, is pairwise flat, has exactly coherent truncations, and both density and sharp-capacity limits hold. |
| Physical energy and optimal stability for the same large prefixes | Mathematical consequence of compiled every-maximal physical capacity and greedy maximality | Established consequence, with each finite prefix fixed before the field limit; no separate growing-codebook field limit is claimed. |

Unqualified declarations in this section belong to PrimeFactorOscillations.FiniteFieldIntegerSignature. The two proof owners and the computable definition owner compile warning-free. All twenty-nine new proof closures use only standard Lean foundations: propext, Classical.choice and Quot.sound; the square-compatibility symmetry proof uses only propext. No earlier unchanged closure was re-audited.

benchmark_status: the coherent infinite density-one construction is proved.
old_bound: a density-one flat family could be chosen separately at each height; no single fixed computable global class was supplied.
new_bound: one decidable infinite G satisfies G_Y=G intersect S_Y for every natural height, card(G_Y)/card(S_Y)->1 and card(G_Y)/(Y^2/log(Y)^2)->1/2; all distinct global native rates are3/8.
components: all-prime endpoint scan; computable square tests; preservation of every old choice and blocker; exact birth-height identity; universal2-deficit consumer; complete positive supply; positive-denominator order limits.
actuals: twenty-nine new proof declarations, seven computable definitions/instances, no finite numerical replacement of a universal estimate.
first_nonpositive_domain: primes include2, all positive gaps are admitted, and small empty prefixes are handled. Asymptotic cutoffs are not effective. Physical consequences keep each finite family fixed before the field limit.

## Arbitrary fixed-degree split-product rejection (2026-11-01)

The following five maintained proof declarations compile warning-free and have completed new-closure assumption audits. Earlier unchanged closures were not re-audited. The full infinite vertex/gap independence and cycle-classification consumer is now proved in the following claim section.

| Claim | Lean declaration | Status |
| --- | --- | --- |
| A positive squarefree factor of a square product divides its partner | Nat.squarefree_dvd_of_positive_square_product | Proved; compiled and audited. |
| Common-prime support gives a fixed-divisor square-class representative | Nat.exists_square_class_divisor_of_common_prime_support | Proved; compiled and audited. |
| A common divisor of two shifts divides the absolute root difference | Nat.dvd_root_difference_of_dvd_shifts | Proved; compiled and audited. |
| Every square split product has a root-difference divisor certificate | Nat.split_square_has_root_difference_divisor | Proved; compiled and audited. |
| Actual-prime square-value density is zero for every fixed nonempty split product | PrimeFactorOscillations.tendsto_prime_split_product_square_values_zero | Proved; compiled and audited. |
| Full infinite prime-vertex/gap squareclass independence and exact cycle kernel | native_prime_cycle_kernel_family | Proved; compiled and audited; see full-family claims below. |

Reusable candidates: Mathlib/Data/Nat/SquareProductSupport.lean and SplitSquareCertificate.lean, both in the Nat namespace and listed in MATHLIB_PORTING.md. The prime limit owner is Proof/AffinePairs/PrimeSplitSquarePolynomials.lean. Natural subtraction is truncated; all inputs at or below the fixed root bound belong to an explicitly bounded zero-density event. Above that bound the expression is the ordinary split polynomial.

benchmark_status: the universal fixed-degree rejection theorem and its full infinite independence/cycle consumer are proved.
old_bound: installed affine and split quadratic square-value sparsity.
new_bound: square-value prime-relative frequency tends to zero for every fixed positive coefficient and every fixed nonempty finite set of distinct natural roots, of arbitrary finite size.
components: positive squarefree decomposition; exact common-prime support absorption; all root differences; a finite union over every divisor of the fixed positive D; proved affine prime-relative sparsity; the bounded small-input event.
actuals: five new audited proofs; no finite numerical test or higher-degree character estimate is substituted for a proof.
first_nonpositive_domain: no uniformity in root count, root size or coefficient is claimed. A=empty and c=0 are excluded and can give frequency1. Small cutoffs including pi(N)=0 are included. No quantitative global vertex growth or new RH/QRH exponent is asserted.

## Full prime-vertex/gap independence and exact cycle kernel (2026-11-01)

Every declaration below belongs to PrimeFactorOscillations.FiniteFieldIntegerSignature. These forty-four new maintained proof closures compile warning-free and have completed new-only assumption audits. All earlier unchanged proofs were left unaudited. Thirteen new definitions/instances implement finite indexed bases, full-relation tests, the computable scan and row incidence data.

| Claim | Lean declaration | Status |
| --- | --- | --- |
| Vertex membership in the indexed basis | native_gap_basis_vertex_mem | Proved; compiled and audited. |
| Strict-edge membership in the indexed basis | native_gap_basis_edge_mem | Proved; compiled and audited. |
| Every prime vertex/gap coordinate is positive | native_gap_basis_value_positive | Proved; compiled and audited. |
| Every supported old subproduct is positive | native_gap_subfamily_product_positive | Proved; compiled and audited. |
| Every old coordinate lies below a larger prime | native_gap_basis_value_lt | Proved; compiled and audited. |
| The empty seed is fully independent | native_gap_independent_empty | Proved; compiled and audited. |
| The coordinate basis preserves vertex-set inclusions | native_gap_basis_monotone | Proved; compiled and audited. |
| A larger new vertex is absent from the old seed | native_gap_new_vertex_not_mem | Proved; compiled and audited. |
| Exact new-coordinate erase/image partition | native_gap_new_part_erase | Proved; compiled and audited. |
| Exact old/new product partition | native_gap_relation_product_partition | Proved; compiled and audited. |
| Exact new-prime and new-gap product | native_gap_new_part_product | Proved; compiled and audited. |
| Empty pieces imply an empty relation | native_gap_relation_empty_of_parts | Proved; compiled and audited. |
| The new prime cannot occur in a square relation | native_gap_new_vertex_excluded | Proved; compiled and audited. |
| Full finite squareclass-independent insertion | native_gap_independent_insert | Proved; compiled and audited. |
| Every new-relation rejection has density zero | tendsto_native_prime_gap_unclear_zero | Proved; compiled and audited. |
| Full rejection plus bounded cutoff has density zero | tendsto_native_prime_gap_rejection_zero | Proved; compiled and audited. |
| Full clear insertion adapter | native_gap_clear_insertion_independent | Proved; compiled and audited. |
| Signed actual reservoir supply with every loss retained | native_prime_gap_reservoir_supply | Proved; compiled and audited. |
| An independent reservoir extension exists above every bound | exists_native_prime_gap_reservoir_extension_above | Proved; compiled and audited. |
| Greedy insertion adds only its candidate | native_prime_gap_insert_subset | Proved; compiled and audited. |
| Greedy insertion preserves old vertices | native_prime_gap_insert_contains | Proved; compiled and audited. |
| Full square independence passes to subsets | native_gap_independent_mono | Proved; compiled and audited. |
| One scan step adds only its candidate | native_gap_reservoir_prefix_step_subset | Proved; compiled and audited. |
| Every prefix contains bounded reservoir primes and is fully independent | native_gap_reservoir_prefix_geometry | Proved; compiled and audited. |
| Prefixes persist | native_gap_reservoir_prefix_monotone | Proved; compiled and audited. |
| Membership was decided at birth | native_gap_reservoir_prefix_mem_birth | Proved; compiled and audited. |
| Exact prefix/global-class coherence | native_gap_reservoir_prefix_mem_iff | Proved; compiled and audited. |
| Global class vertices are reservoir primes | native_gap_reservoir_class_geometry | Proved; compiled and audited. |
| The computable reservoir class is infinite | native_gap_reservoir_class_infinite | Proved; compiled and audited. |
| Every finite global-class subset is fully independent | native_gap_reservoir_class_finite_independent | Proved; compiled and audited. |
| Full infinite independent reservoir family | native_infinite_prime_gap_independent_family_in_reservoir | Proved; compiled and audited. |
| Explicit positive upper density gives infinity | native_gap_reservoir_infinite_of_positive_upper_density | Proved; compiled and audited. |
| Unconditional full-prime infinite independent family | native_infinite_prime_gap_independent_family | Proved; compiled and audited. |
| Exact even/odd coordinate product factorization | native_gap_power_parity_factorization | Proved; compiled and audited. |
| Square products are exactly even exponent vectors | native_gap_square_power_product_iff | Proved; compiled and audited. |
| Exact finite edge support | native_gap_edges_mem_iff | Proved; compiled and audited. |
| Exact vertex incidence exponent | native_gap_row_multiplicity_vertex | Proved; compiled and audited. |
| Exact gap incidence exponent | native_gap_row_multiplicity_edge | Proved; compiled and audited. |
| Finite fiber product identity for coordinates | native_gap_mapped_product | Proved; compiled and audited. |
| Exact lower/upper row product as coordinate powers | native_gap_row_product_powers | Proved; compiled and audited. |
| Complete finite cycle square-product classifier | native_gap_row_product_square_iff | Proved; compiled and audited. |
| Classifier on every finite reservoir-class subset | native_gap_reservoir_row_product_square_iff | Proved; compiled and audited. |
| Infinite independent reservoir family with exact cycle kernel | native_prime_cycle_kernel_family_in_reservoir | Proved; compiled and audited. |
| Unconditional infinite family with exact cycle kernel | native_prime_cycle_kernel_family | Proved; compiled and audited. |

Owners: Definitions/NativePrimeVertexGapIndependent.lean, NativePrimeVertexGapExtension.lean, NativePrimeVertexGapGreedy.lean and NativePrimeCycleRows.lean; Helpers/NativePrimeVertexGapGeometry.lean, NativePrimeVertexGapPartition.lean, NativePrimeVertexGapInsertion.lean, NativePrimeVertexGapGreedy.lean, NativePrimeVertexGapParity.lean, NativePrimeVertexGapIncidence.lean and NativePrimeVertexGapCycles.lean; Proof/AffinePairs/PrimeVertexGapRejections.lean; Assembly/FiniteFieldIndependentPrimeVertexDensity.lean, FiniteFieldIndependentPrimeVertices.lean and FiniteFieldPrimeCycleKernel.lean. The public NativePacking facade exports the complete result. All assumption closures use only propext, Classical.choice and Quot.sound.

benchmark_status: full infinite computable square-independent prime vertex/gap family and exact arbitrary-size row-relation classifier proved.
old_bound: complete native-flat families excluded pairwise lower/upper square collisions; arbitrary larger finite square relations remained uncontrolled.
new_bound: every finite vertex/gap subproduct is square only for empty support. Every lower-A/upper-B row product is square iff A=B and every vertex has even degree in A. At every actual prime cutoff, valid reservoir supply is at least rho_N(R)-epsilon_(P,B0)(N), with epsilon->0 for each fixed finite independent seed and bound.
components: exact disjoint coordinate insertion; the new prime's forced even valuation; every old subproduct and every nonempty new-gap subset; full arbitrary-degree rejection union; signed reservoir supply; finite birth coherence; full odd-support square cancellation; exact edge and vertex incidence counts.
actuals: forty-four new real Lean theorem proofs, forty-four new-only foundational closure audits, thirteen computable definitions/instances; no finite experiment supplies a universal estimate.
first_nonpositive_domain: the finite signed supply may be nonpositive at small cutoffs. For any fixed delta>0 attained by reservoir frequency at unbounded cutoffs, supply is at least delta/2 after epsilon<delta/2. No effective onset, uniformity in growing seeds, global class density, prescribed integer prime-gap value or RH/QRH gain is asserted. Empty supports, isolated vertices, prime2 and pi(N)=0 are included.

## Prescribed prime reservoirs (2026-11-01)

All fifteen claims have maintained Lean proofs and completed new-closure assumption audits. Every declaration below belongs to PrimeFactorOscillations.FiniteFieldIntegerSignature. The three reservoir construction definitions/instances are ordinary computable code using the supplied decision procedure.

| Claim | Lean declaration | Status |
| --- | --- | --- |
| Full signed supply inside an arbitrary prime reservoir | native_prime_vertex_reservoir_supply | Proved; compiled and audited. |
| All collision and bounded-cutoff rejections have relative density zero | tendsto_native_prime_vertex_rejection_zero | Proved; compiled and audited. |
| An actual reservoir extension above every bound | exists_native_prime_vertex_reservoir_extension_above | Proved; compiled and audited. |
| A restricted prefix adds only its candidate vertex | native_reservoir_prefix_step_subset | Proved; compiled and audited. |
| Every prefix is flat and consists of bounded reservoir primes | native_reservoir_prefix_geometry | Proved; compiled and audited. |
| Restricted prefixes persist | native_reservoir_prefix_monotone | Proved; compiled and audited. |
| Restricted membership was decided at birth | native_reservoir_prefix_mem_birth | Proved; compiled and audited. |
| Exact restricted prefix/global-class coherence | native_reservoir_prefix_mem_iff | Proved; compiled and audited. |
| Global vertices are primes satisfying the prescribed predicate | native_reservoir_class_geometry | Proved; compiled and audited. |
| Every nonvanishing-frequency reservoir gives an infinite greedy class | native_reservoir_class_infinite | Proved; compiled and audited. |
| Both square rows separate for all distinct complete pair labels | native_reservoir_class_square_compatible | Proved; compiled and audited. |
| Every distinct complete pair-label native rate is3/8 | native_reservoir_class_agreement | Proved; compiled and audited. |
| Full infinite computable complete family in the prescribed reservoir | native_complete_prime_vertex_family_in_reservoir | Proved; compiled and audited. |
| Explicit positive upper relative density supplies infinity | native_reservoir_infinite_of_positive_upper_density | Proved; compiled and audited. |
| Finite vertex-coloring corollary with existential color selection | native_monochromatic_complete_prime_vertex_family | Proved; compiled and audited. |

Owners: Definitions/NativePrimeVertexReservoir.lean, Assembly/FiniteFieldNativeVertexReservoirExtension.lean and Assembly/FiniteFieldNativeVertexReservoir.lean. Only the fifteen new proof closures were audited; unchanged old closures were not repeated. All focused owners compile warning-free and use only standard Lean foundations. The color corollary does not claim a uniform computable color selector.

benchmark_status: universal reservoir extension and full infinite complete-family theorems proved.
old_bound: the completed vertex construction selected from all primes; no prescribed-reservoir consumer was installed.
new_bound: at every cutoff, admissible reservoir mass is at least rho_N(R)-epsilon_(P,B)(N), with epsilon_(P,B)(N)->0 for every fixed finite flat prime seed and upper bound. Nonvanishing upper relative frequency forces an infinite computable complete family inside R.
components: positive actual reservoir prime frequency; negative complete collision-union and finite-cutoff mass; every overlap retained; prime-supported cover; exact birth coherence and finite-class contradiction.
actuals: fifteen audited proof declarations and three computable definitions/instances; no finite diagnostic or numerical substitute.
first_nonpositive_domain: the finite signed bound may be nonpositive before the rejection mass is small. Under an explicit delta>0 on unbounded reservoir cutoffs, the bound is at least delta/2 once epsilon<delta/2; no effective threshold or global vertex growth estimate is asserted. N=0,1 and arbitrary predicate values on composites are included.

## Complete prime-vertex families (2026-11-01)

All claims below have maintained Lean proofs and completed new-closure assumption audits. The finite extension density is1 for each fixed finite prime vertex set; the global vertex growth rate is unquantified. The six vertex construction definitions/instances are computable. Native declarations without a written namespace below belong to PrimeFactorOscillations.FiniteFieldIntegerSignature.

| Claim | Lean declaration | Status |
| --- | --- | --- |
| Complete square count including zeros | FiniteField.twice_square_values_card | Proved; compiled and audited. |
| Affine complete square count | FiniteField.twice_affine_square_values_card | Proved; compiled and audited. |
| Split quadratic complete square count | FiniteField.twice_split_quadratic_square_values_card | Proved; compiled and audited. |
| Affine unit fraction at most3/4 for field size at least11 | FiniteField.four_affine_unit_square_card_le_three | Proved; compiled and audited. |
| Split quadratic unit fraction at most3/4 for field size at least11 | FiniteField.four_split_quadratic_unit_square_card_le_three | Proved; compiled and audited. |
| Exact first-coordinate prime marginal | PrimeFactorOscillations.prime_pair_probability_first_marginal | Proved; compiled and audited. |
| Unary fixed-modulus prime CRT product limit | PrimeFactorOscillations.tendsto_prime_crt_pattern_probability | Proved; compiled and audited. |
| Prime square sparsity from arbitrarily many unit tests | PrimeFactorOscillations.tendsto_prime_square_values_zero_of_unit_tests | Proved; compiled and audited. |
| Actual-prime affine square sparsity | PrimeFactorOscillations.tendsto_prime_affine_square_values_zero | Proved; compiled and audited. |
| Actual-prime split quadratic square sparsity | PrimeFactorOscillations.tendsto_prime_split_quadratic_square_values_zero | Proved; compiled and audited. |
| Prime-event domination transfer | PrimeFactorOscillations.tendsto_prime_event_zero_of_imp | Proved; compiled and audited. |
| Full finite union has zero prime-relative density | PrimeFactorOscillations.tendsto_prime_finite_union_zero | Proved; compiled and audited. |
| Finite initial prime range has zero relative density | PrimeFactorOscillations.tendsto_prime_bounded_event_zero | Proved; compiled and audited. |
| Complement-zero implies density one | PrimeFactorOscillations.tendsto_prime_event_one_of_complement_zero | Proved; compiled and audited. |
| Decision-independent count equality | PrimeFactorOscillations.prime_filter_ratio_eq_probability | Proved; exact normalization only. |
| Canonical domination interface | PrimeFactorOscillations.tendsto_prime_probability_zero_of_imp | Proved; exact normalization only. |
| Canonical finite-union interface | PrimeFactorOscillations.tendsto_prime_probability_finite_union_zero | Proved; exact normalization only. |
| Canonical finite-range interface | PrimeFactorOscillations.tendsto_prime_probability_bounded_zero | Proved; exact normalization only. |
| Canonical complement interface | PrimeFactorOscillations.tendsto_prime_probability_one_of_complement_zero | Proved; exact normalization only. |
| Every new/old collision excluded by full rejection test | native_prime_vertex_new_old_compatible | Proved; compiled and audited. |
| Both new/new rows excluded, with positive square-factor cancellation | native_prime_vertex_new_new_compatible | Proved; compiled and audited. |
| Complete largest-prime insertion preserves flatness | native_prime_vertex_clear_insertion_flat | Proved; compiled and audited. |
| All rejection families together have prime-relative density zero | tendsto_native_prime_vertex_unclear_zero | Proved; compiled and audited. |
| Clear extensions have prime-relative density one | tendsto_native_prime_vertex_clear_one | Proved; compiled and audited. |
| Valid larger prime extensions have relative density one | tendsto_native_prime_vertex_valid_extensions_one | Proved; compiled and audited. |
| Actual valid prime extension above any fixed bound | exists_native_prime_vertex_extension_above | Proved; compiled and audited. |
| Every accepted insertion preserves old vertices | native_prime_vertex_insert_contains | Proved; compiled and audited. |
| An insertion adds only its candidate vertex | native_prime_vertex_insert_subset | Proved; compiled and audited. |
| Every prefix consists of bounded primes and is completely flat | native_prime_vertex_prefix_geometry | Proved; compiled and audited. |
| All prefixes persist | native_prime_vertex_prefix_monotone | Proved; compiled and audited. |
| Every selected vertex was selected at birth | native_prime_vertex_prefix_mem_birth | Proved; compiled and audited. |
| Exact global-class truncation at every natural height | native_prime_vertex_prefix_mem_iff | Proved; compiled and audited. |
| Every global vertex is prime | native_prime_vertex_class_prime | Proved; compiled and audited. |
| The single computable vertex class is infinite | native_prime_vertex_class_infinite | Proved; compiled and audited. |
| Both square rows separate for all distinct complete pair labels | native_prime_vertex_class_square_compatible | Proved; compiled and audited. |
| Every distinct complete pair-label rate equals3/8 | native_prime_vertex_class_agreement | Proved; compiled and audited. |
| Full computable infinite complete-vertex headline | native_computable_complete_prime_vertex_family | Proved; compiled and audited. |

The candidate owner is Mathlib/NumberTheory/LegendreSymbol/QuadraticSquareDensity.lean. Prime-frequency providers are in Proof/AffinePairs/MarginalLimits.lean, PrimeSquareSieve.lean, PrimeSquarePolynomials.lean, FiniteEventLimits.lean and FiniteEventProbability.lean. The native owners are Assembly/FiniteFieldNativeVertexInsertion.lean, FiniteFieldNativeVertexDensity.lean and FiniteFieldNativeVertexGreedy.lean. Canonical primeEventProbability is an exact noncomputable frequency definition, not an extra arithmetic estimate. All owners compile warning-free; the new closures use only standard Lean foundations. Earlier unchanged closures were not re-audited.

benchmark_status: the fixed finite-extension and full computable infinite complete-vertex theorems are proved.
old_bound: the completed density-one selection kept individual pair labels; it did not supply one prime vertex class retaining all of its positive pairs.
new_bound: every fixed finite flat prime vertex set has relative density1 of valid larger prime extensions; one fixed computable infinite prime vertex class has rate3/8 for every distinct complete pair label.
components: exact square counts with zero values; unit3/4 bound; fixed-modulus unary CRT and exact marginal; all finite rejection overlaps; upper-endpoint recovery; positive square-factor cancellation; deterministic persistence and birth coherence.
actuals: thirty-seven new proof declarations, including five exact normalization interfaces; six computable vertex definitions/instances, one finite rejection predicate and one canonical noncomputable frequency definition. No finite diagnostic replaces a universal estimate.
first_nonpositive_domain: empty and small prefixes and the prime2 are included. Extension density uses fixed P,B before the prime cutoff limit; the global vertex density and effective growth remain unquantified. Each native label stays fixed before the independent field-scale limit.

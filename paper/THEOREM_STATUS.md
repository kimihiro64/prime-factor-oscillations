# Paper theorem and provenance ledger

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

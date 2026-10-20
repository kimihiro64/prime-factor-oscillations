# Prime Factor Oscillations

Formal proofs and research papers on prime-factor densities and a separate
largest-prime-factor dynamical system. The maintained development uses
**Windows Lean 4.34.0** with pinned, cached dependencies.

| Research line | Paper | Formal results |
| --- | --- | --- |
| Prime-factor densities, prime gaps, and RH criteria | [PDF](paper/research-paper.pdf) · [LaTeX](paper/research-paper.tex) | [Theorem ledger](paper/THEOREM_STATUS.md) · [Verification](paper/VERIFICATION.md) |
| Largest-prime-factor dynamics | [PDF](paper/lpf-dynamics.pdf) · [LaTeX](paper/lpf-dynamics.tex) | [Power-saving theorem](PrimeFactorOscillations/Helpers/LPFDensePower.lean) · [Public exports](PrimeFactorOscillations/Assembly/LPFResults.lean) |

## Prime-factor densities

The paper *Prime-factor densities: gap spectra, zeta-zero criteria, and
generalized Robin inequalities* studies how often a prime occurs at a specified
position among the distinct prime factors.

The completed results include:

- **Double-exponential reversals.** Every fixed rank eventually stops rising,
  but the number of separated descent-then-ascent occurrences grows
  double-exponentially with the rank. The general gap-frequency spectrum gives
  the exact double-logarithmic upper growth rate for qualifying local laws,
  including products of distinct affine prime sums.
- **Late ascents and bounded prime gaps.** Recurring short gaps are equivalent
  to an unbounded supply of suitably late ascents, with the stated strict
  coefficient thresholds. Quantitative reversal counts require quantitative
  gap counts; bare infinitude supplies a different conclusion.
- **RH and zero-free criteria.** Precisely centered moving-rank coefficient
  ratios transfer the classical prime-product error with its sign intact.
  Generalized family criteria retain their arithmetic constants, forced-prime
  shifts, and correction terms. Power-saving signed premises yield the stated
  zero-free implications, including the $N^\alpha$ results.
- **Generalized Robin inequalities.** The paper develops the modified-LCM
  comparison and its critical window, distinguishing eventual inequalities
  from unbounded sequences of witnesses.

These are equivalences, transfers, and conditional consequences where indicated.
They do not prove RH, the twin prime conjecture, or a new bounded prime-gap
record. The paper states the exact hypotheses and quantifiers.

The completed research library also retains the signed detector and packet
calculus, Euler-continuation results, and RH-conditional wave second moments
and multiplicity-defect budgets. Its [maintained-owner inventory](paper/completed-research-inventory.json)
records the source hashes and verification status. The paper gives ordinary
proofs of prime-profile rigidity and sharp cubic camouflage, distinguishing
these from their formalized components. The certified unconditional zero-free
boundary remains **7/8**.

## Largest-prime-factor dynamics

Starting with a finite prime set, retain it and repeatedly adjoin the largest
prime factor of $2(p+q)-1$ for every available pair. **Diagonals are allowed
at every generation.**

Our motivating conjectures are **complete generation**: the seed $\{2\}$
generates every prime, and each odd-prime singleton $\{p\}$ generates every
odd prime. Both remain unproved. We also propose affine and higher-arity
extensions using $a(p_1+\cdots+p_m)+b$, with arithmetic restrictions and
non-degeneracy conditions still to be classified.

The separate paper *Density amplification in a largest-prime-factor dynamical
system* proves a robust propagation theorem:

> There are a positive entry fraction and a sufficiently large entry scale
> such that any finite seed missing at most that fraction of the prime prefix
> generates all but $O(X^{79/80})$ primes up to $X$.

The formal theorem controls the actual finite generations at expanding cutoffs
and then the permanently missing primes at every sufficiently large cutoff.
Its proof combines a positive prime-pair supply, exact degree normalization,
and a joint overlap bound uniform over the missing input set. Thus qualifying
finite seeds generate a relative-density-one set of primes.

The finite certificate also proves that generation 9 from $\{2\}$ contains
every prime at most 10,000. **Dense entry, infinitude, and all-prime reachability
from $\{2\}$ remain unproved.** The paper separates this finite bridge from the
completed propagation theorem and explains the available birth-layer
cancellation and energy bounds. Even dense entry would leave the separate
task of proving that every exceptional prime is eventually reached.

## Build and verification

Follow [BUILD.md](BUILD.md) and [dependency reuse](DEPENDENCY_REUSE.md).
Use the pinned Windows Lean environment for research and public proofs;
external dependencies are reused from their released caches.

- `python scripts/build_project.py` checks owned modules.
- `python scripts/proof_audit.py` checks advertised declarations and their axioms.
- `python scripts/check.py --profile research` runs repository checks and the build.

Resolve Python in your environment before running these commands. The new LPF
paper's reproducible PDF build, checks, and focused theorem audit are described
in [its verification record](paper/LPF_VERIFICATION.md).
No CI is configured.

[Contribution guide](CONTRIBUTING.md) · [Research plan](RESEARCH_PLAN.md) ·
[Dependency pins](formalization.yaml) · [Licensing](LICENSING.md)

Registry submissions use the [Palomar submission portal](https://submit.palomar-registry.org/).

Exploratory source-dependent calculations, including the
[6 October QRH refinement note](paper/QRH_REFINEMENT.md), are kept separate from
the maintained theorem claims. Lean code is under Apache 2.0; paper text is
under the license specified in [LICENSING.md](LICENSING.md).

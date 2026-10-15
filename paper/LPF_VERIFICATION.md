# LPF dynamics: theorem and paper verification

The separate paper is [Density amplification in a largest-prime-factor
dynamical system](lpf-dynamics.pdf) ([source](lpf-dynamics.tex)).
This record covers the 15 October 2026 integration.

## Mathematical scope

The new result retains a finite dense-entry hypothesis. There exist an entry
fraction and an eventual entry threshold, uniform over finite seeds, such that
a qualifying seed has at most $O_{S,M}(X^{79/80})$ permanently missing primes
below every sufficiently large cutoff $X$.

The proof first bounds the actual generations at the cutoffs
$m_{j+1}=\lfloor5m_j/4\rfloor$. A first-crossing argument then treats arbitrary
cutoffs. The entry and one-step density constants are chosen independently;
vanishing relative defect justifies the eventual use of the latter.

The complete one-step estimate is

$$
E_{j+1}\le\frac{17}{16}E_j+C m_j^{79/80}+D\log m_j.
$$

The forcing scale grows by at least $13/12$, leaving a difference of $1/48$
from $17/16$. The proof uses $K\ge48(C+2D)$ after the eventual starting stage.
It does not discard a residual $m_j/\log^4m_j$ term from this recurrence.

**Not proved:** dense entry, infinitude, unbounded medians, or all-prime
reachability for the particular seed $\{2\}$. The finite certificate up to
10,000 at generation 9 and the separate explicit $7/6$ preservation theorem
are not substituted for entry in the new $5/4$ theorem.

## Maintained proofs

The owner is [LPFDensePower.lean](../PrimeFactorOscillations/Helpers/LPFDensePower.lean).
The principal declarations are:

- `fullOrbit_defect_power_bound_of_density_zero`
- `exists_fullOrbit_dense_power_bound`
- `fullOrbit_closure_power_bound_of_stage`
- `exists_fullOrbit_dense_closure_power_bound`

These are in namespace `PrimeFactorOscillations.LPF`. The public facade
[LPFResults.lean](../PrimeFactorOscillations/Assembly/LPFResults.lean) exports
the owner, and [Solution.lean](../Solution.lean) consumes the closure result as
`PrimeFactorOscillations.publicLPFDenseClosurePowerBound`.

The initial integration build checked **724 owned modules**, compiling four
changed consumers and reusing 720 unchanged modules. After a statement-preserving
consumer layout correction, the fresh build checked the same 724 modules,
compiling only `Solution.lean` and reusing 723 modules. Both rebuilt **zero
external dependencies**. The full declaration audit checked **2,089 theorem closures**,
including all five declarations above. Their axiom sets are exactly
`Classical.choice`, `Quot.sound`, and `propext`; no target-encoding axiom or
`sorryAx` occurs. The two existing comparator statements also retained
identical compiled types.

The machine-readable [verification receipt](verification/lpf-power-audit.json)
records source hashes, compiler identity, artifact-manifest identity, and the
selected declarations' axiom sets. The [focused audit log](verification/lpf-power-axioms.log)
contains the actual elaborated statements and axiom output.

## Reproduction

Use Windows and the project's pinned Lean **4.34.0** environment. Follow
[BUILD.md](../BUILD.md) to restore the released artifacts. Do not build the
external Erdos 690 dependency.

From the repository root, using a resolved Python executable:

```text
python scripts/build_project.py
python scripts/proof_audit.py
python scripts/check.py --profile research
```

To rebuild the PDF with an installed MiKTeX `pdflatex`, run the
[paper build script](build_lpf_paper.ps1) in PowerShell:

```powershell
& .\paper\build_lpf_paper.ps1
```

An explicit absolute executable may be supplied as `-PdfLatex`. The script
runs three passes, rejects overfull boxes and unresolved references, retains
intermediate logs under `.research/audits/lpf-paper`, and updates the PDF and
[whitespace-normalized LaTeX log](verification/lpf-paper-build.log). The built-in document
compiler also checked the saved source successfully.

The PDF was rendered and visually reviewed, including its equations,
declaration table, and references. Ordinary corollaries on relative density,
appearance time, and medians are proved in the paper; they are not mislabeled
as separately compiled Lean declarations.

The final staged repository checks passed the source, boundary, dependency,
architecture, and metadata gates, including 17 Ruby tests with 86 assertions.
Python formatting, lint, and strict type checks passed for all 31 checked files;
all **95 Python tests** passed. The [repository-check log](verification/lpf-repository-checks.log)
retains the final verification output. The existing theorem catalogs use tuple
unpacking to satisfy the linter; their declaration order and contents are retained.

## Sources and novelty

The paper cites the closest prime-magma work of Caragiu--Vicol and the distinct
recurrence of Back--Caragiu, additive results of Ramare--Ruzsa,
Green--Tao, and Alsetri--Shao, and the OpenAI 2026 analytic source. The
comparison distinguishes their exact operations and hypotheses. The potential
new contribution is robust LPF density amplification and its quantitative
iteration, not a new Goldbach or zero-free estimate. The draft makes no claim
that the literature comparison proves priority.

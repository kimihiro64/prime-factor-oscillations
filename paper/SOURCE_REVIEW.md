# Primary-source review for the revised paper

Checked 28 September 2026. This is a source-alignment record for the historical
and analytic attributions in the paper, not an independent reproof of every
cited article.

| Source and checked version | Location inspected | What the paper uses |
|---|---|---|
| Paul Erdős, *Some unconventional problems in number theory*, Astérisque 61 (1979), 73–82 | [Original scan](https://www.numdam.org/item/AST_1979__61__73_0.pdf), pp. 74–75 | The prime-factor unimodality question and the distinct typical-factor double-exponential scale. The historical claim about the mode is not repeated as current mathematics. |
| Paul Erdős and Gérald Tenenbaum, *Sur les densités de certaines suites d'entiers*, Proc. London Math. Soc. (3) 59 (1989), 417–438 | [Original scan](https://users.renyi.hu/~p_erdos/1989-36.pdf), Corollary 5, equation (1.20), and the preceding correction; [journal identity](https://academic.oup.com/plms/article-abstract/s3-59/3/417/1628107) | A maximizing prime has log p asymptotic to k/log k. The article explicitly corrects the earlier log p asymptotic to k assertion. |
| Stijn Cambie, *Resolution of Erdős' problems about unimodularity* | [arXiv:2501.10333v1](https://arxiv.org/html/2501.10333v1), Theorems 3 and 5 and §3; [journal version](https://www.sciencedirect.com/science/article/pii/S0022314X25002483), J. Number Theory 280 (2026), 271–277 | Ranks 1–3 are unimodal; ranks 4–20 have counterexamples. The many-extrema theorem concerns the separate divisor-interval density of Problem 692. The arXiv history listed v1 only at review time; journal metadata was checked separately. |
| Shouqiao Wang and Davide Crapis, *A Complete Answer to Erdős Problem 690* | [arXiv:2605.08542v1](https://arxiv.org/html/2605.08542v1), Theorem 1.1, Corollary 1.2, Lemmas 3.1–3.2; [version history](https://arxiv.org/abs/2605.08542) | Non-unimodality for every rank at least four and the ordinary first-difference/symmetric-ratio framework. The current listed version was v1, 8 May 2026. This historical account does not promote the dependency repository's conditional full-classification theorem. |
| James Maynard, *Dense clusters of primes in subsets* | [arXiv:1405.2593v2](https://arxiv.org/abs/1405.2593), current listed version dated 16 December 2014; [publisher](https://www.cambridge.org/core/journals/compositio-mathematica/article/dense-clusters-of-primes-in-subsets/B49458BB98CB2D9C93ACF3BB09B4B08D), Compositio Math. 152 (2016), 1517–1554 | Mathematical background for quantitative clusters. The exact width-600, positive-power input is taken from the separately pinned formal extraction identified below; it is not advertised as a verbatim theorem of this article. |

The manuscript's fixed analytic input is the eventual lower bound of X^(1/3)
integer starts in [X,2X] with two primes in their width-600 windows.
Its maintained name is PrimeGaps.eventually_many_prime_windows_600; its
source/artifact provenance is in [DEPENDENCY_REUSE.md](../DEPENDENCY_REUSE.md)
and its actual closure is covered by the recorded theorem audit.
A smaller historical or current gap constant is unnecessary for the stated
positive-constant theorem. The general transfers keep H symbolic.

The source review preserves three different quantifiers: typical factors of
integers, reversals at increasing rank, and recurrence of bounded prime gaps.
It does not infer infinite reversals at a fixed rank, a new prime-gap result,
or a moving-cutoff distribution theorem.

The analytic inputs to the new exposition remain the existing proof inputs.
The editorial expansion adds no mathematical assumption and incorporates no
current exploratory correlation estimate.


## RH and coefficient-transfer review - 4 October 2026

The revised paper distinguishes two potentially new contributions: the exact
gap-frequency spectrum and the uniform transfer of the Nicolas error to the
actual moving-rank coefficient ratio. Failure to find a prior identical
statement is not a certificate of novelty.

| Source and version inspected | Exact role and attribution |
|---|---|
| Jean-Louis Nicolas, *Petites valeurs de la fonction d'Euler*, J. Number Theory 17 (1983), 375-388, [publisher](https://doi.org/10.1016/0022-314X(83)90055-0) | The primorial RH criterion and false-RH oscillations are prior work. The detailed oscillation statement is also recorded in the accessible 2012 source below; the author's 1983 PDF was inaccessible during this review. |
| Nicolas, *Small values of the Euler function and the Riemann hypothesis*, [arXiv:1202.0729v2](https://arxiv.org/pdf/1202.0729v2), Acta Arith. 155 (2012), 311-321 | Definitions (1.9), (1.15)-(1.19), Lemma 2.5 and Proposition 2.1. The zero wave, prime-square constant two, eventual negative sign under RH and logarithmic error scale are classical. The clock displacement is a change of variables in that estimate. |
| Emmanuel Kowalski and Ashkan Nikeghbali, *Mod-Poisson convergence in probability and number theory*, [arXiv:0905.0318v2](https://arxiv.org/abs/0905.0318v2), [author PDF](https://people.math.ethz.ch/~kowalski/mod-poisson.pdf), section 4 | The normalized Euler product and independent prime-divisibility model are established. Their arithmetic and independent models must not be confused: the global-integer model has an additional Gamma factor. |
| Valentin Féray, Pierre-Loïc Méliot and Ashkan Nikeghbali, *Mod-phi convergence, I: Normality zones and precise deviations*, [arXiv:1304.2934v4](https://arxiv.org/pdf/1304.2934v4), sections 3 and 7 | General precise deviation and coefficient-asymptotic background. The potentially new comparison here retains the full reference and an error smaller than the RH signal; generic saddle-point or mod-Poisson asymptotics are not claimed as new. |
| Jeffrey P. S. Lay, *Sign changes in Mertens' first and second theorems*, [arXiv:1505.03589v1](https://arxiv.org/pdf/1505.03589), Theorems 1 and 3 | Classical Landau singularity principle and the distinction between ordinary Mertens errors and the theta-centered Nicolas error. Replacing theta by x does not preserve the RH sign criterion. |
| Jeffrey C. Lagarias, *An elementary problem equivalent to the Riemann hypothesis*, [arXiv:math/0008177v2](https://arxiv.org/pdf/math/0008177v2), Theorem 1.1 and equation (1.2) | Established Lagarias and Robin equivalences. Their combination with the coefficient criterion is a logical consequence, not a new CA optimization estimate. |
| P. X. Gallagher, *On the distribution of primes in short intervals*, Mathematika 23 (1976), 4-9, [primary PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/DCE557AC8750333E68426FCEEC11858C/S0025579300016442a.pdf/on_the_distribution_of_primes_in_short_intervals.pdf) | Formula (1), specialized to twins, is the conditional global count used here. Theorem 1's stronger uniform all-tuple assumption is not used to infer proximity to the deterministic cutoff. |

The current arXiv records still list Wang-Crapis v1 (8 May 2026) and
Cambie v1 (17 January 2025). Their actual theorem statements were inspected,
not inferred from the abstracts. Cambie's journal full text returned an access
error, so no assertion is made that its text was compared line-by-line.

The same-date search found no identical reversal-spectrum identity or
theta-centered moving-rank RH criterion in the inspected primary sources.
A broader expert priority review remains necessary. The paper's RH spectral
input is credited to Nicolas; the coefficient transfer and its stated
applications are identified as potentially new.

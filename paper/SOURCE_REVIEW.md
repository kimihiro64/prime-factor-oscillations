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

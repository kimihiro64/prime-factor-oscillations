# A one-coefficient FI-family change that permits a gap-two rank test

Date: 2026-09-29.

## Status and scope

Replace a^2+b^4 by a^2+2b^4 and retain odd squarefree outputs. This note establishes the exact modular squarefree local factors and an exact gap-two calibration for the associated independent local-law model. It supplies a reproducible finite certificate valid at all subsequent factor-prime endpoints.

It does NOT prove an unbounded supply of ascents, a positive endpoint contrast, or an infinite twin-prime theorem. The arithmetic realization of the entire odd-squarefree ensemble and the precise rank-weighted Type I/Type II bounds require matching the generalized quadratic-form estimates and a square-divisor-tail argument. The raw FI estimates for coefficient 1 are not silently imported for coefficient 2. The exact newer Work-thread sieve-to-ascent theorem was not available in this conversation.

## 1. Why coefficient 2 removes the congruence obstruction

For an odd prime p, p divides a^2+2b^4 with b not divisible by p exactly when -2 is a square modulo p. By the supplementary laws of quadratic reciprocity this occurs for p = 1 or 3 modulo 8.

If p = 5 or 7 modulo 8 divides the output, both a and b must be divisible by p, hence p^2 divides the output. Such a factor is excluded by squarefreeness. Oddness excludes 2. The allowed factor set is therefore

    P = {odd primes p : p mod 8 is 1 or 3}.

It is not a single residue class. It permits p,p+2 (residues 1,3 modulo 8). It does NOT permit a separation of 4: adding 4 to either allowed residue gives a forbidden residue. Thus any positive gap in this set is either 2 or at least 6.

For comparison, coefficient 1 restricts odd squarefree factors to 1 modulo 4, prohibiting gap 2 identically. Retuning a rank cannot remove that obstruction.

## 2. Exact local factors

Let rho_j(p) count pairs (a,b) modulo p^j with a^2+2b^4 divisible by p^j. For an allowed prime,

    rho_1(p) = 2p-1,
    rho_2(p) = 3p^2-2p.

The second identity follows by splitting b modulo p^2 into p-divisible b (p choices, each with p admissible a) and unit b (p^2-p choices, each with two admissible a).

For a forbidden odd prime,

    rho_1(p) = 1,
    rho_2(p) = p^2.

Writing g1=rho_1/p^2 and g2=rho_2/p^4, the p-adic conditional probability given p^2 does not divide the output is

    eta_p = (g1-g2)/(1-g2).

Consequently

    eta_p = 2/(p+2),   1/eta_p = p/2+1,   eta_p/(1-eta_p) = 2/p

on P, and eta_p=0 at the other primes after oddness. This is the SAME formula on the NEW allowed set. Chinese remaindering proves finite local independence when finitely many local squarefree conditions are imposed. Extending this to all squarefree conditions in a natural expanding input region requires a square-divisor-tail estimate; modular algebra alone is not that uniform estimate.

The verifier independently checks rho_1, rho_2, the conditional probability, and the odds at all 45 odd primes through 199, using exact residue histograms.

## 3. The rank law and exact first difference

For p in P let

    E_j(p) = e_j((2/ell) : ell<p, ell in P).

Define the density of the associated independent local-law model by

    D_k(p) = [2/(p+2)] * product_{ell<p,ell in P}[ell/(ell+2)] * E_{k-1}(p).

For consecutive p<q in P, g=q-p, and r=k-1 with E_r(p)>0, put R=E_{r-1}(p)/E_r(p). Directly expanding the additional factor gives

    D_k(q)/D_k(p) = (p+2R)/(q+2),
    D_k(q)>D_k(p)  iff  R>g/2+1.

These are exact identities. The two coordinates use the same k.

## 4. A two-tilt twin-prime calibration

Put

    M_t(p) = sum_{ell<p,ell in P} 2t/(ell+2t),
    k_twin(p) = 1 + floor(M_4(p)).

The tilted elementary-symmetric coefficients t^j E_j are proportional to a Poisson-binomial distribution with Bernoulli probabilities 2t/(ell+2t). Darroch's mean-mode theorem says its mode lies at floor(M_t) or ceil(M_t).

Let r=floor(M_4). Unimodality gives R_r <=4. If M_4-M_2>2, then M_2<r-1, so the mass at r is strictly below that at r-1 under tilt 2; hence R_r>2.

The sufficient condition is a positive partial sum:

    M_4(p)-M_2(p)
       = sum_{ell<p,ell in P} 4ell/((ell+8)(ell+4)) >2.

It follows that

    2 < R_{k_twin(p)-1}(p) <=4.

A gap 2 has first-difference threshold 2. Every other possible positive gap in P is at least 6 and has threshold at least 4. Therefore

    D_{k_twin(p)}(q)>D_{k_twin(p)}(p)  iff  q-p=2.

Unlike a test on all odd primes, there is no intervening gap-4 case to separate. The coefficient-ratio window still has width 2.

## 5. Exact certificate extending to every later endpoint

Sum over the 239 allowed primes ell<=3433. At integer scale

    Q = 79228162514264337593543950336 = 2^96,

round every summand down. The sum of lower numerators is

    L = 158488524505168240256580436918.

The true sum lies between L/Q and (L+239)/Q. In particular

    L-2Q = 32199476639565069492536246 >0.

The decimal value is about 2.0004064145326326, used only for display. Every later term is positive. The exact twin-gap calibration therefore holds for every p in P with p>3433, equivalently p>=3449.

Examples, with the coefficient-ratio signs also checked independently using exact fractions:

| p | q (next in P) | gap | k | R, decimal display | ascent |
|---:|---:|---:|---:|---:|:---|
|3449|3457|8|5|3.0909673932|no|
|3691|3697|6|5|3.0677119180|no|
|3929|3931|2|5|3.0463682642|yes|
|4001|4003|2|5|3.0419855189|yes|
|4049|4051|2|5|3.0362748437|yes|

These examples are checks, not an unbounded ascent supply. The endpoints in the test are factor primes, not necessarily prime values of the sparse polynomial itself.

## 6. Existing analytic input and what must still be transferred

Xiao's Theorem 1.1 treats prime values of f(a,b^2) for primitive irreducible binary quadratic forms without the stated local obstruction. The choice f(x,y)=x^2+2y^2 meets the hypotheses. Thus this is already a proven prime-producing sparse family, not a new unproved prime-value conjecture. Odd prime outputs automatically survive the odd-squarefree restriction.

Source: S. Y. Xiao, *Prime values of f(a,b^2) and f(a,p^2), f quadratic*, Algebra & Number Theory 18 (2024), 1619-1679; DOI 10.2140/ant.2024.18.1619. The theorem was inspected in the author preprint https://arxiv.org/pdf/2111.04136, printed page 2; publication details were checked against the author's publication list.

The preprint's comparison-sieve Type II proposition controls a difference of carefully normalized sequences, with its own rough-support and size conditions. It is not automatically the old raw FI rough-Mobius estimate for arbitrary outer factors. Its Type I section must also be matched to the chosen raw/weighted and primitive/squarefree sequence. Do not equate a theorem about prime outputs with the exact rank-weighted estimate needed to force ascents.

A structural reason this modification is attractive is the norm identity

    N(x+y sqrt(-2))=x^2+2y^2,
    (x+y sqrt(-2))(u+v sqrt(-2))
       = (xu-2yv)+(xv+yu)sqrt(-2).

The second coordinate remains bilinear. The ring Z[sqrt(-2)] is norm-Euclidean: round each coordinate of a quotient to the nearest integer; the remainder's relative norm is at most 1/4+2/4=3/4<1. Thus the change does not introduce a nontrivial ideal-class obstruction. It does change the character sums and analytic estimates, which is why the generalized theorem matters.

The earlier rank coefficient identities, including lambda=mu*b and the divisor bound W<=tau, are combinatorial and continue to hold after replacing the allowed prime set. They do not by themselves give the required analytic cancellation or signed endpoint positivity.

## 7. Final target

For each p in P with p>=3449, let q be its next element and use k=k_twin(p). The desired supply is

    D_k(q)-D_k(p)>0

at arbitrarily large p, proved from the modified family's sieve estimates rather than assumed from the prime gaps. By the exact calibration, this would produce infinitely many ordinary twin-prime gaps.

It would actually supply twins with lower endpoint p=1 modulo 8. Since p>3 and p+2 are both prime, p=2 modulo 3, so p=17 modulo 24. This is a sufficient restricted twin-prime conclusion, not an equivalence to the unrestricted twin-prime conjecture.

No positive endpoint-supply bound is proved in this package. The coefficient change removes the previous modulus obstruction and keeps the local-law algebra; it does not close the endpoint sign argument.

## 8. Reproduce

    python verify.py --output results.json

The program uses only the Python standard library. Exact modular counts, exact rational intervals, and exact rational coefficient comparisons are used for all proof-critical finite comparisons. Decimal fields in results.json are display values only.

Additional primary source for the mean-mode input: A. Gnedin, *Cross Modality of the Extended Binomial Sums*, Section 5.1, https://arxiv.org/html/2408.06477v1 .

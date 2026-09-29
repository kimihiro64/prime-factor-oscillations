# Friedlander–Iwaniec rank-sieve transfer: odd squarefree values

**Date:** 2026-09-29.  
**Status:** Proof derivations from explicitly identified classical inputs, with reproducible exact finite checks. No Lean build, independent proof audit, new bounded-prime-gap theorem, or certified positive ascent-supply margin is claimed. Novelty has not been assessed. This develops the FI route itself; it does not change the previous 39-variable variational score.

## 1. Summary of the established reductions

Keep the original polynomial rather than adding squares or a constant. Weight each positive output by all of its integral representations, then retain only odd squarefree outputs:

\[
a_n=\#\{(a,b)\in\mathbb Z^2:a^2+b^4=n\},\qquad
 a_n^*=a_n\mu^2(n)\mathbf1_{2\nmid n}.
\]

The deductions below establish:

1. The remaining factor coordinates are exactly the primes congruent to 1 modulo 4. Their independent finite local law is
   \[
   g_*(p)=\frac2{p+2},\quad g_*^{-1}(p)=\frac p2+1,\quad
   \frac{g_*(p)}{1-g_*(p)}=\frac2p.
   \]
2. A divisor-weighted Type-I estimate survives squarefree conditioning. For fixed \(B\ge0\), \(\epsilon>0\), and \(1\le D\le X^{3/4}\),
   \[
   \sum_{\substack{d\le D\\d\text{ odd squarefree}}}\tau(d)^B
   |A_d^*(X)-g_*(d)A^*(X)|
   \ll_{B,\epsilon}X^\epsilon
   \left(X^{5/8}D^{1/6}+X^{17/24}\right).
   \tag{1.1}
   \]
   In particular, for \(0<\delta<1/4\), the range \(D=X^{3/4-\delta}\) has error \(O(X^{3/4-\delta/6+\epsilon})\).
3. The rank-dependent signed divisor coefficients are exactly a convolution with the ordinary Möbius function. After absorbing the small primes into the outer coefficient, the **entire** rank count has a rough-Möbius bilinear representation whose outer coefficients are nonnegative and bounded by \(\tau\), independently of rank and factor cutoff.
4. FI's original Proposition 4.1 consequently gives arbitrary fixed logarithmic savings for every balanced block of this representation, uniformly in the rank. No assertion about arbitrary new inner coefficients is needed.
5. An integer-arithmetic certificate proves a sharp rank calibration valid at every split-prime endpoint \(p\ge20,000,000\). At the prescribed rank, an ascent occurs **if and only if** the next split prime is at most 184 away. This is a transfer/calibration theorem, not an assertion that such ascents occur infinitely often.

The unresolved step is a positive one-sided bound on the **small- and large-rough-cofactor endpoint contrast**, at arbitrarily large factor-prime endpoints. The former nonrough remainder can be absorbed exactly; it need not be left as another unknown term.

## 2. Imported analytic inputs and source boundary

### S1: FI, *The polynomial X^2+Y^4 captures its primes*

Source: https://arxiv.org/pdf/math/9811185 . Relevant printed pages 953, 961–964; Propositions 3.5 and 4.1. This package does not redistribute the paper.

Let
\[
 A(X)=\sum_{n\le X}a_n,\qquad A_d(X)=\sum_{\substack{n\le X\\d\mid n}}a_n.
\]
FI prove \(A(X)\asymp X^{3/4}\), and, for cube-free moduli,
\[
 \sum_{d\le D}^{\mathrm{cubefree}}|A_d(X)-g(d)A(X)|
 \ll_\epsilon D^{1/4}X^{9/16+\epsilon}.
 \tag{2.1}
\]
For odd primes, their local factors specialize to
\[
\begin{array}{c|cc}
 &g(p)&g(p^2)\\\hline
p\equiv1\ (4)&(2p-1)/p^2&(3p-2)/p^3\\
p\equiv3\ (4)&1/p^2&1/p^2.
\end{array}
\tag{2.2}
\]
Also \(g(2)=1/2\), and \(g(4)=1/4\).

For the bilinear estimate write \(\Pi(z)=\prod_{\ell\le z}\ell\). With the paper's coefficient parameter \(C=1\), its coefficient \(\beta(v,C)=\mu(v)\sum_{c\mid v,c\le C}\mu(c)\) is exactly \(\mu(v)\). Proposition 4.1 gives arbitrary fixed logarithmic savings for
\[
 \sum_u\left|\sum_{\substack{N<v\le2N\\uv\le X\\(v,u\Pi(z))=1}}
 \mu(v)a_{uv}\right|,
 \tag{2.3}
\]
when
\[
 X^{1/4+\eta}<N<X^{1/2}(\log X)^{-B_0},
 \qquad
 (\log\log X)^2\le\log z\le\frac{\log X}{(\log\log X)^2}.
 \tag{2.4}
\]
Here \(\eta>0\) is fixed, and \(B_0\), constants, and the large-X threshold depend on the requested saving and \(\eta\). These conditions are retained, not silently replaced by an unrestricted bilinear estimate.

We also use the divisor-moment estimate obtained on printed page 964:
\[
 \sum_{n\le X}\mu^2(n)\tau_5(n)a_n
 \ll A(X)(\log X)^{128},
 \tag{2.5}
\]
where \(\tau_5(n)=5^{\omega(n)}\) on squarefree integers. The large exponent is harmless for the fixed-logarithmic-saving arguments below.

FI's prime-value asymptotic is
\[
 \sum_{p\le X}a_p\log p\sim\frac4\pi A(X).
 \tag{2.6}
\]
Every odd prime output is already odd and squarefree. Therefore the left side remains unchanged up to a constant when \(a_p\) is replaced by \(a_p^*\). We are not trying to prove a prime theorem for an altered polynomial.

### S2: Mean-mode theorem for Poisson-binomial distributions

Alexander Gnedin, *Cross Modality of the Extended Binomial Sums*, https://arxiv.org/html/2408.06477v1 , Section 5.1, states and proves the relevant form of Darroch's rule. A finite sum of independent Bernoulli variables has its mode at the floor or ceiling of its mean (at the mean if the mean is integral), with the usual unimodality/log-concavity properties.

### Project context

The first-difference rank-density algebra is compatible with the project's framework, but an infinite deletion of prime coordinates is not the same as its finite-exception hypothesis. We therefore derive the split-prime ascent-to-gap statement explicitly in Section 7 instead of claiming an already compiled all-prime theorem.

Project: https://github.com/kimihiro64/prime-factor-oscillations .
The newer separate Work-thread sieve-to-ascent mechanism is not reconstructed here; its exact statement was not available in this conversation. Its absence from the repository is not evidence that the work does not exist.

## 3. Squarefree conditioning and the exact law

An inert prime \(p\equiv3\pmod4\) dividing \(a^2+b^4\) must divide both \(a\) and \(b\), and hence its square divides the output. Therefore an odd squarefree output has only split prime factors.

At a split prime, conditioning on \(p^2\nmid n\) gives
\[
 \frac{g(p)-g(p^2)}{1-g(p^2)}
 =\frac{2p(p-1)^2}{p(p-1)^2(p+2)}=\frac2{p+2}.
 \tag{3.1}
\]
At inert primes this conditional probability is zero. At 2, conditioning on oddness makes it zero.

Define
\[
 \mathfrak C_* =\frac12\prod_{p>2}(1-g(p^2)).
 \tag{3.2}
\]
The product is positive because \(g(p^2)\ll p^{-2}\). Section 4 justifies passing from finitely many squarefree conditions to all of them and proves
\[
 A^*(X)=\mathfrak C_*A(X)+O_\epsilon(X^{17/24+\epsilon}).
 \tag{3.3}
\]
It also justifies the fixed finite-pattern limits, including their independence. In particular, \(g_*\) is multiplicative on squarefree moduli with the prime factors in (3.1).

The partial product in (3.2) through 10,000,000 is approximately 0.3684480670. This floating-point value is not an interval certificate for the full product; the elementary omitted-tail estimate is \(O(1/10,000,000)\). About 36.8 percent of the representation weight is retained asymptotically.

The retained prime-value theorem can also be written
\[
 \sum_{p\le X}a_p^*\log p
 \sim\frac4{\pi\mathfrak C_*}A^*(X).
 \tag{3.4}
\]
This positive prime-value result remains available, but alone is not a prime-gap theorem.

## 4. Proof of the squarefree Type-I transfer

All estimates in this section may absorb fixed powers of divisor functions into \(X^\epsilon\), shrinking intermediate epsilons as needed. The constants are not numerically evaluated.

### 4.1 A square-divisor tail bound

Pointwise,
\[
 a_n\le r_2(n)\le4\tau(n)\ll_\epsilon n^\epsilon.
\]
For squarefree \(c\), \(g(c^2)\ll_\epsilon c^{-2+\epsilon}\). For
\(1\le Z\le Y=X^{7/24}\), split
\[
 T(Z)=\sum_{\substack{c>Z\\c\ \mathrm{squarefree}}}A_{c^2}(X)
\]
at \(Y\). Formula (2.1), applied to the cube-free moduli \(c^2\le Y^2\), gives
\[
 \sum_{Z<c\le Y} A_{c^2}(X)
 \ll A(X)Z^{-1+\epsilon}+Y^{1/2}X^{9/16+\epsilon}.
\]
For \(c>Y\), the pointwise representation bound gives
\[
 \sum_{c>Y}A_{c^2}(X)
 \ll_\epsilon X^\epsilon\sum_{c>Y}\lfloor X/c^2\rfloor
 \ll_\epsilon X^{1+\epsilon}/Y.
\]
Both error terms equal \(O(X^{17/24+\epsilon})\). Thus
\[
 T(Z)\ll_\epsilon A(X)Z^{-1+\epsilon}+X^{17/24+\epsilon}.
 \tag{4.1}
\]
The same proof tolerates fixed divisor weights, at the cost of adjusting epsilon.

### 4.2 Truncating the squarefree indicator

For odd squarefree \(d\), the exact expansion is
\[
 A_d^*(X)=\sum_{c\text{ odd}}\mu(c)
 \left(A_{[d,c^2]}(X)-A_{[2d,c^2]}(X)\right).
 \tag{4.2}
\]
The notation \([a,b]\) means least common multiple. Truncate at \(c\le Z\).
Summing the absolute discarded part over \(d\le D\) with weight \(\tau(d)^B\) costs at most
\[
 X^\epsilon T(Z).
\]
Indeed, for a given output \(n\), the extra divisor multiplicity is bounded by a fixed power of \(\tau(n)\).

Every retained modulus in (4.2) is cube-free and at most \(2DZ^2\). The number of representations of such a modulus by \((d,c)\), with the divisor weight included, is bounded by a fixed divisor power. Hence (2.1) gives retained remainder
\[
 \ll_{B,\epsilon}D^{1/4}Z^{1/2}X^{9/16+\epsilon}.
 \tag{4.3}
\]
The infinite main term factors exactly as
\[
 \sum_{c\text{ odd}}\mu(c)
 \left(g([d,c^2])-g([2d,c^2])\right)
 =\mathfrak C_*g_*(d).
 \tag{4.4}
\]
Its truncated tail is also bounded by \(A(X)Z^{-1+\epsilon}\) after summing over \(d\). For clarity, one uses
\[
 \sum_{d\le D}^{\mathrm{sf,odd}}\tau(d)^B g([d,c^2])
 \ll_B g(c^2)K_B^{\omega(c)}(\log(2D))^{C_B},
\]
and then sums \(c>Z\). This prevents an unjustified factor of \(D\) in the tail estimate.

It follows that the weighted error relative to \(\mathfrak C_*A(X)g_*(d)\) is
\[
 \ll X^\epsilon\left(D^{1/4}Z^{1/2}X^{9/16}
                 +X^{3/4}/Z+X^{17/24}\right).
 \tag{4.5}
\]
Choose
\[
 Z=X^{1/8}D^{-1/6}
\]
(up to an integer rounding and harmless constant factors). For \(1\le D\le X^{3/4}\), this is in \([1,X^{1/8}]\), within the range of (4.1). The first two terms balance at \(X^{5/8}D^{1/6}\).

Separately, (4.2) with \(d=1\), truncated at \(Y=X^{7/24}\), gives (3.3). Replacing \(\mathfrak C_*A\) by \(A^*\) in the general main term costs at most
\(X^{17/24+\epsilon}\sum_{d\le D}\tau(d)^Bg_*(d)\), whose extra factor is polylogarithmic. This proves (1.1).

**Useful uniformity:** the proof constants depend on fixed divisor-power exponents, not on a rank parameter. Since
\(\binom{\omega(d)}r\le2^{\omega(d)}=\tau(d)\) for squarefree \(d\), growing rank causes no new loss in this estimate.

## 5. Exact conversion of rank coefficients to FI coefficients

Fix a split prime \(p\) and let
\[
 \mathcal S_p=\{\ell<p:\ell\text{ prime},\ \ell\equiv1\pmod4\}.
\]
For a set of primes \(\mathcal S\), let \(\omega_{\mathcal S}(n)\) count the distinct prime factors of \(n\) belonging to \(\mathcal S\). Put
\[
 b_{r,\mathcal S}(n)=\mathbf1_{\omega_{\mathcal S}(n)=r}.
\]
Define the supported squarefree coefficient
\[
 \lambda_{r,\mathcal S}(d)=
 \begin{cases}
 (-1)^{\omega(d)-r}\binom{\omega(d)}r,
 &d\text{ squarefree and all its primes in }\mathcal S,\\
 0,&\text{otherwise}.
 \end{cases}
 \tag{5.1}
\]
A binomial coefficient with an out-of-range lower index is zero. Then
\[
 \boxed{\lambda_{r,\mathcal S}=\mu*b_{r,\mathcal S}.}
 \tag{5.2}
\]
Here \(*\) is Dirichlet convolution, not pointwise multiplication.

Proof: form the generating identity
\[
 \sum_{e\mid n}\mu(e)z^{\omega_{\mathcal S}(n/e)}.
\]
Its prime-power factors vanish at primes outside \(\mathcal S\) and at exponents at least 2; at a prime in \(\mathcal S\) to exponent 1 the factor is \(z-1\). Extract the coefficient of \(z^r\).

Define the exact finite rank count
\[
 C_{r,p}(X)=\sum_{n\le X}a_n^*\mathbf1_{p\mid n}
                       \mathbf1_{\omega_{\mathcal S_p}(n)=r}.
 \tag{5.3}
\]
This counts outputs where \(p\) is the \((r+1)\)-st distinct prime factor. Inclusion–exclusion gives
\[
 C_{r,p}(X)=\sum_d\lambda_{r,\mathcal S_p}(d)A_{pd}^*(X).
 \tag{5.4}
\]
Substitute (5.2) and collect \(u\) to obtain
\[
 C_{r,p}(X)=
 \sum_{\substack{uv\le X\\u,v\text{ odd}\\(u,v)=1}}
 \mu^2(u)\alpha_{r,p}(u)\mu(v)a_{uv},
 \tag{5.5}
\]
where
\[
 \alpha_{r,p}(u)=\mathbf1_{p\mid u}\sum_{m\mid u/p}b_{r,\mathcal S_p}(m),
 \qquad 0\le\alpha_{r,p}(u)\le\tau(u).
 \tag{5.6}
\]
The squarefree and coprimality factors in (5.5) are essential. They are not omitted or absorbed without justification.

### 5.1 Absorb all nonrough factors exactly

Choose a roughness cutoff \(z\ge2\). Factor the Möbius variable into its \(z\)-smooth and \(z\)-rough parts, and move the smooth part into \(u\). On squarefree \(u\) divisible by \(p\), write
\[
 s=\omega_{\mathcal S_p\cap[2,z]}(u/p),\quad
 t=\omega_{\mathcal S_p\cap(z,\infty)}(u/p),\quad
 h=\omega_{\{\ell>z:\ell\notin\mathcal S_p\}}(u/p).
\]
Define
\[
 W_{r,p,z}(u)=\mathbf1_{p\mid u}\,2^h\binom{t}{r-s}.
 \tag{5.7}
\]
Then
\[
 \boxed{C_{r,p}(X)=
 \sum_{u\text{ odd}}\mu^2(u)W_{r,p,z}(u)
 \sum_{\substack{v\ge1\\uv\le X\\(v,u\Pi(z))=1}}
       \mu(v)a_{uv}.}
 \tag{5.8}
\]
In particular,
\[
 \boxed{0\le W_{r,p,z}(u)\le\tau(u),}
 \tag{5.9}
\]
uniformly in \(r,p,z\).

To verify the absorption, the generating polynomial for (5.6), away from the mandatory factor \(p\), has a factor \(1+z_0\) for each prime in \(\mathcal S_p\), and 2 for each other prime. Convolution with the small-prime Möbius function changes these respectively to \(z_0\) and 1 at primes at most the roughness cutoff. The remaining polynomial is
\(z_0^s(1+z_0)^t2^h\), whose coefficient is (5.7).

This is an exact identity. **There is no additional nonrough-Möbius remainder after (5.8).**

## 6. A rank-uniform Type-II corollary

Let \(N,z\) satisfy the original FI conditions (2.4). For every fixed \(L>0\),
\[
 \boxed{
 \sup_{r\ge0,\ p\equiv1\ (4)}
 \sum_{u\text{ odd}}\mu^2(u)W_{r,p,z}(u)
 \left|\sum_{\substack{N<v\le2N\\uv\le X\\(v,u\Pi(z))=1}}
 \mu(v)a_{uv}\right|
 \ll_{L,\eta}A(X)(\log X)^{-L}.}
 \tag{6.1}
\]
All rank and cutoff dependence is now in an outer divisor-bounded coefficient. The inner coefficient is exactly the admissible FI coefficient \(\mu(v)\), obtained by taking their parameter \(C=1\).

Proof: use (5.9), and put \(H=(\log X)^{L+129}\). On \(\tau(u)\le H\), multiply (2.3) by \(H\), selecting FI's exponent parameter \(2L+133\) to make the result \(O(A\log^{-L}X)\).

On \(\tau(u)>H\), discard cancellation. Because \(u\) is squarefree, \(\mu(v)\ne0\), and \((u,v)=1\), the product \(n=uv\) is squarefree. Then
\[
 \sum_{\substack{u\mid n\\\tau(u)>H}}\tau(u)
 \le H^{-1}\sum_{u\mid n}\tau(u)^2
 =H^{-1}5^{\omega(n)}.
\]
Apply (2.5). This contributes \(O(A\log^{-L-1}X)\), proving (6.1).

A signed outer coefficient bounded by a fixed multiple of \(\tau(u)\) satisfies the same conclusion. In particular it applies to the difference between two adjacent factor-prime rank counts at the same rank.

### 6.1 What this does not assert

It does not provide the same estimate for all cofactor sizes, arbitrary roughness cutoffs, arbitrary oscillating inner weights, or relative errors on every tiny rank-density difference. It is an absolute error estimate, and any application must compare it with the size of the proposed positive margin.

It also does not automatically give a lower bound for the small-cofactor endpoint merely because it is called a Type-I region. Formula (1.1) controls specified truncated **divisor sums**; translating every endpoint restriction into those sums is a further argument.

## 7. Exact 184-gap calibration

Let \(p<q\) be consecutive primes congruent to 1 modulo 4, and let \(g=q-p\). Define
\[
 E_j(p)=e_j\left((2/\ell)_{\ell\in\mathcal S_p}\right).
\]
The limiting rank density is
\[
 D_k(p)=\frac2{p+2}
 \prod_{\ell\in\mathcal S_p}\frac{\ell}{\ell+2}\ E_{k-1}(p).
 \tag{7.1}
\]
For \(r=k-1\ge1\) with positive denominator, put \(R_r(p)=E_{r-1}(p)/E_r(p)\). Direct algebra gives
\[
 \frac{D_k(q)}{D_k(p)}=\frac{p+2R_r(p)}{q+2},
 \qquad
 D_k(q)-D_k(p)=D_k(p)\frac{2R_r(p)-g-2}{q+2}.
 \tag{7.2}
\]
In particular,
\[
 D_k(q)>D_k(p)\iff R_r(p)>g/2+1.
 \tag{7.3}
\]
There is no reciprocal-law error term.

### 7.1 Replace a high-degree coefficient ratio by simple means

For \(t>0\), tilt the coefficient distribution by \(t^j\). Its Bernoulli probabilities and mean are
\[
 \frac{2t}{\ell+2t},\qquad
 M_t(p)=\sum_{\ell\in\mathcal S_p}\frac{2t}{\ell+2t}.
 \tag{7.4}
\]
The tilted mass at \(j\) is proportional to \(t^jE_j(p)\).
Darroch's rule and unimodality imply:

- for \(r=\lfloor M_{95}(p)\rfloor\), \(R_r(p)\le95\);
- if additionally \(M_{93}(p)<r-1\), then \(R_r(p)>93\).

A sufficient condition for the second statement is
\[
 M_{95}(p)-M_{93}(p)>2,
\]
because \(\lfloor M_{95}\rfloor-1>M_{95}-2\).
The difference is a positive monotone sum:
\[
 M_{95}(p)-M_{93}(p)
 =\sum_{\ell\in\mathcal S_p}
   \frac{4\ell}{(\ell+190)(\ell+186)}.
 \tag{7.5}
\]

### 7.2 Exact finite certificate valid for every future endpoint

The script `certify_rank_window.py` sums (7.5) over all 635,170 split primes below 20,000,000. It uses integer floors at scale \(Q=2^{96}\), not floating-point comparisons.

\[
\begin{aligned}
Q&=79228162514264337593543950336,\\
L&=158875779462983614403889547784,\\
U&=158875779462983614403890182954.
\end{aligned}
\]
The true sum lies in \([L/Q,U/Q]\). Moreover,
\[
 L-2Q=419454434454939216801647112>0.
\]
Its decimal value is approximately 2.00529425927781. Positivity of all additional terms makes the inequality valid for **every** larger endpoint, not just a finite list of tested endpoints.

Define
\[
 \boxed{k_{184}(p)=1+\lfloor M_{95}(p)\rfloor.}
 \tag{7.6}
\]
For every split prime \(p\ge20,000,000\), the corresponding ratio satisfies
\[
 93<R_{k_{184}(p)-1}(p)\le95.
\]
Split-prime gaps are multiples of 4. Thus
\[
 \boxed{D_{k_{184}(p)}(q)>D_{k_{184}(p)}(p)
        \quad\Longleftrightarrow\quad q-p\le184.}
 \tag{7.7}
\]
Within a comparison, the same rank \(k_{184}(p)\) is used at both \(p\) and \(q\). One must not substitute \(k_{184}(q)\) on the left.

Infinitely many such split-prime gaps imply infinitely many ordinary consecutive-prime gaps at most 184. The converse statement about ordinary prime gaps is not claimed.

For fixed \(t\), the progression prime number theorem gives \(M_t(p)=t\log\log p+O_t(1)\), so the prescribed ranks grow and have \(k_{184}(p)=95\log\log p+O(1)\). The finite theorem above does not rely on an ineffective asymptotic threshold for its sign window.

The calibration can be generalized: for a target \(H\) divisible by 4, use tilt \(H/2+3\), compare it with tilt \(H/2+1\), and certify their mean difference exceeds 2.

## 8. The remaining endpoint inequality, with all terms defined

Take a union of adjacent dyadic cofactor blocks entirely in the FI range (2.4), from \(N_-\) to \(N_+\). Let
\[
 \mathcal E_{r,p}(X)=
 \sum_{u\text{ odd}}\mu^2(u)W_{r,p,z}(u)
 \sum_{\substack{uv\le X\\(v,u\Pi(z))=1\\v\le N_-\ \text{or}\ v>N_+}}
 \mu(v)a_{uv}.
 \tag{8.1}
\]
This is an exact sum over the small- and large-rough-cofactor endpoints. Summing (6.1) over the middle dyadic blocks, with one extra logarithm of saving, gives
\[
 C_{r,p}(X)=\mathcal E_{r,p}(X)
              +O_{L,\eta}(A(X)(\log X)^{-L}),
 \tag{8.2}
\]
uniformly in \(r,p\). All small prime factors have already been absorbed into \(W\); there is no discarded nonrough component.

For \(q=p^+\) in the split-prime sequence, use the same \(r=k_{184}(p)-1\) and define
\[
 \mathcal E_p^\Delta(X)=
 \mathcal E_{r,q}(X)-\mathcal E_{r,p}(X).
 \tag{8.3}
\]
For any fixed finite endpoint interval \([Y,2Y]\), choose nonnegative weights \(w_p\) summing to 1 over its split primes. Taking \(X\to\infty\) first yields the exact limiting relation
\[
 \lim_{X\to\infty}\frac1{A^*(X)}
       \sum_{p\in[Y,2Y]\cap\mathcal P_1}w_p\mathcal E_p^\Delta(X)
 =\sum_{p\in[Y,2Y]\cap\mathcal P_1}w_p
   \bigl(D_{k_{184}(p)}(p^+)-D_{k_{184}(p)}(p)\bigr).
 \tag{8.4}
\]
Every large-X parameter on the left must satisfy FI's ranges. Uniformity of (6.1) makes averaging with weights of total mass 1 harmless.

**A sufficient ascent-supply theorem** would prove the left side of (8.4) is strictly positive for arbitrarily large \(Y\). Equation (7.7) would then supply recurring gaps at most 184.

No such positive endpoint lower bound is proved in this package. Neither the existence of many FI prime values nor the smallness of the middle bilinear blocks establishes its sign. A finite-X positive contrast without a suitable uniform margin or controlled limiting passage is also insufficient.

For a truncated divisor expression, (1.1) already bounds
\[
 \sum_{\substack{d\mid\prod_{\ell\in\mathcal S_p}\ell\\pd\le D}}
 \lambda_{r,\mathcal S_p}(d)
 \bigl(A_{pd}^*(X)-g_*(pd)A^*(X)\bigr),
\]
uniformly in rank. This is a concrete available tool for the endpoint analysis, not a bound for the whole endpoint by assertion.

## 9. Actual finite checks

All integral representations are used, including sign multiplicities and zero coordinates; the zero output is removed.

### 9.1 Representation counts

| X | Raw representation count A(X) | Odd squarefree count A*(X) |
|---:|---:|---:|
| 100,000 | 19,630 | 7,240 |
| 1,000,000 | 110,562 | 40,668 |
| 10,000,000 | 621,996 | 229,116 |

### 9.2 Algebra checks

- 540,000 exact integer tests of \(\lambda=\mu*b\), with zero failures.
- 1,021,440 exact integer tests of the smooth-factor absorption and the nonnegative divisor bound for \(W\), with zero failures.
- Exact modulo-\(p^2\) checks of the conditioned local law at all odd primes through 101.
- Twelve exact finite rank-count decompositions using (5.8), matching direct enumeration. The small chosen cutoffs in these tests are **not** claimed to satisfy the asymptotic FI parameter conditions.
- The rank-window certificate in Section 7.2 uses integer arithmetic for every summand and certifies an inequality beyond the finite computation by positivity of the tail.

### 9.3 Selected calibrated-rank examples

`calibrate_ranks.py` computes Poisson-binomial ratios in extended floating point, but certifies rank floors and the listed ascent signs independently by integer interval means and the mean-mode theorem.

| p | next split prime q | gap | calibrated rank k | ratio (numerical only) |
|---:|---:|---:|---:|---:|
| 997 | 1009 | 12 | 31 | 90.95154 |
| 9973 | 10009 | 36 | 56 | 93.24743 |
| 99989 | 100049 | 60 | 77 | 94.15962 |
| 999961 | 1000033 | 72 | 94 | 94.07133 |
| 9999973 | 10000121 | 148 | 109 | 94.60965 |

These finite examples do not establish an unbounded supply.

`results.json` also contains finite divisor-error and rank-density diagnostics. They are not estimates of the unknown asymptotic constants. Some finite rank contrasts differ in sign from their limiting model because the input cutoff is too small; the data are preserved rather than selected to hide this.

## 10. Reproduce

Python with NumPy and Numba is required for the full tests. The rank-window certificate itself uses NumPy and Python integers and does not need Numba.

```text
python pursue_fi.py --max-x 10000000 --out results.json
python rough_reorganize.py --max-x 1000000 --out rough_results.json
python calibrate_ranks.py
python certify_rank_window.py
```

- `pursue_fi.py`: local laws, finite FI representations, divisor diagnostics, initial convolution checks.
- `rough_reorganize.py`: exact absorption of the smooth Möbius factor and reassembled rank counts.
- `calibrate_ranks.py`: exact mean intervals and numerical tilted coefficient ratios.
- `certify_rank_window.py`: exact universal 184-gap calibration certificate.
- JSON files preserve the completed outputs.
- `MANIFEST.json` records hashes and sizes of the packaged sources and results.

The earlier exploratory FI-local-law package is not included here; these scripts and derivations supersede the relevant route-specific portions.

# LPF generation: averaged deletion and dense-seed contraction

This is a refinement of [the LPF dynamics argument](lpf-dynamics.md).
It uses distinct pairs as sufficient witnesses inside the current all-pairs
system, which starts from $\{2,p\}$ and permits diagonals at every generation.
The two cofactor lifts and the audited exclusion / Dirichlet 7/8 input are
already installed in the repository.

The finite energy consumer, exact residue obstruction, uniform prime-target
moment, averaged overlap, actual upper-sieve inputs, conditional dense-seed
recurrence, and quantitative bounds for the actual fullOrbit states are
compiled in Lean. The positive representation input, controlled exceptional
set, final density-limit theorem, and actual small-seed entry still require
formal proofs. The complete ordinary statements below must be distinguished
from the currently closed Lean declarations. No numerical starting threshold
is evaluated, and novelty is not established.

**Strongest dense-seed consequence.** The
[prime-target moment argument](#prime-target-moments-and-multiple-generations)
allows $E\le\eta M/\log M$: a fixed sufficiently small fraction of the
input primes may be missing. It uses the installed 7/8 estimate and a
multi-generation contraction. The sharper one-step coverage question below
has a different, smaller defect threshold.

## Uniform one-step statements

Write
$$
 \ell_3(M)=1+\log\log\log M
$$
for sufficiently large $M$, so this is positive.

**Upper transfer theorem.** There are absolute $c>0,M_0$ such that if a
finite prime state $S$ omits at most
$$
 E=|P_M\setminus S|\le c\,\frac{M}{\log M\,\ell_3(M)},\qquad M\ge M_0,
$$
primes from $P_M=\{p\le M:p\text{ prime}\}$, then
$$
 |P_{\lfloor5M/4\rfloor}\setminus\operatorname{step}(S)|
 \le E+C M/\log^4 M.
$$
The state can also contain primes above $M$. Iteration gives a generated set
missing $O(x/\log^4 x)$ primes up to $x$, hence relative density one.

This improves the preceding allowance
$M/(\log M(1+\log\log M))$ by an unbounded factor.
The proof below bounds the total overlap of the failed targets, rather
than the largest overlap between an individual pair.

**Matching order obstruction for uniform one-step coverage.** There are
finite prime states $S_M\subseteq P_M$ with
$$
 |P_M\setminus S_M|\asymp\frac{M}{\log M\,\ell_3(M)}
$$
whose next generation misses at least $c'M/\log^{3/2}M$ target primes in
$(M,5M/4]$. Thus a uniform conclusion with $O(M/\log^4 M)$ missing new
targets cannot permit an asymptotically larger defect scale.

The constants in the sufficient bound and the obstruction need not agree.
The obstruction is to this one-step coverage statement. These states are
not claimed to be closed, to occur in a small-seed orbit, or to obstruct
later generations. It does not settle the best hypothesis for eventual
density one, or infinitude from the designated small seeds.

## A uniform moment estimate for the local multiplier

For each positive integer $n$, put
$$
 g(n)=\prod_{\substack{p\mid n\\p>2,\ p\ {\rm prime}}}\frac{p-1}{p-2}.
$$
In particular $g(1)=1$. For every integer $q\ge1$ and real $X\ge1$,
there is one absolute $C_0$ such that
$$
 \sum_{1\le n\le X}g(n)^q
 \le X\bigl(C_0\log(q+2)\bigr)^q.                     \tag{1}
$$
The constant is independent of both $q$ and $X$.

To prove this, write $g(n)^q=\sum_{d\mid n}h_q(d)$, where $h_q$ is
supported on odd squarefree integers, is nonnegative, and
$$
 h_q(p)=\left(\frac{p-1}{p-2}\right)^q-1.
$$
The exact divisor expansion and $\lfloor X/d\rfloor\le X/d$ give
$$
 \sum_{n\le X}g(n)^q
 \le X\prod_{p>2}\left(1+\frac{h_q(p)}p\right).
$$
For $p\le2q$, each Euler factor is at most $((p-1)/(p-2))^q$.
Mertens' theorem and
$$
 \frac{p-1}{p-2}(1-1/p)=1+\frac1{p(p-2)}
$$
bound the product of these factors by $(C\log(q+2))^q$.
For $p>2q$, the inequality
$q\log(1+1/(p-2))\le1$ implies $h_q(p)\le Cq/(p-2)$.
Therefore
$$
 \sum_{p>2q}\frac{h_q(p)}p
 \le Cq\sum_{n>2q}\frac1{n(n-2)}=O(1),
$$
uniformly for integer $q\ge1$ (the case $q=1$ starts at $n=3$).
Absorbing the resulting bounded Euler product into $C_0^q$ proves (1).

## Average overlap of an arbitrary failed-target set

Let $B$ be any set of $b>0$ distinct integer targets in $[M/2,2M]$.
For fixed $t\in B$, every positive difference $|t-s|$ occurs at most twice.
Applying Holder's inequality and (1), with
$q=\max(1,\lceil\log(4M/b)\rceil)$, yields
$$
 \sum_{\substack{s\in B\\s\ne t}}g(|t-s|)
 \le C b\,\log\!\left(3+\log(4M/b)\right).
$$
Indeed the $q$-moment is at most
$4M(C_0\log(q+2))^q$, and $(4M/b)^{1/q}\le e$.
Here $b\le2M$, so the chosen exponent and all logarithms are admissible.
Consequently
$$
 \sum_{t\in B}\sum_{\substack{s\in B\\s\ne t}}g(|t-s|)
 \le C b^2\,\log\!\left(3+\log(4M/b)\right).           \tag{2}
$$
There is no assumption that $B$ is randomly distributed.

Use the normalized incidence columns from the preceding proof:
$w(p,t)={\bf1}_{p\in A_t}/g(t)$.
Outside the explicit exceptional target set, the established analytic
inputs have the following strength:
$$
 \frac{|A_t|-1}{g(t)}\ge L=\frac{aM}{\log^2M},\qquad
 \sum_{p\in P_M}w(p,t)^2\le U_*=\frac{c_0M}{\log^2M},
$$
$$
 \sum_{p\in P_M}w(p,t)w(p,s)
 \le \frac{c_1M}{\log^3M}\,g(|t-s|)\quad(t\ne s).
$$
The lower bound is the bounded-input Coppola--Laporta consequence;
the upper bounds are the uniform two- and three-form sieves with their
local factors retained. Their derivations and primary sources are in
[the normalized-deletion proof](lpf-dynamics.md#retaining-the-local-representation-factors).

The complete degree energy is therefore
$$
 \sum_{p\in P_M}\left(\sum_{t\in B}w(p,t)\right)^2
 \le bU_*+
 \frac{C_1M}{\log^3M}\,b^2\log\!\left(3+\log(4M/b)\right). \tag{3}
$$
No unsigned upper bound has replaced a positive supply term.

## Substitution in the full signed inequality

For failed targets, the same deletion cover and Cauchy--Schwarz give
$$
 b^2L^2\le4E\left[
 bU_*+\frac{C_1M}{\log^3M}\,
 b^2\log\!\left(3+\log(4M/b)\right)\right].             \tag{4}
$$
Suppose, seeking a contradiction, that $b\ge M/\log^4M$.
Then
$$
 \log(3+\log(4M/b))\le C_{\mathrm{av}}\ell_3(M)
$$
for large $M$. Set $K_*=C_1C_{\mathrm{av}}M\ell_3(M)/\log^3M$.
Choose $c\le a^2/(8C_1C_{\mathrm{av}})$ in the defect hypothesis.
The complete coefficient satisfies $8EK_*\le L^2$, so (4) implies
$$
 b\le 8EU_*/L^2
 \le \frac{8c_0c}{a^2}\frac{\log M}{\ell_3(M)}.
$$
This contradicts $b\ge M/\log^4M$ for all sufficiently large $M$.
Hence fewer than $M/\log^4M$ nonexceptional target lifts fail.

The two cofactor lifts are injective on $(M,5M/4]$.
Adding the $O(M/\log^4M)$ exceptional lifts gives the upper transfer theorem.
For the iteration, put $f(M)=M/(\log M\,\ell_3(M))$.
Then $f(\lfloor5M/4\rfloor)/f(M)\to5/4$ and
$(M/\log^4M)/f(M)\to0$.
The same geometric induction as before preserves $E(M)\le c f(M)$.
Summing its errors gives $E_j\le E_0+O(M_j/\log^4M_j)$ and the claimed
density-one conclusion.

The finite estimate consuming (3) is
**Finset.weighted_failed_sum_target_card_le_of_energy**.
It accepts the complete degree energy as an explicit premise.
The underlying Cauchy estimate is
**Finset.covered_target_card_le_of_energy**.
Both are in the maintained candidate layer; neither assumes an analytic
estimate through an axiom or a hidden hypothesis structure.

## Residue construction showing the limitation

Take $z=\tfrac14\log\log M$ and
$Q=\prod_{2<p\le z}p$.
For large $M$, the prime number theorem gives
$\log Q\le2z$, hence $Q\le(\log M)^{1/2}$.
Define
$$
 S_M=\{p\text{ prime}:z<p\le M,\quad
          p\equiv1\pmod\ell\text{ for some odd prime }\ell\le z\}.
$$
The deleted primes above $z$ occupy exactly
$\prod_{2<\ell\le z}(\ell-2)$ unit classes modulo $Q$.
Their fraction among unit classes is
$$
 \delta(z)=\prod_{2<\ell\le z}\frac{\ell-2}{\ell-1}
 \sim \frac{2e^{-\gamma}C_2}{\log z},
 \qquad C_2=\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right).
$$

Here the installed 7/8 input is used directly.
Its uniform prime-row character bound and the compiled orthogonality
estimate bound each reduced progression discrepancy by
$O(M^{7/8}(1+\log Q+\log M)^2)$.
Summing over the selected classes costs at most a factor $Q$:
$$
 |P_M\setminus S_M|
 =\pi(z)+\delta(z)(\pi(M)-\pi(z))
   +O\!\left(QM^{7/8}\log^2M\right).
$$
Because $Q\le\sqrt{\log M}$, this error is smaller than the main term.
Since $\log z\sim\log\log\log M$,
$$
 |P_M\setminus S_M|
 \sim 2e^{-\gamma}C_2\,
       \frac{M}{\log M\,\log\log\log M}.              \tag{5}
$$
The modulus is allowed to grow here; no fixed-modulus theorem is substituted
without checking its range.

Now consider target primes $M<r\le\lfloor5M/4\rfloor$ with
$r\equiv3\pmod4$ and $r\equiv1\pmod Q$.
These conditions specify one reduced class modulo $4Q$.
The same 7/8 discrepancy estimate, together with the ordinary prime number
theorem for the full interval, gives at least
$$
 c'\frac{M}{Q\log M}\ge c'\frac{M}{\log^{3/2}M}       \tag{6}
$$
such target primes.

None belongs to $\operatorname{step}(S_M)$.
To see this, all inputs are odd and at most $M$, so their affine value is
$3\bmod4$ and less than $4M$.
An output prime $r>M$ could only own a value $r$ or $3r$.
The second has residue $1\bmod4$ and is impossible.
The first would require
$p+q=t=(r+1)/2$.
For any $p\in S_M$, choose an odd prime $\ell\le z$ with
$p\equiv1\bmod\ell$.
The target also has $t\equiv1\bmod\ell$, so $\ell\mid q$.
But $q$ is prime and $q>z\ge\ell$, a contradiction.
This argument excludes all pairs, including the distinct pairs used by
the dynamics.

The exact finite LPF obstruction is proved in
[LPFResidueObstruction.lean](../PrimeFactorOscillations/Helpers/LPFResidueObstruction.lean),
especially **not_mem_step_of_prime_residue_cover**.
Equations (5)--(6) are the ordinary analytic application of the installed
7/8 estimate; they are not yet separately compiled asymptotic declarations.

Combining (5) and (6) proves the matching-order obstruction.
To improve the small-seed result further, one can exploit restrictions
specific to generated states, allow multiple generations before requiring
coverage, or control the signed generation count directly.
The construction does not refute any of those approaches.

## Prime-target moments and multiple generations

**Stronger dense-seed theorem.** There are absolute $\eta>0,M_0$ such
that any finite prime seed satisfying
$$
 |P_M\setminus S|\le\eta\,\frac{M}{\log M}
 \quad\hbox{for some }M\ge M_0
$$
generates a relative-density-one subset of primes, missing
$O(x/\log^4x)$ primes up to $x$.
Thus a fixed sufficiently small fraction of the input primes may be absent.
This ordinary proof consumes the audited 7/8 input. Its uniform moment,
averaged overlap, actual upper-sieve inputs, dense-seed recurrence, scale
growth and quantitative fullOrbit iteration are Lean formalized. Positive
representations, controlled exceptions, the final density-limit statement,
and actual orbit entry remain separate obligations.

The improvement uses the prime indexing of the targets, then permits
several generations to reduce the relative defect. It does not strengthen
the uniform one-step statement contradicted above.

### The prime-target moment estimate

Let $T_M$ be the set of target lifts
$t=(mr+1)/2$, where $M<r\le\lfloor5M/4\rfloor$ is prime and
$m=1$ or $3$ according to $r\bmod4$. Put $N=M/\log M$.
For every $t\in T_M$ and integer $1\le k\le10\log\log M$, we have
$$
 \sum_{\substack{s\in T_M\\s\ne t}}g(|t-s|)^k
 \le N\bigl(C\log(k+2)\bigr)^k,                       \tag{7}
$$
uniformly for sufficiently large $M$. The important normalization is
$N=M/\log M$, the scale of the prime target set.

Here is the complete error check. Set $Y=(\log M)/64$ and
$D=\prod_{3<\ell\le Y}\ell$. Then $D\le M^{1/32}$ for large $M$.
For every $1\le v\le2M$, its prime factors above $Y$ contribute
$$
 \log\prod_{\substack{\ell\mid v\\\ell>Y}}\frac{\ell-1}{\ell-2}
 \le\frac{2\log(2M)}{Y\log Y}=O(1/\log\log M).
$$
The factor at 3 is at most 2. Consequently $g(v)\le Cg_D(v)$, where
$g_D(v)$ keeps only the prime factors dividing $D$.

Expand
$$
 g_D(v)^k=\sum_{\substack{d\mid D\\d\mid v}}h_k(d),
 \qquad
 h_k(\ell)=\left(\frac{\ell-1}{\ell-2}\right)^k-1.
$$
All coefficients are nonnegative. For a fixed
$t=(mr+1)/2$ and a target branch $s=(nr'+1)/2$, with $m,n\in\{1,3\}$,
the condition $d\mid(t-s)$ specifies
$$
 r'\equiv mn^{-1}r\pmod d.
$$
It is a reduced class: $d$ is coprime to 6 and $r>M>D$.
The installed uniform prime-row character bound and orthogonality
therefore bound its prime count by
$$
 \frac{R(M)}{\varphi(d)}+O(M^{7/8}\log^2M),
 \qquad R(M)=\pi(\lfloor5M/4\rfloor)-\pi(M)\ll N.
$$
Dropping the branch restriction modulo 4 only enlarges this upper bound.
The excluded diagonal may also be included in the finite divisor count
for an upper bound; no value of $g(0)$ is defined or used.

The main Euler product is
$$
 \prod_{\ell\mid D}\left(1+\frac{h_k(\ell)}{\ell-1}\right)
 \le(C\log(k+2))^k.
$$
Split it at $2k$: the small-prime product is bounded by Mertens as before,
and the remaining logarithm is at most
$Ck\sum_{\ell>2k}((\ell-1)(\ell-2))^{-1}=O(1)$.
The complete analytic error after summing the divisor weights is
$$
 O\!\left(M^{7/8}\log^2M
       \sum_{d\mid D}h_k(d)\right)
 =
 O\!\left(M^{7/8}\log^2M
       \prod_{\ell\mid D}\left(\frac{\ell-1}{\ell-2}\right)^k\right)
 \ll M^{7/8}\log^2M(C\log\log M)^k.                  \tag{8}
$$
For all $1\le k\le10\log\log M$, this is at most $M^{15/16}$
once $M$ is sufficiently large. Indeed,
$2\log\log M+10\log\log M\log(C\log\log M)=o(\log M)$.
Thus it is absorbed on the $N$ scale in (7).
This retains every growing-moment factor in the 7/8 error.

### The coupled bound at the prime-target scale

Suppose $B\subseteq T_M$ is the set of failed nonexceptional lifts,
with $b=|B|\ge M/\log^4M$.
For large $M$, $|T_M|\le N/2$ by PNT.
Take $k=\lceil\log(N/b)\rceil$.
Then $1\le k\le3\log\log M+1\le10\log\log M$.
Holder's inequality applied to (7) gives
$$
 \sum_{t\in B}\sum_{\substack{s\in B\\s\ne t}}g(|t-s|)
 \le Cb^2\log(3+\log(N/b)).
$$
The exact normalized deletion argument now yields
$$
 b^2L^2\le4E\left[
 bU_*+\frac{C_1M}{\log^3M}\,
 b^2\log(3+\log(N/b))\right],                         \tag{9}
$$
where $L=aM/\log^2M$ and $U_*=c_0M/\log^2M$ as before.

Write $\delta=E/N$ and assume first that $E>0$.
If also $b\ge E/16$, the logarithmic factor is at most
$\log(3+\log(16/\delta))$.
Choose $\eta>0$ so small that, for every $0<\delta\le\eta$,
$$
 8C_1\delta\log(3+\log(16/\delta))\le a^2.
$$
Such an $\eta$ exists because
$\delta\log\log(1/\delta)\to0$ as $\delta\downarrow0$.
The finite energy theorem applied to (9) then gives
$$
 b\le\frac{8c_0}{a^2}\delta\log M,
$$
contradicting $b\ge M/\log^4M$ for large $M$.
For $E=0$, the positive representation surplus directly excludes every
nonexceptional failure.
Hence, after adding the exceptional lifts,
$$
 E_{\rm next}(\lfloor5M/4\rfloor)
 \le\frac{17}{16}E+C_A\,\frac{M}{\log^4M},
 \qquad E\le\eta\,\frac{M}{\log M}.                   \tag{10}
$$
This is the full improved recurrence. The allowed absolute defect may
increase, but the prime range grows faster.

### Iteration without assuming that the state fills a prefix

For $M'=\lfloor5M/4\rfloor$ and large $M$,
both $N(M')/N(M)$ and $F(M')/F(M)$ are at least $9/8$,
where $F(M)=M/\log^4M$.
Since $17/16<9/8$ and $F(M)/N(M)\to0$, increasing $M_0$
makes (10) preserve the condition $E\le\eta N(M)$.

Along $M_{j+1}=\lfloor5M_j/4\rfloor$, summing (10) gives
$$
 E_j\le(17/16)^jE_0+16C_A F(M_j).
$$
The initial term is negligible compared with $F(M_j)$, because
$F(M_j)\ge(9/8)^jF(M_0)$.
Thus $E_j=O(M_j/\log^4M_j)$, and the bounded cutoff ratios extend this
to all large $x$. This proves the stronger dense-seed theorem.

The recurrence allows an extra $E/16$ of temporary omissions in each
generation, so it is compatible with the earlier obstruction to
$E_{\rm next}\le E+O(M/\log^4M)$.
Under the current rule, every seed contains 2 and all diagonals are allowed
at every generation. The common-orbit reduction in
[lpf-dynamics.md](lpf-dynamics.md#current-seeds-and-the-common-orbit-from-two)
therefore reduces density entry to the single orbit from $\{2\}$. It still
does not supply a usable starting threshold for the asymptotic theorem.

## Maintained Lean moment components

[LPFPrimeTargetMoment.lean](../PrimeFactorOscillations/Helpers/LPFPrimeTargetMoment.lean)
formalizes twelve components of the prime-target argument. They retain the full
finite weights and consume the existing uniform 7/8 character theorem.

For a finite set $P$ of odd primes, put $f(\ell)=1+1/(\ell-2)$,
$d_A=\prod_{\ell\in A}\ell$, $D=d_P$, and
$h_q(A)=\prod_{\ell\in A}(f(\ell)^q-1)$. The exact finite identities are
$$
 \left(\prod_{\substack{\ell\in P\\\ell\mid v}}f(\ell)\right)^q
 =\sum_{A\subseteq P}h_q(A)\,\mathbf1_{\ell\mid v\text{ for every }\ell\in A},
 \qquad
 \sum_{A\subseteq P}h_q(A)=\left(\prod_{\ell\in P}f(\ell)\right)^q.
$$
The nonnegative weights and the complete second identity are Lean proved.
The identities concern a finite truncated product; they do not define the
untruncated singular factor at zero.

For a prime row $R=\operatorname{largestPrimeFactorRow}(X,y,m)$ and any
choice of reduced residues $a_A\bmod d_A$, one absolute $C>0$ gives
$$
 \sum_{r\in R}\sum_{A\subseteq P}h_q(A)\mathbf1_{r\equiv a_A\pmod{d_A}}
 \le |R|\sum_{A\subseteq P}\frac{h_q(A)}{\varphi(d_A)}
 +C X^{7/8}(1+\log D+\log(X+2))^2
       \left(\prod_{\ell\in P}f(\ell)\right)^q.
$$
The constant precedes all cutoffs, prime sets, moment orders, and residue
choices. The theorem actually permits any finite set of integers at least 3;
primality is needed for the later squarefree interpretation and Euler-product
factorization. No coprimality assumption on all input primes is hidden here:
character orthogonality first retains the exact unit-input count for each
modulus, then bounds that count by $|R|$ to obtain the displayed upper bound.

The asymptotic error normalization is also Lean proved. For each fixed $C>0$,
uniformly for all natural $q\le10\log\log X$ and all sufficiently large $X$,
$$
 C X^{7/8}(\log X)^2(C\log\log X)^q\le X^{15/16}.
$$
In particular, this expression is smaller than the main scale $X/\log X$.
The proof keeps both logarithmic losses and the entire growing-moment factor.
It supplies an existential threshold, not an evaluated numerical cutoff.

The main Euler-product estimate is now also Lean proved, for every finite
set of odd primes and every integer $q\ge1$, uniformly in the outer cutoff:
$$
 \prod_{\ell\in P}\left(1+\frac{f(\ell)^q-1}{\ell-1}\right)
 \le \left(C_*\log(q+2)\right)^q.
$$
One proved choice is
$$
 B=|\mathfrak M|+\frac{E_{\mathrm M}}{\log2}+12,
 \qquad C_*=2\exp(B+12),
$$
where $\mathfrak M$ and $E_{\mathrm M}$ are the Mertens constant and error
constant from the pinned dependency's proved reciprocal-prime estimate.
This is a symbolic uniform constant, not a numerically evaluated entry cutoff.

The proof splits at $2q+2$. The low-prime part uses
$$
 \frac1{\ell-2}\le\frac1\ell+\frac6{\ell^2},\qquad
 \prod_{\substack{\ell\in P\\\ell\le n}}f(\ell)\le e^B\log n\quad(n\ge2).
$$
For $\ell>2q+2$, the proved estimates are
$$
 f(\ell)^q-1\le\frac{2q}{\ell-2},\qquad
 \frac{f(\ell)^q-1}{\ell-1}\le\frac{6q}{\ell^2}.
$$
The high product is at most $\exp(12q)$, independently of the outer cutoff.
That factor is absorbed in $C_*^q$. The proof retains the full product and
works for all positive integer moment orders, not just a fixed order.

[LPFPrimeTargetArithmetic.lean](../PrimeFactorOscillations/Helpers/LPFPrimeTargetArithmetic.lean)
now supplies the exact principal-sum conversion
$$
 \sum_{A\subseteq P}\frac{h_q(A)}{\varphi(d_A)}
 =\prod_{\ell\in P}\left(1+\frac{f(\ell)^q-1}{\ell-1}\right).
$$
Its proved consumer substitutes the uniform Euler bound into the prime-row
inequality above and retains the complete error term.

The same module proves the actual branch arithmetic. Write
$m(r)=3$ for $r\equiv1\pmod4$ and $m(r)=1$ otherwise, and
$t(r)=(m(r)r+1)/2$ for odd prime $r$. Fix $n\in\{1,3\}$.
For any modulus $d$ with $(d,6r)=1$, there is a reduced residue
$a\equiv n^{-1}m(r)r\pmod d$ such that, for every odd prime $s$ with
$m(s)=n$,
$$
 d\mid |t(r)-t(s)|\quad\Longleftrightarrow\quad s\equiv a\pmod d.
$$
The proof uses units, so it handles composite moduli as well as $d=1$.
The required coprimality is also proved for every product of distinct primes
$\ell$ satisfying $3<\ell<r$, hence for every subset modulus in that range.
This excludes the exceptional factors 2 and 3 explicitly.

[LPFPrimeTargetTruncated.lean](../PrimeFactorOscillations/Helpers/LPFPrimeTargetTruncated.lean)
combines the two branches into a bound for actual prime targets. Fix an odd
prime $r$, a finite set $P$ of primes $3<\ell<r$, and a subset $S\subseteq R$
consisting of odd primes. Put
$g_P(v)=\prod_{\ell\in P,\,\ell\mid v}f(\ell)$. Uniformly for every integer
$q\ge1$,
$$
 \sum_{s\in S}g_P(|t(r)-t(s)|)^q
 \le 2|R|\bigl(C_*\log(q+2)\bigr)^q
 +C X^{7/8}(1+\log D+\log(X+2))^2
       \left(\prod_{\ell\in P}f(\ell)\right)^q.
$$
Here $C$ is absolute and selected before all parameters. Both cofactor
branches are included; no reduced-input hypothesis is imposed on $S$.
The finite product permits the diagonal $s=r$.

[LPFPrimeTargetTail.lean](../PrimeFactorOscillations/Helpers/LPFPrimeTargetTail.lean)
proves the large-prime bound. For any $v\ge1$, $Y\ge4$, and any finite set $Q$
of distinct prime divisors of $v$ all at least $Y$,
$$
 \prod_{\ell\in Q}f(\ell)
 \le \exp\!\left(\frac{2\log v}{Y\log Y}\right).
$$
Consequently, for any finite set $Q$ of odd prime divisors of $v$,
$$
 \prod_{\ell\in Q}f(\ell)
 \le 2\exp\!\left(\frac{2\log v}{Y\log Y}\right)
       \prod_{\substack{\ell\in Q\\3<\ell\le Y}}f(\ell).
$$
This retains the exceptional factor at 3. The untruncated application requires
$v>0$; unlike the finite truncated moment, it cannot include a zero difference.

The same module proves the elementary conductor bound
$\log\prod_{\ell\in P}\ell\le(N+1)^2$ whenever $P$ consists of distinct
positive integers at most $N$.
[LPFPrimeTargetLogPower.lean](../PrimeFactorOscillations/Helpers/LPFPrimeTargetLogPower.lean)
proves, for every fixed integer $L\ge0$ and fixed $C>0$, eventually
$$
 C X^{7/8}(\log X)^L(C\log\log X)^q\le X^{15/16}
 \qquad(0\le q\le10\log\log X).
$$
The threshold may depend on $L$ and $C$, but is uniform in $q$.

The formal proof now uses the simpler choice $Y=\log M$. The residue
bound only loses logarithms of $D$, and the branch condition requires each
cutoff prime to be below $r$, not $D<r$. A crude bound
$\log D\le(\lfloor Y\rfloor+1)^2$ introduces at most a fourth logarithmic
power in the error; the new theorem controls it. A small-power primorial
bound such as $D\le M^{1/32}$ is therefore unnecessary.

The complete prime-target moment (7) is now formalized in
[LPFPrimeTargetAsymptotic.lean](../PrimeFactorOscillations/Helpers/LPFPrimeTargetAsymptotic.lean),
as **exists_uniform_primeTarget_moment**. Let
$\mathcal R_M=\{r\text{ prime}:M<r\le\lfloor5M/4\rfloor\}$ and, for $v\ge1$,
$g(v)=\prod_{\ell\mid v,\ \ell\text{ odd prime}}f(\ell)$.
There is one absolute $C_0>0$ such that, for all sufficiently large integer
$M$, every $r\in\mathcal R_M$, and every integer $1\le q\le10\log\log M$,
$$
 \sum_{\substack{s\in\mathcal R_M\\s\ne r}}
       g\bigl(|t(r)-t(s)|\bigr)^q
 \le \frac{M}{\log M}\bigl(C_0\log(q+2)\bigr)^q.
$$
The threshold is uniform in both $r$ and $q$. The proof chooses
$C_0=9(2e^4C_*+1/\log2)$; it does not evaluate the threshold.

[LPFPrimeTargetFull.lean](../PrimeFactorOscillations/Helpers/LPFPrimeTargetFull.lean)
establishes the exact cutoff support, positivity and upper bound $2M$ for
each off-diagonal difference, the full finite moment with every error
retained, and the eventual bound $|\mathcal R_M|\le4M/\log M$ from the
existing prime-counting theorem. Its finite prime-factor product has an
auxiliary value at zero; no arithmetic interpretation or tail estimate
uses that value. The condition $s\ne r$ separates the moment's self-term;
all dynamical input diagonals remain enabled.

The full proof bounds the tail multiplier by $2e^4$, the cutoff weight
by $2e^B\log\log M$, and the squared conductor loss by $64(\log M)^4$.
The entire resulting error is at most $M^{15/16}$ and eventually at most
$M/\log M$. Fixed constants are absorbed uniformly using $q\ge1$.

[LPFPrimeTargetOverlap.lean](../PrimeFactorOscillations/Helpers/LPFPrimeTargetOverlap.lean)
now proves **exists_uniform_primeTarget_overlap**. For one absolute $C>0$,
all sufficiently large $M$, and every subset $B\subseteq\mathcal R_M$ with
$b=|B|\ge M/\log^4M$, it gives
$$
 \sum_{r\in B}\sum_{s\in B\setminus\{r\}}
   g\bigl(|t(r)-t(s)|\bigr)
 \le C b^2\log\!\left(3+\log\frac{M/\log M}{b}\right).
$$
There is no distribution hypothesis on $B$. The proof takes $C=eC_0$ and
uses the separately proved eventual bound $|\mathcal R_M|\le N/2$, where
$N=M/\log M$. For $q=\lceil\log(N/b)\rceil$, the proof verifies
$1\le q\le10\log\log M$ before applying the moment theorem and finite
power-mean inequality. The self-term $r=s$ remains separate in the energy.

## Compiled transfer to the all-pairs step

[LPFAveragedTransfer.lean](../PrimeFactorOscillations/Helpers/LPFAveragedTransfer.lean)
now connects the averaged estimate to actual failed targets of
$\operatorname{fullStep}(S)$. Its analytic premises are explicit, not axioms
or fields of a hidden hypothesis structure.

Write $A_r=\{p\in P:t(r)-p\in P,\ p\le t(r)\}$ and choose nonnegative
weights $v(r)$. Set $w(p,r)=v(r)\mathbf1_{p\in A_r}$.
For any $B\subseteq\mathcal R_M\setminus\operatorname{fullStep}(S)$,
$b=|B|\ge F=M/\log^4M$, the required inputs are
$$
 L\le v(r)|A_r|,\qquad
 \sum_{p\in P}w(p,r)^2\le U,\qquad
 \sum_{p\in P}w(p,r)w(p,s)\le Vg(|t(r)-t(s)|)\quad(r\ne s).
$$
Here $L>0$, $U,V\ge0$, and $E=|P\setminus S|$.
A failed target has no surviving representation, including a diagonal.
The exact deletion cover therefore has $|A_r|\le2|A_r\setminus S|$:
the old distinct-input correction of one is unnecessary.

The proved overlap bound and finite Cauchy inequality give the complete energy
$$
 b^2L^2\le4E\left[bU+VCb^2\log(3+\log(N/b))\right],
 \qquad N=M/\log M.
$$
The theorem **exists_averaged_fullStep_deletion_bound** proves
$$
 8EVC\log(3+\log(N/b))\le L^2
 \quad\Longrightarrow\quad
 b\le\frac{8EU}{L^2}.
$$
The constant $C$ precedes all states, input sets, weights, and parameters.

For $P=P_M$ and an explicit exceptional set $Z$, let
$B=(\mathcal R_M\setminus Z)\setminus\operatorname{fullStep}(S)$.
The theorem **exists_averaged_fullStep_prefix_bound** requires the same
representation and codegree inputs outside $Z$ and the absorption condition
only when $b\ge F$. It concludes
$$
 |P_{\lfloor5M/4\rfloor}\setminus\operatorname{fullStep}(S)|
 \le E+|Z|+\frac{M}{\log^4M}+\frac{8EU}{L^2}.
$$
This carries old omissions, analytic exceptions, small failed sets, and the
diagonal energy term into the actual next generation.

The representation and upper-sieve estimates, the small-density absorption
giving recurrence (10), its iteration, and actual entry of the common
$\{2\}$ orbit remain outside a complete Lean infinitude proof. The new
conditional transfer does not discharge those analytic premises, improve
the on-paper recurrence coefficient, evaluate its constants, or establish
entry or all-prime reachability.

## Formal local Fourier step for the upper sieve

[LPFSieveLocal.lean](../PrimeFactorOscillations/Helpers/LPFSieveLocal.lean)
proves the local Fourier construction needed for the upper-sieve inputs.
Let $p$ be prime and let $\Omega\subseteq\mathbb Z/p\mathbb Z$ have
$0<\nu=|\Omega|<p$. Define $f(x)=1$ off $\Omega$ and
$f(x)=-(p-\nu)/\nu$ on $\Omega$. Its normalized Fourier coefficients $c(a)$
satisfy the exact identities
$$
 c(0)=0,\qquad
 \sum_{a\ne0}|c(a)|^2=\frac{p-\nu}{\nu},\qquad
 \sum_{a\ne0}c(a)e(ax/p)=1\quad(x\notin\Omega).
$$
The coefficient normalization and finite Parseval identity are proved,
not supplied as analytic assumptions.

For every finite set $X$ of nonnegative integers avoiding $\Omega$ modulo
$p$, **localSieve_prime_energy_lower_bound** proves
$$
 \frac{\nu}{p-\nu}|X|^2
 \le\sum_{a\in(\mathbb Z/p\mathbb Z)^\times}
       \left|\sum_{n\in X}e(an/p)\right|^2.
$$
The theorem includes arbitrary forbidden sets and arbitrary finite $X$.
For the three-form sieve the intended forbidden set is $\{0,t,s\}$.

The local step is now extended to complete squarefree moduli by
[LPFSieveCRT.lean](../PrimeFactorOscillations/Helpers/LPFSieveCRT.lean).
For coprime moduli $m,n$, the map
$(a,b)\mapsto an+bm\pmod{mn}$ is proved bijective, preserves primitive
frequencies, and satisfies the exact phase identity. The coefficient
energies multiply without a loss.

More generally, let $P$ be any finite set of distinct primes, let
$\Omega_p\subseteq\mathbb Z/p\mathbb Z$ have $0<\nu_p<p$, and put
$D=\prod_{p\in P}p$. The theorem **exists_sieveProductCertificate** constructs
coefficients supported on units modulo $D$, with squared norm
$\prod_{p\in P}(p-\nu_p)/\nu_p$, that reconstruct 1 on every integer avoiding
all the forbidden residue sets. The empty set is included: $D=1$ retains
its single zero frequency, which is a unit modulo 1.

For every finite avoiding set $X$,
**sieveProduct_primitive_energy_lower_bound** proves
$$
 \left(\prod_{p\in P}\frac{\nu_p}{p-\nu_p}\right)|X|^2
 \le \sum_{a\in(\mathbb Z/D\mathbb Z)^\times}
       \left|\sum_{n\in X}e(an/D)\right|^2.
$$
Thus the complete local weight is retained for each squarefree modulus.
There is no assumed Fourier certificate or arithmetic distribution estimate.

## Compiled finite arithmetic large sieve

[LPFSieveLevel.lean](../PrimeFactorOscillations/Helpers/LPFSieveLevel.lean)
now sums the exact primitive energies over all distinct subset products.
Let $N,Q\ge1$, let $X\subseteq\{0,\ldots,N-1\}$ avoid the residue sets above,
and define the finite denominator
$$
 L_P(Q)=
 \sum_{\substack{A\subseteq P\\ \prod_{p\in A}p\le Q}}
      \prod_{p\in A}\frac{\nu_p}{p-\nu_p}.
$$
The empty subset contributes 1. Theorems **sieveLevelWeight_card_sq_le**,
**sieveLevelWeight_one_le**, and **sieveLevelWeight_card_le** prove
$$
 L_P(Q)|X|^2\le36(N+Q^2)|X|,\qquad L_P(Q)\ge1,\qquad
 |X|\le\frac{36(N+Q^2)}{L_P(Q)}.
$$
The empty survivor set is included. Distinct prime subsets have distinct
product moduli; all primitive frequencies up to $Q$ are then bounded by
the pinned dependency's additive large sieve. This is a formalization of
the standard arithmetic large-sieve mechanism, without a distribution
hypothesis or an extra logarithmic loss.

## Compiled weighted logarithmic truncation

[LPFSieveDenominator.lean](../PrimeFactorOscillations/Helpers/LPFSieveDenominator.lean)
proves the exact total weight and logarithmic moment. Put
$$
 h_p=\frac{\nu_p}{p-\nu_p},\quad T_P=\prod_{p\in P}(1+h_p),\quad
 \mu_P=\sum_{p\in P}\frac{\nu_p}{p}\log p.
$$
For $d_A=\prod_{p\in A}p$ and $h(A)=\prod_{p\in A}h_p$, the identities are
$$
 \sum_{A\subseteq P}h(A)=T_P,\qquad
 \sum_{A\subseteq P}h(A)\log d_A=T_P\mu_P.
$$
They include the empty subset, whose logarithmic contribution is zero.
For $Q>1$, **sieveLevelWeight_half_le** and **sieve_card_le_euler** give
$$
 \mu_P\le\tfrac12\log Q
 \quad\Longrightarrow\quad
 L_P(Q)\ge\tfrac12T_P,\qquad
 |X|\le\frac{72(N+Q^2)}{T_P}.
$$
The cutoff test is explicit and finite. The proof bounds the weight above
$Q$ jointly through its logarithmic moment; it assumes no distribution of $X$.

[LPFSievePrimeCutoff.lean](../PrimeFactorOscillations/Helpers/LPFSievePrimeCutoff.lean)
now discharges the mean test uniformly. If $P$ is any subset of the primes
at most the integer $z\ge1$, and $\nu_p\le K$ for a natural number $K$, then
$$
 \mu_P\le K(\log z+\log4+4).
$$
This uses the cached, proved first Mertens estimate
$$
 \left|\sum_{p\le z}\frac{\log p}{p}-\log z\right|\le\log4+4.
$$
Consequently, the explicit conditions
$$
 \log z\ge\log4+4,\qquad z^{4K}\le Q
$$
imply $\mu_P\le\tfrac12\log Q$. The theorem
**sieve_card_le_euler_of_prime_cutoff** combines this with the finite sieve.
It has no unproved distribution or logarithmic-mean premise.
For two and three forbidden residues, the powers are respectively 8 and 12;
these are sufficient cutoff choices, not optimal exponents.

## Compiled exact collision factors

[LPFSieveCollisions.lean](../PrimeFactorOscillations/Helpers/LPFSieveCollisions.lean)
proves the local comparisons and their complete product over any finite set
$P$ of primes at least 5. For positive, distinct $t,s$, take
$\Omega_p=\{0,t,s\}\pmod p$ and its actual cardinality $\nu_p$. Then
$$
 \prod_{p\in P}\left(\frac p{p-1}\right)^3
 \le T_P\,g(t)g(s)g(|t-s|).
$$
For the two-root set $\Omega_p=\{0,t\}\pmod p$, with $t>0$, it proves
$$
 \prod_{p\in P}\left(\frac p{p-1}\right)^2
 \le T_P\,g(t).
$$
Both use the maintained full singular divisor product $g$.

At each prime the three-root proof retains every collision: no factors
when the roots are distinct, one factor $(p-1)/(p-2)$ when exactly two
coincide, and three factors when all coincide. The cast-equality lemma
identifies the third collision with divisibility of $(t-s)+(s-t)$, so both
orders of the natural targets are covered. Extending the selected divisor
factors to the full $g$ products requires positive arguments; the hypothesis
$t\ne s$ is retained and no value of $g(0)$ is used.

## Compiled logarithmic sieve bounds

[LPFSieveEuler.lean](../PrimeFactorOscillations/Helpers/LPFSieveEuler.lean)
now supplies the logarithmic Euler-product lower bound and both sieve
consumers. Define the fixed positive constant
$$
 c_{\mathrm M}=\exp\!\left(\mathfrak M-\frac{E_{\mathrm M}}{\log2}-1\right),
 \qquad
 P_z=\{p\text{ prime}:5\le p\le z\},
$$
where $\mathfrak M$ and $E_{\mathrm M}\ge0$ are the proved reciprocal-prime
Mertens constants from the pinned dependency. For every integer $z\ge5$
and every natural $j$, including zero,
$$
 c_{\mathrm M}^{\,j}(\log z)^j
 \le\prod_{p\in P_z}\left(\frac p{p-1}\right)^j.
$$
The omitted primes 2 and 3 are handled explicitly; their reciprocal sum
is $5/6\le1$. The constant is selected before the cutoff and exponent.

Let $X_2,X_3\subseteq\{0,\ldots,N-1\}$ avoid the two- and three-root
residue sets respectively at every prime in $P_z$. Assume $N>0$, $Q>1$,
$z\ge5$, and $\log z\ge\log4+4$. Then the compiled bounds are
$$
 z^8\le Q
 \quad\Longrightarrow\quad
 |X_2|\le\frac{72}{c_{\mathrm M}^2}
       \frac{N+Q^2}{(\log z)^2}\,g(t),
 \qquad t>0,
$$
$$
 z^{12}\le Q
 \quad\Longrightarrow\quad
 |X_3|\le\frac{72}{c_{\mathrm M}^3}
       \frac{N+Q^2}{(\log z)^3}\,g(t)g(s)g(|t-s|),
 \qquad t,s>0,\ t\ne s.
$$
Every local collision factor is retained. These statements have no assumed
distribution estimate or unresolved Fourier/Euler-product premise.

## Compiled bounds for actual prime forms

[LPFSievePrimeForms.lean](../PrimeFactorOscillations/Helpers/LPFSievePrimeForms.lean)
now adds the small forms back exactly. Under the cutoff conditions above,
let $X_2$ be any subset of $\{0,\ldots,N-1\}$ whose members $p$ satisfy
$p$ and $t-p$ prime. Let $X_3$ satisfy $p,t-p,s-p$ prime. Then
$$
 |X_2|\le\frac{72}{c_{\mathrm M}^2}
       \frac{N+Q^2}{(\log z)^2}\,g(t)+2z,
$$
$$
 |X_3|\le\frac{72}{c_{\mathrm M}^3}
       \frac{N+Q^2}{(\log z)^3}\,g(t)g(s)g(|t-s|)+3z.
$$
The hypotheses $t>0$ and, for three forms, $s>0$ and $t\ne s$ are retained.
The primality hypotheses imply the natural subtractions are within their
targets. Each form map is injective on the input set, so forms at most $z$
cost at most $z$ input positions. Overlaps among the small-form exceptions
are permitted by the covering bound. All larger prime forms avoid every
selected residue root, by exact divisibility and the prime divisor theorem.

The input diagonal $p=t-p$ remains allowed. The distinctness condition in
the three-form theorem concerns the two target sums, corresponding to the
off-diagonal energy term.

## Compiled uniform input-scale upper bounds

[LPFSieveScale.lean](../PrimeFactorOscillations/Helpers/LPFSieveScale.lean)
now proves the required scale uniformly in all target sums and counted sets.
For each integer $M$, take the largest integer $z$ such that $z^{24}\le M$,
and put $Q=z^{12}$. Maximality gives $M<(z+1)^{24}$. Beyond the explicit,
conservative threshold $M\ge1024^{24}$, the proof verifies
$$
 Q^2\le M,\qquad
 \log M\le48\log z,\qquad
 2z\le\frac{M}{(\log M)^2},\qquad
 3z\le\frac{M}{(\log M)^3}.
$$
This applies to every input size, with no perfect-power restriction.

Define the fixed positive constants
$$
 C_2=\frac{216\cdot48^2}{c_{\mathrm M}^2}+1,\qquad
 C_3=\frac{216\cdot48^3}{c_{\mathrm M}^3}+1.
$$
For every $M\ge1024^{24}$ and every finite
$X_2,X_3\subseteq\{0,\ldots,M\}$ with the respective prime-form hypotheses,
the compiled results are
$$
 |X_2|\le C_2\frac{M}{(\log M)^2}\,g(t),\qquad t>0,
$$
$$
 |X_3|\le C_3\frac{M}{(\log M)^3}\,g(t)g(s)g(|t-s|),
 \qquad t,s>0,\ t\ne s.
$$
Both constants and the threshold are chosen before the targets and counted
sets. The small-prime allowances are included. The corresponding eventual
statements are **exists_uniform_twoForm_upper_bound** and
**exists_uniform_threeForm_upper_bound**.

## Compiled actual generation inputs

[LPFUpperSieve.lean](../PrimeFactorOscillations/Helpers/LPFUpperSieve.lean)
now installs these counts in the actual all-pairs generation bound.
Put $A_r=\{p\in P_M:t(r)-p\in P_M,\ p\le t(r)\}$ and
$w(p,r)={\bf1}_{A_r}(p)/g(t(r))$. For every $M\ge1024^{24}$,
$$
 \sum_{p\in P_M}w(p,r)^2\le C_2\frac{M}{\log^2M},
 \qquad
 \sum_{p\in P_M}w(p,r)w(p,s)
 \le C_3\frac{M}{\log^3M}g(|t(r)-t(s)|).
$$
The cross bound requires distinct target sums. Injectivity of the actual
cofactor lifts on the next prime window supplies this hypothesis for distinct
target primes. Input diagonals remain allowed. Normalization cancels the two
target singular factors exactly.

The declaration **exists_sieved_fullStep_prefix_bound** chooses a fixed
$C>0$ and proves the following eventual implication. Write
$$
 G=R_M\setminus Z,\quad B=G\setminus\operatorname{fullStep}(S),\quad
 E=|P_M\setminus S|,\quad F=M/\log^4M,
$$
$$
 U=C_2M/\log^2M,\qquad V=C_3M/\log^3M,\qquad R_M=(M,5M/4]\cap\mathbb P.
$$
If $L>0$, $|A_r|/g(t(r))\ge L$ for every $r\in G$, and
$$
 |B|\ge F\ \Longrightarrow\
 8EVC\log\!\left(3+\log\frac{M/\log M}{|B|}\right)\le L^2,
$$
then
$$
 |P_{\lfloor5M/4\rfloor}\setminus\operatorname{fullStep}(S)|
 \le E+|Z|+F+\frac{8EU}{L^2}.
$$
The upper inputs $U,V$ are proved; the positive supply and absorption are
explicit hypotheses of this declaration. A small bound on $|Z|$ is also
needed to obtain a useful growth conclusion. The absorption and conditional
iteration are now proved in the maintained modules below. The positive
representation source, controlled exceptional set, and density entry for the
actual $\{2\}$ orbit remain open in Lean.

The dynamics retains 2 at every generation through its initial inclusion.
All generated values are odd, so the generating rule cannot produce 2.
This convention removes the parity obstruction; it does not establish that
every odd prime is reachable.

### Compiled dense-fraction absorption

The same module proves **exists_dense_fraction_absorption**. For every
fixed $a,K>0$, there is $\eta>0$ such that
$$
 0<\delta\le\eta,\qquad 1\le z\le16/\delta
 \quad\Longrightarrow\quad
 8\delta K\log(3+\log z)\le a^2.
$$
The constructive proof takes
$$
 \eta=\min\!\left(1,\frac{a^2}{160K}\right)^2.
$$
Its joint estimate is
$x^2\log(3+\log(16/x^2))\le20x$ for $0<x\le1$.
Thus the logarithmic overlap is controlled together with the missing fraction.

For the generation argument, substitute
$\delta=E/(M/\log M)$, $z=(M/\log M)/b$, and $K=C_3C$.
When $E>0$, $E/16\le b\le M/\log M$, and
$E\le\eta M/\log M$, this gives the required scalar absorption coefficient.
The exact rescaling, zero-defect case, and small-failed-set branch are now
proved in [LPFDenseTransfer.lean](../PrimeFactorOscillations/Helpers/LPFDenseTransfer.lean).
The result **exists_dense_fullStep_prefix_recurrence** states: for every
fixed $a>0$, there is $\eta>0$ such that, eventually for every integer $M$
and every finite pair of sets $S,Z$, if
$$
 E=|P_M\setminus S|\le\eta M/\log M,\qquad
 \frac{|A_r|}{g(t(r))}\ge\frac{aM}{\log^2M}
 \quad(r\in R_M\setminus Z),
$$
then
$$
 |P_{\lfloor5M/4\rfloor}\setminus\operatorname{fullStep}(S)|
 \le\frac{17}{16}E+|Z|+\frac{M}{\log^4M}.
$$
No upper-sieve or absorption hypothesis remains in this declaration.
The constants and threshold precede the state and exceptional set.
The proof keeps reusable input diagonals throughout.

If the number $b$ of failed nonexceptional targets is below $M/\log^4M$
or below $E/16$, its contribution already satisfies the conclusion.
Otherwise the complete deletion estimate applies. For $E>0$ the proved
scalar absorption gives
$b\le8C_2\eta\log M/a^2$, contradicting $b\ge M/\log^4M$ eventually.
For $E=0$ the same deletion estimate gives $b\le0$.
The comparison $D\log M<M/\log^4M$ is proved for every fixed real $D$.

This is a conditional arithmetic transfer. A bound
$|Z|\le C_ZM/\log^4M$ and the positive representation input still require
formal proofs. The quantitative iteration is now compiled as described below;
entry for the actual orbit from $\{2\}$ remains unproved.
It does not establish every-prime reachability.

## Compiled bounds for the actual generated states

[LPFDenseIteration.lean](../PrimeFactorOscillations/Helpers/LPFDenseIteration.lean)
defines the exact integer cutoffs
$$
 M_0=M,\qquad M_{j+1}=\lfloor5M_j/4\rfloor
$$
and uses the actual states $S_j=\operatorname{fullOrbit}(S,j)$. Put
$$
 E_j=|P_{M_j}\setminus S_j|,\qquad
 N_j=M_j/\log M_j,\qquad F_j=M_j/\log^4M_j.
$$
The source hypothesis of **exists_fullOrbit_dense_defect_bounds** is explicit:
fixed $a>0,C\ge0$, and eventually an exceptional set $Z_M$ at every cutoff
with $|Z_M|\le CF(M)$ and normalized representations at least
$aM/\log^2M$ for every target outside $Z_M$.

Under this hypothesis the theorem chooses $\eta>0$ and a uniform starting
threshold. For every sufficiently large initial $M$ and every finite seed $S$,
$$
 E_0\le\eta N_0
 \quad\Longrightarrow\quad
 E_j\le\eta N_j,\qquad
 E_j\le(17/16)^jE_0+16(C+1)F_j\quad\hbox{for every }j\ge0.
$$
Both conclusions refer to generated states. The proof includes the exact
floor at every step, shows that all later cutoffs remain above the common
threshold, and applies the positive-source hypothesis separately there.
The scale bounds $N_{j+1}\ge(9/8)N_j$ and $F_{j+1}\ge(9/8)F_j$ and the
fraction-preservation argument are proved.

For the common orbit from $\{2\}$, one may start this argument at a later
generation once it meets the density-entry condition. The compiled
common-orbit and restart lemmas transfer that entry to every seed $\{2,p\}$.
No such qualifying entry for $\{2\}$ has yet been proved.

## Compiled vanishing defect for generated states

[LPFDenseDensity.lean](../PrimeFactorOscillations/Helpers/LPFDenseDensity.lean)
proves **exists_fullOrbit_dense_density_zero** under exactly the representation
source and initial density-entry conditions above. It concludes
$$
 \frac{E_j}{M_j/\log M_j}\longrightarrow0\qquad(j\longrightarrow\infty).
$$
The threshold and positive entry allowance are chosen before the finite seed.
This is a limit for the actual generated states at the expanding cutoffs,
not a limit for an independently sampled prime-pair ensemble.

The proof first establishes $M_j\ge M+j$ for $M\ge4$, hence $M_j\to\infty$.
The geometric floor satisfies
$$
 F_j\ge(17/16)^j(1+j/17)F_0.
$$
Consequently the initial term $(17/16)^jE_0$ is eventually at most $F_j$.
The remaining relative error is bounded by
$[16(C+1)+1]/\log^3M_j$, which tends to zero. These are the actual
comparisons used by the compiled limit proof; no quantitative numerical
starting threshold is asserted.

With the ordinary prime number theorem, this normalized limit gives a
vanishing proportion of missing primes in $P_{M_j}$. That interpretation is
a mathematical consequence; the new Lean declaration states the displayed
$M_j/\log M_j$ normalization directly. Even density one can leave individual
primes permanently missing. The theorem does not prove density entry or
infinitude from $\{2\}$ without its explicit inputs, or every-prime reachability.

## Compiled conversion of the positive weighted source

[LPFGoldbachPrimePowers.lean](../PrimeFactorOscillations/Helpers/LPFGoldbachPrimePowers.lean)
proves prime-power removal and logarithmic unweighting uniformly in the target.
Let $M\ge1$ and $A\subseteq\{1,\ldots,M\}$ be any finite input set with
$1\le t-p\le M$ for every $p\in A$. Define
$$
 b(n)={\bf1}_{n\text{ prime}}\log n,\quad d(n)=\Lambda(n)-b(n),
$$
$$
 W_A(t)=\sum_{p\in A}\Lambda(p)\Lambda(t-p),\quad
 T_A(t)=\sum_{p\in A}b(p)b(t-p).
$$
The exact identity retains both input positions:
$$
 W_A(t)-T_A(t)=\sum_{p\in A}d(p)\Lambda(t-p)
                  +\sum_{p\in A}b(p)d(t-p).
$$
The partner map is injective on the stated domain, including input diagonals.
The compiled Chebyshev bound gives
$$
 0\le W_A(t)-T_A(t)\le4\sqrt M(\log M)^2,
$$
$$
 T_A(t)\le(\log M)^2|\{p\in A:p\text{ and }t-p\text{ are prime}\}|.
$$
**eventually_goldbach_primePower_loss_small** proves, for every fixed $a>0$,
that the full loss is eventually at most $(a/2)M$, using the maintained integer
power cutoff. **eventually_goldbachMangoldt_to_sumPartners** proves the
actual normalized consumer, uniformly in $A$ and $t$:
$$
 W_A(t)\ge aMg(t)\quad\Longrightarrow\quad
 \frac{|\operatorname{sumPartners}(P_M,t)|}{g(t)}
 \ge\frac{a}{2}\frac{M}{\log^2M}.
$$
The weighted main term is an explicit premise; its prime-power loss and
conversion to the actual partner count are proved. No diagonal is discarded
and no distribution property of a generated state is assumed.

The ordinary analytic source is Coppola and Laporta,
[On the representation of even integers as sum of two almost equal primes](https://www.giovannicoppola.name/files/articoli/8_giovanni_coppola_number_theory_seminar_politecnico_torino_245.pdf),
Theorem 1 (1995). Its mean-square estimate applies on $N<t<2N$ when
$N^{5/8+\varepsilon}<U<N$. The planned LPF specialization uses
$U=\lfloor M/64\rfloor$ and $N=\lfloor M/2\rfloor$ or $N=M$.
The interval and squared-error exceptional-set adapters are now proved
below. The weighted analytic theorem and its singular-series normalization
are not yet formalized here.
Seven-eighths Dirichlet nonvanishing alone does not supply this mean-square
bound, and this module does not establish density entry for $\{2\}$.

## Compiled exact source windows and exception transfer

[LPFGoldbachWindows.lean](../PrimeFactorOscillations/Helpers/LPFGoldbachWindows.lean)
proves that every lifted target in the next prime window is even and belongs
to the appropriate strict source interval:

| Owner residue | Cofactor | Sum target | Source interval parameter |
| --- | ---: | --- | --- |
| $r=3\pmod4$ | 1 | $(r+1)/2$ | $N=\lfloor M/2\rfloor$ |
| $r=1\pmod4$ | 3 | $(3r+1)/2$ | $N=M$ |

The width is $U=\lfloor M/64\rfloor$. The compiled raw input window is
$(t/2-U,t/2+U)\cap\mathbb N$. Its reflection under $p\mapsto t-p$
is exact. At an actual lifted target both inputs lie in $\{1,\ldots,M\}$.
Other even targets near the upper endpoint of the source interval may have
inputs above $M$; the mean-square source uses the raw window without clipping.
For $M\ge128^4+1$, the compiled width theorem gives
$M^3<U^4$ and $U<\lfloor M/2\rfloor\le M$, the integer conditions
corresponding to the chosen $5/8+1/8=3/4$ source exponent.

[LPFGoldbachSourceTransfer.lean](../PrimeFactorOscillations/Helpers/LPFGoldbachSourceTransfer.lean)
fixes $c>0,K\ge0$ before $M$ and uses the full error
$$
 e_M(t)=W_M(t)-4Uc\,g(t),\qquad
 W_M(t)=W_{(t/2-U,t/2+U)\cap\mathbb N}(t).
$$
The two analytic premises of **exists_primeTarget_supply_of_goldbach_meanSquare**
are, eventually and separately at $N=\lfloor M/2\rfloor$ and $N=M$,
$$
 \sum_{\substack{N<t<2N\\t\text{ even}}}e_M(t)^2
 \le\frac{KNU^2}{\log^4N}.
$$
These premises are explicit; they are not axioms or newly proved analytic
estimates. The two finite source intervals are disjoint. The proof keeps
the natural half-cutoff and establishes $\log M\le2\log\lfloor M/2\rfloor$.
Thus their complete squared-error sum is at most
$9KMU^2/\log^4M$.

Let $Z_M$ consist of owner primes whose weighted target supply is below
$2Uc\,g(t(r))$. Each bad target contributes at least $4U^2c^2$ to the
squared-error sum. Injectivity of the actual cofactor lifts retains its full
multiplicity. The compiled conclusion is
$$
 |Z_M|\le\frac{9K}{4c^2}\frac{M}{\log^4M},\qquad
 \frac{|\operatorname{sumPartners}(P_M,t(r))|}{g(t(r))}
 \ge\frac{c}{128}\frac{M}{\log^2M}\quad(r\in R_M\setminus Z_M).
$$
The second bound includes the complete prime-power correction and all input
diagonals. These are exactly the two source conditions of the maintained
actual-state recurrence and density-limit theorem. Their composition is a
mathematical consequence of the compiled inputs; the newly audited consumer
itself returns the displayed source conditions.

The remaining analytic task is to prove the two mean-square premises with
the source's positive Euler-product constant, or a stronger uniform bound
that implies them. Density entry for the actual $\{2\}$ orbit and every-prime
reachability remain unproved.

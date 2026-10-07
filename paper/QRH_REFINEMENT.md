# A source-dependent refinement of the compensated quasi-RH probe

**Status: ordinary paper proof, conditional on the analytic results cited below;
not Lean-formalized.** This note derives a slightly stronger boundary from the
estimates stated in OpenAI's September 30, 2026 manuscript. The full proof and
Lean dependency closure of that manuscript have not been independently certified
by this project. Accordingly this note is not advertised as an independently
verified unconditional zero-free theorem.

The source is OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re(s)>7/8*, at
[revision adc7f124](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex).
All named source results and equation labels below refer to that exact text.
The source supplies the arithmetic, theta transformations, moment estimates,
zero detector and continuation mechanism. The contribution of this note is
a change in the compensated probe's scale allocation, including the associated
error estimates.

## Statement

Assume the source's common zero-free theorem with boundary $7/8$, its
reflected-energy and additive-Gram estimates, its marked inverse and plain
fourth-moment estimates, and its stated detector and exact transformation
identities. Then every finite-order Hecke $L$-function over
$K=\mathbb Q(\sqrt{-3})$ has no zero in

$
 \Re s>\sigma_1,\qquad
 \sigma_1=\frac{349999}{400000}=\frac78-\frac1{400000}.
$

Principal poles are excluded from the term *zero*. The source's norm-character
factorization transfers this conclusion to Dirichlet $L$-functions and
$\zeta$.

The new conclusion is conditional on these **existing source estimates**.
No new unproved higher-moment hypothesis is used in its derivation. This is
a small refinement of that source, not a proof of RH.

## 1. Geometry and the unchanged signal

Put

$
 t=\frac1{100000},\quad b=\frac18,\quad
 \ell=\frac16+t,\quad
 l_x=\frac{1-\ell-b}{2},\quad l_y=l_x+b,\quad
 h=1+\ell-l_x.
$

Then $l_x+l_y+\ell=1$, and

$
 h=\frac{13}{16}+\frac{3t}{2},\qquad
 l_x=\frac{17}{48}-\frac t2,\qquad
 l_y=\frac{23}{48}-\frac t2.
$

Use the source's finite compensated probe
`eq:compensated-probe-definition`, with these lengths and a fixed
even number of disjoint prime slots of total length $\ell$.
The local operations and zero masks are unchanged. Slot supports remain at
their original scales in every rescaled summand.

The exact high representation has signal exponent
`eq:stage-mellin-exponent`:

$
 C(s)=s+\frac{l_x}{2}-1+\frac h6=s-\frac{11}{16}.
$

Thus the signal is unchanged, whereas the prospective low exponent is

$
 L=\frac{l_x}{2}+\frac b{12}
   =\frac3{16}-\frac t4=C(\sigma_1).
$

## 2. The rescaled subsets allow the improved low estimate

This is the point where the source's fixed allocation can be relaxed.

For a rescaled subset of slots of total length $d$, write

$
 0\le d\le\ell,\qquad M'=1-\ell-2d,\qquad \ell'=\ell-d.
$

Repeat the proof of the source's compensated completed-row norm, retaining
the unspecialized expression on source lines 8294--8307. The reflected-energy
lemma applies to bounded log-length ranges. Its two branches give, including
arbitrarily small annular and height-independent losses,

$
 \sum_{0<N(m)\ll Q}|B^J_m|^2
 \ll Z^{M'+\frac14(5\ell-1+d)_++\varepsilon}.
 \tag{1}
$

For clarity, the unspecialized numerator is
$1+3\ell'-2M'=5\ell-1+d$. All preceding comparisons in that argument use
$M'+\ell'-1=-3d$, $2A_0\le O+o(1)$, $N_0\le A_0$, and
$z_a\le\ell'$, which continue to hold. The actual dyadic row deficit is
retained until its monotone upper bound is taken. The source's Gaussian
annulus and common-profile arguments apply in the same bounded ranges.

The additive Gram estimate is stated for arbitrary polynomially bounded
$Q,Y'\ge1$. Here

$
 P_a=Y'^2/Q\asymp Z^b,\qquad
 l_y-d-\frac{11b}{6}
 \ge l_y-\ell-\frac{11b}{6}>0.
$

Consequently its bracket
$1+P_a^{1/6}+P_a^2/Y'$ is $O(P_a^{1/6})$.
Cauchy--Schwarz with (1) bounds one separated summand by

$
 Z^{l_x/2+b/12-d/2+(5\ell-1+d)_+/8+\varepsilon}.
$

There are $O(Z^{d+\varepsilon})$ rescaled tuples, and the exact coefficient
has size $O(Z^{-3d/2})$. Their total extra exponent, relative to $L$, is

$
 f_\ell(d)=-d+\frac{(5\ell-1+d)_+}{8}.
$

Since $\ell<1/5$, either the positive part vanishes or it is at most $d$.
Therefore $f_\ell(d)\le0$ for **every** rescaled subset. Summing the fixed
finite set of subsets proves

$
 |I_{\eta,\mathrm{modified}}(Z)|\ll Z^{L+\varepsilon}.
 \tag{2}
$

The other size requirements hold with strict margins:
$M'\ge1-3\ell>0$, $l_x-d\ge l_x-\ell>0$, and $l_y-d>0$.
It is unnecessary to require every individual row norm in (1) to have
zero excess before including its rescaling coefficient.

## 3. Extending the principal Euler region

The source states its second Euler region with $\Re s\ge7/8$.
To use a smaller boundary we must extend that region; this is not an implicit
appeal to continuity.

In its explicit local formulas and table, replace that lower bound by
$s_r\ge87/100$, retaining $w_r\ge19/20$ and $z_r\ge33/200$.
The geometric denominators still satisfy $|R|,|V|,|D|<1$, uniformly away
from one. The local defect formula
`eq:local-H-defect` gives

$
 H_p-1=O(Np^{-181/100})\quad(p\nmid u),\qquad
 H_p-1=O(Np^{-82/100})\quad(p\mid u).
 \tag{3}
$

Indeed the closest good-prime exponents are
$1-s_r-w_r-6z_r\le-181/100$ and
$-s_r-w_r\le-182/100$; the other terms in the table and defect formula are
smaller. At a ramified prime the closest term is
$1-s_r-w_r\le-82/100$.

The good-prime product converges normally. For $u=1$, its tail after the
fixed cutoff $P_0$ is $O(P_0^{-81/100})$, so $P_0$ can be fixed to make
the principal correction $H_\eta(s)$ satisfy
$|H_\eta(s)-1|\le1/2$ throughout $\Re s>87/100$.

The four principal compensation error exponents, listed in the source at
lines 9066--9069, are

$
 -s_r,\quad -6z_r,\quad 4-5s_r-6z_r,\quad 1-w_r-6z_r.
$

All are at most $-87/100$ on the enlarged region. Thus
$\mathcal B_p=-1+O(Np^{-87/100})$. The principal prime-slot normalizer remains
nonzero and of size a fixed power of $(\log Z)^{-1}$. Its relative
approximation error has a fixed positive power saving because each slot
length is positive.

The source's principal-residue proof now applies verbatim with this enlarged
region: its use of $7/8$ is to keep the contour in the second Euler region.
The residue locations $w=1,z=1/6$, the factor $1/6$, and the signal
$C(s)$ are unchanged. The two geometric error savings remain
$l_y/20>0$ and $h/600>0$.

For the small-row contour $s_r=\beta_*+e,w_r=1/2,z_r=17/50$, use
$\epsilon_0=1/3$ in the first Euler region, rather than $3/8$.
All selected good-prime error exponents remain negative when
$\beta_*\ge\sigma_1>87/100$; the selected ramified-prime bound remains
$G_p\ll Np^{1/2}$. Thus the absolute small-row tuple estimate also persists.

## 4. Row counts under the already available $7/8$ theorem

Suppose, for contradiction, that the common zero supremum satisfies

$
 \sigma_1<\beta_*\le7/8.
$

Use the source's plain-moment lemma with the **fixed** admissible parameter
$\kappa=3/4$. Its zero-free hypothesis
$\beta_*\le(1+\kappa)/2$ is satisfied. We do not substitute
$2\beta_*-1<3/4$ into a theorem whose domain excludes that value.

The detector still applies since $\beta_*>51/100$. For a nonfloor bin put
$\delta=2a-1$, so $1/50<\delta\le3/4$, and let $q=x\delta$, $0\le x\le1/2$.
The proof of the source's row-count proposition, using its inverse and plain
moment estimates, now has the baseline plain capacity $2(1-2m)/9$ exactly.
Its $\Delta/4$ capacity surcharge is zero. Repeating its two affine
comparisons therefore gives

$
 R=R_*(\delta,x)+\varepsilon,
$

where, with $\alpha=5/6$,

$
 D_x=3-\frac{17x}{9},\quad P_x=(2-\tfrac{8x}{9})(1-x),\quad
 \mathcal J=(\alpha-\delta)D_x+\delta P_x,
$
$
 R_*=1-\delta+
       \frac{(\alpha-\delta)\delta P_x}{2\mathcal J}.
$

The source's balancing and witness inequalities require no hypothesis
$\beta_*>7/8$ beyond the moment capacity now supplied by $\kappa=3/4$.
In particular $P_x\le D_x$ and $\mathcal J>0$ give
$1-\delta\le R_*\le1$.

Prime supply is sufficient: $\ell/h>1/5>7/37$, and a small fixed extension
to $d\le h+\zeta$ preserves it. Choose a sufficiently fine fixed slot mesh.
As in the source, only $d\ge1/2$ uses selected slots in a moment estimate.
All physical slots remain in the correction in every range.

## 5. Complete high-exponent comparison

Retaining the same central contour $z_r=17/50$, the raw high exponent
relative to $C(\sigma_1)$ is

$
 E_t(d)=a-\sigma_1+h(\tfrac{17}{50}-\tfrac16)
       -a l_y-(1-a)\ell-(\delta/2-q)\ell
       +d(R+\delta/2-\tfrac{17}{50}).
 \tag{4}
$

This follows directly from the outside powers in the exact high identity and
the source's local compensation bounds. At $d=h$, its derivative with
respect to $t$, with $\delta,q,R$ fixed, is

$
 \frac{d}{dt}E_t(h_t)=\delta-\frac14+q+\frac32R
 \le\frac{19}{8}.
$

The source's compensated endpoint certificate, on the larger range
$0\le\delta\le5/6$, $0\le x\le1/2$, gives

$
 E_0(h_0)\le-\frac{49}{440640}.
$

It follows that the adaptive nonfloor bins satisfy

$
 E_t(h_t)\le-\frac{49}{440640}+\frac{19t}{8}<0.
 \tag{5}
$

The exact positive remaining margin is
$96337/1101600000$. The slope in $d$ is positive and smaller than two.
Choose $\zeta>0$ sufficiently small; extending to $h+\zeta$ costs at most
$2\zeta$.

The other ranges are controlled separately:

| Range | Source error-free margin | Maximum extra cost from this change |
|---|---:|---:|
| Floor bin at $d=h$ | $7/1200$ | $2t$ |
| $1/100\le d\le1/2$, including floor | $49/14400$ | $t$ |
| Small rows $d<1/100$, relative to $C(\beta_*)$ | $63/800$ | $51t/100$ |
| Principal $w$- and $z$-remainders | $l_y/20,\ h/600$ | retained directly |

For the floor use $R=1,\delta=1/50,q\le1/100$ in (4).
For intermediate rows use $R=76/75-2\delta/3$, whose slope is positive;
the derivative at $d=1/2$ is $1/100+a/2+q<1$.
The small-row margin comes from
$h(17/50-1/6)-l_y/2+2/100$, whose derivative is $51/100$.
All margins in the table remain positive.

The large-row estimate is unchanged in form:

$
 \sum_{U>Z^{h+\zeta}}|\mathscr R_\eta(U;Z)|
 \ll Z^{B_0+(h+\zeta)(1+\varepsilon)-\zeta z_\infty+\varepsilon}.
$

Fixing $z_\infty$ sufficiently large gives any required saving.
The relevant all-height correction bounds hold on these unchanged absolute
contours.

## 6. Completion and order of choices

All ideal high margins are strictly positive. Fix $\zeta$, the real
moment/detector losses, capacity decrements, and a sufficiently fine fixed
slot mesh within these margins. The number of slots may depend on those
choices but is fixed before $Z$ tends to infinity.

Set $\Delta_1=\beta_*-\sigma_1>0$. Reserve a positive fraction of
$\Delta_1$ for the low estimate (2) and its logarithmic normalizer.
For each fixed target character, choose the height exponent after the internal
seminorm orders, following the source's late-height closure. Then choose the
external tail orders and the eventual threshold. The power margins are
independent of the target; constants and thresholds may depend on it.

For the same normalized physical probe and its principal Mellin signal this
gives

$
 |J_\eta(Z)|\ll_\eta Z^{C(\sigma_1)+\omega},
 \qquad 0<\omega<\Delta_1,
$
$
 |J_\eta(Z)-f_\eta(Z)|\ll_\eta Z^{C(\beta_*)-\sigma}
 \qquad\text{for some common }\sigma>0.
$

The principal correction is holomorphic and bounded away from zero on
$\Re s>\sigma_1$ by (3). The source's continuation-from-a-common-signal
proposition, whose boundary parameter is variable, contradicts
$\beta_*>\sigma_1$. This proves the stated conditional refinement.

## Verification and interpretation

[The exact arithmetic checker](verification/check_qrh_refinement.py) verifies
the rational scale identities, every displayed numerical margin, the local
Euler exponent comparisons, and the polynomial identity underlying the
source's endpoint certificate. Its saved result is
[qrh-refinement-check.json](verification/qrh-refinement-check.json).

The checker does not verify the source's analytic theorems. The proof above
is an ordinary derivation from those explicitly identified inputs. There is
no corresponding new Lean declaration, no claim that the project's existing
Lean build verifies this note, and no change to the project's Lean toolchain.

The improvement is small. Increasing the prime-slot length indefinitely is
not justified by this calculation. A route to RH would require stronger
control of the exact signed nonresonant higher moments or another substantive
analytic improvement.

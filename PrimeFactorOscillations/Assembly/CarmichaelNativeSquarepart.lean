/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelNativeHyperbola
import PrimeFactorOscillations.Assembly.CarmichaelSquarepartCancellation

/-!
# Exact native square-part coefficients

The rational square norms carry the nonprincipal squared-character companion
with the exact Mobius-square support. Any cube divisor annihilates the native
coefficient. The full pointwise square-part formula treats overlaps as zero,
without deleting inert or ramified prime-square terms by assumption.
The exact finite reconstruction retains every companion row and both cross
masks for the original rational unit, without a symmetry premise. The remaining
signed small-square estimate and full reciprocal-L Abel consumer remain open.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelNativeSquarepart

open OAI.ShortDraftHeckeBridge

private theorem squarepart_prime_value {q p : Nat}
    (chi : DirichletCharacter Complex q) (hp : Nat.Prime p) :
    baseChangeChar (chi ^ 2) (p : ZMod (q * 3)) =
      chi (p : ZMod q) * baseChangeChar chi (p : ZMod (q * 3)) := by
  rw [baseChangeChar_prime_apply _ hp, baseChangeChar_prime_apply _ hp,
    pow_two, MulChar.mul_apply]
  ring

/-- All rational square norms retain exactly the squared-character companion. -/
theorem native_square_coeff {q : Nat} (chi : DirichletCharacter Complex q)
    (n : Nat) (hn : 0 < n) :
    normFiberCoeff (baseChangeWeight chi) (n ^ 2) =
      (ArithmeticFunction.moebius n : Complex) ^ 2 *
        baseChangeChar (chi ^ 2) (n : ZMod (q * 3)) := by
  classical
  let F : ArithmeticFunction Complex :=
    toArithmeticFunction (fun k => normFiberCoeff (baseChangeWeight chi) (k ^ 2))
  let M : ArithmeticFunction Complex := ArithmeticFunction.moebius
  let K : ArithmeticFunction Complex :=
    toArithmeticFunction (fun k => baseChangeChar (chi ^ 2) (k : ZMod (q * 3)))
  let R : ArithmeticFunction Complex := (M.pmul M).pmul K
  have hF : F.IsMultiplicative := by
    constructor
    . change normFiberCoeff (baseChangeWeight chi) (1 ^ 2) = 1
      rw [one_pow, normFiberCoeff_baseChangeWeight_one]
    . intro m k hcop
      by_cases hm : m = 0
      . subst m
        simp [F, toArithmeticFunction]
      by_cases hk : k = 0
      . subst k
        simp [F, toArithmeticFunction]
      change (if m * k = 0 then 0 else
          normFiberCoeff (baseChangeWeight chi) ((m * k) ^ 2)) =
        (if m = 0 then 0 else normFiberCoeff (baseChangeWeight chi) (m ^ 2)) *
          (if k = 0 then 0 else normFiberCoeff (baseChangeWeight chi) (k ^ 2))
      rw [ite_eq_right (mul_ne_zero hm hk), ite_eq_right hm, ite_eq_right hk, mul_pow]
      exact baseChange_normFiber_mul chi _ _ (hcop.pow 2 2)
  have hM : M.IsMultiplicative := ArithmeticFunction.isMultiplicative_moebius.intCast
  have hK : K.IsMultiplicative :=
    (baseChangeChar (chi ^ 2)).isMultiplicative_toArithmeticFunction
  have hR : R.IsMultiplicative := (hM.pmul hM).pmul hK
  have hFR : F = R := by
    apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers F hF R hR).mpr
    intro p i hp
    have hp0 : Not (p = 0) := hp.ne_zero
    have hpi0 : Not (p ^ i = 0) := pow_ne_zero i hp0
    change (if p ^ i = 0 then 0 else
        normFiberCoeff (baseChangeWeight chi) ((p ^ i) ^ 2)) =
      ((ArithmeticFunction.moebius (p ^ i) : Complex) *
        (ArithmeticFunction.moebius (p ^ i) : Complex)) *
        (if p ^ i = 0 then 0 else
          baseChangeChar (chi ^ 2) ((p ^ i : Nat) : ZMod (q * 3)))
    rw [ite_eq_right hpi0, ite_eq_right hpi0]
    by_cases hi0 : i = 0
    . subst i
      simp [normFiberCoeff_baseChangeWeight_one]
    by_cases hi1 : i = 1
    . subst i
      have hmup : ArithmeticFunction.moebius p = -1 := by
        simpa using
          ArithmeticFunction.moebius_apply_prime_pow hp (by decide : Not (1 = 0))
      rw [pow_one, normFiberCoeff_eq_pairAF_prime_sq chi hp, pairAF_prime_sq chi _ hp,
        hmup, squarepart_prime_value chi hp]
      norm_num
    . have hi : 3 <= i * 2 := by omega
      rw [<- pow_mul, normFiberCoeff_baseChangeWeight_prime_pow_ge_three chi hp hi]
      rw [ArithmeticFunction.moebius_apply_prime_pow hp hi0, ite_eq_right hi1]
      simp
  have he := congrArg (fun A : ArithmeticFunction Complex => A n) hFR
  have hn0 : Not (n = 0) := Nat.ne_of_gt hn
  change (if n = 0 then 0 else normFiberCoeff (baseChangeWeight chi) (n ^ 2)) =
    ((ArithmeticFunction.moebius n : Complex) *
      (ArithmeticFunction.moebius n : Complex)) *
      (if n = 0 then 0 else baseChangeChar (chi ^ 2) (n : ZMod (q * 3))) at he
  rw [ite_eq_right hn0, ite_eq_right hn0] at he
  simpa only [pow_two] using he

/-- A coprime square part carries no missing phase or squarefree premise. -/
theorem native_coprime_squarepart {q : Nat}
    (chi : DirichletCharacter Complex q) (r s : Nat)
    (hs : 0 < s) (hcop : Nat.Coprime r s) :
    normFiberCoeff (baseChangeWeight chi) (r * s ^ 2) =
      normFiberCoeff (baseChangeWeight chi) r *
        ((ArithmeticFunction.moebius s : Complex) ^ 2 *
          baseChangeChar (chi ^ 2) (s : ZMod (q * 3))) := by
  rw [baseChange_normFiber_mul chi r (s ^ 2)
    ((Nat.coprime_pow_right_iff (by decide : 0 < 2) r s).mpr hcop),
    native_square_coeff chi s hs]

/-- Cubes cannot occur in any nonzero native coefficient. -/
theorem native_zero_of_cube_dvd {q : Nat}
    (chi : DirichletCharacter Complex q) (n p : Nat)
    (hn : 0 < n) (hp : Nat.Prime p) (hdvd : Dvd.dvd (p ^ 3) n) :
    normFiberCoeff (baseChangeWeight chi) n = 0 := by
  classical
  let F := toArithmeticFunction (normFiberCoeff (baseChangeWeight chi))
  have hf : F.IsMultiplicative := baseChange_normFiber_isMultiplicative chi
  have hn0 : Not (n = 0) := Nat.ne_of_gt hn
  have hexp : 3 <= n.factorization p := by
    have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero 3 hp.ne_zero) hn0).mpr hdvd
    have hh := hle p
    simpa [Nat.factorization_pow, hp.factorization] using hh
  have hmem : Membership.mem n.factorization.support p :=
    Finsupp.mem_support_iff.mpr (by omega)
  have hlocal : F (p ^ n.factorization p) = 0 := by
    change (if p ^ n.factorization p = 0 then 0 else
      normFiberCoeff (baseChangeWeight chi) (p ^ n.factorization p)) = 0
    rw [ite_eq_right (pow_ne_zero _ hp.ne_zero),
      normFiberCoeff_baseChangeWeight_prime_pow_ge_three chi hp hexp]
  have hfac := ArithmeticFunction.IsMultiplicative.multiplicative_factorization F hf hn0
  have hFn : F n = normFiberCoeff (baseChangeWeight chi) n := by
    change (if n = 0 then 0 else normFiberCoeff (baseChangeWeight chi) n) = _
    rw [ite_eq_right hn0]
  rw [<- hFn, hfac]
  change n.factorization.support.prod (fun r => F (r ^ n.factorization r)) = 0
  exact Finset.prod_eq_zero hmem hlocal

/-- The complete square-part formula includes every overlap as an exact zero. -/
theorem native_squarepart_formula {q : Nat}
    (chi : DirichletCharacter Complex q) (r s : Nat)
    (hr : 0 < r) (hs : 0 < s) :
    normFiberCoeff (baseChangeWeight chi) (r * s ^ 2) =
      if Nat.Coprime r s then
        normFiberCoeff (baseChangeWeight chi) r *
          ((ArithmeticFunction.moebius s : Complex) ^ 2 *
            baseChangeChar (chi ^ 2) (s : ZMod (q * 3)))
      else 0 := by
  by_cases hcop : Nat.Coprime r s
  . rw [ite_eq_left hcop]
    exact native_coprime_squarepart chi r s hs hcop
  . rw [ite_eq_right hcop]
    have hg : Not (Nat.gcd r s = 1) := by
      intro h
      exact hcop (Nat.coprime_iff_gcd_eq_one.mpr h)
    choose p hp using Nat.exists_prime_and_dvd hg
    have hpr : Dvd.dvd p r := dvd_trans hp.2 (Nat.gcd_dvd_left r s)
    have hps : Dvd.dvd p s := dvd_trans hp.2 (Nat.gcd_dvd_right r s)
    choose u hu using hpr
    choose v hv using hps
    have hcube : Dvd.dvd (p ^ 3) (r * s ^ 2) :=
      Exists.intro (u * v ^ 2) (by rw [hu, hv]; ring)
    exact native_zero_of_cube_dvd chi (r * s ^ 2) p
      (Nat.mul_pos hr (pow_pos hs 2)) hp.1 hcube

/-- The complete finite square-part domain; only the first factor is filtered squarefree. -/
def squarepartPairs (N : Nat) : Finset (Prod Nat Nat) := by
  classical
  exact (((Finset.Icc 1 N).filter (fun r => Squarefree r)).product
    (Finset.Icc 1 (Nat.sqrt N))).filter (fun rs => rs.1 * rs.2 ^ 2 <= N)

/-- The native coefficient after keeping the square-part phase and every overlap. -/
def squarepartCoefficient {q : Nat} (chi : DirichletCharacter Complex q)
    (r s : Nat) : Complex :=
  if Nat.Coprime r s then
    normFiberCoeff (baseChangeWeight chi) r *
      ((ArithmeticFunction.moebius s : Complex) ^ 2 *
        baseChangeChar (chi ^ 2) (s : ZMod (q * 3)))
  else 0

private theorem squarepartPairs_mem (N r s : Nat) :
    Membership.mem (squarepartPairs N) (r, s) <->
      (((1 <= r /\ r <= N) /\ Squarefree r) /\
        (1 <= s /\ s <= Nat.sqrt N)) /\ r * s ^ 2 <= N := by
  classical
  constructor
  . intro h
    have hh := Finset.mem_filter.mp h
    have hp := Finset.mem_product.mp hh.1
    have hr := Finset.mem_filter.mp hp.1
    exact And.intro
      (And.intro (And.intro (Finset.mem_Icc.mp hr.1) hr.2)
        (Finset.mem_Icc.mp hp.2)) hh.2
  . intro h
    apply Finset.mem_filter.mpr
    refine And.intro ?_ h.2
    apply Finset.mem_product.mpr
    exact And.intro
      (Finset.mem_filter.mpr (And.intro (Finset.mem_Icc.mpr h.1.1.1) h.1.1.2))
      (Finset.mem_Icc.mpr h.1.2)

private theorem squarepart_unique (r s u v : Nat)
    (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v)
    (hrsf : Squarefree r) (husf : Squarefree u)
    (he : r * s ^ 2 = u * v ^ 2) : r = u /\ s = v := by
  have hs2 : Dvd.dvd (s ^ 2) (v ^ 2 * u) :=
    Exists.intro r (by nlinarith [he])
  have hv2 : Dvd.dvd (v ^ 2) (s ^ 2 * r) :=
    Exists.intro u (by nlinarith [he])
  have hsv : Dvd.dvd s v :=
    (CarmichaelSquarepartCancellation.square_dvd_square_mul_squarefree_iff
      v u s (Nat.ne_of_gt hv) (Nat.ne_of_gt hu) husf).mp hs2
  have hvs : Dvd.dvd v s :=
    (CarmichaelSquarepartCancellation.square_dvd_square_mul_squarefree_iff
      s r v (Nat.ne_of_gt hs) (Nat.ne_of_gt hr) hrsf).mp hv2
  have hsame : s = v := Nat.dvd_antisymm hsv hvs
  have hrsame : r = u := by
    rw [<- hsame] at he
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hs 2) he
  exact And.intro hrsame hsame

private theorem squarepart_sum_bij (N : Nat) (F : Nat -> Complex) :
    (Finset.Icc 1 N).sum F =
      (squarepartPairs N).sum (fun rs => F (rs.1 * rs.2 ^ 2)) := by
  classical
  symm
  apply Finset.sum_bij (fun rs _ => rs.1 * rs.2 ^ 2)
  . intro rs hrs
    have h := (squarepartPairs_mem N rs.1 rs.2).mp hrs
    exact Finset.mem_Icc.mpr
      (And.intro (Nat.mul_pos h.1.1.1.1 (pow_pos h.1.2.1 2)) h.2)
  . intro rs hrs uv huv he
    have h := (squarepartPairs_mem N rs.1 rs.2).mp hrs
    have k := (squarepartPairs_mem N uv.1 uv.2).mp huv
    have hsame := squarepart_unique rs.1 rs.2 uv.1 uv.2
      h.1.1.1.1 h.1.2.1 k.1.1.1.1 k.1.2.1 h.1.1.2 k.1.1.2 he
    exact Prod.ext hsame.1 hsame.2
  . intro n hn
    have h := Finset.mem_Icc.mp hn
    choose r hr using Nat.sq_mul_squarefree_of_pos h.1
    choose s hs using hr
    have hrpos : 0 < r := hs.1
    have hspos : 0 < s := hs.2.1
    have hprod : r * s ^ 2 = n := by
      rw [Nat.mul_comm]
      exact hs.2.2.1
    have hrN : r <= N :=
      (Nat.le_of_dvd h.1 (Exists.intro (s ^ 2) hprod.symm)).trans h.2
    have hs2N : s ^ 2 <= N :=
      (Nat.le_of_dvd h.1 (Exists.intro r hs.2.2.1.symm)).trans h.2
    have hsN : s <= Nat.sqrt N := Nat.le_sqrt.mpr (by nlinarith)
    have hmem : Membership.mem (squarepartPairs N) (r, s) :=
      (squarepartPairs_mem N r s).mpr
        (And.intro
          (And.intro (And.intro (And.intro hrpos hrN) hs.2.2.2)
            (And.intro hspos hsN))
          (hprod.le.trans h.2))
    exact Exists.intro (r, s) (Exists.intro hmem hprod)
  . intro rs _
    rfl

/-- Exact finite native square-part transfer for every complex weight, including N=0. -/
theorem native_squarepart_sum {q : Nat} (chi : DirichletCharacter Complex q)
    (N : Nat) (W : Nat -> Complex) :
    (Finset.Icc 1 N).sum
        (fun n => normFiberCoeff (baseChangeWeight chi) n * W n) =
      (squarepartPairs N).sum (fun rs =>
        squarepartCoefficient chi rs.1 rs.2 * W (rs.1 * rs.2 ^ 2)) := by
  rw [squarepart_sum_bij]
  apply Finset.sum_congr rfl
  intro rs hrs
  have h := (squarepartPairs_mem N rs.1 rs.2).mp hrs
  rw [native_squarepart_formula chi rs.1 rs.2 h.1.1.1.1 h.1.2.1]
  by_cases hcop : Nat.Coprime rs.1 rs.2
  . simp only [squarepartCoefficient, ite_eq_left hcop]
  . simp only [squarepartCoefficient, ite_eq_right hcop, zero_mul]

/-- Both finite columns transfer with every complex phase and compensation in the kernel. -/
theorem native_squarepart_bilinear {q : Nat}
    (chi : DirichletCharacter Complex q) (N M : Nat) (K : Nat -> Nat -> Complex) :
    (Finset.Icc 1 N).sum (fun n => (Finset.Icc 1 M).sum (fun m =>
      normFiberCoeff (baseChangeWeight chi) n *
        star (normFiberCoeff (baseChangeWeight chi) m) * K n m)) =
      (squarepartPairs N).sum (fun rs => (squarepartPairs M).sum (fun uv =>
        squarepartCoefficient chi rs.1 rs.2 *
          star (squarepartCoefficient chi uv.1 uv.2) *
            K (rs.1 * rs.2 ^ 2) (uv.1 * uv.2 ^ 2))) := by
  rw [squarepart_sum_bij]
  apply Finset.sum_congr rfl
  intro rs hrs
  rw [squarepart_sum_bij]
  apply Finset.sum_congr rfl
  intro uv huv
  have h := (squarepartPairs_mem N rs.1 rs.2).mp hrs
  have k := (squarepartPairs_mem M uv.1 uv.2).mp huv
  have hl : normFiberCoeff (baseChangeWeight chi) (rs.1 * rs.2 ^ 2) =
      squarepartCoefficient chi rs.1 rs.2 :=
    native_squarepart_formula chi rs.1 rs.2 h.1.1.1.1 h.1.2.1
  have hr : normFiberCoeff (baseChangeWeight chi) (uv.1 * uv.2 ^ 2) =
      squarepartCoefficient chi uv.1 uv.2 :=
    native_squarepart_formula chi uv.1 uv.2 k.1.1.1.1 k.1.2.1
  rw [hl, hr]

open scoped Classical

/-- Every native square-part pair and every plain companion row, including b=d=1. -/
def squarepartNativePacket {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H N : Nat) (W : Nat -> Nat -> Complex) : Complex :=
  (squarepartPairs N).sum (fun rs => (squarepartPairs N).sum (fun uv =>
    let a := rs.1 * rs.2 ^ 2
    let c := uv.1 * uv.2 ^ 2
    if CarmichaelNativeHyperbola.unitGood H a c then
      squarepartCoefficient chi rs.1 rs.2 *
        star (squarepartCoefficient chi uv.1 uv.2) *
        CarmichaelCompanionCancellation.weightedCompanionPacket
          (baseChangeChar chi) (H * c) (H * a) (N / a) (N / c)
          (CarmichaelCompanionMasks.amplifiedWindow G a (W a))
          (CarmichaelCompanionMasks.amplifiedWindow G c (W c))
    else 0))

/-- The full native packet has an exact square-part reconstruction with all cross masks. -/
theorem full_native_squarepart_packet {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H N : Nat) (W : Nat -> Nat -> Complex) :
    CarmichaelNativeHyperbola.fullNativePacket chi G H N W =
      squarepartNativePacket chi G H N W := by
  classical
  let K : Nat -> Nat -> Complex := fun a c =>
    if CarmichaelNativeHyperbola.unitGood H a c then
      CarmichaelCompanionCancellation.weightedCompanionPacket
        (baseChangeChar chi) (H * c) (H * a) (N / a) (N / c)
        (CarmichaelCompanionMasks.amplifiedWindow G a (W a))
        (CarmichaelCompanionMasks.amplifiedWindow G c (W c))
    else 0
  have hrow : CarmichaelNativeHyperbola.fullNativePacket chi G H N W =
      (Finset.Icc 1 N).sum (fun a => (Finset.Icc 1 N).sum (fun c =>
        normFiberCoeff (baseChangeWeight chi) a *
          star (normFiberCoeff (baseChangeWeight chi) c) * K a c)) := by
    unfold CarmichaelNativeHyperbola.fullNativePacket
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    simp only [K, CarmichaelNativeLowSector.nativeTerm,
      CarmichaelNativeLowSector.nativeCoefficient, mul_ite, mul_zero]
  calc
    _ = _ := hrow
    _ = (squarepartPairs N).sum (fun rs => (squarepartPairs N).sum (fun uv =>
        squarepartCoefficient chi rs.1 rs.2 *
          star (squarepartCoefficient chi uv.1 uv.2) *
            K (rs.1 * rs.2 ^ 2) (uv.1 * uv.2 ^ 2))) :=
      native_squarepart_bilinear chi N N K
    _ = squarepartNativePacket chi G H N W := by
      unfold squarepartNativePacket
      apply Finset.sum_congr rfl
      intro rs _
      apply Finset.sum_congr rfl
      intro uv _
      simp only [K, mul_ite, mul_zero]

/-- The original full rational unit transfers without a phase or symmetry hypothesis. -/
theorem rational_unit_squarepart_packet {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H N : Nat) (W : Nat -> Complex) :
    CarmichaelNativeHyperbola.rationalUnit chi G H N W =
      squarepartNativePacket chi G H N (CarmichaelNativeHyperbola.productWindow W) :=
  (CarmichaelNativeHyperbola.rational_unit_native_packet chi G H N W).trans
    (full_native_squarepart_packet chi G H N (CarmichaelNativeHyperbola.productWindow W))

end PrimeFactorOscillations.CarmichaelNativeSquarepart

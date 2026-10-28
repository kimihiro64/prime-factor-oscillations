/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNormPacket
import PrimeFactorOscillations.Helpers.CubicGaussianWindow

/-!
# Native physical Carmichael norm packet

Proves the rational-period quotient and canonical trace identification,
actual Gaussian Poisson transfer, convergent signed four-Gaussian window,
all four compensation terms and the complete isotropic unit correction.
The native consumers derive split roots from the cubic-label divisibility
hypothesis, with no separate phase, symmetry or root-existence premise.
No arithmetic reciprocal-L bound or estimate of the Abel unit is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelNormPhysical
open OAI OAI.SevenEighths
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss
open ConcreteTraceCRT EisensteinEmbedding CubicSieve
open CubicReciprocalGaussian ProbeRadialMellin
local notation "Eis" => ActualEisensteinCubic.O

theorem coords_eval (a b : Int) : coords (eval a b) = (a, b) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext h.1 h.2

theorem eval_sub (a b c d : Int) :
    eval a b - eval c d = eval (a - c) (b - d) := by
  dsimp [eval]
  push_cast
  ring

theorem eval_nat_mul (q : Nat) (a b : Int) :
    (q : Eis) * eval a b = eval ((q : Int) * a) ((q : Int) * b) := by
  dsimp [eval]
  push_cast
  ring

theorem omega_conj : (starRingEnd Complex) omega3 = -1 - omega3 := by
  simp [omega3, map_ofNat]
  ring

theorem lambda_conj : (starRingEnd Complex) eisLam = -eisLam := by
  change (starRingEnd Complex) (1 + 2 * omega3) = -(1 + 2 * omega3)
  rw [map_add, map_mul]
  simp only [map_one, map_ofNat]
  rw [omega_conj]
  ring

theorem trace_coordinate_fraction (q : Nat) [NeZero q] (a b : Int) :
    ((a : Complex) + (b : Complex) * omega3) /
        ((q : Complex) * eisLam) +
      star (((a : Complex) + (b : Complex) * omega3) /
        ((q : Complex) * eisLam)) = (b : Complex) / (q : Complex) := by
  have hq : Not ((q : Complex) = 0) := Nat.cast_ne_zero.mpr (NeZero.ne q)
  let A : Complex := (a : Complex) + (b : Complex) * omega3
  let D : Complex := (q : Complex) * eisLam
  have hD : Not (D = 0) := mul_ne_zero hq eisLam_ne_zero
  have hsD : Not (star D = 0) := by
    intro h
    apply hD
    have hh := congrArg star h
    simpa only [star_star, star_zero] using hh
  have hDiv : star (A / D) = star A / star D := by
    apply (eq_div_iff hsD).mpr
    change (starRingEnd Complex) (A / D) * (starRingEnd Complex) D =
      (starRingEnd Complex) A
    rw [<- map_mul]
    congr 1
    field_simp [hD]
  change A / D + star (A / D) = (b : Complex) / (q : Complex)
  rw [hDiv]
  change A / D + (starRingEnd Complex) A / (starRingEnd Complex) D = _
  dsimp [A, D]
  simp only [map_add, map_mul, map_intCast, map_natCast, omega_conj, lambda_conj]
  field_simp [hq, eisLam_ne_zero]
  unfold eisLam
  ring

theorem trace_coordinate_character (q : Nat) [NeZero q] (a b : Int) :
    ShortDraftTrace.breveE
      (((a : Complex) + (b : Complex) * omega3) / ((q : Complex) * eisLam)) =
      ZMod.stdAddChar (b : ZMod q) := by
  rw [ZMod.stdAddChar_coe]
  change Complex.exp (2 * (Real.pi : Complex) * Complex.I *
    ((((a : Complex) + (b : Complex) * omega3) / ((q : Complex) * eisLam)) +
      star (((a : Complex) + (b : Complex) * omega3) / ((q : Complex) * eisLam)))) =
    Complex.exp (2 * (Real.pi : Complex) * Complex.I * (b : Complex) / (q : Complex))
  rw [trace_coordinate_fraction]
  congr 1
  ring

theorem trace_quotient_eval (q : Nat) [NeZero q]
    (hq : Not ((q : Eis) = 0)) (a b : Int) :
    (TraceCharacter.traceCharacter (q : Eis) hq)
      (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) (eval a b)) =
      ZMod.stdAddChar (b : ZMod q) := by
  rw [TraceCharacter.traceCharacter_mk, ActualEisensteinCubic.eisEmbedding_eval]
  have hCast : eisEmbedding (q : Eis) = (q : Complex) := map_natCast _ _
  rw [hCast]
  exact trace_coordinate_character q a b


abbrev residueRing (q : Nat) : Type :=
  HasQuotient.Quotient Eis (Ideal.span {(q : Eis)})

theorem quotient_eval_eq_iff (q : Nat) [NeZero q] (a b c d : Int) :
    Ideal.Quotient.mk (Ideal.span {(q : Eis)}) (eval a b) =
        Ideal.Quotient.mk (Ideal.span {(q : Eis)}) (eval c d) <->
      And ((a : ZMod q) = (c : ZMod q)) ((b : ZMod q) = (d : ZMod q)) := by
  constructor
  . intro h
    have hz : Ideal.Quotient.mk (Ideal.span {(q : Eis)})
        (eval (a - c) (b - d)) = 0 := by
      rw [<- eval_sub, map_sub, h, sub_self]
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hDvd := Ideal.mem_span_singleton.mp hm
    choose u hu using hDvd
    have hCoordinates := unique_coordinates (hu.trans
      ((congrArg (fun z : Eis => (q : Eis) * z) (eval_coords u).symm).trans
        (eval_nat_mul q (coords u).1 (coords u).2)))
    have ha : ((a - c : Int) : ZMod q) = 0 := by
      rw [hCoordinates.1]
      push_cast
      simp
    have hb : ((b - d : Int) : ZMod q) = 0 := by
      rw [hCoordinates.2]
      push_cast
      simp
    exact And.intro (sub_eq_zero.mp (by simpa only [Int.cast_sub] using ha))
      (sub_eq_zero.mp (by simpa only [Int.cast_sub] using hb))
  . intro h
    have ha : ((a - c : Int) : ZMod q) = 0 := by
      simpa only [Int.cast_sub] using sub_eq_zero.mpr h.1
    have hb : ((b - d : Int) : ZMod q) = 0 := by
      simpa only [Int.cast_sub] using sub_eq_zero.mpr h.2
    choose A hA using (ZMod.intCast_zmod_eq_zero_iff_dvd (a - c) q).mp ha
    choose B hB using (ZMod.intCast_zmod_eq_zero_iff_dvd (b - d) q).mp hb
    apply sub_eq_zero.mp
    rw [<- map_sub, eval_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    refine Exists.intro (eval A B) ?_
    rw [hA, hB, eval_nat_mul]

def pairResidue (q : Nat) [NeZero q] (u : Prod (ZMod q) (ZMod q)) :
    residueRing q :=
  Ideal.Quotient.mk (Ideal.span {(q : Eis)})
    (eval (u.1.val : Int) (u.2.val : Int))

theorem pairResidue_injective (q : Nat) [NeZero q] :
    Function.Injective (pairResidue q) := by
  intro u v h
  have hh := (quotient_eval_eq_iff q (u.1.val : Int) (u.2.val : Int)
    (v.1.val : Int) (v.2.val : Int)).mp h
  exact Prod.ext (by simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hh.1)
    (by simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hh.2)

theorem pairResidue_surjective (q : Nat) [NeZero q] :
    Function.Surjective (pairResidue q) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro z
  let a := (coords z).1
  let b := (coords z).2
  have hz : eval a b = z := eval_coords z
  refine Exists.intro ((a : ZMod q), (b : ZMod q)) ?_
  change Ideal.Quotient.mk (Ideal.span {(q : Eis)})
    (eval (((a : ZMod q).val) : Int) (((b : ZMod q).val) : Int)) =
      Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z
  rw [<- hz]
  apply (quotient_eval_eq_iff q _ _ _ _).mpr
  constructor <;> simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

def coordinateQuotientEquiv (q : Nat) [NeZero q] :
    Equiv (Prod (ZMod q) (ZMod q)) (residueRing q) :=
  Equiv.ofBijective (pairResidue q)
    (And.intro (pairResidue_injective q) (pairResidue_surjective q))

theorem trace_pairResidue (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (hq : Not ((q : Eis) = 0)) (u v : Prod (ZMod q) (ZMod q)) :
    (TraceCharacter.traceCharacter (q : Eis) hq) (pairResidue q u * pairResidue q v) =
      ZMod.stdAddChar (CubicNormFourier.traceForm u.1 u.2 v.1 v.2) := by
  unfold pairResidue
  rw [<- map_mul, ActualEisensteinCoordinates.eval_mul, trace_quotient_eval]
  apply congrArg ZMod.stdAddChar
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val, CubicNormFourier.traceForm]


def quotientProfile (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (x : residueRing q) : Complex :=
  let u := (coordinateQuotientEquiv q).symm x
  CarmichaelNormPacket.centeredProfile q l ZMod.stdAddChar u.1 u.2

theorem quotientProfile_pairResidue (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (u : Prod (ZMod q) (ZMod q)) :
    quotientProfile q l (pairResidue q u) =
      CarmichaelNormPacket.centeredProfile q l ZMod.stdAddChar u.1 u.2 := by
  change CarmichaelNormPacket.centeredProfile q l ZMod.stdAddChar
      ((coordinateQuotientEquiv q).symm ((coordinateQuotientEquiv q) u)).1
      ((coordinateQuotientEquiv q).symm ((coordinateQuotientEquiv q) u)).2 = _
  rw [Equiv.symm_apply_apply]

theorem quotient_profile_transform (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    [Fintype (residueRing q)] (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (r s : ZMod q) (hrs : Not (r = s)) (hSum : r + s = -1) (hProd : r * s = 1)
    (hq : Not ((q : Eis) = 0)) (w : residueRing q) :
    Finset.univ.sum (fun x : residueRing q =>
      quotientProfile q l x * (TraceCharacter.traceCharacter (q : Eis) hq) (w * x)) =
      (q : Complex) * quotientProfile q l w := by
  let v := (coordinateQuotientEquiv q).symm w
  have hv : pairResidue q v = w := (coordinateQuotientEquiv q).apply_symm_apply w
  have hPoint (u : Prod (ZMod q) (ZMod q)) :
      CarmichaelNormPacket.centeredProfile q l ZMod.stdAddChar u.1 u.2 *
        ZMod.stdAddChar (CubicNormFourier.traceForm u.1 u.2 v.1 v.2) =
      quotientProfile q l ((coordinateQuotientEquiv q) u) *
        (TraceCharacter.traceCharacter (q : Eis) hq)
          (w * (coordinateQuotientEquiv q) u) := by
    rw [<- hv]
    change _ = quotientProfile q l (pairResidue q u) *
      (TraceCharacter.traceCharacter (q : Eis) hq) (pairResidue q v * pairResidue q u)
    rw [quotientProfile_pairResidue, mul_comm (pairResidue q v),
      trace_pairResidue q hq u v]
  have hSumEq := Fintype.sum_equiv (coordinateQuotientEquiv q)
    (fun u : Prod (ZMod q) (ZMod q) =>
      CarmichaelNormPacket.centeredProfile q l ZMod.stdAddChar u.1 u.2 *
        ZMod.stdAddChar (CubicNormFourier.traceForm u.1 u.2 v.1 v.2))
    (fun x : residueRing q => quotientProfile q l x *
      (TraceCharacter.traceCharacter (q : Eis) hq) (w * x)) hPoint
  have hFourier := CarmichaelNormPacket.centered_profile_transform q l hLabel hDiv
    r s hrs hSum hProd ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar q) v.1 v.2
  rw [<- hSumEq]
  change CarmichaelNormPacket.centeredProfileTransform q l ZMod.stdAddChar v.1 v.2 =
    (q : Complex) * CarmichaelNormPacket.centeredProfile q l ZMod.stdAddChar v.1 v.2
  simpa only [ZMod.card] using hFourier

def theta (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (a : Real) : Complex :=
  tsum fun z : Eis =>
    quotientProfile q l (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
      gaussian a (eisEmbedding z)

theorem gaussian_poisson (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (r s : ZMod q) (hrs : Not (r = s)) (hSum : r + s = -1) (hProd : r * s = 1)
    (a : Real) (ha : 0 < a) :
    theta q l a = ((1 / (a * (q : Real)) : Real) : Complex) *
      theta q l (1 / (a * (q : Real) ^ 2)) := by
  have hq : Not ((q : Eis) = 0) := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have : Finite (residueRing q) := finite_quotient_span hq
  let : Fintype (residueRing q) := Fintype.ofFinite _
  have hp := CubicGaussianPair.periodic_gaussian (q : Eis) hq
    (quotientProfile q l) a ha
  simp_rw [quotient_profile_transform q l hLabel hDiv r s hrs hSum hProd hq] at hp
  have hn : norm (eisEmbedding (q : Eis)) ^ 2 = (q : Real) ^ 2 := by
    rw [map_natCast]
    simp
  rw [hn] at hp
  have hSeries :
      (tsum fun z : Eis =>
        ((q : Complex) * quotientProfile q l
          (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z)) *
          gaussian (1 / (a * (q : Real) ^ 2)) (eisEmbedding z)) =
      (q : Complex) * theta q l (1 / (a * (q : Real) ^ 2)) := by
    unfold theta
    rw [<- tsum_mul_left]
    apply tsum_congr
    intro z
    ring
  rw [hSeries] at hp
  have hFactor :
      ((1 / (a * (q : Real) ^ 2) : Real) : Complex) * (q : Complex) =
        ((1 / (a * (q : Real)) : Real) : Complex) := by
    have haC : Not ((a : Complex) = 0) := Complex.ofReal_ne_zero.mpr ha.ne'
    have hqC : Not ((q : Complex) = 0) := Nat.cast_ne_zero.mpr (NeZero.ne q)
    push_cast
    field_simp [haC, hqC]
  change theta q l a = _ at hp
  rw [<- mul_assoc, hFactor] at hp
  exact hp

def compensatedTheta (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (c : Complex) (aAA aAB aBA aBB : Real) : Complex :=
  theta q l aAA - star c * theta q l aAB - c * theta q l aBA +
    c * star c * theta q l aBB

theorem compensated_gaussian_poisson (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (r s : ZMod q) (hrs : Not (r = s)) (hSum : r + s = -1) (hProd : r * s = 1)
    (c : Complex) (aAA aAB aBA aBB : Real)
    (hAA : 0 < aAA) (hAB : 0 < aAB) (hBA : 0 < aBA) (hBB : 0 < aBB) :
    compensatedTheta q l c aAA aAB aBA aBB =
      ((1 / (aAA * (q : Real)) : Real) : Complex) *
        theta q l (1 / (aAA * (q : Real) ^ 2)) -
      star c * (((1 / (aAB * (q : Real)) : Real) : Complex) *
        theta q l (1 / (aAB * (q : Real) ^ 2))) -
      c * (((1 / (aBA * (q : Real)) : Real) : Complex) *
        theta q l (1 / (aBA * (q : Real) ^ 2))) +
      c * star c * (((1 / (aBB * (q : Real)) : Real) : Complex) *
        theta q l (1 / (aBB * (q : Real) ^ 2))) := by
  unfold compensatedTheta
  rw [gaussian_poisson q l hLabel hDiv r s hrs hSum hProd aAA hAA,
    gaussian_poisson q l hLabel hDiv r s hrs hSum hProd aAB hAB,
    gaussian_poisson q l hLabel hDiv r s hrs hSum hProd aBA hBA,
    gaussian_poisson q l hLabel hDiv r s hrs hSum hProd aBB hBB]


private theorem periodic_gaussian_summable (q : Nat) [NeZero q]
    (P : residueRing q -> Complex) (a : Real) (ha : 0 < a) :
    Summable (fun z : Eis =>
      P (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) * gaussian a (eisEmbedding z)) := by
  have hq : Not ((q : Eis) = 0) := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have : Finite (residueRing q) := finite_quotient_span hq
  let : Fintype (residueRing q) := Fintype.ofFinite _
  let B : Real := Finset.univ.sum (fun x : residueRing q => norm (P x))
  have hBound (z : Eis) :
      norm (P (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) * gaussian a (eisEmbedding z)) <=
        B * norm (gaussian a (eisEmbedding z)) := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact Finset.single_le_sum (fun x _ => norm_nonneg (P x)) (Finset.mem_univ _)
  have hs : Summable (fun z : Eis => norm (gaussian a (eisEmbedding z))) := by
    simpa only [div_one] using
      (CubicGaussianUnit.gaussian_lattice_summable a 1 ha (by norm_num)).norm
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hBound (hs.mul_left B)).of_norm

def windowPacket (q : Nat) [NeZero q] (P : residueRing q -> Complex)
    (M : Real) : Complex :=
  tsum fun z : Eis =>
    P (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
      carrierProfile (norm (eisEmbedding z) ^ 2 / M)

private theorem periodic_window_hasSum (q : Nat) [NeZero q]
    (P : residueRing q -> Complex) (M : Real) (hM : 0 < M) :
    HasSum (fun z : Eis =>
      P (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
        carrierProfile (norm (eisEmbedding z) ^ 2 / M))
      (Finset.univ.sum (fun i : Fin 4 => coefficients i *
        tsum (fun z : Eis =>
          P (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
            gaussian (scales i / M) (eisEmbedding z)))) := by
  classical
  let A : Eis -> Complex := fun z => P (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z)
  have hFinite (S : Finset (Fin 4)) :
      HasSum (fun z : Eis => S.sum (fun i =>
        coefficients i * (A z * gaussian (scales i / M) (eisEmbedding z))))
        (S.sum (fun i => coefficients i *
          tsum (fun z : Eis => A z * gaussian (scales i / M) (eisEmbedding z)))) := by
    induction S using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        (hasSum_zero : HasSum (fun _ : Eis => (0 : Complex)) 0)
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      have hh := (periodic_gaussian_summable q P (scales i / M)
        (div_pos (scales_pos i) hM)).hasSum
      change HasSum (fun z : Eis => A z * gaussian (scales i / M) (eisEmbedding z))
        (tsum (fun z : Eis => A z * gaussian (scales i / M) (eisEmbedding z))) at hh
      exact (hh.mul_left (coefficients i)).add ih
  have hPoint (z : Eis) :
      A z * carrierProfile (norm (eisEmbedding z) ^ 2 / M) =
        Finset.univ.sum (fun i : Fin 4 =>
          coefficients i * (A z * gaussian (scales i / M) (eisEmbedding z))) := by
    rw [CubicGaussianWindow.profile_eq_gaussian_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [<- hPoint, A] using hFinite Finset.univ

def physicalKernel (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (M : Real) : Complex :=
  windowPacket q (quotientProfile q l) M

theorem physical_eq_gaussian_sum (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (M : Real) (hM : 0 < M) :
    physicalKernel q l M =
      Finset.univ.sum (fun i : Fin 4 => coefficients i * theta q l (scales i / M)) :=
  (periodic_window_hasSum q (quotientProfile q l) M hM).tsum_eq

theorem physical_anti_reflection (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (r s : ZMod q) (hrs : Not (r = s)) (hSum : r + s = -1) (hProd : r * s = 1)
    (M : Real) (hM : 0 < M) :
    physicalKernel q l M = -((M : Complex) / (q : Complex)) *
      physicalKernel q l ((q : Real) ^ 2 / M) := by
  have hq : 0 < (q : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hDual : 0 < (q : Real) ^ 2 / M := div_pos (sq_pos_of_pos hq) hM
  rw [physical_eq_gaussian_sum q l M hM,
    physical_eq_gaussian_sum q l ((q : Real) ^ 2 / M) hDual]
  calc
    _ = Finset.univ.sum (fun i : Fin 4 => coefficients i *
        (1 / (((scales i / M : Real) : Complex) * (q : Complex)) *
          theta q l (1 / ((scales i / M) * (q : Real) ^ 2)))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg (fun x : Complex => coefficients i * x)
      simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one,
        Complex.ofReal_natCast] using
        gaussian_poisson q l hLabel hDiv r s hrs hSum hProd
          (scales i / M) (div_pos (scales_pos i) hM)
    _ = _ := by
      simpa only [Complex.ofReal_natCast, one_mul, mul_one] using
        CubicGaussianWindow.reciprocal_four_sum (theta q l) M (q : Real) 1

theorem physical_selfdual_zero (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (r s : ZMod q) (hrs : Not (r = s)) (hSum : r + s = -1) (hProd : r * s = 1) :
    physicalKernel q l (q : Real) = 0 := by
  have hq : 0 < (q : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqC : Not ((q : Complex) = 0) := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hDual : (q : Real) ^ 2 / (q : Real) = (q : Real) := by
    field_simp [hq.ne']
  have h := physical_anti_reflection q l hLabel hDiv r s hrs hSum hProd (q : Real) hq
  rw [hDual] at h
  simp only [Complex.ofReal_natCast, div_self hqC, neg_one_mul] at h
  linear_combination (1 / 2 : Complex) * h

def compensatedKernel (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (c : Complex) (MAA MAB MBA MBB : Real) : Complex :=
  physicalKernel q l MAA - star c * physicalKernel q l MAB -
    c * physicalKernel q l MBA + c * star c * physicalKernel q l MBB

theorem compensated_physical_reflection (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (r s : ZMod q) (hrs : Not (r = s)) (hSum : r + s = -1) (hProd : r * s = 1)
    (c : Complex) (MAA MAB MBA MBB : Real)
    (hAA : 0 < MAA) (hAB : 0 < MAB) (hBA : 0 < MBA) (hBB : 0 < MBB) :
    compensatedKernel q l c MAA MAB MBA MBB =
      -((MAA : Complex) / (q : Complex)) *
        physicalKernel q l ((q : Real) ^ 2 / MAA) +
      star c * ((MAB : Complex) / (q : Complex)) *
        physicalKernel q l ((q : Real) ^ 2 / MAB) +
      c * ((MBA : Complex) / (q : Complex)) *
        physicalKernel q l ((q : Real) ^ 2 / MBA) -
      c * star c * ((MBB : Complex) / (q : Complex)) *
        physicalKernel q l ((q : Real) ^ 2 / MBB) := by
  unfold compensatedKernel
  rw [physical_anti_reflection q l hLabel hDiv r s hrs hSum hProd MAA hAA,
    physical_anti_reflection q l hLabel hDiv r s hrs hSum hProd MAB hAB,
    physical_anti_reflection q l hLabel hDiv r s hrs hSum hProd MBA hBA,
    physical_anti_reflection q l hLabel hDiv r s hrs hSum hProd MBB hBB]
  ring


def normalizedQuotientProfile (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (x : residueRing q) : Complex :=
  let u := (coordinateQuotientEquiv q).symm x
  CarmichaelNormPacket.normalizedProfile q l ZMod.stdAddChar
    (CubicNormFourier.normForm u.1 u.2)

def isotropicProfile (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (x : residueRing q) : Complex :=
  let u := (coordinateQuotientEquiv q).symm x
  if CubicNormFourier.normForm u.1 u.2 = 0 then 1 else 0

theorem quotient_profile_unit_normalization (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (x : residueRing q) :
    (q : Complex) * quotientProfile q l x =
      normalizedQuotientProfile q l x - ((q : Complex) - 1) * isotropicProfile q x := by
  let u := (coordinateQuotientEquiv q).symm x
  change (q : Complex) * CarmichaelNormPacket.centeredProfile q l ZMod.stdAddChar u.1 u.2 =
    CarmichaelNormPacket.normalizedProfile q l ZMod.stdAddChar
      (CubicNormFourier.normForm u.1 u.2) -
    ((q : Complex) - 1) * (if CubicNormFourier.normForm u.1 u.2 = 0 then 1 else 0)
  simpa only [ZMod.card] using
    CarmichaelNormPacket.centered_profile_normalization q l ZMod.stdAddChar u.1 u.2

theorem physical_unit_normalization (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (M : Real) (hM : 0 < M) :
    (q : Complex) * physicalKernel q l M =
      windowPacket q (normalizedQuotientProfile q l) M -
        ((q : Complex) - 1) * windowPacket q (isotropicProfile q) M := by
  have hPacket (P : residueRing q -> Complex) :
      HasSum (fun z : Eis =>
        P (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
          carrierProfile (norm (eisEmbedding z) ^ 2 / M))
        (windowPacket q P M) :=
    (periodic_window_hasSum q P M hM).summable.hasSum
  have hCentered := (hPacket (quotientProfile q l)).mul_left (q : Complex)
  have hNormalized := hPacket (normalizedQuotientProfile q l)
  have hIsotropic := (hPacket (isotropicProfile q)).mul_left ((q : Complex) - 1)
  have hPoint (z : Eis) :
      (q : Complex) * (quotientProfile q l
        (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
          carrierProfile (norm (eisEmbedding z) ^ 2 / M)) =
      normalizedQuotientProfile q l (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
          carrierProfile (norm (eisEmbedding z) ^ 2 / M) -
        ((q : Complex) - 1) *
          (isotropicProfile q (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
            carrierProfile (norm (eisEmbedding z) ^ 2 / M)) := by
    calc
      _ = ((q : Complex) * quotientProfile q l
          (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z)) *
            carrierProfile (norm (eisEmbedding z) ^ 2 / M) := by ring
      _ = _ := by
        rw [quotient_profile_unit_normalization]
        ring
  simp_rw [hPoint] at hCentered
  exact hCentered.unique (hNormalized.sub hIsotropic)

def compensatedWindow (q : Nat) [NeZero q] (P : residueRing q -> Complex)
    (c : Complex) (MAA MAB MBA MBB : Real) : Complex :=
  windowPacket q P MAA - star c * windowPacket q P MAB -
    c * windowPacket q P MBA + c * star c * windowPacket q P MBB

theorem compensated_unit_normalization (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (c : Complex) (MAA MAB MBA MBB : Real)
    (hAA : 0 < MAA) (hAB : 0 < MAB) (hBA : 0 < MBA) (hBB : 0 < MBB) :
    (q : Complex) * compensatedKernel q l c MAA MAB MBA MBB =
      compensatedWindow q (normalizedQuotientProfile q l) c MAA MAB MBA MBB -
        ((q : Complex) - 1) *
          compensatedWindow q (isotropicProfile q) c MAA MAB MBA MBB := by
  have h1 := physical_unit_normalization q l MAA hAA
  have h2 := physical_unit_normalization q l MAB hAB
  have h3 := physical_unit_normalization q l MBA hBA
  have h4 := physical_unit_normalization q l MBB hBB
  unfold compensatedKernel compensatedWindow
  linear_combination h1 - star c * h2 - c * h3 + (c * star c) * h4

theorem split_roots_of_three_dvd (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (hThree : Dvd.dvd 3 (Monoid.exponent (Units (ZMod q)))) :
    exists r s : ZMod q, Not (r = s) /\ r + s = -1 /\ r * s = 1 := by
  have : Fact (Nat.Prime 3) := Fact.mk (by decide)
  have hCard : Dvd.dvd 3 (Fintype.card (Units (ZMod q))) :=
    hThree.trans Group.exponent_dvd_card
  choose u hu using exists_prime_orderOf_dvd_card (G := Units (ZMod q)) 3 hCard
  let r : ZMod q := u
  have hCube : r ^ 3 = 1 := by
    have hh : u ^ 3 = 1 := by
      rw [<- hu]
      exact pow_orderOf_eq_one u
    exact congrArg Units.val hh
  have hNonzero : Not (r = 0) := Units.ne_zero u
  have hOne : Not (r = 1) := by
    intro h
    have huOne : u = 1 := Units.ext h
    rw [huOne, orderOf_one] at hu
    norm_num at hu
  have hFactor : (r - 1) * (r ^ 2 + r + 1) = 0 := by
    calc
      _ = r ^ 3 - 1 := by ring
      _ = 0 := by rw [hCube]; ring
  have hQuad : r ^ 2 + r + 1 = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left (sub_ne_zero.mpr hOne)
  have hSum : r + r ^ 2 = -1 := by linear_combination hQuad
  have hProd : r * r ^ 2 = 1 := by
    calc
      _ = r ^ 3 := by ring
      _ = 1 := hCube
  have hDistinct : Not (r = r ^ 2) := by
    intro h
    have hz : r * (r - 1) = 0 := by linear_combination -h
    exact hOne (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hNonzero))
  exact Exists.intro r (Exists.intro (r ^ 2)
    (And.intro hDistinct (And.intro hSum hProd)))

theorem native_gaussian_poisson (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (a : Real) (ha : 0 < a) :
    theta q l a = ((1 / (a * (q : Real)) : Real) : Complex) *
      theta q l (1 / (a * (q : Real) ^ 2)) := by
  have hThree : Dvd.dvd 3 (Monoid.exponent (Units (ZMod q))) := by
    simpa only [hLabel] using hDiv
  choose r s hrs hSum hProd using split_roots_of_three_dvd q hThree
  exact gaussian_poisson q l hLabel hDiv r s hrs hSum hProd a ha

theorem native_physical_anti_reflection (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (M : Real) (hM : 0 < M) :
    physicalKernel q l M = -((M : Complex) / (q : Complex)) *
      physicalKernel q l ((q : Real) ^ 2 / M) := by
  have hThree : Dvd.dvd 3 (Monoid.exponent (Units (ZMod q))) := by
    simpa only [hLabel] using hDiv
  choose r s hrs hSum hProd using split_roots_of_three_dvd q hThree
  exact physical_anti_reflection q l hLabel hDiv r s hrs hSum hProd M hM

theorem native_compensated_physical_reflection (q : Nat) [NeZero q]
    [Fact (Nat.Prime q)] (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (c : Complex) (MAA MAB MBA MBB : Real)
    (hAA : 0 < MAA) (hAB : 0 < MAB) (hBA : 0 < MBA) (hBB : 0 < MBB) :
    compensatedKernel q l c MAA MAB MBA MBB =
      -((MAA : Complex) / (q : Complex)) *
        physicalKernel q l ((q : Real) ^ 2 / MAA) +
      star c * ((MAB : Complex) / (q : Complex)) *
        physicalKernel q l ((q : Real) ^ 2 / MAB) +
      c * ((MBA : Complex) / (q : Complex)) *
        physicalKernel q l ((q : Real) ^ 2 / MBA) -
      c * star c * ((MBB : Complex) / (q : Complex)) *
        physicalKernel q l ((q : Real) ^ 2 / MBB) := by
  have hThree : Dvd.dvd 3 (Monoid.exponent (Units (ZMod q))) := by
    simpa only [hLabel] using hDiv
  choose r s hrs hSum hProd using split_roots_of_three_dvd q hThree
  exact compensated_physical_reflection q l hLabel hDiv r s hrs hSum hProd
    c MAA MAB MBA MBB hAA hAB hBA hBB

end PrimeFactorOscillations.CarmichaelNormPhysical

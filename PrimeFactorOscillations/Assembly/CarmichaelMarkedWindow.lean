/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNormPhysical
import PrimeFactorOscillations.Helpers.CarmichaelSeed

/-!
# Marked native Carmichael physical rows

The full Euler and Mobius packets multiply a native profile by unit marks.
Actual Fourier transfer inverts each mark; no individual marked row is
assumed phase balanced or symmetric. All compensation coefficients remain.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelMarkedWindow
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT EisensteinEmbedding CubicSieve
open CubicReciprocalGaussian ProbeRadialMellin CarmichaelNormPhysical
local notation "Eis" => ActualEisensteinCubic.O

def unitDilation (q : Nat) [NeZero q] (A : Units (residueRing q)) :
    Equiv (residueRing q) (residueRing q) where
  toFun := fun x => A.val * x
  invFun := fun x => A.inv * x
  left_inv := fun x => by
    change A.inv * (A.val * x) = x
    rw [<- mul_assoc, A.inv_val, one_mul]
  right_inv := fun x => by
    change A.val * (A.inv * x) = x
    rw [<- mul_assoc, A.val_inv, one_mul]

def markedProfile (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (A : Units (residueRing q)) (x : residueRing q) : Complex :=
  quotientProfile q l (A.val * x)

theorem markedProfile_one (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (x : residueRing q) :
    markedProfile q l 1 x = quotientProfile q l x := by
  change quotientProfile q l ((1 : residueRing q) * x) = _
  rw [one_mul]

theorem markedProfile_mul (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (A B : Units (residueRing q)) (x : residueRing q) :
    markedProfile q l (A * B) x = markedProfile q l A (B.val * x) := by
  change quotientProfile q l ((A.val * B.val) * x) =
    quotientProfile q l (A.val * (B.val * x))
  rw [mul_assoc]

theorem marked_quotient_transform (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    [Fintype (residueRing q)] (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hq : Not ((q : Eis) = 0)) (A : Units (residueRing q)) (w : residueRing q) :
    Finset.univ.sum (fun x : residueRing q =>
      markedProfile q l A x * (TraceCharacter.traceCharacter (q : Eis) hq) (w * x)) =
      (q : Complex) * markedProfile q l (Inv.inv A : Units (residueRing q)) w := by
  let e := unitDilation q A
  have hPoint (x : residueRing q) :
      markedProfile q l A x * (TraceCharacter.traceCharacter (q : Eis) hq) (w * x) =
      quotientProfile q l (e x) *
        (TraceCharacter.traceCharacter (q : Eis) hq) ((A.inv * w) * e x) := by
    change quotientProfile q l (A.val * x) *
        (TraceCharacter.traceCharacter (q : Eis) hq) (w * x) =
      quotientProfile q l (A.val * x) *
        (TraceCharacter.traceCharacter (q : Eis) hq) ((A.inv * w) * (A.val * x))
    have hMul : (A.inv * w) * (A.val * x) = w * x := by
      calc
        _ = (A.inv * A.val) * (w * x) := by ring
        _ = _ := by rw [A.inv_val, one_mul]
    rw [hMul]
  have hs := Fintype.sum_equiv e
    (fun x : residueRing q =>
      markedProfile q l A x * (TraceCharacter.traceCharacter (q : Eis) hq) (w * x))
    (fun x : residueRing q =>
      quotientProfile q l x * (TraceCharacter.traceCharacter (q : Eis) hq) ((A.inv * w) * x))
    hPoint
  rw [hs]
  have hThree : Dvd.dvd 3 (Monoid.exponent (Units (ZMod q))) := by
    simpa only [hLabel] using hDiv
  choose r s hrs hSum hProd using split_roots_of_three_dvd q hThree
  change Finset.univ.sum (fun x : residueRing q =>
      quotientProfile q l x * (TraceCharacter.traceCharacter (q : Eis) hq) ((A.inv * w) * x)) =
    (q : Complex) * quotientProfile q l (A.inv * w)
  exact quotient_profile_transform q l hLabel hDiv r s hrs hSum hProd hq (A.inv * w)

def theta (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (A : Units (residueRing q)) (a : Real) : Complex :=
  tsum fun z : Eis =>
    markedProfile q l A (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
      gaussian a (eisEmbedding z)

theorem theta_one (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (a : Real) :
    theta q l 1 a = CarmichaelNormPhysical.theta q l a := by
  unfold theta CarmichaelNormPhysical.theta
  apply tsum_congr
  intro z
  rw [markedProfile_one]

theorem gaussian_poisson (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (A : Units (residueRing q)) (a : Real) (ha : 0 < a) :
    theta q l A a = ((1 / (a * (q : Real)) : Real) : Complex) *
      theta q l (Inv.inv A : Units (residueRing q)) (1 / (a * (q : Real) ^ 2)) := by
  have hq : Not ((q : Eis) = 0) := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have : Finite (residueRing q) := finite_quotient_span hq
  let : Fintype (residueRing q) := Fintype.ofFinite _
  have hp := CubicGaussianPair.periodic_gaussian (q : Eis) hq
    (markedProfile q l A) a ha
  simp_rw [marked_quotient_transform q l hLabel hDiv hq A] at hp
  have hn : norm (eisEmbedding (q : Eis)) ^ 2 = (q : Real) ^ 2 := by
    rw [map_natCast]
    simp
  rw [hn] at hp
  have hSeries :
      (tsum fun z : Eis =>
        ((q : Complex) * markedProfile q l (Inv.inv A : Units (residueRing q))
          (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z)) *
          gaussian (1 / (a * (q : Real) ^ 2)) (eisEmbedding z)) =
      (q : Complex) * theta q l (Inv.inv A : Units (residueRing q))
        (1 / (a * (q : Real) ^ 2)) := by
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
  change theta q l A a = _ at hp
  rw [<- mul_assoc, hFactor] at hp
  exact hp

def physicalKernel (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (A : Units (residueRing q)) (M : Real) : Complex :=
  windowPacket q (markedProfile q l A) M

theorem physical_one (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (M : Real) :
    physicalKernel q l 1 M = CarmichaelNormPhysical.physicalKernel q l M := by
  unfold physicalKernel CarmichaelNormPhysical.physicalKernel windowPacket
  apply tsum_congr
  intro z
  rw [markedProfile_one]

theorem physical_eq_gaussian_sum (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (A : Units (residueRing q)) (M : Real) (hM : 0 < M) :
    physicalKernel q l A M =
      Finset.univ.sum (fun i : Fin 4 => coefficients i * theta q l A (scales i / M)) :=
  windowPacket_eq_gaussian_sum q (markedProfile q l A) M hM

theorem physical_reflection (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (A : Units (residueRing q)) (M : Real) (hM : 0 < M) :
    physicalKernel q l A M = -((M : Complex) / (q : Complex)) *
      physicalKernel q l (Inv.inv A : Units (residueRing q)) ((q : Real) ^ 2 / M) := by
  have hq : 0 < (q : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hDual : 0 < (q : Real) ^ 2 / M := div_pos (sq_pos_of_pos hq) hM
  rw [physical_eq_gaussian_sum q l A M hM,
    physical_eq_gaussian_sum q l (Inv.inv A : Units (residueRing q))
      ((q : Real) ^ 2 / M) hDual]
  calc
    _ = Finset.univ.sum (fun i : Fin 4 => coefficients i *
        (1 / (((scales i / M : Real) : Complex) * (q : Complex)) *
          theta q l (Inv.inv A : Units (residueRing q))
            (1 / ((scales i / M) * (q : Real) ^ 2)))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg (fun x : Complex => coefficients i * x)
      simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one,
        Complex.ofReal_natCast] using
        gaussian_poisson q l hLabel hDiv A
          (scales i / M) (div_pos (scales_pos i) hM)
    _ = _ := by
      simpa only [Complex.ofReal_natCast, one_mul, mul_one] using
        CubicGaussianWindow.reciprocal_four_sum
          (theta q l (Inv.inv A : Units (residueRing q))) M (q : Real) 1

def compensatedKernel (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (c : Complex) (AAA AAB ABA ABB : Units (residueRing q))
    (MAA MAB MBA MBB : Real) : Complex :=
  physicalKernel q l AAA MAA - star c * physicalKernel q l AAB MAB -
    c * physicalKernel q l ABA MBA + c * star c * physicalKernel q l ABB MBB

theorem compensated_reflection (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (c : Complex) (AAA AAB ABA ABB : Units (residueRing q))
    (MAA MAB MBA MBB : Real)
    (hAA : 0 < MAA) (hAB : 0 < MAB) (hBA : 0 < MBA) (hBB : 0 < MBB) :
    compensatedKernel q l c AAA AAB ABA ABB MAA MAB MBA MBB =
      -((MAA : Complex) / (q : Complex)) *
        physicalKernel q l (Inv.inv AAA : Units (residueRing q)) ((q : Real) ^ 2 / MAA) +
      star c * ((MAB : Complex) / (q : Complex)) *
        physicalKernel q l (Inv.inv AAB : Units (residueRing q)) ((q : Real) ^ 2 / MAB) +
      c * ((MBA : Complex) / (q : Complex)) *
        physicalKernel q l (Inv.inv ABA : Units (residueRing q)) ((q : Real) ^ 2 / MBA) -
      c * star c * ((MBB : Complex) / (q : Complex)) *
        physicalKernel q l (Inv.inv ABB : Units (residueRing q)) ((q : Real) ^ 2 / MBB) := by
  unfold compensatedKernel
  rw [physical_reflection q l hLabel hDiv AAA MAA hAA,
    physical_reflection q l hLabel hDiv AAB MAB hAB,
    physical_reflection q l hLabel hDiv ABA MBA hBA,
    physical_reflection q l hLabel hDiv ABB MBB hBB]
  ring

def finitePacket {I : Type} (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (S : Finset I) (w : I -> Complex)
    (A : I -> Units (residueRing q)) (M : I -> Real) : Complex :=
  S.sum (fun i => w i * physicalKernel q l (A i) (M i))

theorem finitePacket_reflection {I : Type} (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (S : Finset I) (w : I -> Complex) (A : I -> Units (residueRing q))
    (M : I -> Real) (hM : forall i, Membership.mem S i -> 0 < M i) :
    finitePacket q l S w A M =
      S.sum (fun i => -(w i * ((M i : Real) : Complex) / (q : Complex)) *
        physicalKernel q l (Inv.inv (A i) : Units (residueRing q))
          ((q : Real) ^ 2 / M i)) := by
  unfold finitePacket
  apply Finset.sum_congr rfl
  intro i hi
  rw [physical_reflection q l hLabel hDiv (A i) (M i) (hM i hi)]
  ring

theorem finitePacket_hasSum {I : Type} (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (S : Finset I) (w : I -> Complex)
    (A : I -> Units (residueRing q)) (M : I -> Real)
    (hM : forall i, Membership.mem S i -> 0 < M i) :
    HasSum (fun z : Eis => S.sum (fun i =>
      w i * (markedProfile q l (A i)
        (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
          carrierProfile (norm (eisEmbedding z) ^ 2 / M i))))
      (finitePacket q l S w A M) := by
  classical
  unfold finitePacket
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using
      (hasSum_zero : HasSum (fun _ : Eis => (0 : Complex)) 0)
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hSingle := (windowPacket_hasSum q (markedProfile q l (A i))
      (M i) (hM i (Finset.mem_insert_self i S))).mul_left (w i)
    have hRest := ih (fun j hj => hM j (Finset.mem_insert_of_mem hj))
    exact hSingle.add hRest

theorem marked_profile_normalization (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (A : Units (residueRing q)) (x : residueRing q) :
    (q : Complex) * markedProfile q l A x =
      normalizedQuotientProfile q l (A.val * x) -
        ((q : Complex) - 1) * isotropicProfile q (A.val * x) :=
  quotient_profile_unit_normalization q l (A.val * x)

theorem physical_unit_normalization (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (A : Units (residueRing q)) (M : Real) (hM : 0 < M) :
    (q : Complex) * physicalKernel q l A M =
      windowPacket q (fun x => normalizedQuotientProfile q l (A.val * x)) M -
        ((q : Complex) - 1) *
          windowPacket q (fun x => isotropicProfile q (A.val * x)) M := by
  have hCentered := (windowPacket_hasSum q (markedProfile q l A) M hM).mul_left
    (q : Complex)
  have hNormalized := windowPacket_hasSum q
    (fun x => normalizedQuotientProfile q l (A.val * x)) M hM
  have hIsotropic := (windowPacket_hasSum q
    (fun x => isotropicProfile q (A.val * x)) M hM).mul_left ((q : Complex) - 1)
  have hPoint (z : Eis) :
      (q : Complex) * (markedProfile q l A
        (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
          carrierProfile (norm (eisEmbedding z) ^ 2 / M)) =
      normalizedQuotientProfile q l
        (A.val * Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
          carrierProfile (norm (eisEmbedding z) ^ 2 / M) -
        ((q : Complex) - 1) *
          (isotropicProfile q
            (A.val * Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
              carrierProfile (norm (eisEmbedding z) ^ 2 / M)) := by
    rw [<- mul_assoc, marked_profile_normalization]
    ring
  have hSum := hNormalized.sub hIsotropic
  apply hCentered.unique
  simpa only [hPoint] using hSum

theorem finitePacket_unit_normalization {I : Type} (q : Nat) [NeZero q]
    [Fact (Nat.Prime q)] (l : Nat.Primes) (S : Finset I) (w : I -> Complex)
    (A : I -> Units (residueRing q)) (M : I -> Real)
    (hM : forall i, Membership.mem S i -> 0 < M i) :
    (q : Complex) * finitePacket q l S w A M =
      S.sum (fun i => w i *
        (windowPacket q (fun x => normalizedQuotientProfile q l ((A i).val * x)) (M i) -
          ((q : Complex) - 1) *
            windowPacket q (fun x => isotropicProfile q ((A i).val * x)) (M i))) := by
  unfold finitePacket
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = w i * ((q : Complex) * physicalKernel q l (A i) (M i)) := by ring
    _ = _ := by rw [physical_unit_normalization q l (A i) (M i) (hM i hi)]

def normalizedWindow (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (A : Units (residueRing q)) (M : Real) : Complex :=
  windowPacket q (fun x => normalizedQuotientProfile q l (A.val * x)) M

def isotropicWindow (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (A : Units (residueRing q)) (M : Real) : Complex :=
  windowPacket q (fun x => isotropicProfile q (A.val * x)) M

theorem compensated_unit_normalization (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (c : Complex) (AAA AAB ABA ABB : Units (residueRing q))
    (MAA MAB MBA MBB : Real)
    (hAA : 0 < MAA) (hAB : 0 < MAB) (hBA : 0 < MBA) (hBB : 0 < MBB) :
    (q : Complex) * compensatedKernel q l c AAA AAB ABA ABB MAA MAB MBA MBB =
      (normalizedWindow q l AAA MAA - star c * normalizedWindow q l AAB MAB -
        c * normalizedWindow q l ABA MBA + c * star c * normalizedWindow q l ABB MBB) -
      ((q : Complex) - 1) *
        (isotropicWindow q AAA MAA - star c * isotropicWindow q AAB MAB -
          c * isotropicWindow q ABA MBA + c * star c * isotropicWindow q ABB MBB) := by
  have h1 := physical_unit_normalization q l AAA MAA hAA
  have h2 := physical_unit_normalization q l AAB MAB hAB
  have h3 := physical_unit_normalization q l ABA MBA hBA
  have h4 := physical_unit_normalization q l ABB MBB hBB
  change (q : Complex) * _ = _
  unfold compensatedKernel normalizedWindow isotropicWindow
  linear_combination h1 - star c * h2 - c * h3 + c * star c * h4

theorem seed_auxiliary_inert (q p : Nat) (hThree : Dvd.dvd 3 (q - 1))
    (hFactor : Dvd.dvd (q - 1) (p + 1)) : p % 3 = 2 := by
  have hMod := Nat.dvd_iff_mod_eq_zero.mp (dvd_trans hThree hFactor)
  omega

theorem seed_auxiliary_lower_bound (q p : Nat)
    (hFactor : Dvd.dvd (q - 1) (p + 1)) : q - 2 <= p := by
  have hLe := Nat.le_of_dvd (by omega : 0 < p + 1) hFactor
  omega

theorem seed_auxiliary_mod_twelve (q p : Nat)
    (hThree : Dvd.dvd 3 (q - 1)) (hFour : Dvd.dvd 4 (q - 1))
    (hFactor : Dvd.dvd (q - 1) (p + 1)) : p % 12 = 11 := by
  have h3 := seed_auxiliary_inert q p hThree hFactor
  have h4 := CarmichaelSeed.seed_factor_mod_four q p hFour hFactor
  omega

theorem scalar_cast_q_zero (q : Nat) [NeZero q] :
    (q : residueRing q) = 0 := by
  have hZero : (Ideal.Quotient.mk (Ideal.span {(q : Eis)})) (q : Eis) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [map_natCast] using hZero

def scalarUnit (q d : Nat) [NeZero q] (hC : Nat.Coprime d q) :
    Units (residueRing q) :=
  Units.mkOfMulEqOne (d : residueRing q) ((Nat.gcdA d q : Int) : residueRing q) (by
    have hBez : (d : Int) * Nat.gcdA d q + (q : Int) * Nat.gcdB d q = 1 := by
      rw [<- Nat.gcd_eq_gcd_ab, hC.gcd_eq_one]
      rfl
    have hCast := congrArg (fun z : Int => (z : residueRing q)) hBez
    push_cast at hCast
    simpa only [scalar_cast_q_zero, zero_mul, add_zero] using hCast)

theorem scalarUnit_val (q d : Nat) [NeZero q] (hC : Nat.Coprime d q) :
    (scalarUnit q d hC).val = (d : residueRing q) := rfl

theorem rational_finite_reflection {I : Type} (q : Nat) [NeZero q]
    [Fact (Nat.Prime q)] (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (S : Finset I) (w : I -> Complex) (d : I -> Nat)
    (hC : forall i, Nat.Coprime (d i) q)
    (hD : forall i, Membership.mem S i -> 0 < d i) (M : Real) (hM : 0 < M) :
    S.sum (fun i => w i * physicalKernel q l (scalarUnit q (d i) (hC i))
      (M / (d i : Real) ^ 2)) =
      -((M : Complex) / (q : Complex)) *
        S.sum (fun i => (w i / (d i : Complex) ^ 2) *
          physicalKernel q l (Inv.inv (scalarUnit q (d i) (hC i)) : Units (residueRing q))
            ((q : Real) ^ 2 * (d i : Real) ^ 2 / M)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hdR : 0 < (d i : Real) := by exact_mod_cast hD i hi
  have hDual : (q : Real) ^ 2 / (M / (d i : Real) ^ 2) =
      (q : Real) ^ 2 * (d i : Real) ^ 2 / M := by
    field_simp [hM.ne', hdR.ne']
  rw [physical_reflection q l hLabel hDiv _ _ (div_pos hM (sq_pos_of_pos hdR)), hDual]
  push_cast
  ring

def divisorUnit (q B : Nat) [NeZero q] (hC : Nat.Coprime B q) (d : B.divisors) :
    Units (residueRing q) :=
  scalarUnit q d.val (Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_divisors d.property) hC)

def depletedPacket (q B : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (hC : Nat.Coprime B q) (M : Real) : Complex :=
  Finset.univ.sum (fun d : B.divisors =>
    (ArithmeticFunction.moebius d.val : Complex) *
      physicalKernel q l (divisorUnit q B hC d) (M / (d.val : Real) ^ 2))

def dualDepletedPacket (q B : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (hC : Nat.Coprime B q) (M : Real) : Complex :=
  Finset.univ.sum (fun d : B.divisors =>
    ((ArithmeticFunction.moebius d.val : Complex) / (d.val : Complex) ^ 2) *
      physicalKernel q l (Inv.inv (divisorUnit q B hC d) : Units (residueRing q))
        ((q : Real) ^ 2 * (d.val : Real) ^ 2 / M))

theorem depleted_reflection (q B : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hC : Nat.Coprime B q) (M : Real) (hM : 0 < M) :
    depletedPacket q B l hC M =
      -((M : Complex) / (q : Complex)) * dualDepletedPacket q B l hC M := by
  exact rational_finite_reflection q l hLabel hDiv Finset.univ
    (fun d : B.divisors => (ArithmeticFunction.moebius d.val : Complex))
    (fun d => d.val)
    (fun d => Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_divisors d.property) hC)
    (fun d _ => Nat.pos_of_mem_divisors d.property) M hM

theorem depleted_hasSum (q B : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hC : Nat.Coprime B q) (M : Real) (hM : 0 < M) :
    HasSum (fun z : Eis => Finset.univ.sum (fun d : B.divisors =>
      (ArithmeticFunction.moebius d.val : Complex) *
        (markedProfile q l (divisorUnit q B hC d)
          (Ideal.Quotient.mk (Ideal.span {(q : Eis)}) z) *
            carrierProfile (norm (eisEmbedding z) ^ 2 / (M / (d.val : Real) ^ 2)))))
      (depletedPacket q B l hC M) := by
  exact finitePacket_hasSum q l Finset.univ
    (fun d : B.divisors => (ArithmeticFunction.moebius d.val : Complex))
    (divisorUnit q B hC) (fun d => M / (d.val : Real) ^ 2)
    (fun d _ => div_pos hM (sq_pos_of_pos (by exact_mod_cast Nat.pos_of_mem_divisors d.property)))

theorem depleted_unit_normalization (q B : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hC : Nat.Coprime B q) (M : Real) (hM : 0 < M) :
    (q : Complex) * depletedPacket q B l hC M =
      Finset.univ.sum (fun d : B.divisors =>
        (ArithmeticFunction.moebius d.val : Complex) *
          (normalizedWindow q l (divisorUnit q B hC d) (M / (d.val : Real) ^ 2) -
            ((q : Complex) - 1) *
              isotropicWindow q (divisorUnit q B hC d) (M / (d.val : Real) ^ 2))) := by
  exact finitePacket_unit_normalization q l Finset.univ
    (fun d : B.divisors => (ArithmeticFunction.moebius d.val : Complex))
    (divisorUnit q B hC) (fun d => M / (d.val : Real) ^ 2)
    (fun d _ => div_pos hM (sq_pos_of_pos (by exact_mod_cast Nat.pos_of_mem_divisors d.property)))

def depletedCompensation (q B : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hC : Nat.Coprime B q) (c : Complex)
    (MAA MAB MBA MBB : Real) : Complex :=
  depletedPacket q B l hC MAA - star c * depletedPacket q B l hC MAB -
    c * depletedPacket q B l hC MBA + c * star c * depletedPacket q B l hC MBB

theorem depleted_compensated_reflection (q B : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hC : Nat.Coprime B q) (c : Complex) (MAA MAB MBA MBB : Real)
    (hAA : 0 < MAA) (hAB : 0 < MAB) (hBA : 0 < MBA) (hBB : 0 < MBB) :
    depletedCompensation q B l hC c MAA MAB MBA MBB =
      -((MAA : Complex) / (q : Complex)) * dualDepletedPacket q B l hC MAA +
      star c * ((MAB : Complex) / (q : Complex)) * dualDepletedPacket q B l hC MAB +
      c * ((MBA : Complex) / (q : Complex)) * dualDepletedPacket q B l hC MBA -
      c * star c * ((MBB : Complex) / (q : Complex)) * dualDepletedPacket q B l hC MBB := by
  unfold depletedCompensation
  rw [depleted_reflection q B l hLabel hDiv hC MAA hAA,
    depleted_reflection q B l hLabel hDiv hC MAB hAB,
    depleted_reflection q B l hLabel hDiv hC MBA hBA,
    depleted_reflection q B l hLabel hDiv hC MBB hBB]
  ring

theorem depleted_split_unit (q B : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hC : Nat.Coprime B q) (hB : Not (B = 0)) (M : Real) :
    let e : B.divisors :=
      Subtype.mk 1 (Nat.mem_divisors.mpr (And.intro (one_dvd B) hB))
    depletedPacket q B l hC M =
      CarmichaelNormPhysical.physicalKernel q l M +
        (Finset.univ.erase e).sum (fun d : B.divisors =>
          (ArithmeticFunction.moebius d.val : Complex) *
            physicalKernel q l (divisorUnit q B hC d) (M / (d.val : Real) ^ 2)) := by
  classical
  dsimp only
  let e : B.divisors :=
    Subtype.mk 1 (Nat.mem_divisors.mpr (And.intro (one_dvd B) hB))
  let f : B.divisors -> Complex := fun d =>
    (ArithmeticFunction.moebius d.val : Complex) *
      physicalKernel q l (divisorUnit q B hC d) (M / (d.val : Real) ^ 2)
  have heVal : e.val = 1 := rfl
  have he : divisorUnit q B hC e = 1 := by
    apply Units.ext
    exact scalarUnit_val q 1 _
  have hUnit : f e = CarmichaelNormPhysical.physicalKernel q l M := by
    dsimp only [f]
    rw [he, heVal]
    have hMu : (ArithmeticFunction.moebius 1 : Complex) = 1 := by norm_num
    rw [hMu, one_mul, Nat.cast_one, one_pow, div_one, physical_one]
  calc
    depletedPacket q B l hC M = Finset.univ.sum f := rfl
    _ = (Finset.univ.erase e).sum f + f e :=
      (Finset.sum_erase_add Finset.univ f (Finset.mem_univ e)).symm
    _ = _ := by rw [hUnit, add_comm]

end PrimeFactorOscillations.CarmichaelMarkedWindow

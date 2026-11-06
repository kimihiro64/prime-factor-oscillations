/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import OAI.NumberTheory.DirichletL.Nonvanishing
import PrimeFactorOscillations.Assembly.CarmichaelPowerTrace
import PrimeFactorOscillations.Helpers.CarmichaelTransportDefect

/-!
# Coupled power multiplicity transport in a fixed zero strip

The affine map expands the real deficit by e/d. A fixed zero strip therefore
gives a finite escape depth. The installed seven-eighths theorem supplies an
unconditional strip for actual zeta zeros; it is not an improved boundary.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelStripCarrier

open DirichletCompensatedProbe CarmichaelWeightedSignal

def stripTransport (r : Real) (z : Complex) : Complex :=
  1 - (r : Complex) * (1 - z)

def powerSource (d : Real) (z : Complex) : Complex :=
  (d : Complex) * z - ((d : Complex) - 1)

theorem stripTransport_re (r : Real) (z : Complex) :
    (stripTransport r z).re = 1 - r * (1 - z.re) := by
  simp [stripTransport, Complex.mul_re]

theorem stripTransport_im (r : Real) (z : Complex) :
    (stripTransport r z).im = r * z.im := by
  simp [stripTransport, Complex.mul_im]

theorem stripTransport_injective (r : Real) (hr : 0 < r) :
    Function.Injective (stripTransport r) := by
  have hrc : Not ((r : Complex) = 0) := by exact_mod_cast hr.ne'
  intro x y hxy
  unfold stripTransport at hxy
  have hDiff : (r : Complex) * (x - y) = 0 := by
    linear_combination hxy
  exact sub_eq_zero.mp ((mul_eq_zero.mp hDiff).resolve_left hrc)

theorem stripTransport_iter_re (r : Real) (n : Nat) (z : Complex) :
    (transportIter (stripTransport r) n z).re = 1 - r ^ n * (1 - z.re) := by
  induction n with
  | zero => simp [transportIter]
  | succ n ih =>
    simp only [transportIter, stripTransport_re, ih, pow_succ]
    ring

theorem powerSource_im (d : Real) (z : Complex) :
    (powerSource d z).im = d * z.im := by
  simp [powerSource, Complex.mul_im]

theorem powerMap_powerSource (d : Real) (hd : 0 < d) (z : Complex) :
    powerMap d (powerSource d z) = z := by
  have hdC : Not ((d : Complex) = 0) := by exact_mod_cast hd.ne'
  unfold powerMap powerSource
  field_simp [hdC]
  ring

theorem powerSource_powerMap (d : Real) (hd : 0 < d) (z : Complex) :
    powerSource d (powerMap d z) = z := by
  have hdC : Not ((d : Complex) = 0) := by exact_mod_cast hd.ne'
  unfold powerMap powerSource
  field_simp [hdC]
  ring

theorem powerMap_powerSource_eq_transport (d e : Real) (hd : 0 < d)
    (z : Complex) :
    powerMap d (powerSource e z) = stripTransport (e / d) z := by
  have hdC : Not ((d : Complex) = 0) := by exact_mod_cast hd.ne'
  simp only [powerMap, powerSource, stripTransport, Complex.ofReal_div]
  field_simp [hdC]
  ring

def rightZeroSupport (T : Real) : Finset Complex :=
  (upperZeroValues T).filter (fun z => (1 / 2 : Real) < z.re)

def zetaSquareMass (z : Complex) : Real :=
  zetaWeightedMultiplicity (fun t => 1 / t ^ 2) z

def rightZeroMass (T : Real) (z : Complex) : Real :=
  if Membership.mem (rightZeroSupport T) z then zetaSquareMass z else 0

theorem zetaSquareMass_nonneg (z : Complex) : 0 <= zetaSquareMass z := by
  exact mul_nonneg (Nat.cast_nonneg _) (one_div_nonneg.mpr (sq_nonneg _))

theorem rightZeroMass_nonneg (T : Real) (z : Complex) : 0 <= rightZeroMass T z := by
  unfold rightZeroMass
  split_ifs
  . exact zetaSquareMass_nonneg z
  . exact le_rfl

theorem rightZeroMass_support (T : Real) (z : Complex)
    (hz : Not (Membership.mem (rightZeroSupport T) z)) :
    rightZeroMass T z = 0 := by
  simp only [rightZeroMass, if_neg hz]

theorem zeta_order_pos_of_window (T : Real) (z : Complex) (hz : zetaZeroWindow T z) :
    0 < analyticOrderNatAt riemannZeta z := by
  have hOne : Not (z = 1) := by
    intro h
    have hIm := congrArg Complex.im h
    simp only [Complex.one_im] at hIm
    linarith [hz.2.2.2.1]
  have hXi : Complex.riemannXi z = 0 := by
    rw [riemannXi_eq_xiZetaUnit_mul hz.2.1 hOne, hz.1, mul_zero]
  rw [<- xiZeroMultiplicity_eq_zetaOrder hz.2.1 hOne]
  exact (xiZeroMultiplicity_pos_iff z).mpr hXi

theorem rightZeroSupport_seven_eighths (T : Real) (z : Complex)
    (hz : Membership.mem (rightZeroSupport T) z) : z.re <= (7 / 8 : Real) := by
  have hw := (mem_upperZeroValues T z).mp (Finset.mem_filter.mp hz).1
  by_contra hNot
  exact OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re (lt_of_not_ge hNot) hw.1

theorem strip_transport_escape
    (S : Finset Complex) (b : Complex -> Real)
    (hb : forall z, Not (Membership.mem S z) -> b z = 0)
    (sigma r : Real) (hr : 0 <= r)
    (hStrip : forall z, Membership.mem S z -> (1 / 2 : Real) < z.re /\ z.re <= sigma)
    (L : Nat) (hDepth : (1 / 2 : Real) <= r ^ L * (1 - sigma)) :
    forall z, Membership.mem S z -> b (transportIter (stripTransport r) L z) = 0 := by
  intro z hz
  apply hb
  intro hMem
  have hStart := (hStrip z hz).2
  have hEnd := (hStrip _ hMem).1
  have hDeficit := mul_le_mul_of_nonneg_left
    (sub_le_sub_left hStart 1) (pow_nonneg hr L)
  rw [stripTransport_iter_re] at hEnd
  linarith

theorem rightZeroMass_escape (T sigma r : Real) (hr : 0 <= r)
    (hStrip : forall z, Membership.mem (rightZeroSupport T) z -> z.re <= sigma)
    (L : Nat) (hDepth : (1 / 2 : Real) <= r ^ L * (1 - sigma)) :
    forall z, Membership.mem (rightZeroSupport T) z ->
      rightZeroMass T (transportIter (stripTransport r) L z) = 0 := by
  apply strip_transport_escape (rightZeroSupport T) (rightZeroMass T)
    (rightZeroMass_support T) sigma r hr
  . intro z hz
    exact And.intro (Finset.mem_filter.mp hz).2 (hStrip z hz)
  . exact hDepth

end PrimeFactorOscillations.CarmichaelStripCarrier

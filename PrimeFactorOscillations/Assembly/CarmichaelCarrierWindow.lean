/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPhysicalPacket
import PrimeFactorOscillations.Helpers.CubicCarrierMellin
/-!
# Physical transfer in the actual Eisenstein norm coordinate

Transfers arbitrary signed finite nonzero carrier supports, using their
integer norms and both quartic Mellin factors. Both factors are nonzero
in the off-critical strip. This does not assert the infinite prime-selector
transfer, Schwartz realization, or the arithmetic Abel-endpoint bound.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelCarrierWindow
open MeasureTheory OAI OAI.SevenEighths
open ActualEisensteinCubic ConcreteTraceCRT EisensteinEmbedding
open CubicReciprocalGaussian CubicCarrierMellin
local notation "Eis" => ActualEisensteinCubic.O

def physicalCarrierPacket (Z : Finset Eis) (a : Eis -> Complex) (t : Real) : Complex :=
  Z.sum (fun z => a z * carrierProfile (norm (eisEmbedding z) ^ 2 / t))

def dirichletCarrierPacket (Z : Finset Eis) (a : Eis -> Complex) (s : Complex) : Complex :=
  Z.sum (fun z => a z * (Ideal.absNorm (Ideal.span {z}) : Complex) ^ (-s))

theorem physicalCarrierPacket_hasMellin (Z : Finset Eis) (a : Eis -> Complex)
    (s : Complex) (hs : 0 < s.re)
    (hpos : forall z : Eis, Membership.mem Z z -> Not (z = 0)) :
    HasMellin (physicalCarrierPacket Z a) (-s)
      (carrierMultiplier s * dirichletCarrierPacket Z a s) := by
  classical
  induction Z using Finset.induction_on with
  | empty =>
    simp [physicalCarrierPacket, dirichletCarrierPacket, HasMellin, MellinConvergent, mellin]
  | @insert z Z hz ih =>
    have hzn : Not (z = 0) := hpos z (Finset.mem_insert_self z Z)
    have hn : 0 < Ideal.absNorm (Ideal.span {z}) :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr hzn))
    have hnR : (0 : Real) < Ideal.absNorm (Ideal.span {z}) := by exact_mod_cast hn
    have hsmall := ih (fun w hw => hpos w (Finset.mem_insert_of_mem hw))
    have ht := CarmichaelPhysicalPacket.scaledWindow_hasMellin carrierProfile s
      (carrierMultiplier s) (carrierProfile_hasMellin s hs)
      (Ideal.absNorm (Ideal.span {z})) hnR
    have hcoef := hasMellin_const_smul ht.1 (a z)
    rw [ht.2] at hcoef
    have hterm : HasMellin (fun t : Real =>
        a z * carrierProfile (norm (eisEmbedding z) ^ 2 / t)) (-s)
        (a z * ((Ideal.absNorm (Ideal.span {z}) : Complex) ^ (-s) *
          carrierMultiplier s)) := by
      simpa only [eisEmbedding_norm_sq_eq_absNorm_span, smul_eq_mul,
        Complex.ofReal_natCast] using hcoef
    have hadd := hasMellin_add hterm.1 hsmall.1
    rw [hterm.2, hsmall.2] at hadd
    have he : physicalCarrierPacket (insert z Z) a =
        (fun t : Real => a z * carrierProfile (norm (eisEmbedding z) ^ 2 / t) +
          physicalCarrierPacket Z a t) := by
      funext t
      simp only [physicalCarrierPacket, Finset.sum_insert hz]
    rw [he]
    simpa only [dirichletCarrierPacket, Finset.sum_insert hz,
      mul_add, mul_left_comm, mul_comm, mul_assoc] using hadd

theorem quartic_physicalCarrierPacket_mellin (Z : Finset Eis) (a : Eis -> Complex)
    (s : Complex) (hs : 0 < s.re)
    (hpos : forall z : Eis, Membership.mem Z z -> Not (z = 0)) :
    mellin (CarmichaelWindowTransfer.quarticPhysicalProbe (physicalCarrierPacket Z a)) (-s) =
      carrierMultiplier s * dirichletCarrierPacket Z a s -
        HSMul.hSMul ((4 : Real) ^ (-1 : Int))
          (carrierMultiplier (DirichletCompensatedProbe.quarticMap s) *
            dirichletCarrierPacket Z a (DirichletCompensatedProbe.quarticMap s)) := by
  have hq : 0 < (DirichletCompensatedProbe.quarticMap s).re := by
    dsimp [DirichletCompensatedProbe.quarticMap]
    simp only [Complex.div_ofNat_re, Complex.add_re]
    norm_num
    linarith
  have hMain := physicalCarrierPacket_hasMellin Z a s hs hpos
  have hReference := physicalCarrierPacket_hasMellin Z a
    (DirichletCompensatedProbe.quarticMap s) hq hpos
  have h := CarmichaelWindowTransfer.quarticPhysicalProbe_mellin
    (physicalCarrierPacket Z a) s hMain.1 hReference.1
  rw [hMain.2, hReference.2] at h
  exact h

theorem both_multipliers_ne_zero (s : Complex)
    (hs : (1 / 2 : Real) < s.re) (hs1 : s.re < 1) :
    Not (carrierMultiplier s = 0) /\
      Not (carrierMultiplier (DirichletCompensatedProbe.quarticMap s) = 0) := by
  have he : (DirichletCompensatedProbe.quarticMap s).re = (s.re + 3) / 4 := by
    dsimp [DirichletCompensatedProbe.quarticMap]
    simp only [Complex.div_ofNat_re, Complex.add_re]
    norm_num
  exact And.intro (carrierMultiplier_ne_zero s hs hs1)
    (carrierMultiplier_ne_zero _ (by rw [he]; linarith) (by rw [he]; linarith))

end PrimeFactorOscillations.CarmichaelCarrierWindow

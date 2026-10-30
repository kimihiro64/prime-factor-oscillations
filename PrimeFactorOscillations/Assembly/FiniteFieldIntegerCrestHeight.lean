/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerHeight

/-!
# Global CRT crests and the natural integer-height window

The same integer residue retains its full positive crest inequalities
and frozen-factor identity while satisfying the new height exclusion.
The theorem does not return an arbitrary integer location.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerCrestHeight

open FiniteFieldIntegerMass
open FiniteFieldIntegerAffine
open FiniteFieldIntegerExtrema
open FiniteFieldFrozenGrowth

def crestClass (h Q a : Nat) : Prop :=
  forall K : Nat, 12 <= K -> K <= Q -> forall t : Nat,
    0 < hybridPacket K (h : Int) Q (a + primePeriod Q * t) /\
    actualPacket (h : Int) Q (a + primePeriod Q * t) /
      hybridPacket K (h : Int) Q (a + primePeriod Q * t) =
        Real.exp (frozenLogSum K (h : Int) a (primePeriod Q) Q) /\
    growthLower h * normalizedRatio K Q <=
      actualPacket (h : Int) Q (a + primePeriod Q * t) /
        hybridPacket K (h : Int) Q (a + primePeriod Q * t) /\
    actualPacket (h : Int) Q (a + primePeriod Q * t) /
      hybridPacket K (h : Int) Q (a + primePeriod Q * t) <=
        growthUpper * normalizedRatio K Q

theorem exists_crest_outside_natural_height :
    exists C : Real, And (0 < C)
      (forall h Q : Nat, 0 < h -> Dvd.dvd 2 h ->
        exists a : Nat, And (a < primePeriod Q) (And (crestClass h Q a)
          (forall K : Nat, 12 <= K -> h < Q -> K <= Q ->
            (3 + Real.log ((4 * h * (Q * Q) : Nat) : Real)) ^ 64 <= ((K + 1 : Nat) : Real) ->
            Real.exp (2 * C + 8 / (K : Real)) < growthLower h * normalizedRatio K Q ->
            forall t : Nat,
              Or (a + primePeriod Q * t <= Q) (Q * Q < a + primePeriod Q * t + h)))) := by
  let C : Real := Classical.choose FiniteFieldIntegerHeight.exists_natural_height_packet_comparison
  have hSpec := Classical.choose_spec FiniteFieldIntegerHeight.exists_natural_height_packet_comparison
  refine Exists.intro C (And.intro hSpec.1 ?_)
  intro h Q hh heven
  let a : Nat := Classical.choose (sharp_frozen_packet_ratio h Q hh heven)
  have ha := Classical.choose_spec (sharp_frozen_packet_ratio h Q hh heven)
  refine Exists.intro a (And.intro ha.1 (And.intro ha.2 ?_))
  intro K hK hhQ hKQ hcut hGain t
  let n : Nat := a + primePeriod Q * t
  by_cases hn : n <= Q
  . exact Or.inl hn
  . apply Or.inr
    change Q * Q < n + h
    by_contra hnot
    have hnQ : n + h <= Q * Q := by omega
    have hc := ha.2 K hK hKQ t
    have hp := hSpec.2 K h Q n (by omega) hh hhQ hKQ (by omega) hnQ hcut
    have hV : 0 < hybridPacket K (h : Int) Q n := hc.1
    have hl := mul_le_mul_of_nonneg_right hc.2.2.1 hV.le
    have hid :
        (actualPacket (h : Int) Q n / hybridPacket K (h : Int) Q n) *
          hybridPacket K (h : Int) Q n = actualPacket (h : Int) Q n := by
      field_simp [ne_of_gt hV]
    rw [hid] at hl
    have hg := mul_lt_mul_of_pos_right hGain hV
    linarith only [hl, hp.2, hg]

end PrimeFactorOscillations.FiniteFieldIntegerCrestHeight

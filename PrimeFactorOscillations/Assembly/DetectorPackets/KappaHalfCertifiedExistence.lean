/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.CertifiedExistence
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfCappedSuccessor

/-!
# KappaHalfCertifiedExistence

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors

Certified width induction for every fixed kappa>1/2. The beta
lower bound and beta compatibility remain explicit.
-/

set_option maxHeartbeats 800000

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.KappaHalfCertifiedExistence

open HeckeFamily CenteredMomentEnergyWidthSchedule

local notation "O" => HeckeFamily.O

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
variable (M : Ideal O) [NeZero M]
local instance : Finite (HasQuotient.Quotient O M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (Units (HasQuotient.Quotient O M)))
  (hH : RayOrthogonality.globalUnits M <= H)

theorem certified_bands
    (W : Real -> Complex) (aslot bslot a b radial Bmask L lo hi Mcap kappa eps : Real)
    (haslot : 0 < aslot) (hWs : Function.support W <= Set.Icc aslot bslot)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (hbslot : 0 <= bslot) (ha : 0 < a) (haUpper : a <= 1/4) (hb : 1 <= b)
    (hrad : 2 <= radial) (hmask : 0 <= Bmask) (hMcap : 0 < Mcap)
    (hkappa : 1/2 < kappa) (heps : 0 < eps)
    (hbeta : 51/100 <= HeckeZeroSupremum.beta)
    (hkappaBeta : 2*HeckeZeroSupremum.beta-1 <= kappa) :
    forall k : Nat, k <= count Mcap eps ->
      @CenteredMomentEnergyCappedWidthInduction.CertifiedBand
        alpha M inferInstance H hH W bslot a b radial Bmask L lo hi Mcap kappa eps k := by
  intro k
  induction k with
  | zero =>
    intro _
    exact @CenteredMomentEnergyCappedWidthInduction.certified_floor
      alpha inferInstance inferInstance M inferInstance H hH
      W aslot bslot a b radial Bmask L lo hi Mcap kappa eps
      haslot hWs hW ha (by linarith) (by linarith) hmask hMcap.le
      (by linarith) heps hbeta hkappaBeta
  | succ k ih =>
    intro hk
    have hprevious := ih (Nat.le_of_succ_le hk)
    have hstep : k < count Mcap eps := by omega
    exact @KappaHalfCappedSuccessor.actual_successor
      alpha inferInstance inferInstance M inferInstance H hH
      W aslot bslot a b radial Bmask L lo hi Mcap kappa eps
      haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hkappa heps hbeta hkappaBeta
      k hstep hprevious

theorem terminal_certificate
    (W : Real -> Complex) (aslot bslot a b radial Bmask L lo hi Mcap kappa eps : Real)
    (haslot : 0 < aslot) (hWs : Function.support W <= Set.Icc aslot bslot)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (hbslot : 0 <= bslot) (ha : 0 < a) (haUpper : a <= 1/4) (hb : 1 <= b)
    (_hrad : 0 < radial) (hmask : 0 <= Bmask) (hMcap : 0 < Mcap)
    (hkappa : 1/2 < kappa) (heps : 0 < eps)
    (hbeta : 51/100 <= HeckeZeroSupremum.beta)
    (hkappaBeta : 2*HeckeZeroSupremum.beta-1 <= kappa) :
    @CenteredMomentEnergyCappedWidthInduction.CertifiedBand
      alpha M inferInstance H hH W bslot a b radial Bmask L lo hi Mcap kappa eps
      (count Mcap eps) := by
  apply CenteredMomentEnergyCappedRadialTransport.certified_from_max_two
    M H hH W bslot a b radial Bmask L lo hi Mcap kappa eps
  exact @certified_bands alpha inferInstance inferInstance M inferInstance H hH
    W aslot bslot a b (max 2 radial) Bmask L lo hi Mcap kappa eps
    haslot hWs hW hbslot ha haUpper hb (le_max_left _ _) hmask hMcap hkappa heps hbeta
    hkappaBeta _ le_rfl

end SevenEighths.KappaHalfCertifiedExistence

end

end OAI


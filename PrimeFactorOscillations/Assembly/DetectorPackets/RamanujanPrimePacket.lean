/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.RamanujanGcdPacket
import PrimeFactorOscillations.Assembly.DetectorPackets.RamanujanIncidenceOperator

/-!
# RamanujanPrimePacket

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
-/

set_option maxHeartbeats 2000000

noncomputable section
namespace OAI.SevenEighths.RamanujanIncidenceGram
open scoped Classical BigOperators
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def primeNumerator (A Q : Id) : Real :=
  (primeSupport Q).prod fun P=>if Dvd.dvd P A then (P.absNorm:Real)-1 else -1

def primePacket (A Q : Id) : Complex :=
  (primeNumerator A Q:Complex)/(Real.sqrt (Q.absNorm:Real):Complex)

theorem primeNumerator_bound (A Q : Id) (hA : Not (A=0)) (hQ : Not (Q=0)) :
    abs (primeNumerator A Q)<=sharedMass A Q := by
  let S := (primeSupport Q).filter fun P=>Dvd.dvd P A
  let G := S.prod id
  have hSQ : S<=primeSupport Q := Finset.filter_subset _ _
  have hSA : S<=primeSupport A := by
    intro P hP
    have hh := Finset.mem_filter.mp hP
    have hp := support_prime hh.1
    exact Multiset.mem_toFinset.mpr ((mem_normalizedFactors_iff hA).mpr (And.intro hp hh.2))
  have hGQ : Dvd.dvd G Q := support_product_dvd hQ hSQ
  have hGA : Dvd.dvd G A := support_product_dvd hA hSA
  have hGmem : Membership.mem (idealDivisors Q) G := (mem_idealDivisors hQ).mpr hGQ
  have hGN : (G.absNorm:Real)=S.prod (fun P=>(P.absNorm:Real)) := by
    simp only [G,map_prod,Nat.cast_prod,id_eq]
  have hh := PrimeFactorOscillations.RamanujanGcdPacket.absolute_selected_bound
    (primeSupport Q) (fun P:Id=>(P.absNorm:Real)) (fun P=>Dvd.dvd P A)
    (fun P hP=>by
      have hp := support_prime hP
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero))
  change abs (primeNumerator A Q)<=_ at hh
  have hmass : (G.absNorm:Real)<=sharedMass A Q := by
    have hh := Finset.single_le_sum
      (s:=idealDivisors Q)
      (f:=fun D=>if Dvd.dvd D A then (D.absNorm:Real) else 0)
      (fun D hD=>by split_ifs <;> positivity) hGmem
    simpa only [if_pos hGA,sharedMass] using hh
  exact hh.trans (hGN.symm.le.trans hmass)

theorem primePacket_bound (A Q : Id) (hA : Not (A=0)) (hQ : Not (Q=0)) :
    norm (primePacket A Q)<=sharedMass A Q/Real.sqrt (Q.absNorm:Real) := by
  rw [primePacket,norm_div,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right (primeNumerator_bound A Q hA hQ) (Real.sqrt_nonneg _)

theorem primePacket_energy (eps : Real) (heps : 0<eps) :
    Exists fun K : Real => 0<K /\
    forall (R C : Finset Id) (M Q : Real), 1<=M -> 1<=Q ->
    (forall A, Membership.mem R A -> Not (A=0) /\ (A.absNorm:Real)<=M) ->
    (forall I, Membership.mem C I -> Not (I=0) /\ (I.absNorm:Real)<=Q) ->
    forall phase : Id -> Id -> Complex,
    (forall A, Membership.mem R A -> forall I, Membership.mem C I -> norm (phase A I)<=1) ->
    forall b : Id -> Complex,
    (R.sum fun A=>norm (C.sum fun I=>b I*(phase A I*primePacket A I))^2)<=
      K*M*(M*Q)^eps*(C.sum fun I=>norm (b I)^2) := by
  choose K hK hb using normalized_energy eps heps
  refine Exists.intro K (And.intro hK ?_)
  intro R C M Q hM hQ hR hC phase hp b
  exact hb R C M Q hM hQ hR hC (fun A I=>phase A I*primePacket A I)
    (fun A hA I hI=>by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hp A hA I hI)).trans
        (primePacket_bound A I (hR A hA).1 (hC I hI).1)) b

end OAI.SevenEighths.RamanujanIncidenceGram

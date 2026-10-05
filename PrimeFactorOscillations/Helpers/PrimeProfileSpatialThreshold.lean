/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPrimeProductCriterion
import PrimeFactorOscillations.Helpers.PrimeProfileCanonical
import PrimeFactorOscillations.Helpers.PrimeProfileReferenceCrossing

/-!
# Spatial finite-prefix sign tests

The existing inverse-cutoff clock error becomes a logarithmic spatial
buffer when both double-exponential clocks are bounded by a fixed multiple
of the prime cutoff. No RH or occurrence of a prime gap is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open BombieriVinogradov.ComplexAnalysis

theorem exists_primePrefixProfile_spatial_sign_transfer
    (a b D gamma : Real) (ha : 0 < a) (hab : a <= b) (hD : 1 <= D) :
    exists r0 N0 : Nat, exists K : Real,
      0 < r0 /\ 2 <= N0 /\ 0 <= K /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      forall B L : Real,
      (forall u : Real, Set.Icc (min B L) (max B L) u ->
        0 < u /\ a <= (r : Real) / u /\ (r : Real) / u <= b) ->
      Real.exp (Real.exp (B - gamma)) <= D * (N : Real) ->
      Real.exp (Real.exp (L - gamma)) <= D * (N : Real) ->
      0 < Nat.factorialConvolution
        (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) r B /\
      0 < Nat.factorialConvolution primeProfileRealCoefficient r L /\
      (K * Real.log (N : Real) <
          Real.exp (Real.exp (L - gamma)) - Real.exp (Real.exp (B - gamma)) ->
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
            Nat.factorialConvolution primeProfileRealCoefficient r L <
          Nat.factorialConvolution
              (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) (r - 1) B /
            Nat.factorialConvolution
              (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) r B) /\
      (K * Real.log (N : Real) <
          Real.exp (Real.exp (B - gamma)) - Real.exp (Real.exp (L - gamma)) ->
        Nat.factorialConvolution
            (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) (r - 1) B /
          Nat.factorialConvolution
            (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) r B <
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
          Nat.factorialConvolution primeProfileRealCoefficient r L) := by
  choose r0 n0 C hr0 hn0 hC hSign using
    exists_primePrefixProfile_clock_sign_transfer a b ha hab
  choose nD hnD using exists_nat_gt D
  let K := 2 * D * C
  have hDpos : 0 < D := by linarith
  refine Exists.intro r0 (Exists.intro (max n0 (max 2 nD)) (Exists.intro K
    (And.intro hr0 (And.intro (by omega) (And.intro (by dsimp [K]; positivity) ?_)))))
  intro r hr N hN B L hsegment hB hL
  have hn0N : n0 <= N := (le_max_left _ _).trans hN
  have hn2 : 2 <= N := (le_max_left 2 nD).trans ((le_max_right _ _).trans hN)
  have hnDN : nD <= N := (le_max_right 2 nD).trans ((le_max_right _ _).trans hN)
  have hNR : (0 : Real) < N := by exact_mod_cast (by omega : 0 < N)
  have hn2R : (2 : Real) <= N := by exact_mod_cast hn2
  have hDNR : D <= (N : Real) := hnD.le.trans (by exact_mod_cast hnDN)
  have hLogN : 0 < Real.log (N : Real) := Real.log_pos (by linarith)
  have hTransfer := hSign r hr N hn0N B L hsegment
  have hSpatial (v w : Real)
      (hw : Real.exp (Real.exp (w - gamma)) <= D * (N : Real))
      (hSep : K * Real.log (N : Real) <
        Real.exp (Real.exp (w - gamma)) - Real.exp (Real.exp (v - gamma))) :
      C / (N : Real) < w - v := by
    let P := Real.exp (Real.exp (v - gamma))
    let Q := Real.exp (Real.exp (w - gamma))
    have hP : 0 < P := Real.exp_pos _
    have hQ : 0 < Q := Real.exp_pos _
    have hLogP : 0 < Real.log P := by dsimp [P]; rw [Real.log_exp]; positivity
    have hLogQ : 0 < Real.log Q := by dsimp [Q]; rw [Real.log_exp]; positivity
    have hLogD : Real.log D <= Real.log (N : Real) := Real.log_le_log hDpos hDNR
    have hLogQBound : Real.log Q <= 2 * Real.log (N : Real) := by
      have ht := Real.log_le_log hQ hw
      rw [Real.log_mul hDpos.ne' hNR.ne'] at ht
      linarith
    have hQBound : Q * Real.log Q <= (D * (N : Real)) * (2 * Real.log (N : Real)) :=
      mul_le_mul hw hLogQBound hLogQ.le (by positivity)
    have hSecant {x y : Real} (hx : 0 < x) (hy : 0 < y) :
        Real.log x - Real.log y <= (x - y) / y := by
      calc
        _ = Real.log (x / y) := (Real.log_div hx.ne' hy.ne').symm
        _ <= x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx hy)
        _ = _ := by field_simp
    have hOuter := hSecant hLogP hLogQ
    have hInner := (div_le_div_iff_of_pos_right hLogQ).2 (hSecant hP hQ)
    have hLogs : Real.log (Real.log P) - Real.log (Real.log Q) = v - w := by
      dsimp [P, Q]
      simp only [Real.log_exp]
      ring
    have hNested : ((P - Q) / Q) / Real.log Q = (P - Q) / (Q * Real.log Q) := by ring
    rw [hNested] at hInner
    rw [hLogs] at hOuter
    have hSlope : v - w <= (P - Q) / (Q * Real.log Q) := hOuter.trans hInner
    have hDen : 0 < Q * Real.log Q := mul_pos hQ hLogQ
    have hScaled := mul_le_mul_of_nonneg_right hSlope hDen.le
    have hCancel : (P - Q) / (Q * Real.log Q) * (Q * Real.log Q) = P - Q := by
      field_simp
    rw [hCancel] at hScaled
    by_contra hNot
    have hSmall : w - v <= C / (N : Real) := le_of_not_gt hNot
    have hUpper := mul_le_mul_of_nonneg_right hSmall hDen.le
    have hUpper2 := mul_le_mul_of_nonneg_left hQBound (div_nonneg hC hNR.le)
    have hExact : C / (N : Real) *
        ((D * (N : Real)) * (2 * Real.log (N : Real))) =
        K * Real.log (N : Real) := by
      dsimp [K]
      field_simp
    rw [hExact] at hUpper2
    change K * Real.log (N : Real) < Q - P at hSep
    nlinarith only [hScaled, hUpper, hUpper2, hSep]
  refine And.intro hTransfer.1 (And.intro hTransfer.2.1 (And.intro ?_ ?_))
  . intro hSep
    exact hTransfer.2.2.1 (hSpatial B L hL hSep)
  . intro hSep
    have hReverse := hSpatial L B hB hSep
    apply hTransfer.2.2.2
    rw [neg_div]
    linarith only [hReverse]

theorem nicolasPrimeProductClock_nat_eq_prefix_clock (N : Nat) :
    nicolasPrimeProductClock (N : Real) =
      Real.exp (Real.exp ((primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat))) -
          Real.eulerMascheroniConstant)) := by
  classical
  let B := (primeProfilePrefixSet N).sum
    (fun p => Real.log (1 + primeProfileWeight (p : Nat)))
  have hPrefix : Nat.primesLE N = (Finset.Ioc 0 N).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    . intro hp
      exact And.intro (And.intro hp.2.pos hp.1) hp.2
    . intro hp
      exact And.intro hp.1.2 hp.2
  have hFactor (p : Nat) (hp : Membership.mem ((Finset.Ioc 0 N).filter Nat.Prime) p) :
      0 < 1 - 1 / (p : Real) := by
    have hpPrime := (Finset.mem_filter.mp hp).2
    have hpR : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hpR)
  have hLogM : Real.log (Robin1984.nicolasMertensProduct (N : Real)) = -B := by
    unfold Robin1984.nicolasMertensProduct
    rw [Nat.floor_natCast, hPrefix,
      Real.log_prod (fun p hp => (hFactor p hp).ne')]
    dsimp [B]
    rw [primePrefixProfile_logSum_eq_neg_logProduct]
    ring
  have hPos : 0 < Real.exp (-Real.eulerMascheroniConstant) /
      Robin1984.nicolasMertensProduct (N : Real) :=
    div_pos (Real.exp_pos _) (Robin1984.nicolasMertensProduct_pos _)
  have hLog : Real.log (Real.exp (-Real.eulerMascheroniConstant) /
      Robin1984.nicolasMertensProduct (N : Real)) =
      B - Real.eulerMascheroniConstant := by
    rw [Real.log_div (Real.exp_pos _).ne'
      (Robin1984.nicolasMertensProduct_pos _).ne', Real.log_exp, hLogM]
    ring
  change Real.exp (Real.exp (-Real.eulerMascheroniConstant) /
    Robin1984.nicolasMertensProduct (N : Real)) =
      Real.exp (Real.exp (B - Real.eulerMascheroniConstant))
  rw [<- hLog, Real.exp_log hPos]

theorem exists_densityRatio_spatial_sign_transfer
    (a b D : Real) (ha : 0 < a) (hab : a <= b) (hD : 1 <= D) :
    exists r0 N0 : Nat, exists K : Real,
      0 < r0 /\ 2 <= N0 /\ 0 <= K /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      forall L : Real,
      let B := (primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat)))
      (forall u : Real, Set.Icc (min B L) (max B L) u ->
        0 < u /\ a <= (r : Real) / u /\ (r : Real) / u <= b) ->
      nicolasPrimeProductClock (N : Real) <= D * (N : Real) ->
      Real.exp (Real.exp (L - Real.eulerMascheroniConstant)) <= D * (N : Real) ->
      0 < (PrimeFactorUnimodality.weightEsymm
        (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) /\
      0 < Nat.factorialConvolution primeProfileRealCoefficient r L /\
      (K * Real.log (N : Real) <
          Real.exp (Real.exp (L - Real.eulerMascheroniConstant)) -
            nicolasPrimeProductClock (N : Real) ->
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
            Nat.factorialConvolution primeProfileRealCoefficient r L <
          (PrimeFactorUnimodality.densityRatio
            (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real)) /\
      (K * Real.log (N : Real) <
          nicolasPrimeProductClock (N : Real) -
            Real.exp (Real.exp (L - Real.eulerMascheroniConstant)) ->
        (PrimeFactorUnimodality.densityRatio
          (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) <
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
          Nat.factorialConvolution primeProfileRealCoefficient r L) := by
  choose r0 N0 K hr0 hN0 hK hTransfer using
    exists_primePrefixProfile_spatial_sign_transfer a b D
      Real.eulerMascheroniConstant ha hab hD
  refine Exists.intro r0 (Exists.intro N0 (Exists.intro K
    (And.intro hr0 (And.intro hN0 (And.intro hK ?_)))))
  intro r hr N hN L
  dsimp only
  intro hsegment hClock hReference
  rw [nicolasPrimeProductClock_nat_eq_prefix_clock] at hClock
  have h := hTransfer r hr N hN
    ((primeProfilePrefixSet N).sum
      (fun p => Real.log (1 + primeProfileWeight (p : Nat))))
    L hsegment hClock hReference
  rw [<- densityRatio_eq_primePrefixProfile_factorialConvolution,
    primePrefixProfile_factorialConvolution_eq_weightEsymm,
    <- nicolasPrimeProductClock_nat_eq_prefix_clock] at h
  exact h

theorem exists_densityRatio_local_spatial_threshold
    (s D : Real) (hs : 0 < s) (hD : 1 <= D) :
    exists A : Real, exists r0 N0 : Nat, exists K : Real,
      0 < A /\ 0 < r0 /\ 2 <= N0 /\ 0 <= K /\
      forall r : Nat, r0 <= r -> exists L : Real,
        Set.Ioo ((r : Real) / s - A) ((r : Real) / s + A) L /\
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
          Nat.factorialConvolution primeProfileRealCoefficient r L = s /\
        (forall v : Real,
          Set.Icc ((r : Real) / s - A) ((r : Real) / s + A) v ->
          Nat.factorialConvolution primeProfileRealCoefficient (r - 1) v /
            Nat.factorialConvolution primeProfileRealCoefficient r v = s -> v = L) /\
        forall N : Nat, N0 <= N ->
          let B := (primeProfilePrefixSet N).sum
            (fun p => Real.log (1 + primeProfileWeight (p : Nat)))
          Set.Icc ((r : Real) / s - A) ((r : Real) / s + A) B ->
          nicolasPrimeProductClock (N : Real) <= D * (N : Real) ->
          Real.exp (Real.exp (L - Real.eulerMascheroniConstant)) <= D * (N : Real) ->
          0 < (PrimeFactorUnimodality.weightEsymm
            (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) /\
          (K * Real.log (N : Real) <
              Real.exp (Real.exp (L - Real.eulerMascheroniConstant)) -
                nicolasPrimeProductClock (N : Real) ->
            s < (PrimeFactorUnimodality.densityRatio
              (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real)) /\
          (K * Real.log (N : Real) <
              nicolasPrimeProductClock (N : Real) -
                Real.exp (Real.exp (L - Real.eulerMascheroniConstant)) ->
            (PrimeFactorUnimodality.densityRatio
              (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) < s) := by
  choose A rC hA hrC hCross using exists_primeProfile_reference_local_crossing s hs
  choose rS N0 K hrS hN0 hK hSpatial using
    exists_densityRatio_spatial_sign_transfer (s / 2) (2 * s) D
      (by positivity) (by linarith) hD
  refine Exists.intro A (Exists.intro (max rC rS) (Exists.intro N0 (Exists.intro K
    (And.intro hA (And.intro (hrC.trans_le (le_max_left _ _))
      (And.intro hN0 (And.intro hK ?_)))))))
  intro r hr
  have hrC' : rC <= r := (le_max_left _ _).trans hr
  have hrS' : rS <= r := (le_max_right _ _).trans hr
  have hCrossing := hCross r hrC'
  choose L hLI hRoot hUnique using hCrossing.2
  refine Exists.intro L (And.intro hLI (And.intro hRoot (And.intro hUnique ?_)))
  intro N hN
  dsimp only
  intro hB hClock hReference
  have hLIcc : Set.Icc ((r : Real) / s - A) ((r : Real) / s + A) L :=
    And.intro hLI.1.le hLI.2.le
  have hsegment (u : Real)
      (hu : Set.Icc
        (min ((primeProfilePrefixSet N).sum
          (fun p => Real.log (1 + primeProfileWeight (p : Nat)))) L)
        (max ((primeProfilePrefixSet N).sum
          (fun p => Real.log (1 + primeProfileWeight (p : Nat)))) L) u) :
      0 < u /\ s / 2 <= (r : Real) / u /\ (r : Real) / u <= 2 * s := by
    have hIn : Set.Icc ((r : Real) / s - A) ((r : Real) / s + A) u :=
      And.intro ((le_min hB.1 hLIcc.1).trans hu.1)
        (hu.2.trans (max_le hB.2 hLIcc.2))
    have hw := hCrossing.1 u hIn
    exact And.intro hw.1 (And.intro hw.2.1 hw.2.2.1)
  have h := hSpatial r hrS' N hN L hsegment hClock hReference
  rw [hRoot] at h
  exact And.intro h.1 h.2.2

end PrimeFactorOscillations

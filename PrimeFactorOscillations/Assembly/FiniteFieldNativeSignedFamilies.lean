/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeFourCycleLaw

/-! # Witnessed sharpness inside every admissible infinite prime reservoir -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter FiniteFieldIntegerWindowTransfer

theorem native_reservoir_signed_eight_row_failure
    (R : Nat -> Prop) [DecidablePred R]
    (hR : Not (Tendsto (fun N : Nat => primeEventProbability N R) atTop (nhds 0))) :
    exists p q r s : Nat,
      And (p < q) (And (q < r) (And (r < s)
        (And (Membership.mem (nativePrimeVertexGapReservoirClass R) p)
          (And (Membership.mem (nativePrimeVertexGapReservoirClass R) q)
            (And (Membership.mem (nativePrimeVertexGapReservoirClass R) r)
              (And (Membership.mem (nativePrimeVertexGapReservoirClass R) s)
                (And
                  (Tendsto (fun U : Nat =>
                    nativeSignedWordMass (nativePrimeFourCycle p q r s)
                      (nativePrimeFourCycle p q r s) (fun _ => true) (fun _ => true)
                      (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
                        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
                    atTop (nhds (1 / 128 : Real)))
                  (Not (Tendsto (fun U : Nat =>
                    nativeSignedWordMass (nativePrimeFourCycle p q r s)
                      (nativePrimeFourCycle p q r s) (fun _ => true) (fun _ => true)
                      (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
                        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
                    atTop (nhds (1 / 256 : Real))))))))))) := by
  have hInf := (native_infinite_signed_word_family_in_reservoir R hR).1
  choose p hp using hInf.nonempty
  choose q hq using hInf.exists_gt p
  choose r hr using hInf.exists_gt q
  choose s hs using hInf.exists_gt r
  let P : Finset Nat := {p, q, r, s}
  have hP : forall x : Nat, Membership.mem P x ->
      Membership.mem (nativePrimeVertexGapReservoirClass R) x := by
    intro x hx
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    . exact hp
    . exact hq.1
    . exact hr.1
    . exact hs.1
  have hpP : Membership.mem P p := by simp [P]
  have hqP : Membership.mem P q := by simp [P]
  have hrP : Membership.mem P r := by simp [P]
  have hsP : Membership.mem P s := by simp [P]
  have hC := native_four_cycle_support P p q r s hpP hqP hrP hsP hq.2 hr.2 hs.2
  have ht := native_reservoir_signed_word_ratio_tendsto R P hP
    (nativePrimeFourCycle p q r s) (nativePrimeFourCycle p q r s)
    hC hC (fun _ => true) (fun _ => true)
  rw [native_four_cycle_all_positive_rate P p q r s hpP hqP hrP hsP hq.2 hr.2 hs.2] at ht
  have hn : Not (Tendsto (fun U : Nat =>
      nativeSignedWordMass (nativePrimeFourCycle p q r s) (nativePrimeFourCycle p q r s)
        (fun _ => true) (fun _ => true)
        (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / 256 : Real))) := by
    intro hu
    have heq : (1 / 128 : Real) = 1 / 256 := tendsto_nhds_unique ht hu
    norm_num at heq
  exact Exists.intro p (Exists.intro q (Exists.intro r (Exists.intro s
    (And.intro hq.2 (And.intro hr.2 (And.intro hs.2
      (And.intro hp (And.intro hq.1 (And.intro hr.1
        (And.intro hs.1 (And.intro ht hn)))))))))))

end PrimeFactorOscillations.FiniteFieldIntegerSignature

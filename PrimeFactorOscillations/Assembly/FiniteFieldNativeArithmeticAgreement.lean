/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeAgreementClassification
import PrimeFactorOscillations.Assembly.FiniteFieldNativeSquareCharacter

/-!
# Arithmetic classification of native prime-pair agreement

The two full-modulus character conditions are exactly integer square tests.
The endpoints are fixed before the independent field scale tends to infinity.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter FiniteFieldIntegerWindowTransfer

theorem native_agreement_rate_eq_square_test (n h m k : Nat)
    (hn : 0 < n) (hh : 0 < h) (hm : 0 < m) (hk : 0 < k) :
    nativeAgreementRate n h m k =
      (3 + (if IsSquare (h * k * n * m) then (1 : Real) else 0) +
        (if IsSquare (h * k * (n + h) * (m + k)) then (1 : Real) else 0)) / 8 := by
  classical
  have hfirst := numerator_principal_indicator_nat_eq_square
    (h * k * n * m) (by positivity)
  have hsecond := numerator_principal_indicator_nat_eq_square
    (h * k * (n + h) * (m + k)) (by positivity)
  have hcast1 : ((h * k * n * m : Nat) : Int) =
      (h : Int) * (k : Int) * (n : Int) * (m : Int) := by
    simp only [Nat.cast_mul]
  have hcast2 : ((h * k * (n + h) * (m + k) : Nat) : Int) =
      (h : Int) * (k : Int) * ((n + h : Nat) : Int) * ((m + k : Nat) : Int) := by
    simp only [Nat.cast_mul]
  unfold nativeAgreementRate
  rw [<- hcast1, <- hcast2, hfirst, hsecond]

theorem native_agreement_arithmetic_classification (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hneq : Not (And (n = m) (h = k))) :
    And
      ((nativeAgreementRate n h m k = 1 / 2) <->
        Or (IsSquare (h * k * n * m)) (IsSquare (h * k * (n + h) * (m + k))))
      ((nativeAgreementRate n h m k = 3 / 8) <->
        And (Not (IsSquare (h * k * n * m)))
          (Not (IsSquare (h * k * (n + h) * (m + k))))) := by
  classical
  have hformula := native_agreement_rate_eq_square_test n h m k hn.pos hh hm.pos hk
  have hdich := native_agreement_rate_dichotomy n h m k hn hnh hm hmk hh hk hneq
  have hnotboth : Not (And (IsSquare (h * k * n * m))
      (IsSquare (h * k * (n + h) * (m + k)))) := by
    intro hboth
    have hbad : nativeAgreementRate n h m k = 5 / 8 := by
      rw [hformula, ite_eq_left hboth.1, ite_eq_left hboth.2]
      norm_num
    rcases hdich with hrate | hrate <;> linarith only [hbad, hrate]
  by_cases hfirst : IsSquare (h * k * n * m)
  . by_cases hsecond : IsSquare (h * k * (n + h) * (m + k))
    . exact False.elim (hnotboth (And.intro hfirst hsecond))
    . norm_num [hformula, hfirst, hsecond]
  . by_cases hsecond : IsSquare (h * k * (n + h) * (m + k))
    . norm_num [hformula, hfirst, hsecond]
    . norm_num [hformula, hfirst, hsecond]

theorem native_agreement_ratio_tendsto_square_rate (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hneq : Not (And (n = m) (h = k))) :
    Tendsto (fun U : Nat =>
      nativeAgreementMass n h m k (preciseCore U + 1)
          (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds
        ((3 + (if IsSquare (h * k * n * m) then (1 : Real) else 0) +
          (if IsSquare (h * k * (n + h) * (m + k)) then (1 : Real) else 0)) / 8)) := by
  classical
  rw [<- native_agreement_rate_eq_square_test n h m k hn.pos hh hm.pos hk]
  exact native_agreement_ratio_tendsto_rate n h m k hn hnh hm hmk hh hk hneq

end PrimeFactorOscillations.FiniteFieldIntegerSignature

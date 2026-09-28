import PrimeFactorOscillations.Helpers.GenericOddWeightSums
import PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Group.FiniteCutoff

set_option autoImplicit false

/-!
# A uniform sublinear allowance for finite sets of prime odds

For either law, at most `r` distinct prime weights contribute at most
`M+1+r/M`, for every fixed positive integer `M`. Taking `M` from the desired
tolerance before increasing the rank gives the uniform sublinear loss needed
in the upper density-ratio denominator.
-/

namespace PrimeFactorOscillations

/-- Every ordinary prime weight is at most one. -/
theorem ordinaryWeight_le_one (p : Nat) (hp : 2 <= p) :
    PrimeFactorUnimodality.primeWeight p <= 1 := by
  have hd : (1 : Rat) <= ((p - 1 : Nat) : Rat) := by
    exact_mod_cast (show 1 <= p - 1 by omega)
  have h := div_le_div_of_nonneg_left (by norm_num : (0 : Rat) <= 1)
    (by norm_num : (0 : Rat) < 1) hd
  simpa [PrimeFactorUnimodality.primeWeight] using h

/-- Above a fixed integer cutoff the reciprocal weight is uniformly small. -/
theorem ordinaryWeight_le_inverse_cutoff (p M : Nat) (hM : 0 < M)
    (hp : M + 1 <= p) :
    PrimeFactorUnimodality.primeWeight p <= 1 / (M : Rat) := by
  have hpos : (0 : Rat) < (M : Rat) := by exact_mod_cast hM
  have hd : (M : Rat) <= ((p - 1 : Nat) : Rat) := by
    exact_mod_cast (show M <= p - 1 by omega)
  exact div_le_div_of_nonneg_left (by norm_num) hpos hd

/-- The exceptional prime two and all later generic weights are dominated. -/
theorem genericOddWeight_le_ordinary (p : Nat) (hp : 2 <= p) :
    genericOddWeight p <= PrimeFactorUnimodality.primeWeight p := by
  by_cases heq : p = 2
  next =>
    subst p
    norm_num [genericOddWeight, genericOddEta, PrimeFactorUnimodality.primeWeight]
  next =>
    have hgt : 2 < p := by omega
    have hpos : 0 < PrimeFactorUnimodality.primeWeight p - genericOddWeight p := by
      rw [ordinaryWeight_cast p (by omega), genericOddWeight]
      exact (genericOdd_weight_correction_bound p hgt).1
    linarith

/-- Uniform allowance for every finite set of distinct ordinary prime weights. -/
theorem ordinary_primeWeight_allowance (s : Finset Nat)
    (hs : forall p, Membership.mem s p -> Nat.Prime p) (M : Nat) (hM : 0 < M) :
    s.sum PrimeFactorUnimodality.primeWeight <=
      (M : Rat) + 1 + (s.card : Rat) / (M : Rat) := by
  have h := Finset.sum_le_cutoff_add_card_mul s PrimeFactorUnimodality.primeWeight
    (M + 1) (1 / (M : Rat)) (div_nonneg (by norm_num) (Nat.cast_nonneg M))
    (fun p hp _ => ordinaryWeight_le_one p (hs p hp).two_le)
    (fun p _ hp => ordinaryWeight_le_inverse_cutoff p M hM hp)
  simpa [div_eq_mul_inv] using h

/-- The same allowance for generic odd weights, including prime two exactly. -/
theorem genericOdd_primeWeight_allowance (s : Finset Nat)
    (hs : forall p, Membership.mem s p -> Nat.Prime p) (M : Nat) (hM : 0 < M) :
    s.sum genericOddWeight <= (M : Rat) + 1 + (s.card : Rat) / (M : Rat) := by
  apply le_trans (Finset.sum_le_sum (fun p hp =>
    genericOddWeight_le_ordinary p (hs p hp).two_le))
  exact ordinary_primeWeight_allowance s hs M hM

end PrimeFactorOscillations

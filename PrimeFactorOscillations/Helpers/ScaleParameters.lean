import PrimeFactorOscillations.Helpers.WeightSumLower

set_option autoImplicit false

/-! # Fixed parameters chosen before the rank and prime cutoff vary -/

namespace PrimeFactorOscillations

/-- Choose the finite-prefix cutoff from epsilon, then one rank threshold
absorbs its fixed cost for every larger rank. -/
theorem exists_upper_scale_parameters (epsilon : Real) (he : 0 < epsilon) :
    exists M : Nat, 0 < M /\ (1 : Real) / M <= epsilon / 8 /\
      exists K : Nat, 1 <= K /\ forall k : Nat, K <= k ->
        primeWeightLowerConstant + M + 1 <= (epsilon / 8) * k := by
  choose M hM using exists_nat_gt (max (4 : Real) (8 / epsilon))
  have hfour : (4 : Real) < M := (le_max_left _ _).trans_lt hM
  have hMpos : (0 : Real) < M := by linarith
  have hMnat : 0 < M := by exact_mod_cast hMpos
  have hreciprocal : (8 : Real) / epsilon < M := (le_max_right _ _).trans_lt hM
  have hden : (0 : Real) < 8 / epsilon := div_pos (by norm_num) he
  have hsmall : (1 : Real) / M <= epsilon / 8 := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 1)
      hden hreciprocal.le
    have hid : (1 : Real) / (8 / epsilon) = epsilon / 8 := by field_simp
    rwa [hid] at h
  refine Exists.intro M (And.intro hMnat (And.intro hsmall ?_))
  choose K hK using exists_nat_gt
    (max (1 : Real) ((primeWeightLowerConstant + M + 1) / (epsilon / 8)))
  have hone : (1 : Real) < K := (le_max_left _ _).trans_lt hK
  have hKnat : 1 <= K := by
    have h : (1 : Nat) < K := by exact_mod_cast hone
    omega
  refine Exists.intro K (And.intro hKnat ?_)
  intro k hk
  have ht : (0 : Real) < epsilon / 8 := div_pos he (by norm_num)
  have hratio : (primeWeightLowerConstant + M + 1) / (epsilon / 8) < K :=
    (le_max_right _ _).trans_lt hK
  have hscaled := mul_lt_mul_of_pos_right hratio ht
  have hcancel : forall a : Real, (a / (epsilon / 8)) * (epsilon / 8) = a := by
    intro a
    field_simp
  rw [hcancel] at hscaled
  have hkk : (K : Real) <= k := by exact_mod_cast hk
  have hmon := mul_le_mul_of_nonneg_right hkk (le_of_lt ht)
  simpa only [mul_comm] using hscaled.le.trans hmon

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimePowerRootGrid

/-!
# The exact primary clock at every odd prime-power frequency

The root trace vanishes precisely off the gcd clock. This supplies the
missing zero branch of the full compensated odd-modulus classification;
the unit-reference clock is retained separately in that consumer.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

theorem prime_dvd_quotient_of_primary_clock_not_dvd
    (p m a s h : Nat) (hp : Nat.Prime p)
    (hpa : Dvd.dvd (p ^ a) h)
    (hnd : Not (Dvd.dvd (Nat.gcd m (p ^ s)) h)) :
    Dvd.dvd p (m / Nat.gcd m (p ^ a)) := by
  by_contra hn
  have hcop : Nat.Coprime (Nat.gcd m (p ^ s))
      (m / Nat.gcd m (p ^ a)) :=
    Nat.Coprime.of_dvd_left (Nat.gcd_dvd_right m (p ^ s))
      (((hp.coprime_iff_not_dvd).mpr hn).pow_left s)
  have hmul : Nat.gcd m (p ^ a) * (m / Nat.gcd m (p ^ a)) = m :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left m (p ^ a))
  have hdiv : Dvd.dvd (Nat.gcd m (p ^ s)) (Nat.gcd m (p ^ a)) :=
    hcop.dvd_of_dvd_mul_right (by rw [hmul]; exact Nat.gcd_dvd_left _ _)
  exact hnd (dvd_trans hdiv (dvd_trans (Nat.gcd_dvd_right _ _) hpa))

theorem root_trace_zero_off_primary_grid (p s k h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (hnd : Not (Dvd.dvd (Nat.gcd k (p ^ s)) h)) :
    returnTransform (p ^ (s + 1)) k h = 0 := by
  have hgpos : 0 < Nat.gcd h (p ^ (s + 1)) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hd := Nat.gcd_dvd_right h (p ^ (s + 1))
    rw [hz, zero_dvd_iff] at hd
    exact (pow_ne_zero (s + 1) hp.ne_zero) hd
  choose a ha using (Nat.dvd_prime_pow hp).mp
    (Nat.gcd_dvd_right h (p ^ (s + 1)))
  have hpa : Dvd.dvd (p ^ a) h := by
    rw [<- ha.right]
    exact Nat.gcd_dvd_left _ _
  have has : a <= s := by
    by_contra hn
    have heq : a = s + 1 := by omega
    have hfull : Dvd.dvd (p ^ (s + 1)) h := by rwa [<- heq]
    exact hnd (dvd_trans (Nat.gcd_dvd_right k (p ^ s))
      (dvd_trans (pow_dvd_pow p (Nat.le_succ s)) hfull))
  choose b hb using Nat.exists_eq_add_of_le has
  subst s
  choose u hu using hpa
  have hpa : Dvd.dvd (p ^ a) h := by
    rw [hu]
    exact dvd_mul_right _ _
  have hpow : p ^ (a + b + 1) = p ^ a * p ^ (b + 1) := by
    rw [show a + b + 1 = a + (b + 1) by omega, pow_add]
  have hdivh : h / p ^ a = u := by
    rw [hu, Nat.mul_div_cancel_left u (pow_pos hp.pos a)]
  have hdivn : p ^ (a + b + 1) / p ^ a = p ^ (b + 1) := by
    rw [hpow, Nat.mul_div_cancel_left _ (pow_pos hp.pos a)]
  have hcop : Nat.Coprime u (p ^ (b + 1)) := by
    have hc := Nat.coprime_div_gcd_div_gcd hgpos
    rw [ha.right, hdivh, hdivn] at hc
    exact hc
  let H := powerKernel (p ^ (a + b + 1)) k
  have hmass : Nat.gcd (Nat.card H) (p ^ (a + b)) =
      Nat.gcd k (p ^ (a + b)) :=
    (root_kernel_mass_factors p (a + b) k hp hp2).right.left
  have hndmass : Not (Dvd.dvd (Nat.gcd (Nat.card H) (p ^ (a + b))) h) := by
    rwa [hmass]
  have hquot := prime_dvd_quotient_of_primary_clock_not_dvd
    p (Nat.card H) a (a + b) h hp hpa hndmass
  change subgroupTrace (p ^ (a + b + 1)) H h = 0
  rw [hu]
  exact (subgroup_nonprimitive_zero_iff p a b u hp hp2 H hcop).mpr hquot

/-- Complete local root-trace support, including frequency zero and power zero. -/
theorem root_trace_zero_iff_primary_clock_not_dvd (p s k h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2)) :
    returnTransform (p ^ (s + 1)) k h = 0 <->
      Not (Dvd.dvd (Nat.gcd k (p ^ s)) h) := by
  constructor
  { intro hz hd
    exact root_trace_nonzero_of_primary_clock_dvd p s k h hp hp2 hd hz }
  { exact root_trace_zero_off_primary_grid p s k h hp hp2 }

end PrimeFactorOscillations.PrimePowerReturnSpectrum

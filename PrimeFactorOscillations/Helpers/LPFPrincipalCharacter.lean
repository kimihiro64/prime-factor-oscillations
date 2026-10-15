/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrincipalPrefix
import PrimeFactorOscillations.Helpers.QRHCharacterChebyshev

/-!
# The principal character in the uniform LPF character-prefix input

The modulus-one character sum is the actual Chebyshev psi. The existing
finite Euler correction is reused for the principal character as well.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

open BombieriVinogradov.SiegelWalfisz Robin1984

theorem principalPsi_power_bound {x : Real} (hx : 65536 <= x) :
    abs (Chebyshev.psi x - x) <=
      lpfPrincipalPointwiseConstant * x ^ (15 / 16 : Real) := by
  have hLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos
      (by norm_num : (0 : Real) < Inv.inv (2 : Real))
    rw [Real.log_inv] at h
    norm_num at h
    linarith only [h]
  have hLogBase : (2 : Real) <= Real.log 65536 := by
    rw [show (65536 : Real) = 2 ^ (16 : Nat) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hLogTwo]
  have hLog := hLogBase.trans (Real.log_le_log (by norm_num) hx)
  exact abs_psi_sub_self_le_fifteen_sixteenths hx hLog

theorem characterChebyshevSum_one_level_one (x : Nat) :
    characterChebyshevSum x (1 : DirichletCharacter Complex 1) =
      (Chebyshev.psi (x : Real) : Complex) := by
  have hChar : forall n : Nat,
      (1 : DirichletCharacter Complex 1) (n : ZMod 1) = 1 := by
    intro n
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _]
    exact map_one _
  have hSet : Finset.Ioc (0 : Nat) x = Finset.Icc 1 x := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  simp [characterChebyshevSum, BombieriVinogradov.VaughanMeanValue.psiCharacterSum,
    Chebyshev.psi, hSet, hChar]

/-- The exact finite Euler correction also applies to the principal character. -/
theorem norm_principal_characterChebyshevSum_sub_nat_le
    {N x : Nat} [NeZero N] (hx : 65536 <= x) :
    norm (characterChebyshevSum x (1 : DirichletCharacter Complex N) - (x : Complex)) <=
      (lpfPrincipalPointwiseConstant + 1 / Real.log (2 : Real)) *
        (x : Real) ^ (15 / 16 : Real) *
          (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2 := by
  have hNne := NeZero.ne N
  have hNR : (1 : Real) <= (N : Real) := by
    exact_mod_cast (by omega : 1 <= N)
  have hxR : (1 : Real) <= (x : Real) := by
    exact_mod_cast (by omega : 1 <= x)
  have hxPos : 0 < (x : Real) := zero_lt_one.trans_le hxR
  have hL2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hLogN := Real.log_nonneg hNR
  have hLogX := Real.log_nonneg hxR
  have hLogX2 : 0 <= Real.log ((x : Real) + 2) := Real.log_nonneg (by linarith)
  have hLogs : Real.log (x : Real) <= Real.log ((x : Real) + 2) :=
    Real.log_le_log hxPos (by linarith)
  let B : Real := 1 + Real.log N + Real.log ((x : Real) + 2)
  have hB : 1 <= B := by dsimp [B]; linarith only [hLogN, hLogX2]
  have hBsq : 1 <= B ^ 2 := by nlinarith only [hB]
  have hPow : 0 <= (x : Real) ^ (15 / 16 : Real) := Real.rpow_nonneg hxPos.le _
  have hOnePow : 1 <= (x : Real) ^ (15 / 16 : Real) :=
    Real.one_le_rpow hxR (by norm_num)
  have hC := lpfPrincipalPointwiseConstant_pos
  have hPrimitive : characterChebyshevSum x
      (1 : DirichletCharacter Complex N).primitiveCharacter =
        (Chebyshev.psi (x : Real) : Complex) := by
    have hLevel : (1 : DirichletCharacter Complex N).conductor = 1 :=
      @DirichletCharacter.conductor_one Complex inferInstance N inferInstance
    rw [@DirichletCharacter.primitiveCharacter_one Complex inferInstance N inferInstance,
      hLevel]
    exact characterChebyshevSum_one_level_one x
  have hCorrection := norm_characterChebyshevSum_sub_primitive_le
    hNne (1 : DirichletCharacter Complex N) (by omega : 0 < x)
  rw [hPrimitive] at hCorrection
  have hProduct : Real.log N * Real.log (x : Real) <= B ^ 2 := by
    have hn : Real.log N <= B := by dsimp [B]; linarith only [hLogX2]
    have ht : Real.log (x : Real) <= B := by dsimp [B]; linarith only [hLogs, hLogN]
    simpa only [pow_two] using mul_le_mul hn ht hLogX (zero_le_one.trans hB)
  have hProduct' : Real.log N * Real.log (x : Real) <=
      (x : Real) ^ (15 / 16 : Real) * B ^ 2 := by
    calc
      _ <= B ^ 2 := hProduct
      _ = 1 * B ^ 2 := by ring
      _ <= _ := mul_le_mul_of_nonneg_right hOnePow (sq_nonneg B)
  have hCorrection' : norm (characterChebyshevSum x
      (1 : DirichletCharacter Complex N) - (Chebyshev.psi (x : Real) : Complex)) <=
        (1 / Real.log (2 : Real)) * (x : Real) ^ (15 / 16 : Real) * B ^ 2 := by
    calc
      _ <= Real.log N * Real.log (x : Real) / Real.log (2 : Real) := hCorrection
      _ <= ((x : Real) ^ (15 / 16 : Real) * B ^ 2) / Real.log (2 : Real) :=
        div_le_div_of_nonneg_right hProduct' hL2.le
      _ = _ := by ring
  have hPsi := principalPsi_power_bound (by exact_mod_cast hx : (65536 : Real) <= (x : Real))
  have hPsiNorm : norm ((Chebyshev.psi (x : Real) : Complex) - (x : Complex)) <=
      lpfPrincipalPointwiseConstant * (x : Real) ^ (15 / 16 : Real) := by
    have h : norm ((Chebyshev.psi (x : Real) - (x : Real) : Real) : Complex) <=
        lpfPrincipalPointwiseConstant * (x : Real) ^ (15 / 16 : Real) := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hPsi
    simpa only [Complex.ofReal_sub, Complex.ofReal_natCast] using h
  have hPsiNorm' : norm ((Chebyshev.psi (x : Real) : Complex) - (x : Complex)) <=
      lpfPrincipalPointwiseConstant * (x : Real) ^ (15 / 16 : Real) * B ^ 2 := by
    calc
      _ <= lpfPrincipalPointwiseConstant * (x : Real) ^ (15 / 16 : Real) := hPsiNorm
      _ = (lpfPrincipalPointwiseConstant * (x : Real) ^ (15 / 16 : Real)) * 1 := by ring
      _ <= _ := mul_le_mul_of_nonneg_left hBsq (mul_nonneg hC.le hPow)
  have hTriangle : norm (characterChebyshevSum x
      (1 : DirichletCharacter Complex N) - (x : Complex)) <=
        norm (characterChebyshevSum x (1 : DirichletCharacter Complex N) -
          (Chebyshev.psi (x : Real) : Complex)) +
        norm ((Chebyshev.psi (x : Real) : Complex) - (x : Complex)) := by
    calc
      _ = norm ((characterChebyshevSum x (1 : DirichletCharacter Complex N) -
          (Chebyshev.psi (x : Real) : Complex)) +
          ((Chebyshev.psi (x : Real) : Complex) - (x : Complex))) := by
        congr 1
        ring
      _ <= _ := norm_add_le _ _
  change norm (characterChebyshevSum x (1 : DirichletCharacter Complex N) - (x : Complex)) <=
    (lpfPrincipalPointwiseConstant + 1 / Real.log (2 : Real)) *
      (x : Real) ^ (15 / 16 : Real) * B ^ 2
  nlinarith only [hTriangle, hCorrection', hPsiNorm']

end PrimeFactorOscillations.QRH

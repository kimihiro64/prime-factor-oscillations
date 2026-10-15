/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFGridReference
import PrimeFactorOscillations.Helpers.LPFRationalApprox

/-!
# Exact lifting into the rational major grid

An integer numerator congruent to a unit lifts to its canonical rational
center, with the exact bounded signed offset. The denominator divides N;
no prime-denominator restriction is imposed. The physical error gives the
exact signed offset bound. Outside the actual major grid, the chosen unit
approximation has P<q<=2M/P and error at most P/(M*q).
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_mem_rational_grid_of_unit_lift {N : Nat} [NeZero N]
    (P W q : Nat) (k a ell : Int) (u : Units (ZMod q))
    (hq : 0 < q) (hqP : q <= P) (hDiv : Dvd.dvd q N)
    (hu : (a : ZMod q) = (u : ZMod q))
    (hLo : -(W : Int) <= ell) (hHi : ell <= (W : Int))
    (hLift : ((N / q : Nat) : Int) * a + ell = k) :
    Membership.mem (lpfRationalGrid N P W) (k : ZMod N) := by
  classical
  let i : Fin P := Fin.mk (q - 1) (by omega)
  have hi : i.val + 1 = q := by dsimp [i]; omega
  have hUnit : IsUnit (a : ZMod (i.val + 1)) := by
    rw [hi, hu]
    exact u.isUnit
  let v : Units (ZMod (i.val + 1)) := hUnit.unit
  let aval : Nat := (v : ZMod (i.val + 1)).val
  have hValCast : ((aval : Int) : ZMod (i.val + 1)) = (v : ZMod (i.val + 1)) := by
    simp only [aval, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hACast : (a : ZMod (i.val + 1)) = ((aval : Int) : ZMod (i.val + 1)) :=
    hUnit.unit_spec.symm.trans hValCast.symm
  have hDvd := (ZMod.intCast_eq_intCast_iff_dvd_sub a (aval : Int) (i.val + 1)).mp hACast
  rw [hi] at hDvd
  choose z hz using hDvd
  have hMul : ((N / q : Nat) : Int) * (q : Int) = (N : Int) := by
    exact_mod_cast (Nat.div_mul_cancel hDiv)
  have hScaled : ((N / q : Nat) : Int) * (aval : Int) - ((N / q : Nat) : Int) * a =
      (N : Int) * z := by
    calc
      _ = ((N / q : Nat) : Int) * ((aval : Int) - a) := by ring
      _ = ((N / q : Nat) : Int) * ((q : Int) * z) := by rw [hz]
      _ = (((N / q : Nat) : Int) * (q : Int)) * z := by ring
      _ = _ := by rw [hMul]
  have hCenters : ((((N / q : Nat) : Int) * a : Int) : ZMod N) =
      ((((N / q : Nat) : Int) * (aval : Int) : Int) : ZMod N) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mpr (Exists.intro z hScaled)
  have hPoint : lpfRationalPacketPoint N (Sigma.mk i v, ell) = (k : ZMod N) := by
    change (((N / (i.val + 1) * aval : Nat) : ZMod N) + (ell : ZMod N)) = (k : ZMod N)
    rw [hi]
    have hCenter : ((N / q * aval : Nat) : ZMod N) =
        ((((N / q : Nat) : Int) * a : Int) : ZMod N) := by
      simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul] using hCenters.symm
    rw [hCenter, <- Int.cast_add, hLift]
  unfold lpfRationalGrid
  apply Finset.mem_image.mpr
  refine Exists.intro (Sigma.mk i v, ell) (And.intro ?_ hPoint)
  unfold lpfRationalPackets
  exact Finset.mem_product.mpr (And.intro (Finset.mem_univ _)
    (Finset.mem_Icc.mpr (And.intro hLo hHi)))

theorem lpf_small_denominator_mem_rational_grid {N : Nat} [NeZero N]
    (M P q : Nat) (k a : Int) (u : Units (ZMod q)) (beta : Real)
    (hM : 0 < M) (hq : 0 < q) (hqP : q <= P)
    (hDivM : Dvd.dvd M N) (hDivq : Dvd.dvd q N)
    (hu : (a : ZMod q) = (u : ZMod q))
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta <= (P : Real) / ((M : Real) * (q : Real))) :
    Membership.mem (lpfRationalGrid N P ((N / M) * P)) (k : ZMod N) := by
  let ell : Int := k - ((N / q : Nat) : Int) * a
  have hNR : (0 : Real) < (N : Real) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hMR : (0 : Real) < (M : Real) := Nat.cast_pos.mpr hM
  have hqR : (0 : Real) < (q : Real) := Nat.cast_pos.mpr hq
  have hQuotq : ((N / q : Nat) : Real) = (N : Real) / (q : Real) := by
    have h : ((N / q : Nat) : Real) * (q : Real) = (N : Real) := by
      exact_mod_cast (Nat.div_mul_cancel hDivq)
    field_simp [ne_of_gt hqR]
    nlinarith only [h]
  have hQuotM : ((N / M : Nat) : Real) = (N : Real) / (M : Real) := by
    have h : ((N / M : Nat) : Real) * (M : Real) = (N : Real) := by
      exact_mod_cast (Nat.div_mul_cancel hDivM)
    field_simp [ne_of_gt hMR]
    nlinarith only [h]
  have hEll : (ell : Real) = (N : Real) * beta := by
    have hCastQuot : (((N / q : Nat) : Int) : Real) = ((N / q : Nat) : Real) :=
      Int.cast_natCast _
    dsimp only [ell]
    rw [Int.cast_sub, Int.cast_mul, hCastQuot]
    rw [hQuotq]
    field_simp [ne_of_gt hNR, ne_of_gt hqR] at hAlpha
    field_simp [ne_of_gt hqR]
    nlinarith only [hAlpha]
  have hqOne : (1 : Real) <= (q : Real) := by exact_mod_cast hq
  have hPQ : (P : Real) <= (P : Real) * (q : Real) := by
    nlinarith only [hqOne, (show (0 : Real) <= (P : Real) from Nat.cast_nonneg P)]
  have hCompare := div_le_div_of_nonneg_right hPQ
    (by positivity : 0 <= (M : Real) * (q : Real))
  have hCancel : ((P : Real) * (q : Real)) / ((M : Real) * (q : Real)) =
      (P : Real) / (M : Real) := by field_simp [ne_of_gt hMR, ne_of_gt hqR]
  rw [hCancel] at hCompare
  have hOffset : abs (ell : Real) <= (((N / M) * P : Nat) : Real) := by
    rw [hEll, abs_mul, abs_of_pos hNR]
    calc
      _ <= (N : Real) * ((P : Real) / ((M : Real) * (q : Real))) :=
        mul_le_mul_of_nonneg_left hBeta hNR.le
      _ <= (N : Real) * ((P : Real) / (M : Real)) :=
        mul_le_mul_of_nonneg_left hCompare hNR.le
      _ = ((N / M : Nat) : Real) * (P : Real) := by rw [hQuotM]; ring
      _ = _ := by rw [Nat.cast_mul]
  have hBounds := abs_le.mp hOffset
  have hLo : -(((N / M) * P : Nat) : Int) <= ell := by
    have h : ((-(((N / M) * P : Nat) : Int) : Int) : Real) <= (ell : Real) := by
      simpa only [Int.cast_neg, Int.cast_natCast] using hBounds.1
    exact Int.cast_le.mp h
  have hHi : ell <= (((N / M) * P : Nat) : Int) := by
    have h : (ell : Real) <= ((((N / M) * P : Nat) : Int) : Real) := by
      simpa only [Int.cast_natCast] using hBounds.2
    exact Int.cast_le.mp h
  apply lpf_mem_rational_grid_of_unit_lift P ((N / M) * P) q k a ell u
    hq hqP hDivq hu hLo hHi
  dsimp [ell]
  ring
theorem lpf_exists_minor_unit_approximation {N : Nat} [NeZero N]
    (M P : Nat) (k : Int) (hP : 0 < P) (hPM : P <= M)
    (hDivM : Dvd.dvd M N) (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N)
    (hMinor : Not (Membership.mem (lpfRationalGrid N P ((N / M) * P)) (k : ZMod N))) :
    exists a : Int, exists q : Nat, exists u : Units (ZMod q), exists beta : Real,
      And (0 < q) (And (P < q) (And (q <= 2 * M)
        (And ((q : Real) <= 2 * (M : Real) / (P : Real))
          (And ((a : ZMod q) = (u : ZMod q))
            (And ((k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
              (abs beta <= (P : Real) / ((M : Real) * (q : Real)))))))) := by
  choose a q u beta hq hqNat hqTop hu hAlpha hBeta using
    lpf_exists_physical_unit_approximation ((k : Real) / (N : Real)) M P hP hPM
  have hLarge : P < q := by
    by_contra hNot
    have hqP : q <= P := by omega
    exact hMinor (lpf_small_denominator_mem_rational_grid M P q k a u beta
      (hP.trans_le hPM) hq hqP hDivM (hDiv q hq hqP) hu hAlpha hBeta)
  exact Exists.intro a (Exists.intro q (Exists.intro u (Exists.intro beta
    (And.intro hq (And.intro hLarge (And.intro hqNat (And.intro hqTop
      (And.intro hu (And.intro hAlpha hBeta)))))))))
end PrimeFactorOscillations.LPF

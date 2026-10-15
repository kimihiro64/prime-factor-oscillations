/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import PrimeFactorOscillations.Helpers.LPFCyclicFourier
import PrimeFactorOscillations.Helpers.LPFRamanujan

/-!
# Exact separation of the rational major-frequency grid

The complete physical squared-error budget retains M^3/P, M^(13/5),
M^(2*alpha+1)*P^4, M^(4*alpha-1)*P^9 and M^2*P^2, with logarithms.
The major packet is the coupled S^2-A^2=2*A*(S-A)+(S-A)^2. This probe
closes its actual grid disjointness condition: denominators<=P, offsets
in [-W,W], every denominator divides N, and 2*W*P^2<N. Together with
the maintained Parseval interface, the intended consumer has normalized
reference energy O(M*P) and grid size O(P^3/M). No minor or tail bound
is assumed proved here, and no actual-state entry follows from separation.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

def lpfRationalGridPoint (N q a : Nat) (k : Int) : ZMod N :=
  (((N / q) * a : Nat) : ZMod N) + (k : ZMod N)

theorem lpfRationalGridPoint_injective {N : Nat} [NeZero N]
    (P W q r a b : Nat) (k ell : Int)
    (hq : 0 < q) (hr : 0 < r) (hqP : q <= P) (hrP : r <= P)
    (hqd : Dvd.dvd q N) (hrd : Dvd.dvd r N)
    (ha : a < q) (hb : b < r) (haq : Nat.Coprime a q) (hbr : Nat.Coprime b r)
    (hklo : -(W : Int) <= k) (hkhi : k <= (W : Int))
    (hello : -(W : Int) <= ell) (helhi : ell <= (W : Int))
    (hWidth : 2 * W * P ^ 2 < N)
    (hEq : lpfRationalGridPoint N q a k = lpfRationalGridPoint N r b ell) :
    And (q = r) (And (a = b) (k = ell)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNi : 0 < (N : Int) := by exact_mod_cast hN
  have hqi : 0 < (q : Int) := by exact_mod_cast hq
  have hri : 0 < (r : Int) := by exact_mod_cast hr
  have hqMul : (q : Int) * ((N / q : Nat) : Int) = (N : Int) := by
    exact_mod_cast (Nat.mul_div_cancel' hqd)
  have hrMul : (r : Int) * ((N / r : Nat) : Int) = (N : Int) := by
    exact_mod_cast (Nat.mul_div_cancel' hrd)
  have hCast : ((((N / q * a : Nat) : Int) + k : Int) : ZMod N) =
      ((((N / r * b : Nat) : Int) + ell : Int) : ZMod N) := by
    simpa only [Int.cast_add, Int.cast_natCast, lpfRationalGridPoint] using hEq
  have hD := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp hCast
  have hDmul : Dvd.dvd (N : Int) ((q : Int) * (r : Int) *
      ((((N / r * b : Nat) : Int) + ell) - (((N / q * a : Nat) : Int) + k))) :=
    dvd_mul_of_dvd_right hD ((q : Int) * (r : Int))
  have hIdentity : (q : Int) * (r : Int) *
      ((((N / r * b : Nat) : Int) + ell) - (((N / q * a : Nat) : Int) + k)) =
      (N : Int) * ((q : Int) * b - (r : Int) * a) +
        (q : Int) * (r : Int) * (ell - k) := by
    simp only [Nat.cast_mul]
    calc
      _ = (q : Int) * (((r : Int) * ((N / r : Nat) : Int)) * b) -
          (r : Int) * (((q : Int) * ((N / q : Nat) : Int)) * a) +
          (q : Int) * (r : Int) * (ell - k) := by ring
      _ = _ := by rw [hqMul, hrMul]; ring
  rw [hIdentity] at hDmul
  have hSmall : Dvd.dvd (N : Int) ((q : Int) * (r : Int) * (ell - k)) := by
    have h := dvd_sub hDmul (dvd_mul_right (N : Int) ((q : Int) * b - (r : Int) * a))
    simpa only [add_sub_cancel_left] using h
  have hQRNat : q * r <= P ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hqP hrP
  have hQR : (q : Int) * (r : Int) <= (P : Int) ^ 2 := by exact_mod_cast hQRNat
  have hWi : 2 * (W : Int) * (P : Int) ^ 2 < (N : Int) := by exact_mod_cast hWidth
  have hDeltaLo : -(2 * (W : Int)) <= ell - k := by omega
  have hDeltaHi : ell - k <= 2 * (W : Int) := by omega
  have hLow := mul_le_mul_of_nonneg_left hDeltaLo (by positivity : 0 <= (q : Int) * r)
  have hHigh := mul_le_mul_of_nonneg_left hDeltaHi (by positivity : 0 <= (q : Int) * r)
  have hCap := mul_le_mul_of_nonneg_right hQR (by positivity : 0 <= 2 * (W : Int))
  have hLo : -(N : Int) < (q : Int) * r * (ell - k) := by nlinarith only [hLow, hCap, hWi]
  have hHi : (q : Int) * r * (ell - k) < (N : Int) := by nlinarith only [hHigh, hCap, hWi]
  choose z hz using hSmall
  have hzZero : z = 0 := by
    by_contra hzNe
    have hCases : Or (z <= -1) (1 <= z) := by omega
    rcases hCases with hNeg | hPos
    next =>
      have hMul := mul_le_mul_of_nonneg_left hNeg hNi.le
      nlinarith only [hLo, hz, hMul]
    next =>
      have hMul := mul_le_mul_of_nonneg_left hPos hNi.le
      nlinarith only [hHi, hz, hMul]
  have hZero : (q : Int) * r * (ell - k) = 0 := by rw [hz, hzZero, mul_zero]
  have hKL : k = ell := by
    have hNZ : Not ((q : Int) * r = 0) := ne_of_gt (mul_pos hqi hri)
    have hD0 := (mul_eq_zero.mp hZero).resolve_left hNZ
    omega
  have hCenter : ((N / q * a : Nat) : ZMod N) = ((N / r * b : Nat) : ZMod N) := by
    have h := congrArg (fun z : ZMod N => z - (ell : ZMod N)) hEq
    simpa [lpfRationalGridPoint, hKL] using h
  have hqDPos : 0 < N / q := Nat.div_pos (Nat.le_of_dvd hN hqd) hq
  have hrDPos : 0 < N / r := Nat.div_pos (Nat.le_of_dvd hN hrd) hr
  have hCenterA : N / q * a < N := by
    have h := Nat.mul_lt_mul_of_pos_left ha hqDPos
    simpa only [Nat.div_mul_cancel hqd] using h
  have hCenterB : N / r * b < N := by
    have h := Nat.mul_lt_mul_of_pos_left hb hrDPos
    simpa only [Nat.div_mul_cancel hrd] using h
  have hNatCenter : N / q * a = N / r * b := by
    have h := congrArg (fun x : ZMod N => x.val) hCenter
    simpa only [ZMod.val_natCast_of_lt hCenterA, ZMod.val_natCast_of_lt hCenterB] using h
  have hCrossScaled : N * (a * r) = N * (b * q) := by
    calc
      _ = (q * (N / q)) * (a * r) := by rw [Nat.mul_div_cancel' hqd]
      _ = (N / q * a) * (q * r) := by ring
      _ = (N / r * b) * (q * r) := by rw [hNatCenter]
      _ = (r * (N / r)) * (b * q) := by ring
      _ = _ := by rw [Nat.mul_div_cancel' hrd]
  have hCross : a * r = b * q := Nat.eq_of_mul_eq_mul_left hN hCrossScaled
  have hqDr : Dvd.dvd q r := haq.symm.dvd_of_dvd_mul_left (by rw [hCross]; exact dvd_mul_left q b)
  have hrDq : Dvd.dvd r q := hbr.symm.dvd_of_dvd_mul_left (by rw [<- hCross]; exact dvd_mul_left r a)
  have hQR : q = r := Nat.dvd_antisymm hqDr hrDq
  have hAB : a = b := by
    rw [hQR] at hCross
    apply Nat.eq_of_mul_eq_mul_right hr
    exact hCross
  exact And.intro hQR (And.intro hAB hKL)

abbrev lpfRationalCenters (P : Nat) : Type :=
  Sigma (fun q : Fin P => Units (ZMod (q.val + 1)))

theorem lpfRationalCenters_ext {P : Nat} (i j : lpfRationalCenters P)
    (hDen : i.1.val + 1 = j.1.val + 1)
    (hVal : (i.2 : ZMod (i.1.val + 1)).val = (j.2 : ZMod (j.1.val + 1)).val) : i = j := by
  cases i with
  | mk qi ai =>
    cases j with
    | mk qj aj =>
      dsimp only at hDen hVal
      have hQ : qi = qj := Fin.ext (by omega)
      subst qj
      have hA : ai = aj := Units.ext ((ZMod.val_injective (qi.val + 1)) hVal)
      cases hA
      rfl

def lpfRationalPacketPoint {P : Nat} (N : Nat) (u : Prod (lpfRationalCenters P) Int) : ZMod N :=
  lpfRationalGridPoint N (u.1.1.val + 1) (u.1.2 : ZMod (u.1.1.val + 1)).val u.2

theorem lpfRationalPacketPoint_injective {N : Nat} [NeZero N] (P W : Nat)
    (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N) (hWidth : 2 * W * P ^ 2 < N) :
    Set.InjOn (lpfRationalPacketPoint (P := P) N)
      ((SProd.sprod (Finset.univ : Finset (lpfRationalCenters P)) (Finset.Icc (-(W : Int)) (W : Int))) :
        Set (Prod (lpfRationalCenters P) Int)) := by
  intro u hu v hv hEq
  have hU := Finset.mem_Icc.mp (Finset.mem_product.mp hu).2
  have hV := Finset.mem_Icc.mp (Finset.mem_product.mp hv).2
  have hUP : u.1.1.val + 1 <= P := by have h := u.1.1.isLt; omega
  have hVP : v.1.1.val + 1 <= P := by have h := v.1.1.isLt; omega
  have hPack := lpfRationalGridPoint_injective P W
    (u.1.1.val + 1) (v.1.1.val + 1)
    (u.1.2 : ZMod (u.1.1.val + 1)).val (v.1.2 : ZMod (v.1.1.val + 1)).val u.2 v.2
    (Nat.succ_pos _) (Nat.succ_pos _) hUP hVP
    (hDiv _ (Nat.succ_pos _) hUP) (hDiv _ (Nat.succ_pos _) hVP)
    (ZMod.val_lt _) (ZMod.val_lt _)
    (ZMod.val_coe_unit_coprime u.1.2) (ZMod.val_coe_unit_coprime v.1.2)
    hU.1 hU.2 hV.1 hV.2 hWidth hEq
  exact Prod.ext (lpfRationalCenters_ext u.1 v.1 hPack.1 hPack.2.1) hPack.2.2

theorem lpfRationalCenters_card_le (P : Nat) :
    Fintype.card (lpfRationalCenters P) <= P ^ 2 := by
  rw [Fintype.card_sigma]
  have hTerm (q : Fin P) : Fintype.card (Units (ZMod (q.val + 1))) <= P := by
    rw [ZMod.card_units_eq_totient]
    have hq := q.isLt
    exact (Nat.totient_le (q.val + 1)).trans (by omega)
  calc
    _ <= Finset.sum Finset.univ (fun _ : Fin P => P) :=
      Finset.sum_le_sum (fun q _ => hTerm q)
    _ = _ := by simp [pow_two]

noncomputable def lpfRationalCoefficient (q : Nat) : Complex :=
  (ArithmeticFunction.moebius q : Complex) / (q.totient : Complex)

theorem norm_lpfRationalCoefficient_le (q : Nat) (hq : 0 < q) :
    norm (lpfRationalCoefficient q) <= 1 / (q.totient : Real) := by
  have hPhi : 0 < (q.totient : Real) := by exact_mod_cast (Nat.totient_pos.mpr hq)
  have hMu : norm (ArithmeticFunction.moebius q : Complex) <= 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  unfold lpfRationalCoefficient
  rw [norm_div]
  simpa using div_le_div_of_nonneg_right hMu hPhi.le

theorem lpfRationalCoefficient_energy_le_one (q : Nat) (hq : 0 < q) :
    (q.totient : Real) * Complex.normSq (lpfRationalCoefficient q) <= 1 := by
  have hPhi : 0 < (q.totient : Real) := by exact_mod_cast (Nat.totient_pos.mpr hq)
  have hPhiOne : 1 <= (q.totient : Real) := by
    exact_mod_cast (show 1 <= q.totient from Nat.totient_pos.mpr hq)
  have hRho := norm_lpfRationalCoefficient_le q hq
  have hScaled : norm (lpfRationalCoefficient q) * (q.totient : Real) <= 1 := by
    calc
      _ <= (1 / (q.totient : Real)) * (q.totient : Real) :=
        mul_le_mul_of_nonneg_right hRho hPhi.le
      _ = 1 := by field_simp
  have hNonneg := norm_nonneg (lpfRationalCoefficient q)
  have hSq : (norm (lpfRationalCoefficient q) * (q.totient : Real)) ^ 2 <= 1 := by
    have h := mul_le_mul hScaled hScaled (mul_nonneg hNonneg hPhi.le) zero_le_one
    simpa only [pow_two, one_mul] using h
  have hPhiSq : (q.totient : Real) <= (q.totient : Real) ^ 2 := by nlinarith
  have hMul := mul_le_mul_of_nonneg_right hPhiSq (sq_nonneg (norm (lpfRationalCoefficient q)))
  rw [Complex.normSq_eq_norm_sq]
  nlinarith only [hSq, hMul]

theorem lpfRationalCenters_coefficient_energy (P : Nat) :
    Finset.sum Finset.univ (fun i : lpfRationalCenters P =>
      Complex.normSq (lpfRationalCoefficient (i.1.val + 1))) <= (P : Real) := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card_units_eq_totient]
  calc
    _ <= Finset.sum Finset.univ (fun _ : Fin P => (1 : Real)) :=
      Finset.sum_le_sum (fun q _ => lpfRationalCoefficient_energy_le_one _ (Nat.succ_pos _))
    _ = _ := by simp

end PrimeFactorOscillations.LPF

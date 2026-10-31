/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerSignatureReturn

/-!
# The full signed energy of native integer prime-pair weights

The actual local weight retains the sum of its two characters. Its squared
difference has four diagonal terms and six signed correlations. Distinct
positively oriented prime pairs share at most one endpoint, so at most one
cross correlation can retain a principal contribution. The original negative
phases and every overlap remain in this calculation.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open QuadraticCarrierPacket IntegerQuadraticSieve
open FiniteFieldIntegerWindowTransfer FiniteFieldIntegerCharacter

def primeCorrelation (D : Int) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum
    (fun p => (1 / (p : Real)) * (numeratorKernel D p).re)

def nativeTrace (n h p : Nat) : Real :=
  (numeratorKernel (-((h : Int) * (n : Int))) p).re +
    (numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p).re

def nativeTraceEnergy (n h m k Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum
    (fun p => (1 / (p : Real)) * (nativeTrace n h p - nativeTrace m k p) ^ 2)

theorem real_kernel_mul (D E : Int) (p : Nat) :
    (numeratorKernel (D * E) p).re =
      (numeratorKernel D p).re * (numeratorKernel E p).re := by
  have hD : (numeratorKernel D p).im = 0 := by
    by_cases ho : Odd p <;> simp [numeratorKernel, ho]
  have hE : (numeratorKernel E p).im = 0 := by
    by_cases ho : Odd p <;> simp [numeratorKernel, ho]
  rw [numerator_kernel_mul_numerators, Complex.mul_re, hD, hE]
  ring

theorem real_kernel_le_one (D : Int) (p : Nat)
    (hp : Nat.Prime p) (hp2 : Not (p = 2)) :
    (numeratorKernel D p).re <= 1 := by
  have : Fact (Nat.Prime p) := Fact.mk hp
  rw [numerator_kernel_prime D p hp2]
  simpa using FiniteField.QuadraticPairTwistEuler.character_le_one (D : ZMod p)

theorem real_kernel_square_endpoint (h P p : Nat)
    (hh : 0 < h) (hP : Nat.Prime P) (hp : Nat.Prime p)
    (hp2 : 2 < p) (hhp : h < p) (hpP : p < P)
    (D : Int) (hsign : Or (D = (h : Int) * (P : Int))
      (D = -((h : Int) * (P : Int)))) :
    (numeratorKernel D p).re ^ 2 = 1 := by
  have : Fact (Nat.Prime p) := Fact.mk hp
  have hhn : Not ((h : ZMod p) = 0) := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt hh hhp) ((ZMod.natCast_eq_zero_iff h p).mp hz)
  have hPn : Not ((P : ZMod p) = 0) := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff P p).mp hz
    cases (Nat.dvd_prime hP).mp hd with
    | inl he => exact hp.ne_one he
    | inr he => omega
  have hbase : Not ((((h : Int) * (P : Int)) : ZMod p) = 0) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using mul_ne_zero hhn hPn
  have hDn : Not ((D : ZMod p) = 0) := by
    cases hsign with
    | inl he => simpa [he, Int.cast_mul, Int.cast_natCast] using hbase
    | inr he => simpa [he, Int.cast_neg, Int.cast_mul, Int.cast_natCast] using hbase
  rw [numerator_kernel_prime D p (by omega)]
  exact_mod_cast quadraticChar_sq_one hDn

theorem prime_correlation_le_mass (D : Int) (Y X : Nat) (hY : 2 < Y) :
    primeCorrelation D Y X <= reciprocalBand Y X := by
  unfold primeCorrelation reciprocalBand
  apply Finset.sum_le_sum
  intro p hp
  have hdata := Finset.mem_filter.mp hp
  have hband := Finset.mem_Ico.mp hdata.1
  have hle := real_kernel_le_one D p hdata.2 (by omega)
  have hn : 0 <= 1 / (p : Real) := by positivity
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hle hn

theorem exists_coprime_prime_correlation_bound :
    exists C : Real, And (0 < C)
      (forall h P : Nat, 0 < h -> Nat.Prime P -> 2 < P -> Nat.Coprime P h ->
        forall D : Int,
          Or (D = (h : Int) * (P : Int)) (D = -((h : Int) * (P : Int))) ->
        forall Y X : Nat, 1 <= Y ->
          abs (primeCorrelation D Y X) <=
            C * (3 + Real.log ((4 * h * P : Nat) : Real)) ^ 2 *
              (Y : Real) ^ (-1 / 32 : Real)) := by
  choose C hCpos hC using QRH.exists_primeCharacter_reciprocal_tail_bound
  refine Exists.intro C (And.intro hCpos ?_)
  intro h P hh hP hP2 hPh D hSign Y X hY
  have hAbs : D.natAbs = h * P := by
    cases hSign with
    | inl hs => simp only [hs, Int.natAbs_mul, Int.natAbs_natCast]
    | inr hs => simp only [hs, Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast]
  have hprod : 0 < h * P := Nat.mul_pos hh hP.pos
  have hD : Not (D = 0) := by
    intro hz
    rw [hz, Int.natAbs_zero] at hAbs
    omega
  have : NeZero (4 * D.natAbs) := NeZero.mk (by
    apply ne_of_gt
    apply Nat.mul_pos (by decide : 0 < (4 : Nat))
    rw [hAbs]
    exact hprod)
  have hn := numerator_character_ne_one_of_coprime_prime_factor h P hh hP hP2 hPh
    D hD hSign
  have ht := hC (numeratorCharacter D hD) hn Y X hY
  simp only [numerator_character_natCast] at ht
  have hlevel : 4 * D.natAbs = 4 * h * P := by rw [hAbs, Nat.mul_assoc]
  rw [hlevel] at ht
  have hid : primeCorrelation D Y X =
      (Finset.sum ((Finset.Ico Y X).filter Nat.Prime)
        (fun p => HSMul.hSMul (1 / (p : Real)) (numeratorKernel D p))).re := by
    simp [primeCorrelation]
  rw [hid]
  exact (Complex.abs_re_le_norm _).trans ht

theorem exists_endpoint_prime_correlation_bound :
    exists C : Real, And (0 < C)
      (forall h k P R H T Y X : Nat,
        0 < h -> 0 < k -> Nat.Prime P -> Nat.Prime R -> Not (P = R) ->
        h <= H -> k <= H -> H < P -> 2 < P -> P <= T -> R <= T -> 1 <= Y ->
        forall D : Int,
          Or (D = (h : Int) * (k : Int) * (P : Int) * (R : Int))
            (D = -((h : Int) * (k : Int) * (P : Int) * (R : Int))) ->
          abs (primeCorrelation D Y X) <=
            C * (3 + Real.log ((4 * H * H * T * T : Nat) : Real)) ^ 2 *
              (Y : Real) ^ (-1 / 32 : Real)) := by
  choose C hCpos hC using exists_coprime_prime_correlation_bound
  refine Exists.intro C (And.intro hCpos ?_)
  intro h k P R H T Y X hh hk hP hR hPR hhH hkH hHP hP2 hPT hRT hY D hsign
  let c : Nat := h * k * R
  have hc : 0 < c := Nat.mul_pos (Nat.mul_pos hh hk) hR.pos
  have hco : Nat.Coprime P c :=
    endpoint_coefficient_coprime h k P R hh hk hP hR
      (hhH.trans_lt hHP) (hkH.trans_lt hHP) hPR
  have hsgn : Or (D = (c : Int) * (P : Int)) (D = -((c : Int) * (P : Int))) := by
    cases hsign with
    | inl he =>
      left
      rw [he]
      dsimp [c]
      ring
    | inr he =>
      right
      rw [he]
      dsimp [c]
      ring
  have hb := hC c P hc hP hP2 hco D hsgn Y X hY
  exact hb.trans (endpoint_cost_le_uniform C h k P R H T Y hCpos.le
    hh hk hP.pos hR.pos hhH hkH hPT hRT)

theorem native_trace_energy_identity (n h m k Y X : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hhY : h < Y) (hkY : k < Y)
    (hY : 2 < Y) (hXn : X <= n) (hXm : X <= m) :
    let A : Int := -((h : Int) * (n : Int))
    let B : Int := (h : Int) * ((n + h : Nat) : Int)
    let C : Int := -((k : Int) * (m : Int))
    let D : Int := (k : Int) * ((m + k : Nat) : Int)
    nativeTraceEnergy n h m k Y X =
      4 * reciprocalBand Y X +
        2 * primeCorrelation (A * B) Y X + 2 * primeCorrelation (C * D) Y X -
        2 * primeCorrelation (A * C) Y X - 2 * primeCorrelation (A * D) Y X -
        2 * primeCorrelation (B * C) Y X - 2 * primeCorrelation (B * D) Y X := by
  dsimp only
  let A : Int := -((h : Int) * (n : Int))
  let B : Int := (h : Int) * ((n + h : Nat) : Int)
  let C : Int := -((k : Int) * (m : Int))
  let D : Int := (k : Int) * ((m + k : Nat) : Int)
  have hpoint : forall p : Nat, Membership.mem ((Finset.Ico Y X).filter Nat.Prime) p ->
      (1 / (p : Real)) * (nativeTrace n h p - nativeTrace m k p) ^ 2 =
        4 * (1 / (p : Real)) +
          2 * ((1 / (p : Real)) * (numeratorKernel (A * B) p).re) +
          2 * ((1 / (p : Real)) * (numeratorKernel (C * D) p).re) -
          2 * ((1 / (p : Real)) * (numeratorKernel (A * C) p).re) -
          2 * ((1 / (p : Real)) * (numeratorKernel (A * D) p).re) -
          2 * ((1 / (p : Real)) * (numeratorKernel (B * C) p).re) -
          2 * ((1 / (p : Real)) * (numeratorKernel (B * D) p).re) := by
    intro p hp
    have hdata := Finset.mem_filter.mp hp
    have hband := Finset.mem_Ico.mp hdata.1
    have hp2 : 2 < p := by omega
    have hhp : h < p := by omega
    have hkp : k < p := by omega
    have hpN : p < n := by omega
    have hpM : p < m := by omega
    have ha := real_kernel_square_endpoint h n p hh hn hdata.2 hp2 hhp hpN
      A (Or.inr rfl)
    have hb := real_kernel_square_endpoint h (n + h) p hh hnh hdata.2 hp2 hhp
      (by omega) B (Or.inl rfl)
    have hc := real_kernel_square_endpoint k m p hk hm hdata.2 hp2 hkp hpM
      C (Or.inr rfl)
    have hd := real_kernel_square_endpoint k (m + k) p hk hmk hdata.2 hp2 hkp
      (by omega) D (Or.inl rfl)
    have halgebra :
        ((numeratorKernel A p).re + (numeratorKernel B p).re -
          ((numeratorKernel C p).re + (numeratorKernel D p).re)) ^ 2 =
          4 + 2 * ((numeratorKernel A p).re * (numeratorKernel B p).re) +
            2 * ((numeratorKernel C p).re * (numeratorKernel D p).re) -
            2 * ((numeratorKernel A p).re * (numeratorKernel C p).re) -
            2 * ((numeratorKernel A p).re * (numeratorKernel D p).re) -
            2 * ((numeratorKernel B p).re * (numeratorKernel C p).re) -
            2 * ((numeratorKernel B p).re * (numeratorKernel D p).re) := by
      nlinarith only [ha, hb, hc, hd]
    change (1 / (p : Real)) *
      ((numeratorKernel A p).re + (numeratorKernel B p).re -
        ((numeratorKernel C p).re + (numeratorKernel D p).re)) ^ 2 = _
    rw [halgebra, real_kernel_mul A B p, real_kernel_mul C D p,
      real_kernel_mul A C p, real_kernel_mul A D p,
      real_kernel_mul B C p, real_kernel_mul B D p]
    ring
  unfold nativeTraceEnergy
  rw [Finset.sum_congr rfl hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum,
    primeCorrelation, reciprocalBand, A, B, C, D]

theorem exists_native_trace_energy_lower :
    exists C : Real, And (0 < C)
      (forall H T n m h k Y X : Nat,
        Nat.Prime n -> Nat.Prime (n + h) -> Nat.Prime m -> Nat.Prime (m + k) ->
        0 < h -> 0 < k -> h <= H -> k <= H -> H < Y -> 2 < Y -> Y < X ->
        X <= n -> X <= m -> n + h <= T -> m + k <= T ->
        Not (And (n = m) (h = k)) ->
        2 * reciprocalBand Y X -
          10 * (C * (3 + Real.log ((4 * H * H * T * T : Nat) : Real)) ^ 2 *
            (Y : Real) ^ (-1 / 32 : Real)) <= nativeTraceEnergy n h m k Y X) := by
  choose C hCpos hC using exists_endpoint_prime_correlation_bound
  refine Exists.intro C (And.intro hCpos ?_)
  intro H T n m h k Y X hn hnh hm hmk hh hk hhH hkH hHY hY hYX hXn hXm hnT hmT hneq
  let t0 : Int := -((h : Int) * (n : Int))
  let t1 : Int := (h : Int) * ((n + h : Nat) : Int)
  let u0 : Int := -((k : Int) * (m : Int))
  let u1 : Int := (k : Int) * ((m + k : Nat) : Int)
  let M : Real := reciprocalBand Y X
  let B : Real := C * (3 + Real.log ((4 * H * H * T * T : Nat) : Real)) ^ 2 *
    (Y : Real) ^ (-1 / 32 : Real)
  have hn0 : n <= T := by omega
  have hm0 : m <= T := by omega
  have hY1 : 1 <= Y := by omega
  have hab : -B <= primeCorrelation (t0 * t1) Y X := by
    have hb := hC h h n (n + h) H T Y X hh hh hn hnh (by omega) hhH hhH
      (by omega) (by omega) hn0 hnT hY1 (t0 * t1) (Or.inr (by dsimp [t0, t1]; ring))
    exact (abs_le.mp hb).1
  have hcd : -B <= primeCorrelation (u0 * u1) Y X := by
    have hb := hC k k m (m + k) H T Y X hk hk hm hmk (by omega) hkH hkH
      (by omega) (by omega) hm0 hmT hY1 (u0 * u1) (Or.inr (by dsimp [u0, u1]; ring))
    exact (abs_le.mp hb).1
  have h00 : Not (n = m) -> primeCorrelation (t0 * u0) Y X <= B := by
    intro hne
    have hb := hC h k n m H T Y X hh hk hn hm hne hhH hkH
      (by omega) (by omega) hn0 hm0 hY1 (t0 * u0) (Or.inl (by dsimp [t0, u0]; ring))
    exact (abs_le.mp hb).2
  have h01 : Not (n = m + k) -> primeCorrelation (t0 * u1) Y X <= B := by
    intro hne
    have hb := hC h k n (m + k) H T Y X hh hk hn hmk hne hhH hkH
      (by omega) (by omega) hn0 hmT hY1 (t0 * u1) (Or.inr (by dsimp [t0, u1]; ring))
    exact (abs_le.mp hb).2
  have h10 : Not (n + h = m) -> primeCorrelation (t1 * u0) Y X <= B := by
    intro hne
    have hb := hC h k (n + h) m H T Y X hh hk hnh hm hne hhH hkH
      (by omega) (by omega) hnT hm0 hY1 (t1 * u0) (Or.inr (by dsimp [t1, u0]; ring))
    exact (abs_le.mp hb).2
  have h11 : Not (n + h = m + k) -> primeCorrelation (t1 * u1) Y X <= B := by
    intro hne
    have hb := hC h k (n + h) (m + k) H T Y X hh hk hnh hmk hne hhH hkH
      (by omega) (by omega) hnT hmT hY1 (t1 * u1) (Or.inl (by dsimp [t1, u1]; ring))
    exact (abs_le.mp hb).2
  have h00all : primeCorrelation (t0 * u0) Y X <= M :=
    prime_correlation_le_mass _ Y X hY
  have h01all : primeCorrelation (t0 * u1) Y X <= M :=
    prime_correlation_le_mass _ Y X hY
  have h10all : primeCorrelation (t1 * u0) Y X <= M :=
    prime_correlation_le_mass _ Y X hY
  have h11all : primeCorrelation (t1 * u1) Y X <= M :=
    prime_correlation_le_mass _ Y X hY
  have hid : nativeTraceEnergy n h m k Y X =
      4 * M + 2 * primeCorrelation (t0 * t1) Y X + 2 * primeCorrelation (u0 * u1) Y X -
        2 * primeCorrelation (t0 * u0) Y X - 2 * primeCorrelation (t0 * u1) Y X -
        2 * primeCorrelation (t1 * u0) Y X - 2 * primeCorrelation (t1 * u1) Y X :=
    native_trace_energy_identity n h m k Y X hn hnh hm hmk hh hk
      (hhH.trans_lt hHY) (hkH.trans_lt hHY) hY hXn hXm
  change 2 * M - 10 * B <= nativeTraceEnergy n h m k Y X
  rw [hid]
  by_cases he0 : n = m
  . have hb01 := h01 (by omega)
    have hb10 := h10 (by omega)
    have hb11 := h11 (by omega)
    linarith only [hab, hcd, h00all, hb01, hb10, hb11]
  . by_cases he1 : n = m + k
    . have hb00 := h00 he0
      have hb10 := h10 (by omega)
      have hb11 := h11 (by omega)
      linarith only [hab, hcd, h01all, hb00, hb10, hb11]
    . by_cases he2 : n + h = m
      . have hb00 := h00 he0
        have hb01 := h01 he1
        have hb11 := h11 (by omega)
        linarith only [hab, hcd, h10all, hb00, hb01, hb11]
      . have hb00 := h00 he0
        have hb01 := h01 he1
        have hb10 := h10 he2
        linarith only [hab, hcd, h11all, hb00, hb01, hb10]

end PrimeFactorOscillations.FiniteFieldIntegerSignature

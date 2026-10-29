/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.DetectorPackets.MobiusCompensatedCovariance
import PrimeFactorOscillations.Assembly.DetectorPackets.MobiusWindowTail

/-!
# Quantitative removal of power compensation in the signed character packet

Every positive divisor row is retained. Only the exact difference between
the compensated and uncompensated packets is estimated; the signed main
packet is never replaced by its absolute coefficient mass.
The window is smooth and compactly supported away from zero. Constants
depend on its window, character, fixed depletion mask and exponent slack.
No extension to the noncompact radial carrier, growing conductors, general
prime-sampled quotient, or improved zero-free boundary is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

noncomputable section
namespace PrimeFactorOscillations.CarmichaelPowerCompensation
open scoped Classical
open DepletedMobius

/-- The actual depleted smooth multiple row, including its Mobius sign. -/
def smoothRow {q : Nat} (chi : DirichletCharacter Complex q)
    (r : Nat) (W : Real -> Complex) (b : Real) (h : Nat) (D : Real) : Complex :=
  smoothMultipleMasked h r (fun n => chi (n : ZMod q)) W b (D / (h : Real))

/-- The complete signed positive-divisor packet through its inclusive cutoff. -/
def signedPacket (A : Nat -> Real -> Complex) (N : Nat) (D : Real) : Complex :=
  (Finset.Icc 1 N).sum (fun h =>
    (ArithmeticFunction.moebius h : Complex) * A h D * star (A h D))

/-- Compensation acts on each complex row before its quadratic packet. -/
def powerRow (A : Nat -> Real -> Complex) (d h : Nat) (D : Real) : Complex :=
  A h D - ((D ^ (1 - (d : Real)) : Real) : Complex) * A h (D ^ d)

private theorem reciprocal_weight_prefix (N : Nat) :
    (Finset.Icc 1 N).sum (fun h => (h : Real) ^ (-(7 / 4 : Real))) <= 7 / 3 := by
  have hsubset : Finset.Icc 1 N <= insert 1 (Finset.Ioc 1 N) := by
    intro h hh
    have hm := Finset.mem_Icc.mp hh
    simp only [Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hnot : Not (Membership.mem (Finset.Ioc 1 N) 1) := by simp
  have hcomp := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun h _ _ => Real.rpow_nonneg (Nat.cast_nonneg h) (-(7 / 4 : Real)))
  rw [Finset.sum_insert hnot] at hcomp
  have htail := sum_Ioc_negative_rpow_le 1 N (by omega) (7 / 4) (by norm_num)
  norm_num at hcomp htail
  linarith

private theorem quadratic_difference_bound (x y : Complex) (c : Real) (hc : 0 <= c) :
    norm ((x - (c : Complex) * y) * star (x - (c : Complex) * y) -
      x * star x) <=
      2 * c * norm x * norm y + c ^ 2 * (norm y) ^ 2 := by
  have heq :
      (x - (c : Complex) * y) * star (x - (c : Complex) * y) - x * star x =
      -((c : Complex) * y * star x) - ((c : Complex) * x * star y) +
        ((c : Complex) * (c : Complex)) * y * star y := by
    have hstar : star (c : Complex) = (c : Complex) := by simp
    simp only [star_sub, star_mul, hstar]
    ring
  rw [heq]
  calc
    _ <= norm (-((c : Complex) * y * star x) - ((c : Complex) * x * star y)) +
        norm (((c : Complex) * (c : Complex)) * y * star y) := norm_add_le _ _
    _ <= (norm (-((c : Complex) * y * star x)) +
        norm ((c : Complex) * x * star y)) +
        norm (((c : Complex) * (c : Complex)) * y * star y) :=
      add_le_add (norm_sub_le _ _) (le_refl _)
    _ = _ := by
      simp only [norm_neg, norm_mul, norm_star, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hc]
      ring

private theorem packet_difference_bound (A : Nat -> Real -> Complex)
    (K alpha D E c : Real) (N : Nat)
    (hK : 0 <= K) (hD : 0 < D) (hE : 0 < E) (hc : 0 <= c)
    (hA : forall h, 0 < h -> norm (A h D) <=
      K * D ^ alpha * (h : Real) ^ (-(7 / 8 : Real)))
    (hB : forall h, 0 < h -> norm (A h E) <=
      K * E ^ alpha * (h : Real) ^ (-(7 / 8 : Real))) :
    norm (signedPacket (fun h X => A h X - (c : Complex) * A h E) N D -
      signedPacket A N D) <=
      (7 / 3 : Real) * K ^ 2 *
        (2 * c * D ^ alpha * E ^ alpha + c ^ 2 * (E ^ alpha) ^ 2) := by
  let Z : Real := K ^ 2 *
    (2 * c * D ^ alpha * E ^ alpha + c ^ 2 * (E ^ alpha) ^ 2)
  have hZ : 0 <= Z := by dsimp only [Z]; positivity
  have hterm (h : Nat) (hh : Membership.mem (Finset.Icc 1 N) h) :
      norm ((ArithmeticFunction.moebius h : Complex) *
        ((A h D - (c : Complex) * A h E) * star (A h D - (c : Complex) * A h E) -
          A h D * star (A h D))) <= Z * (h : Real) ^ (-(7 / 4 : Real)) := by
    have hp : 0 < h := (Finset.mem_Icc.mp hh).1
    have hr : 0 < (h : Real) := Nat.cast_pos.mpr hp
    have hm : norm (ArithmeticFunction.moebius h : Complex) <= 1 :=
      moebius_cast_norm_le h
    have hw : ((h : Real) ^ (-(7 / 8 : Real))) ^ 2 =
        (h : Real) ^ (-(7 / 4 : Real)) := by
      rw [<- Real.rpow_mul_natCast hr.le]
      norm_num
    calc
      _ <= 1 * norm ((A h D - (c : Complex) * A h E) *
          star (A h D - (c : Complex) * A h E) - A h D * star (A h D)) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)
      _ <= 2 * c * norm (A h D) * norm (A h E) +
          c ^ 2 * (norm (A h E)) ^ 2 := by
        simpa only [one_mul] using quadratic_difference_bound (A h D) (A h E) c hc
      _ <= 2 * c * (K * D ^ alpha * (h : Real) ^ (-(7 / 8 : Real))) *
          (K * E ^ alpha * (h : Real) ^ (-(7 / 8 : Real))) +
          c ^ 2 * (K * E ^ alpha * (h : Real) ^ (-(7 / 8 : Real))) ^ 2 := by
        gcongr
        all_goals first | exact hA h hp | exact hB h hp
      _ = _ := by
        dsimp only [Z]
        nlinarith [hw]
  have heq : signedPacket (fun h X => A h X - (c : Complex) * A h E) N D -
      signedPacket A N D =
      (Finset.Icc 1 N).sum (fun h =>
        (ArithmeticFunction.moebius h : Complex) *
          ((A h D - (c : Complex) * A h E) * star (A h D - (c : Complex) * A h E) -
            A h D * star (A h D))) := by
    unfold signedPacket
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [heq]
  calc
    _ <= (Finset.Icc 1 N).sum (fun h => Z * (h : Real) ^ (-(7 / 4 : Real))) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = Z * (Finset.Icc 1 N).sum (fun h => (h : Real) ^ (-(7 / 4 : Real))) :=
      (Finset.mul_sum _ _ _).symm
    _ <= Z * (7 / 3) := mul_le_mul_of_nonneg_left (reciprocal_weight_prefix N) hZ
    _ = _ := by dsimp only [Z]; ring

private theorem smooth_row_bound {q : Nat} (chi : DirichletCharacter Complex q)
    (hq : 0 < q) (r : Nat) (hr : Not (r = 0))
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo) (hhi : 0 <= hi)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (u : Real) (hu : 0 < u) (hfit : (7 / 8 : Real) + u <= 2) :
    exists K : Real, 0 <= K /\
      forall (h : Nat) (D : Real), 0 < h -> 0 < D ->
        norm (smoothRow chi r W hi h D) <=
          K * D ^ ((7 / 8 : Real) + u) * (h : Real) ^ (-(7 / 8 : Real)) := by
  choose K hK hb using MobiusWindow.character_normalized_smooth_size_bound
    chi hq r hr W lo hi hlo hhi hsupp hW u hu hfit
  refine Exists.intro K (And.intro hK ?_)
  intro h D hh hD
  have hrow := mul_le_mul_of_nonneg_left (hb h D (Nat.ne_of_gt hh) hD)
    (Real.rpow_nonneg hD.le (1 / 2))
  have hcancel : D ^ (1 / 2 : Real) * D ^ (-(1 / 2 : Real)) = 1 := by
    rw [<- Real.rpow_add hD]
    norm_num
  have hcombine : D ^ (1 / 2 : Real) * D ^ ((3 / 8 : Real) + u) =
      D ^ ((7 / 8 : Real) + u) := by
    rw [<- Real.rpow_add hD]
    congr 1
    ring
  unfold normalizedSmoothSize at hrow
  calc
    _ = D ^ (1 / 2 : Real) *
        (D ^ (-(1 / 2 : Real)) *
          norm (smoothMultipleMasked h r (fun n => chi (n : ZMod q)) W hi
            (D / (h : Real)))) := by
      rw [<- mul_assoc, hcancel, one_mul]
      rfl
    _ <= D ^ (1 / 2 : Real) *
        (K * D ^ ((3 / 8 : Real) + u) * (h : Real) ^ (-(7 / 8 : Real))) := hrow
    _ = _ := by
      calc
        _ = K * (D ^ (1 / 2 : Real) * D ^ ((3 / 8 : Real) + u)) *
            (h : Real) ^ (-(7 / 8 : Real)) := by ring
        _ = _ := by rw [hcombine]

private theorem power_remainder_of_row_bound
    (A : Nat -> Real -> Complex) (K alpha : Real) (hK : 0 <= K)
    (hrow : forall h D, 0 < h -> 0 < D ->
      norm (A h D) <= K * D ^ alpha * (h : Real) ^ (-(7 / 8 : Real)))
    (d N : Nat) (D : Real) (hD : 0 < D) :
    norm (signedPacket (powerRow A d) N D - signedPacket A N D) <=
      (7 / 3 : Real) * K ^ 2 *
        (2 * D ^ (1 + alpha + (d : Real) * (alpha - 1)) +
          D ^ (2 + 2 * (d : Real) * (alpha - 1))) := by
  have hd : 0 < D ^ d := pow_pos hD d
  have h := packet_difference_bound A K alpha D (D ^ d)
    (D ^ (1 - (d : Real))) N hK hD hd (Real.rpow_nonneg hD.le _)
    (fun h hh => hrow h D hh hD) (fun h hh => hrow h (D ^ d) hh hd)
  have hpow : (D ^ d) ^ alpha = D ^ ((d : Real) * alpha) := by
    rw [<- Real.rpow_natCast D d, <- Real.rpow_mul hD.le]
  have hab : D ^ (1 - (d : Real)) * D ^ alpha * (D ^ d) ^ alpha =
      D ^ (1 + alpha + (d : Real) * (alpha - 1)) := by
    rw [hpow, <- Real.rpow_add hD, <- Real.rpow_add hD]
    congr 1
    ring
  have hbb : (D ^ (1 - (d : Real))) ^ 2 * ((D ^ d) ^ alpha) ^ 2 =
      D ^ (2 + 2 * (d : Real) * (alpha - 1)) := by
    rw [hpow, <- mul_pow, <- Real.rpow_add hD,
      <- Real.rpow_mul_natCast hD.le]
    congr 1
    norm_num
    ring
  have hid : signedPacket (powerRow A d) N D =
      signedPacket (fun h X => A h X - ((D ^ (1 - (d : Real)) : Real) : Complex) *
        A h (D ^ d)) N D := by rfl
  rw [hid]
  calc
    _ <= (7 / 3 : Real) * K ^ 2 *
        (2 * D ^ (1 - (d : Real)) * D ^ alpha * (D ^ d) ^ alpha +
          (D ^ (1 - (d : Real))) ^ 2 * ((D ^ d) ^ alpha) ^ 2) := h
    _ = _ := by
      rw [show 2 * D ^ (1 - (d : Real)) * D ^ alpha * (D ^ d) ^ alpha =
        2 * (D ^ (1 - (d : Real)) * D ^ alpha * (D ^ d) ^ alpha) by ring,
        hab, hbb]

/-- Uniform in every divisor cutoff and every positive power scale.
The complete cross and reference contribution is bounded, while AA stays signed. -/
theorem character_power_compensation_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (r : Nat) (hr : Not (r = 0))
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo) (hhi : 0 <= hi)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (u : Real) (hu : 0 < u) (hfit : (7 / 8 : Real) + u <= 2) :
    exists K : Real, 0 <= K /\
      forall (d N : Nat) (D : Real), 0 < D ->
        norm (signedPacket (powerRow (smoothRow chi r W hi) d) N D -
          signedPacket (smoothRow chi r W hi) N D) <=
          (7 / 3 : Real) * K ^ 2 *
            (2 * D ^ ((15 - (d : Real)) / 8 + ((d : Real) + 1) * u) +
              D ^ ((8 - (d : Real)) / 4 + 2 * (d : Real) * u)) := by
  choose K hK hb using smooth_row_bound chi hq r hr W lo hi hlo hhi hsupp hW u hu hfit
  refine Exists.intro K (And.intro hK ?_)
  intro d N D hD
  have h := power_remainder_of_row_bound (smoothRow chi r W hi) K
    (7 / 8 + u) hK hb d N D hD
  have ha : 1 + ((7 / 8 : Real) + u) + (d : Real) * (((7 / 8 : Real) + u) - 1) =
      (15 - (d : Real)) / 8 + ((d : Real) + 1) * u := by ring
  have hb' : 2 + 2 * (d : Real) * (((7 / 8 : Real) + u) - 1) =
      (8 - (d : Real)) / 4 + 2 * (d : Real) * u := by ring
  rwa [ha, hb'] at h

/-- The full complex character portfolio is combined before compensation or squaring. -/
def portfolioRow {I : Type*} {q : Nat} (S : Finset I)
    (chi : I -> DirichletCharacter Complex q) (weight : I -> Complex)
    (r : Nat) (W : Real -> Complex) (b : Real) (h : Nat) (D : Real) : Complex :=
  S.sum (fun i => weight i * smoothRow (chi i) r W b h D)

/-- A single constant controls every power and cutoff of a fixed finite character
portfolio, including every mixed-character compensation term. -/
theorem portfolio_power_compensation_bound {I : Type*} {q : Nat}
    (S : Finset I) (chi : I -> DirichletCharacter Complex q)
    (weight : I -> Complex) (hq : 0 < q)
    (r : Nat) (hr : Not (r = 0))
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo) (hhi : 0 <= hi)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (u : Real) (hu : 0 < u) (hfit : (7 / 8 : Real) + u <= 2) :
    exists K : Real, 0 <= K /\
      forall (d N : Nat) (D : Real), 0 < D ->
        norm (signedPacket (powerRow (portfolioRow S chi weight r W hi) d) N D -
          signedPacket (portfolioRow S chi weight r W hi) N D) <=
          (7 / 3 : Real) * K ^ 2 *
            (2 * D ^ ((15 - (d : Real)) / 8 + ((d : Real) + 1) * u) +
              D ^ ((8 - (d : Real)) / 4 + 2 * (d : Real) * u)) := by
  choose K hK hb using (fun i : I =>
    smooth_row_bound (chi i) hq r hr W lo hi hlo hhi hsupp hW u hu hfit)
  let C : Real := S.sum (fun i => norm (weight i) * K i)
  have hC : 0 <= C :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hK i))
  have hrow : forall h D, 0 < h -> 0 < D ->
      norm (portfolioRow S chi weight r W hi h D) <=
        C * D ^ ((7 / 8 : Real) + u) * (h : Real) ^ (-(7 / 8 : Real)) := by
    intro h D hh hD
    unfold portfolioRow
    calc
      _ <= S.sum (fun i => norm (weight i * smoothRow (chi i) r W hi h D)) :=
        norm_sum_le _ _
      _ <= S.sum (fun i => norm (weight i) * K i *
          D ^ ((7 / 8 : Real) + u) * (h : Real) ^ (-(7 / 8 : Real))) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        have hx := mul_le_mul_of_nonneg_left (hb i h D hh hD) (norm_nonneg (weight i))
        convert hx using 1 <;> ring
      _ = _ := by
        rw [<- Finset.sum_mul, <- Finset.sum_mul]
  refine Exists.intro C (And.intro hC ?_)
  intro d N D hD
  have h := power_remainder_of_row_bound (portfolioRow S chi weight r W hi) C
    (7 / 8 + u) hC hrow d N D hD
  have ha : 1 + ((7 / 8 : Real) + u) + (d : Real) * (((7 / 8 : Real) + u) - 1) =
      (15 - (d : Real)) / 8 + ((d : Real) + 1) * u := by ring
  have hb' : 2 + 2 * (d : Real) * (((7 / 8 : Real) + u) - 1) =
      (8 - (d : Real)) / 4 + 2 * (d : Real) * u := by ring
  rwa [ha, hb'] at h

/-- Fourth-power compensation is strictly below the target3/2 in every fixed
smooth compact character portfolio. The signed AA packet is not estimated. -/
theorem portfolio_quartic_compensation_subpower {I : Type*} {q : Nat}
    (S : Finset I) (chi : I -> DirichletCharacter Complex q)
    (weight : I -> Complex) (hq : 0 < q)
    (r : Nat) (hr : Not (r = 0))
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo) (hhi : 0 <= hi)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 <= C /\
      forall (N : Nat) (D : Real), 1 <= D ->
        norm (signedPacket (powerRow (portfolioRow S chi weight r W hi) 4) N D -
          signedPacket (portfolioRow S chi weight r W hi) N D) <=
          C * D ^ ((11 / 8 : Real) + eps) := by
  let u : Real := min (eps / 10) (1 / 100)
  have hu : 0 < u := lt_min (by positivity) (by norm_num)
  have he : u <= eps / 10 := min_le_left _ _
  have hc : u <= 1 / 100 := min_le_right _ _
  choose K hK hb using portfolio_power_compensation_bound S chi weight hq r hr
    W lo hi hlo hhi hsupp hW u hu (by linarith)
  refine Exists.intro (7 * K ^ 2) (And.intro (by positivity) ?_)
  intro N D hD
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num : (0 : Real) < 1) hD
  have h := hb 4 N D hDpos
  norm_num at h
  have hleft : D ^ ((11 / 8 : Real) + 5 * u) <=
      D ^ ((11 / 8 : Real) + eps) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hright : D ^ ((1 : Real) + 8 * u) <=
      D ^ ((11 / 8 : Real) + eps) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  calc
    _ <= (7 / 3 : Real) * K ^ 2 *
        (2 * D ^ ((11 / 8 : Real) + 5 * u) + D ^ ((1 : Real) + 8 * u)) := h
    _ <= (7 / 3 : Real) * K ^ 2 *
        (2 * D ^ ((11 / 8 : Real) + eps) + D ^ ((11 / 8 : Real) + eps)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hleft (by norm_num)) hright) (by positivity)
    _ = _ := by ring

/-- Eighth-power compensation is below the RH energy scale D, uniformly over
every divisor cutoff. Constants retain the fixed portfolio and window costs. -/
theorem portfolio_octic_compensation_subpower {I : Type*} {q : Nat}
    (S : Finset I) (chi : I -> DirichletCharacter Complex q)
    (weight : I -> Complex) (hq : 0 < q)
    (r : Nat) (hr : Not (r = 0))
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo) (hhi : 0 <= hi)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 <= C /\
      forall (N : Nat) (D : Real), 1 <= D ->
        norm (signedPacket (powerRow (portfolioRow S chi weight r W hi) 8) N D -
          signedPacket (portfolioRow S chi weight r W hi) N D) <=
          C * D ^ ((7 / 8 : Real) + eps) := by
  let u : Real := min (eps / 18) (1 / 100)
  have hu : 0 < u := lt_min (by positivity) (by norm_num)
  have he : u <= eps / 18 := min_le_left _ _
  have hc : u <= 1 / 100 := min_le_right _ _
  choose K hK hb using portfolio_power_compensation_bound S chi weight hq r hr
    W lo hi hlo hhi hsupp hW u hu (by linarith)
  refine Exists.intro (7 * K ^ 2) (And.intro (by positivity) ?_)
  intro N D hD
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num : (0 : Real) < 1) hD
  have h := hb 8 N D hDpos
  norm_num at h
  have hleft : D ^ ((7 / 8 : Real) + 9 * u) <=
      D ^ ((7 / 8 : Real) + eps) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hright : D ^ (16 * u) <=
      D ^ ((7 / 8 : Real) + eps) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  calc
    _ <= (7 / 3 : Real) * K ^ 2 *
        (2 * D ^ ((7 / 8 : Real) + 9 * u) + D ^ (16 * u)) := h
    _ <= (7 / 3 : Real) * K ^ 2 *
        (2 * D ^ ((7 / 8 : Real) + eps) + D ^ ((7 / 8 : Real) + eps)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hleft (by norm_num)) hright) (by positivity)
    _ = _ := by ring

end PrimeFactorOscillations.CarmichaelPowerCompensation

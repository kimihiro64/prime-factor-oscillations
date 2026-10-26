/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelSingleAscent
import PrimeFactorOscillations.Assembly.CarmichaelTwoPowerConductor

/-!
# Complementary native zero masks retain localized RH witnesses

The original large two-power kernel and its actual residue translate by five
form an exact two-channel cover. Each channel may vanish. Their complete
signed ascent excesses sum to twice the unweighted excess. Joint boundedness
is equivalent to RH, and failure of RH makes one fixed channel unbounded.
No assertion that five times a prime is prime is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelComplementaryAscent

open Filter PrimeFactorUnimodality CarmichaelPrimePacket CarmichaelCorrelation
open CarmichaelCorrelationSpectrum CarmichaelTwoPowerConductor
open TwoPowerCharacterConductor

def mask (r : Nat) (phase : Bool) (u : Units (ZMod (2 ^ (r + 4)))) : Real :=
  kernel (weight (2 ^ (r + 4)) labelTwo)
    (if phase then fiveUnit (r + 1) * u else u)

theorem five_kernel_zero (r : Nat) :
    kernel (weight (2 ^ (r + 4)) labelTwo) (fiveUnit (r + 1)) = 0 := by
  have hNot : Not (fiveUnit (r + 1) ^ (2 ^ (r + 1)) = 1) := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [fiveUnit_order] at hd
    have hPos : 0 < 2 ^ (r + 1) := pow_pos (by decide) _
    have hLt : 2 ^ (r + 1) < 2 ^ ((r + 1) + 1) := by
      rw [pow_succ]
      omega
    exact (Nat.not_le_of_gt hLt) (Nat.le_of_dvd hPos hd)
  apply (large_zero_mask_iff r _).mpr
  simp [CarmichaelCorrelationLocal.returnBit, large_half_exponent, hNot]

theorem mask_sum (r : Nat) (u : Units (ZMod (2 ^ (r + 4)))) :
    mask r false u + mask r true u = 2 := by
  choose chi hChi hConductor hCoefficient using
    exists_large_conductor_eight_survivor r
  have hNonzero : Not (coefficient (weight (2 ^ (r + 4)) labelTwo) chi = 0) := by
    rw [hCoefficient]
    norm_num
  have hAtFive := large_kernel_two_modes r chi hChi hNonzero (fiveUnit (r + 1))
  rw [five_kernel_zero, Complex.ofReal_zero] at hAtFive
  have hPhase : unitCharacter chi (Inv.inv (fiveUnit (r + 1))) = -1 := by
    calc
      _ = (1 + unitCharacter chi (Inv.inv (fiveUnit (r + 1)))) - 1 := by ring
      _ = 0 - 1 := congrArg (fun z : Complex => z - 1) hAtFive.symm
      _ = -1 := by ring
  have hComplex :
      (kernel (weight (2 ^ (r + 4)) labelTwo) u : Complex) +
        (kernel (weight (2 ^ (r + 4)) labelTwo) (fiveUnit (r + 1) * u) : Complex) = 2 := by
    rw [large_kernel_two_modes r chi hChi hNonzero u,
      large_kernel_two_modes r chi hChi hNonzero (fiveUnit (r + 1) * u),
      mul_inv_rev, map_mul, hPhase]
    ring
  exact_mod_cast hComplex

theorem mask_nonneg (r : Nat) (phase : Bool)
    (u : Units (ZMod (2 ^ (r + 4)))) : 0 <= mask r phase u := by
  unfold mask
  rw [large_kernel_boolean]
  split_ifs <;> norm_num

theorem mask_false_zero_or_two (r : Nat)
    (u : Units (ZMod (2 ^ (r + 4)))) :
    Or (mask r false u = 0) (mask r false u = 2) := by
  simp only [mask, Bool.false_eq_true, ite_false]
  rw [large_kernel_boolean]
  split_ifs <;> simp

theorem signed_channel_alternative (r : Nat)
    (u : Units (ZMod (2 ^ (r + 4)))) (B : Real) :
    Or (And (mask r false u * B = 0) (mask r true u * B = 2 * B))
      (And (mask r false u * B = 2 * B) (mask r true u * B = 0)) := by
  have hSum := mask_sum r u
  rcases mask_false_zero_or_two r u with h | h
  . have hOther : mask r true u = 2 := by linarith
    exact Or.inl (by simp [h, hOther])
  . have hOther : mask r true u = 0 := by linarith
    exact Or.inr (by simp [h, hOther])

def channelExcess (H : Nat) (a : Nat -> Nat)
    (w : Bool -> Nat -> Real) (phase : Bool) (X : Nat) : Real :=
  w phase X * localAscentPairExcess H X (a X)

theorem channel_sum (H : Nat) (a : Nat -> Nat) (w : Bool -> Nat -> Real)
    (X : Nat) (hCover : w false X + w true X = 2) :
    channelExcess H a w false X + channelExcess H a w true X =
      2 * localAscentPairExcess H X (a X) := by
  unfold channelExcess
  rw [<- add_mul, hCover]

theorem riemannHypothesis_iff_joint_bounded
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (w : Bool -> Nat -> Real)
    (hNonneg : Filter.Eventually (fun X : Nat => forall phase, 0 <= w phase X) atTop)
    (hCover : Filter.Eventually (fun X : Nat => w false X + w true X = 2) atTop) :
    RiemannHypothesis <->
      forall phase : Bool, exists C : Real, Filter.Eventually (fun X : Nat =>
        channelExcess H a w phase X <= C) atTop := by
  constructor
  . intro hRH phase
    refine Exists.intro 0 ?_
    filter_upwards [singleAscentPairExcess_nonpos_eventually_of_RH H a hs hRH, hNonneg]
      with X hB hW
    exact mul_nonpos_of_nonneg_of_nonpos (hW phase) hB
  . intro hBounds
    choose C0 h0 using hBounds false
    choose C1 h1 using hBounds true
    apply (riemannHypothesis_iff_eventually_singleAscent_bounded H a hs).mpr
    refine Exists.intro ((C0 + C1) / 2) ?_
    filter_upwards [h0, h1, hCover] with X h0 h1 hCover
    have hSum := channel_sum H a w X hCover
    linarith

theorem riemannHypothesis_iff_joint_nonpos
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (w : Bool -> Nat -> Real)
    (hNonneg : Filter.Eventually (fun X : Nat => forall phase, 0 <= w phase X) atTop)
    (hCover : Filter.Eventually (fun X : Nat => w false X + w true X = 2) atTop) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat => forall phase : Bool,
        channelExcess H a w phase X <= 0) atTop := by
  constructor
  . intro hRH
    filter_upwards [singleAscentPairExcess_nonpos_eventually_of_RH H a hs hRH, hNonneg]
      with X hB hW phase
    exact mul_nonpos_of_nonneg_of_nonpos (hW phase) hB
  . intro hBounds
    apply (riemannHypothesis_iff_joint_bounded H a hs w hNonneg hCover).mpr
    intro phase
    exact Exists.intro 0 (hBounds.mono (fun _ h => h phase))

theorem fixed_channel_unbounded_of_not_RH
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (w : Bool -> Nat -> Real)
    (hNonneg : Filter.Eventually (fun X : Nat => forall phase, 0 <= w phase X) atTop)
    (hCover : Filter.Eventually (fun X : Nat => w false X + w true X = 2) atTop)
    (hNotRH : Not RiemannHypothesis) :
    exists phase : Bool, forall C X0 : Real, exists n : Nat,
      X0 < (n : Real) /\ C < channelExcess H a w phase n := by
  classical
  by_contra hNone
  push Not at hNone
  apply hNotRH
  apply (riemannHypothesis_iff_joint_bounded H a hs w hNonneg hCover).mpr
  intro phase
  choose C X0 hBound using hNone phase
  refine Exists.intro C ?_
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hCast.eventually (eventually_gt_atTop X0)] with n hn
  exact hBound n hn

def primeMask (r : Nat) (phase : Bool) (p : Nat) : Real := by
  classical
  exact if h : Nat.Coprime p (2 ^ (r + 4)) then
    mask r phase (ZMod.unitOfCoprime p h)
  else 0

theorem primeMask_nonneg (r : Nat) (phase : Bool) (p : Nat) :
    0 <= primeMask r phase p := by
  classical
  unfold primeMask
  split_ifs
  . exact mask_nonneg r phase _
  . exact le_rfl

theorem primeMask_sum (r p : Nat) (hp : Nat.Coprime p (2 ^ (r + 4))) :
    primeMask r false p + primeMask r true p = 2 := by
  classical
  simp only [primeMask, dite_eq_left hp]
  exact mask_sum r _

theorem primeMask_false_eq_original (r p : Nat) :
    primeMask r false p = carmichaelPrimeWeight (2 ^ (r + 4)) {labelTwo} p := by
  classical
  unfold primeMask carmichaelPrimeWeight
  split_ifs with hp
  . rfl
  . rfl

theorem selected_prime_coprime_eventually
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) (r : Nat -> Nat) :
    Filter.Eventually (fun X : Nat =>
      Nat.Coprime (primeAt (a X)) (2 ^ (r X + 4))) atTop := by
  filter_upwards [hs, eventually_ge_atTop 2] with X hPair hX
  have hLow : X < primeAt (a X) := by
    have hNat : X <= primeAt (a X) - 1 := by exact_mod_cast hPair.2.2.1
    have hp := (prime_primeAt (a X)).two_le
    omega
  have hNot : Not (Dvd.dvd (primeAt (a X)) 2) := by
    intro hDiv
    have hLe := Nat.le_of_dvd (by decide : 0 < 2) hDiv
    omega
  exact ((prime_primeAt (a X)).coprime_iff_not_dvd.mpr hNot).pow_right _

def primeAscentExcess (H : Nat) (a r : Nat -> Nat) (phase : Bool) (X : Nat) : Real :=
  channelExcess H a (fun phase X => primeMask (r X) phase (primeAt (a X))) phase X

theorem prime_cover_eventually
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) (r : Nat -> Nat) :
    Filter.Eventually (fun X : Nat =>
      primeMask (r X) false (primeAt (a X)) +
        primeMask (r X) true (primeAt (a X)) = 2) atTop := by
  filter_upwards [selected_prime_coprime_eventually H a hs r] with X hX
  exact primeMask_sum (r X) _ hX

theorem prime_signed_sum_eventually
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) (r : Nat -> Nat) :
    Filter.Eventually (fun X : Nat =>
      primeAscentExcess H a r false X + primeAscentExcess H a r true X =
        2 * localAscentPairExcess H X (a X)) atTop := by
  filter_upwards [prime_cover_eventually H a hs r] with X hX
  exact channel_sum H a _ X hX

theorem prime_signed_alternative_eventually
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) (r : Nat -> Nat) :
    Filter.Eventually (fun X : Nat =>
      Or (And (primeAscentExcess H a r false X = 0)
          (primeAscentExcess H a r true X = 2 * localAscentPairExcess H X (a X)))
        (And (primeAscentExcess H a r false X = 2 * localAscentPairExcess H X (a X))
          (primeAscentExcess H a r true X = 0))) atTop := by
  classical
  filter_upwards [selected_prime_coprime_eventually H a hs r] with X hX
  simp only [primeAscentExcess, channelExcess, primeMask, dite_eq_left hX]
  exact signed_channel_alternative (r X) _ _

theorem prime_false_eq_original (H : Nat) (a r : Nat -> Nat) (X : Nat) :
    primeAscentExcess H a r false X =
      carmichaelSingleAscentExcess H a (fun Y => 2 ^ (r Y + 4))
        (fun _ => {labelTwo}) X := by
  unfold primeAscentExcess channelExcess carmichaelSingleAscentExcess
  dsimp only
  rw [primeMask_false_eq_original]

theorem riemannHypothesis_iff_prime_channels_bounded
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) (r : Nat -> Nat) :
    RiemannHypothesis <->
      forall phase : Bool, exists C : Real, Filter.Eventually (fun X : Nat =>
        primeAscentExcess H a r phase X <= C) atTop := by
  exact riemannHypothesis_iff_joint_bounded H a hs _
    (Filter.Eventually.of_forall (fun X phase => primeMask_nonneg (r X) phase _))
    (prime_cover_eventually H a hs r)

theorem riemannHypothesis_iff_prime_channels_nonpos
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) (r : Nat -> Nat) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat => forall phase : Bool,
        primeAscentExcess H a r phase X <= 0) atTop := by
  exact riemannHypothesis_iff_joint_nonpos H a hs _
    (Filter.Eventually.of_forall (fun X phase => primeMask_nonneg (r X) phase _))
    (prime_cover_eventually H a hs r)

theorem prime_fixed_channel_unbounded_of_not_RH
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) (r : Nat -> Nat)
    (hNotRH : Not RiemannHypothesis) :
    exists phase : Bool, forall C X0 : Real, exists n : Nat,
      X0 < (n : Real) /\ C < primeAscentExcess H a r phase n := by
  exact fixed_channel_unbounded_of_not_RH H a hs _
    (Filter.Eventually.of_forall (fun X phase => primeMask_nonneg (r X) phase _))
    (prime_cover_eventually H a hs r) hNotRH

end PrimeFactorOscillations.CarmichaelComplementaryAscent

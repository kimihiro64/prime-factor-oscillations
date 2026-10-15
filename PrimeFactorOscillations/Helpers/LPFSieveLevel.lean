/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Proof.LargeSieve.CharacterReduction
import PrimeFactorOscillations.Helpers.LPFSieveCRT

/-!
# Finite arithmetic large sieve for LPF representation bounds

Combine the exact primitive CRT certificates with the cached additive large sieve.
The denominator remains an explicit finite sum of local sieve weights.
-/

namespace PrimeFactorOscillations.LPF

open BombieriVinogradov.LargeSieve

noncomputable def sieveModulusEnergy (X : Finset Nat) (q : Nat) : Real :=
  if hq : q = 0 then 0 else
    letI : NeZero q := NeZero.mk hq
    Finset.sum Finset.univ (fun u : Units (ZMod q) =>
      norm (localSieveSample X (u : ZMod q)) ^ 2)

theorem sieveModulusEnergy_eq (X : Finset Nat) (q : Nat) [NeZero q] :
    sieveModulusEnergy X q = Finset.sum Finset.univ (fun u : Units (ZMod q) =>
      norm (localSieveSample X (u : ZMod q)) ^ 2) := by
  simp [sieveModulusEnergy, NeZero.ne q]

theorem sieveModulusEnergy_nonneg (X : Finset Nat) (q : Nat) :
    0 <= sieveModulusEnergy X q := by
  classical
  unfold sieveModulusEnergy
  split
  next => exact le_rfl
  next => exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private theorem primitive_sum_eq_units {q : Nat} [NeZero q] (f : ZMod q -> Real) :
    Finset.sum (Finset.univ.filter (fun a : ZMod q => IsUnit a)) f =
      Finset.sum Finset.univ (fun u : Units (ZMod q) => f (u : ZMod q)) := by
  classical
  symm
  apply Finset.sum_bij (fun (u : Units (ZMod q)) _ => (u : ZMod q))
  next =>
    intro u hu
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) u.isUnit)
  next =>
    intro u hu v hv h
    exact Units.ext h
  next =>
    intro a ha
    obtain hUnit := (Finset.mem_filter.mp ha).2
    choose u hu using hUnit
    exact Exists.intro u (Exists.intro (Finset.mem_univ u) hu)
  next => intro u hu; rfl

private noncomputable def sieveIndicator (X : Finset Nat) (n : Nat) : Complex :=
  if Membership.mem X n then 1 else 0

private theorem indicator_fareySample (X : Finset Nat) {N Q : Nat}
    (hX : X <= Finset.range N) (i : FareyIndex Q) [NeZero (i.1 : Nat)] :
    fareyAdditiveSample (sieveIndicator X) N i =
      localSieveSample X (i.2 : ZMod (i.1 : Nat)) := by
  classical
  have hpos : 0 < (i.1 : Nat) := (Finset.mem_Icc.mp i.1.2).1
  letI : NeZero (i.1 : Nat) := NeZero.of_pos hpos
  unfold fareyAdditiveSample
  calc
    _ = Finset.sum X (fun n => sieveIndicator X n *
        additivePhase ((n : Real) * (fareyValue i : Real))) := by
      symm
      apply Finset.sum_subset hX
      intro n hn hNot
      simp [sieveIndicator, hNot]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hPhase := additivePhase_int_unitFraction (n : Int) i.2
      simpa [sieveIndicator, hn, fareyValue, mul_comm] using hPhase

private theorem indicator_energy (X : Finset Nat) {N : Nat}
    (hX : X <= Finset.range N) :
    Finset.sum (Finset.range N) (fun n => norm (sieveIndicator X n) ^ 2) =
      (X.card : Real) := by
  classical
  calc
    _ = Finset.sum X (fun n => norm (sieveIndicator X n) ^ 2) := by
      symm
      apply Finset.sum_subset hX
      intro n hn hNot
      simp [sieveIndicator, hNot]
    _ = Finset.sum X (fun _ => (1 : Real)) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [sieveIndicator, hn]
    _ = _ := by simp

theorem sieveModulusEnergy_sum_le (X : Finset Nat) {N Q : Nat}
    (hN : 0 < N) (hQ : 0 < Q) (hX : X <= Finset.range N) :
    Finset.sum (Finset.Icc 1 Q) (sieveModulusEnergy X) <=
      36 * ((N : Real) + (Q : Real) ^ 2) * (X.card : Real) := by
  classical
  have hEnergy :
      Finset.sum (fareyIndices Q) (fun i =>
        norm (fareyAdditiveSample (sieveIndicator X) N i) ^ 2) =
      Finset.sum (Finset.Icc 1 Q) (sieveModulusEnergy X) := by
    unfold fareyIndices
    rw [Finset.sum_sigma]
    calc
      _ = Finset.sum (Finset.Icc 1 Q).attach (fun q => sieveModulusEnergy X q) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hpos : 0 < (q : Nat) := (Finset.mem_Icc.mp q.2).1
        letI : NeZero (q : Nat) := NeZero.of_pos hpos
        rw [sieveModulusEnergy_eq]
        simp only [indicator_fareySample X hX]
        apply Finset.sum_congr
        next => ext u; simp
        next => intro u hu; rfl
      _ = _ := Finset.sum_attach _ _
  have h := additiveLargeSieve hQ hN (sieveIndicator X)
  rw [hEnergy, indicator_energy X hX] at h
  exact h

noncomputable def sieveLevelWeight (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p)) (Q : Nat) : Real :=
  Finset.sum (P.powerset.filter (fun S => Finset.prod S (fun p => p) <= Q))
    (fun S => Finset.prod S (fun p => ((A p).card : Real) / ((p : Real) - (A p).card)))

/-- Finite upper sieve from exact local exclusion; no distribution assumption. -/
theorem sieveLevelWeight_card_sq_le (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p))
    (hPrime : forall p, Membership.mem P p -> Nat.Prime p)
    (hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p))
    (X : Finset Nat) {N Q : Nat} (hN : 0 < N) (hQ : 0 < Q)
    (hX : X <= Finset.range N)
    (hAvoid : forall k, Membership.mem X k ->
      forall p, Membership.mem P p -> Not (Membership.mem (A p) (k : ZMod p))) :
    sieveLevelWeight P A Q * (X.card : Real) ^ 2 <=
      36 * ((N : Real) + (Q : Real) ^ 2) * (X.card : Real) := by
  classical
  let F := P.powerset.filter (fun S => Finset.prod S (fun p => p) <= Q)
  let d := fun S : Finset Nat => Finset.prod S (fun p => p)
  have hSub : forall S, Membership.mem F S -> S <= P :=
    fun S hS => Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hInject : Set.InjOn d (F : Set (Finset Nat)) := by
    intro S hS T hT he
    have hs := Nat.primeFactors_prod (fun p hp => hPrime p (hSub S hS hp))
    have ht := Nat.primeFactors_prod (fun p hp => hPrime p (hSub T hT hp))
    exact hs.symm.trans ((congrArg Nat.primeFactors he).trans ht)
  have hRange : F.image d <= Finset.Icc 1 Q := by
    intro q hq
    choose S hS he using Finset.mem_image.mp hq
    subst q
    apply Finset.mem_Icc.mpr
    constructor
    next =>
      have hne : Not (d S = 0) := Finset.prod_ne_zero_iff.mpr
        (fun p hp => (hPrime p (hSub S hS hp)).ne_zero)
      exact Nat.one_le_iff_ne_zero.mpr hne
    next => exact (Finset.mem_filter.mp hS).2
  calc
    _ = Finset.sum F (fun S =>
        (Finset.prod S (fun p => ((A p).card : Real) / ((p : Real) - (A p).card))) *
          (X.card : Real) ^ 2) := by rw [sieveLevelWeight, Finset.sum_mul]
    _ <= Finset.sum F (fun S => sieveModulusEnergy X (d S)) := by
      apply Finset.sum_le_sum
      intro S hS
      have hne : Not (d S = 0) := Finset.prod_ne_zero_iff.mpr
        (fun p hp => (hPrime p (hSub S hS hp)).ne_zero)
      letI : NeZero (d S) := NeZero.mk hne
      have h := sieveProduct_primitive_energy_lower_bound S A
        (fun p hp => hPrime p (hSub S hS hp))
        (fun p hp => hA p (hSub S hS hp)) X
        (fun k hk p hp => hAvoid k hk p (hSub S hS hp))
      rw [primitive_sum_eq_units] at h
      simpa only [sieveModulusEnergy_eq] using h
    _ = Finset.sum (F.image d) (sieveModulusEnergy X) :=
      (Finset.sum_image hInject).symm
    _ <= Finset.sum (Finset.Icc 1 Q) (sieveModulusEnergy X) :=
      Finset.sum_le_sum_of_subset_of_nonneg hRange
        (fun q _ _ => sieveModulusEnergy_nonneg X q)
    _ <= _ := sieveModulusEnergy_sum_le X hN hQ hX

theorem sieveLevelWeight_one_le (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p))
    (hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p))
    {Q : Nat} (hQ : 0 < Q) : 1 <= sieveLevelWeight P A Q := by
  classical
  unfold sieveLevelWeight
  have hEmpty : Membership.mem
      (P.powerset.filter (fun S => Finset.prod S (fun p => p) <= Q)) {} := by
    simpa using Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hQ)
  have hNonneg : forall S, Membership.mem
      (P.powerset.filter (fun S => Finset.prod S (fun p => p) <= Q)) S ->
      0 <= Finset.prod S
        (fun p => ((A p).card : Real) / ((p : Real) - (A p).card)) := by
    intro S hS
    apply Finset.prod_nonneg
    intro p hp
    have hpP := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1 hp
    have hlt : ((A p).card : Real) < (p : Real) := by exact_mod_cast (hA p hpP).2
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have h := Finset.single_le_sum hNonneg hEmpty
  simpa using h

/-- The complete finite sieve bound, including the empty survivor set. -/
theorem sieveLevelWeight_card_le (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p))
    (hPrime : forall p, Membership.mem P p -> Nat.Prime p)
    (hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p))
    (X : Finset Nat) {N Q : Nat} (hN : 0 < N) (hQ : 0 < Q)
    (hX : X <= Finset.range N)
    (hAvoid : forall k, Membership.mem X k ->
      forall p, Membership.mem P p -> Not (Membership.mem (A p) (k : ZMod p))) :
    (X.card : Real) <= 36 * ((N : Real) + (Q : Real) ^ 2) /
      sieveLevelWeight P A Q := by
  have hWeight : 0 < sieveLevelWeight P A Q :=
    lt_of_lt_of_le zero_lt_one (sieveLevelWeight_one_le P A hA hQ)
  rw [div_eq_mul_inv]
  apply (mul_le_mul_iff_of_pos_right hWeight).mp
  have hne : Not (sieveLevelWeight P A Q = 0) := ne_of_gt hWeight
  have hCancel : Inv.inv (sieveLevelWeight P A Q) * sieveLevelWeight P A Q = 1 := by
    field_simp
  rw [mul_assoc, hCancel, mul_one]
  have h := sieveLevelWeight_card_sq_le P A hPrime hA X hN hQ hX hAvoid
  have hn : (0 : Real) <= (N : Real) := Nat.cast_nonneg N
  by_cases hc : X.card = 0
  next => simp only [hc, Nat.cast_zero, zero_mul]; positivity
  next =>
    have hcPos : (0 : Real) < X.card := by exact_mod_cast Nat.pos_of_ne_zero hc
    nlinarith

end PrimeFactorOscillations.LPF

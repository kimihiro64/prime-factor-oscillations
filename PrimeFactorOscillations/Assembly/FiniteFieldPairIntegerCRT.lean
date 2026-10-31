/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerMass
import PrimeFactorOscillations.Assembly.FiniteFieldPairSubperiodMass
import PrimeFactorOscillations.Assembly.PeriodicPairAffinity
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePastWave

/-!
# Native CRT transport to consecutive integer samples

The canonical ring CRT map sends every natural integer to its actual
residue tuple. A sample no longer than the modulus product is injective.
The exact finite subset energy bound therefore applies below one period;
longer samples inherit the normalized affinity bound. No independence
hypothesis or assumed prime-pair mass enters the transport.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldPairIntegerCRT
attribute [local instance] Classical.propDecidable
open PeriodicPairAffinity FiniteFieldPairSubperiodMass
variable {I : Type*} [Fintype I] [DecidableEq I]

def modulus (m : I -> Nat) : Nat := Finset.univ.prod m

def residueTuple (m : I -> Nat) (n : Nat) : (i : I) -> ZMod (m i) :=
  fun _ => n

def sampled (m : I -> Nat) (F : ((i : I) -> ZMod (m i)) -> Real) (n : Nat) : Real :=
  F (residueTuple m n)

theorem zmod_sum_range (M : Nat) [NeZero M] (f : ZMod M -> Real) :
    (Finset.range M).sum (fun n => f (n : ZMod M))=Finset.univ.sum f := by
  refine Finset.sum_bij (s := Finset.range M) (t := Finset.univ)
    (fun (n : Nat) _ => (n : ZMod M)) ?_ ?_ ?_ ?_
  . intro n _
    exact Finset.mem_univ _
  . intro a ha b hb he
    have hv := congrArg (fun x : ZMod M => x.val) he
    rw [ZMod.val_natCast,ZMod.val_natCast,
      Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] at hv
    exact hv
  . intro x _
    refine Exists.intro x.val (Exists.intro (Finset.mem_range.mpr (ZMod.val_lt x)) ?_)
    simp
  . intro n _
    rfl

variable (m : I -> Nat) [forall i, NeZero (m i)] [NeZero (modulus m)]

def crtEquiv (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) :
    RingEquiv (ZMod (modulus m)) ((i : I) -> ZMod (m i)) :=
  ZMod.prodEquivPi m hcop

theorem crt_natCast (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) (n : Nat) :
    crtEquiv m hcop (n : ZMod (modulus m))=residueTuple m n := by
  rw [map_natCast]
  rfl

theorem crt_period_sum (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (F : ((i : I) -> ZMod (m i)) -> Real) :
    (Finset.range (modulus m)).sum (sampled m F)=Finset.univ.sum F := by
  calc
    _ = (Finset.range (modulus m)).sum
        (fun n => F (crtEquiv m hcop (n : ZMod (modulus m)))) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [crt_natCast]
      rfl
    _ = Finset.univ.sum (fun z => F (crtEquiv m hcop z)) :=
      zmod_sum_range (modulus m) (fun z => F (crtEquiv m hcop z))
    _ = _ := (crtEquiv m hcop).toEquiv.sum_comp F

theorem sampled_periodic (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (F : ((i : I) -> ZMod (m i)) -> Real) (n : Nat) :
    sampled m F (n+modulus m)=sampled m F n := by
  have he : ((n+modulus m : Nat) : ZMod (modulus m))=(n : ZMod (modulus m)) := by simp
  have ht := congrArg (crtEquiv m hcop) he
  rw [crt_natCast,crt_natCast] at ht
  exact congrArg F ht

def windowImage (A N : Nat) : Finset ((i : I) -> ZMod (m i)) :=
  (Finset.range N).image (fun j => residueTuple m (A+j))

theorem window_injective (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (A N : Nat) (hNM : N<=modulus m) :
    Set.InjOn (fun j => residueTuple m (A+j)) (Finset.range N) := by
  intro i hi j hj he
  have hz : ((A+i : Nat) : ZMod (modulus m))=((A+j : Nat) : ZMod (modulus m)) := by
    apply (crtEquiv m hcop).injective
    simpa only [crt_natCast] using he
  have hij : (i : ZMod (modulus m))=(j : ZMod (modulus m)) := by
    simp only [Nat.cast_add] at hz
    exact add_left_cancel hz
  have hv := congrArg (fun x : ZMod (modulus m) => x.val) hij
  rw [ZMod.val_natCast,ZMod.val_natCast,
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) hNM),
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hj) hNM)] at hv
  exact hv

theorem window_image_card (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (A N : Nat) (hNM : N<=modulus m) :
    (windowImage m A N).card=N := by
  unfold windowImage
  rw [Finset.card_image_of_injOn (window_injective m hcop A N hNM),Finset.card_range]

theorem window_image_sum (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (A N : Nat) (hNM : N<=modulus m)
    (F : ((i : I) -> ZMod (m i)) -> Real) :
    (windowImage m A N).sum F=intervalMass (sampled m F) A N := by
  symm
  unfold intervalMass windowImage sampled
  apply Finset.sum_bij (fun j _ => residueTuple m (A+j))
  . intro j hj
    exact Finset.mem_image_of_mem _ hj
  . intro i hi j hj he
    exact window_injective m hcop A N hNM hi hj he
  . intro x hx
    exact Exists.elim (Finset.mem_image.mp hx) (fun j hj =>
      Exists.intro j (Exists.intro hj.1 hj.2))
  . intro j _
    rfl

theorem residue_space_card :
    Fintype.card ((i : I) -> ZMod (m i))=modulus m := by
  simp only [Fintype.card_pi,ZMod.card,modulus]

theorem missing_window_count (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (A N : Nat) (hNM : N<=modulus m) :
    missingCount (windowImage m A N)=modulus m-N := by
  simp only [missingCount,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,
    window_image_card m hcop A N hNM,residue_space_card m]

theorem integer_subperiod_mass_lower
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (A N : Nat) (hNM : N<=modulus m)
    (F : ((i : I) -> ZMod (m i)) -> Real) (E : Real)
    (hmean : Finset.univ.sum F=(modulus m : Real))
    (henergy : (Finset.univ.sum fun x => (F x)^2)=(modulus m : Real)*E) :
    (modulus m : Real)-
      Real.sqrt (((modulus m : Real)-(N : Real))*((modulus m : Real)*E)) <=
        intervalMass (sampled m F) A N := by
  have hb := subset_mass_lower (windowImage m A N) F (modulus m : Real) hmean
  rw [henergy,missing_window_count m hcop A N hNM,Nat.cast_sub hNM,
    window_image_sum m hcop A N hNM F] at hb
  exact hb

theorem integer_subperiod_mass_positive
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (A N : Nat) (hNM : N<=modulus m)
    (F : ((i : I) -> ZMod (m i)) -> Real) (E : Real)
    (hmean : Finset.univ.sum F=(modulus m : Real))
    (henergy : (Finset.univ.sum fun x => (F x)^2)=(modulus m : Real)*E)
    (hroom : ((modulus m : Real)-(N : Real))*E<(modulus m : Real)) :
    0 < intervalMass (sampled m F) A N := by
  have hM : 0 < (modulus m : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne (modulus m)))
  have ht := mul_lt_mul_of_pos_left hroom hM
  have hc : (missingCount (windowImage m A N) : Real)*
      (Finset.univ.sum fun x => (F x)^2)<(modulus m : Real)^2 := by
    rw [henergy,missing_window_count m hcop A N hNM,Nat.cast_sub hNM]
    nlinarith only [ht]
  have hp := subset_mass_positive (windowImage m A N) F (modulus m : Real) hM hmean hc
  rw [window_image_sum m hcop A N hNM F] at hp
  exact hp

theorem integer_long_interval_affinity
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (A N : Nat) (hMN : modulus m<=N)
    (U V : ((i : I) -> ZMod (m i)) -> Real)
    (hU : forall x, 0<=U x) (hV : forall x, 0<=V x)
    (hmeanU : Finset.univ.sum U=(modulus m : Real))
    (hmeanV : Finset.univ.sum V=(modulus m : Real)) :
    And (0 < intervalMass (sampled m U) A N)
      (And (0 < intervalMass (sampled m V) A N)
        (intervalAffinity (sampled m U) (sampled m V) A N <=
          2*FiniteFieldPairAffinity.affinity (modulus m : Real) U V)) := by
  have hM : 0 < modulus m := Nat.pos_of_ne_zero (NeZero.ne (modulus m))
  have hmU : (Finset.range (modulus m)).sum (sampled m U)=(modulus m : Real) := by
    rw [crt_period_sum m hcop U,hmeanU]
  have hmV : (Finset.range (modulus m)).sum (sampled m V)=(modulus m : Real) := by
    rw [crt_period_sum m hcop V,hmeanV]
  have hb := interval_affinity_le_twice (modulus m) A N hM hMN
    (sampled m U) (sampled m V) (fun n => hU _) (fun n => hV _)
    (sampled_periodic m hcop U) (sampled_periodic m hcop V) hmU hmV
  have he : periodAffinity (modulus m) (sampled m U) (sampled m V)=
      FiniteFieldPairAffinity.affinity (modulus m : Real) U V := by
    unfold periodAffinity FiniteFieldPairAffinity.affinity
    congr 1
    exact crt_period_sum m hcop (fun x => Real.sqrt (U x*V x))
  rw [he] at hb
  exact hb


section PrimeModuli
variable [forall i, Fact (Nat.Prime (m i))]

theorem raw_integer_subperiod_mass_lower
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (h A N : Nat) (hNM : N<=modulus m)
    (hodd : forall i, Not (ringChar (ZMod (m i))=2))
    (hh : forall i, Not ((h : ZMod (m i))=0))
    (hq : forall i, 16<=(m i : Real)) :
    (modulus m : Real)-
      Real.sqrt (((modulus m : Real)-(N : Real))*
        ((modulus m : Real)*rawEnergy (fun i => ZMod (m i)) (fun _ => h))) <=
      intervalMass (sampled m
        (rawPacket (fun i => ZMod (m i)) (fun _ => h))) A N := by
  have hc (i : I) : 16<=(Fintype.card (ZMod (m i)) : Real) := by
    simpa only [ZMod.card] using hq i
  apply integer_subperiod_mass_lower m hcop A N hNM
  . simpa only [residue_space_card m] using
      raw_packet_mean (fun i => ZMod (m i)) (fun _ => h) hodd hh hc
  . simpa only [residue_space_card m] using
      raw_packet_square_sum (fun i => ZMod (m i)) (fun _ => h) hodd hh hc

theorem raw_integer_subperiod_mass_positive
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (h A N : Nat) (hNM : N<=modulus m)
    (hodd : forall i, Not (ringChar (ZMod (m i))=2))
    (hh : forall i, Not ((h : ZMod (m i))=0))
    (hq : forall i, 16<=(m i : Real))
    (hroom : ((modulus m : Real)-(N : Real))*
      rawEnergy (fun i => ZMod (m i)) (fun _ => h)<(modulus m : Real)) :
    0 < intervalMass (sampled m
      (rawPacket (fun i => ZMod (m i)) (fun _ => h))) A N := by
  have hc (i : I) : 16<=(Fintype.card (ZMod (m i)) : Real) := by
    simpa only [ZMod.card] using hq i
  apply integer_subperiod_mass_positive m hcop A N hNM _ _ _ _ hroom
  . simpa only [residue_space_card m] using
      raw_packet_mean (fun i => ZMod (m i)) (fun _ => h) hodd hh hc
  . simpa only [residue_space_card m] using
      raw_packet_square_sum (fun i => ZMod (m i)) (fun _ => h) hodd hh hc

end PrimeModuli


theorem prime_pair_of_nonzero_packet (Y h n : Nat)
    (hY : 1<=Y) (hlo : Y<n) (hhi : n+h<=Y*Y)
    (hcover : forall p : Nat, Nat.Prime p -> p<=Y ->
      exists i : I, m i=p)
    (F : ((i : I) -> ZMod (m i)) -> Real)
    (hmask : forall (i : I) (x : (i : I) -> ZMod (m i)),
      (x i=0 \/ x i=-(h : ZMod (m i))) -> F x=0)
    (hnz : Not (sampled m F n=0)) :
    Nat.Prime n /\ Nat.Prime (n+h) := by
  apply And.intro
  . apply (PrimeFactorOscillations.PrimeClassDeletion.prime_iff_no_past_prime_divisor
      Y n hY hlo (by omega)).mpr
    intro p hp hpY hpn
    let i : I := Classical.choose (hcover p hp hpY)
    have hi : m i=p := Classical.choose_spec (hcover p hp hpY)
    have hd : Dvd.dvd (m i) n := by simpa only [hi] using hpn
    have hz : (n : ZMod (m i))=0 :=
      (CharP.cast_eq_zero_iff (ZMod (m i)) (m i) n).mpr hd
    exact hnz (hmask i (residueTuple m n) (Or.inl hz))
  . apply (PrimeFactorOscillations.PrimeClassDeletion.prime_iff_no_past_prime_divisor
      Y (n+h) hY (by omega) hhi).mpr
    intro p hp hpY hpn
    let i : I := Classical.choose (hcover p hp hpY)
    have hi : m i=p := Classical.choose_spec (hcover p hp hpY)
    have hd : Dvd.dvd (m i) (n+h) := by simpa only [hi] using hpn
    have hz : ((n+h : Nat) : ZMod (m i))=0 :=
      (CharP.cast_eq_zero_iff (ZMod (m i)) (m i) (n+h)).mpr hd
    have hn : (n : ZMod (m i))=-(h : ZMod (m i)) := by
      rw [Nat.cast_add] at hz
      exact eq_neg_of_add_eq_zero_left hz
    exact hnz (hmask i (residueTuple m n) (Or.inr hn))

theorem prime_pair_of_positive_integer_mass (Y h A N : Nat)
    (hY : 1<=Y)
    (hlo : forall j : Nat, j<N -> Y<A+j)
    (hhi : forall j : Nat, j<N -> A+j+h<=Y*Y)
    (hcover : forall p : Nat, Nat.Prime p -> p<=Y ->
      exists i : I, m i=p)
    (F : ((i : I) -> ZMod (m i)) -> Real)
    (hmask : forall (i : I) (x : (i : I) -> ZMod (m i)),
      (x i=0 \/ x i=-(h : ZMod (m i))) -> F x=0)
    (hmass : 0 < intervalMass (sampled m F) A N) :
    exists j : Nat, j<N /\ Nat.Prime (A+j) /\ Nat.Prime (A+j+h) := by
  have hex : exists j : Nat, j<N /\ 0 < sampled m F (A+j) := by
    by_contra hn
    have hz : intervalMass (sampled m F) A N<=0 := by
      unfold intervalMass
      apply Finset.sum_nonpos
      intro j hj
      apply le_of_not_gt
      intro hp
      exact hn (Exists.intro j (And.intro (Finset.mem_range.mp hj) hp))
    exact (not_lt_of_ge hz) hmass
  let j : Nat := Classical.choose hex
  have hj := Classical.choose_spec hex
  have hp := prime_pair_of_nonzero_packet m Y h (A+j) hY (hlo j hj.1)
    (hhi j hj.1) hcover F hmask (ne_of_gt hj.2)
  exact Exists.intro j (And.intro hj.1 hp)

theorem prime_pair_of_subperiod_energy
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (Y h A N : Nat) (hNM : N<=modulus m) (hY : 1<=Y)
    (hlo : forall j : Nat, j<N -> Y<A+j)
    (hhi : forall j : Nat, j<N -> A+j+h<=Y*Y)
    (hcover : forall p : Nat, Nat.Prime p -> p<=Y ->
      exists i : I, m i=p)
    (F : ((i : I) -> ZMod (m i)) -> Real)
    (hmask : forall (i : I) (x : (i : I) -> ZMod (m i)),
      (x i=0 \/ x i=-(h : ZMod (m i))) -> F x=0)
    (E : Real) (hmean : Finset.univ.sum F=(modulus m : Real))
    (henergy : (Finset.univ.sum fun x => (F x)^2)=(modulus m : Real)*E)
    (hroom : ((modulus m : Real)-(N : Real))*E<(modulus m : Real)) :
    exists j : Nat, j<N /\ Nat.Prime (A+j) /\ Nat.Prime (A+j+h) := by
  exact prime_pair_of_positive_integer_mass m Y h A N hY hlo hhi hcover F hmask
    (integer_subperiod_mass_positive m hcop A N hNM F E hmean henergy hroom)

end PrimeFactorOscillations.FiniteFieldPairIntegerCRT

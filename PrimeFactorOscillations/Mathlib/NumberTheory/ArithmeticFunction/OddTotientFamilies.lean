/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.TotientSubsetSumIntervals

/-!
# Explicit odd-totient degree families

Tower stages, primitive degrees and polynomial probe indices are separate.
The five auxiliary primes feed both exceptional-characteristic families.
All equal weights at distinct degrees are retained.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

namespace Nat

def oddTotientAuxiliaryPrimes : Finset Nat := {7,11,13,17,19}

def oddTotientBaseThree : Finset Nat := {5,7,11,13,17,19}
def oddTotientBaseFive : Finset Nat := {3,7,9,11,13,17,19}
def oddTotientBaseOther : Finset Nat := {3,5}

def oddTotientScaledBlock (r i : Nat) : Finset Nat :=
  oddTotientAuxiliaryPrimes.image (fun e => e*r^(i+1))

def oddTotientOtherBlock (i : Nat) : Finset Nat :=
  {3^(i+2),5*3^(i+1)}

def oddTotientThreeDegrees : Nat -> Finset Nat
  | 0 => Union.union oddTotientBaseThree (oddTotientScaledBlock 5 0)
  | j+1 => Union.union (oddTotientThreeDegrees j) (oddTotientScaledBlock 5 (j+1))

def oddTotientFiveDegrees : Nat -> Finset Nat
  | 0 => Union.union oddTotientBaseFive (oddTotientScaledBlock 3 0)
  | j+1 => Union.union (oddTotientFiveDegrees j) (oddTotientScaledBlock 3 (j+1))

def oddTotientOtherDegrees : Nat -> Finset Nat
  | 0 => Union.union oddTotientBaseOther (oddTotientOtherBlock 0)
  | j+1 => Union.union (oddTotientOtherDegrees j) (oddTotientOtherBlock (j+1))

theorem oddTotient_auxiliary_data (e : Nat)
    (he : Membership.mem oddTotientAuxiliaryPrimes e) :
    Nat.Prime e /\ Odd e /\ 7<=e /\ e<=19 /\
      Not (Dvd.dvd 3 e) /\ Not (Dvd.dvd 5 e) /\ Dvd.dvd e.totient 720 := by
  have hfinite : forall a : Nat, Membership.mem oddTotientAuxiliaryPrimes a ->
      Nat.Prime a /\ Odd a /\ 7<=a /\ a<=19 /\
        Not (Dvd.dvd 3 a) /\ Not (Dvd.dvd 5 a) /\ Dvd.dvd a.totient 720 := by
    decide
  exact hfinite e he

theorem oddTotient_prime_power_unit_injective (r u v a b : Nat)
    (hr : Nat.Prime r) (hu : 0<u) (hv : 0<v)
    (hru : Not (Dvd.dvd r u)) (hrv : Not (Dvd.dvd r v))
    (heq : u*r^a=v*r^b) : u=v /\ a=b := by
  have hleft : (u*r^a).factorization r=a := by
    rw [Nat.factorization_mul (by omega : Not (u=0)) (pow_ne_zero a hr.ne_zero)]
    simp [Nat.factorization_pow,hr.factorization,
      Nat.factorization_eq_zero_of_not_dvd hru]
  have hright : (v*r^b).factorization r=b := by
    rw [Nat.factorization_mul (by omega : Not (v=0)) (pow_ne_zero b hr.ne_zero)]
    simp [Nat.factorization_pow,hr.factorization,
      Nat.factorization_eq_zero_of_not_dvd hrv]
  have hab : a=b := by
    have hh := congrArg (fun n : Nat => n.factorization r) heq
    rw [hleft,hright] at hh
    exact hh
  have huv : u=v := by
    apply Nat.mul_left_cancel (pow_pos hr.pos a)
    calc
      _ = u*r^a := Nat.mul_comm _ _
      _ = v*r^b := heq
      _ = r^a*v := by rw [hab,Nat.mul_comm v (r^b)]
  exact And.intro huv hab

theorem oddTotient_scaled_three_weight (e i : Nat) (he : Nat.Coprime 3 e) :
    (e*3^(i+1)).totient/2=e.totient*3^i := by
  rw [Nat.totient_mul (Nat.Coprime.pow_right (i+1) he.symm),
    Nat.totient_prime_pow (by decide : Nat.Prime 3) (by omega : 0 < (i+1)),
    show i+1-1=i by omega,show (3 : Nat)-1=2 from rfl,<- Nat.mul_assoc]
  omega

theorem oddTotient_scaled_five_weight (e i : Nat) (he : Nat.Coprime 5 e) :
    (e*5^(i+1)).totient/2=2*(e.totient*5^i) := by
  rw [Nat.totient_mul (Nat.Coprime.pow_right (i+1) he.symm),
    Nat.totient_prime_pow (by decide : Nat.Prime 5) (by omega : 0 < (i+1)),
    show i+1-1=i by omega,show (5 : Nat)-1=4 from rfl,<- Nat.mul_assoc]
  omega

theorem oddTotient_scaled_blocks_disjoint (r i j : Nat) (hr : Nat.Prime r)
    (hunit : forall e, Membership.mem oddTotientAuxiliaryPrimes e -> Not (Dvd.dvd r e))
    (hne : Not (i=j)) :
    Disjoint (oddTotientScaledBlock r i) (oddTotientScaledBlock r j) := by
  apply Finset.disjoint_left.mpr
  intro d hleft hright
  choose u hu using Finset.mem_image.mp hleft
  choose v hv using Finset.mem_image.mp hright
  have hdu := oddTotient_auxiliary_data u hu.1
  have hdv := oddTotient_auxiliary_data v hv.1
  have hs := oddTotient_prime_power_unit_injective r u v (i+1) (j+1) hr
    (by have hh := hdu.2.2.1; omega) (by have hh := hdv.2.2.1; omega)
    (hunit u hu.1) (hunit v hv.1) (hu.2.trans hv.2.symm)
  have hij : i=j := by have hh := hs.2; omega
  exact hne hij

theorem oddTotient_base_scaled_block_disjoint (B : Finset Nat) (r i : Nat)
    (hr : 3<=r) (hB : forall d, Membership.mem B d -> d<=19) :
    Disjoint B (oddTotientScaledBlock r i) := by
  apply Finset.disjoint_left.mpr
  intro d hd hb
  choose e he using Finset.mem_image.mp hb
  have hde := oddTotient_auxiliary_data e he.1
  have he7 := hde.2.2.1
  have hpow : r<=r^(i+1) := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (n:=r) (i:=1) (j:=i+1) (by omega) (by omega))
  have hprod := Nat.mul_le_mul he7 (show 3<=r^(i+1) by omega)
  have hdsmall := hB d hd
  omega

theorem oddTotient_scaled_five_block_sum (i : Nat) :
    (oddTotientScaledBlock 5 i).sum (fun d => d.totient/2)=124*5^i := by
  rw [oddTotientScaledBlock,Finset.sum_image]
  . calc
      oddTotientAuxiliaryPrimes.sum (fun e => (e*5^(i+1)).totient/2) =
          oddTotientAuxiliaryPrimes.sum (fun e => 2*(e.totient*5^i)) := by
        apply Finset.sum_congr rfl
        intro e he
        have hd := oddTotient_auxiliary_data e he
        exact oddTotient_scaled_five_weight e i
          ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr hd.2.2.2.2.2.1)
      _ = (oddTotientAuxiliaryPrimes.sum (fun e => 2*e.totient))*5^i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        exact (Nat.mul_assoc 2 e.totient (5^i)).symm
      _ = 124*5^i := by
        have hs : oddTotientAuxiliaryPrimes.sum (fun e => 2*e.totient)=124 := by decide
        rw [hs]
  . intro u hu v hv heq
    apply Nat.mul_left_cancel (pow_pos (by decide : 0<(5 : Nat)) (i+1))
    calc
      _ = u*5^(i+1) := Nat.mul_comm _ _
      _ = v*5^(i+1) := heq
      _ = _ := Nat.mul_comm _ _

theorem oddTotient_scaled_three_block_sum (i : Nat) :
    (oddTotientScaledBlock 3 i).sum (fun d => d.totient/2)=62*3^i := by
  rw [oddTotientScaledBlock,Finset.sum_image]
  . calc
      oddTotientAuxiliaryPrimes.sum (fun e => (e*3^(i+1)).totient/2) =
          oddTotientAuxiliaryPrimes.sum (fun e => e.totient*3^i) := by
        apply Finset.sum_congr rfl
        intro e he
        have hd := oddTotient_auxiliary_data e he
        exact oddTotient_scaled_three_weight e i
          ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hd.2.2.2.2.1)
      _ = (oddTotientAuxiliaryPrimes.sum (fun e => e.totient))*3^i :=
        (Finset.sum_mul _ _ _).symm
      _ = 62*3^i := by
        have hs : oddTotientAuxiliaryPrimes.sum (fun e => e.totient)=62 := by decide
        rw [hs]
  . intro u hu v hv heq
    apply Nat.mul_left_cancel (pow_pos (by decide : 0<(3 : Nat)) (i+1))
    calc
      _ = u*3^(i+1) := Nat.mul_comm _ _
      _ = v*3^(i+1) := heq
      _ = _ := Nat.mul_comm _ _

theorem oddTotient_base_weight_sums :
    oddTotientBaseThree.sum (fun d => d.totient/2)=33 /\
      oddTotientBaseFive.sum (fun d => d.totient/2)=35 /\
      oddTotientBaseOther.sum (fun d => d.totient/2)=3 := by
  decide


theorem oddTotient_three_mem_cases (d j : Nat) :
    Membership.mem (oddTotientThreeDegrees j) d ->
      Membership.mem oddTotientBaseThree d \/
        exists i : Nat, i<=j /\ Membership.mem (oddTotientScaledBlock 5 i) d := by
  induction j with
  | zero =>
    intro hd
    cases Finset.mem_union.mp hd with
    | inl hb => exact Or.inl hb
    | inr hs => exact Or.inr (Exists.intro 0 (And.intro (by omega) hs))
  | succ j ih =>
    intro hd
    cases Finset.mem_union.mp hd with
    | inl hold =>
      cases ih hold with
      | inl hb => exact Or.inl hb
      | inr hex =>
        choose i hi using hex
        exact Or.inr (Exists.intro i (And.intro (by omega) hi.2))
    | inr hs => exact Or.inr (Exists.intro (j+1) (And.intro (by omega) hs))

theorem oddTotient_five_mem_cases (d j : Nat) :
    Membership.mem (oddTotientFiveDegrees j) d ->
      Membership.mem oddTotientBaseFive d \/
        exists i : Nat, i<=j /\ Membership.mem (oddTotientScaledBlock 3 i) d := by
  induction j with
  | zero =>
    intro hd
    cases Finset.mem_union.mp hd with
    | inl hb => exact Or.inl hb
    | inr hs => exact Or.inr (Exists.intro 0 (And.intro (by omega) hs))
  | succ j ih =>
    intro hd
    cases Finset.mem_union.mp hd with
    | inl hold =>
      cases ih hold with
      | inl hb => exact Or.inl hb
      | inr hex =>
        choose i hi using hex
        exact Or.inr (Exists.intro i (And.intro (by omega) hi.2))
    | inr hs => exact Or.inr (Exists.intro (j+1) (And.intro (by omega) hs))

theorem oddTotient_other_mem_cases (d j : Nat) :
    Membership.mem (oddTotientOtherDegrees j) d ->
      Membership.mem oddTotientBaseOther d \/
        exists i : Nat, i<=j /\ Membership.mem (oddTotientOtherBlock i) d := by
  induction j with
  | zero =>
    intro hd
    cases Finset.mem_union.mp hd with
    | inl hb => exact Or.inl hb
    | inr hs => exact Or.inr (Exists.intro 0 (And.intro (by omega) hs))
  | succ j ih =>
    intro hd
    cases Finset.mem_union.mp hd with
    | inl hold =>
      cases ih hold with
      | inl hb => exact Or.inl hb
      | inr hex =>
        choose i hi using hex
        exact Or.inr (Exists.intro i (And.intro (by omega) hi.2))
    | inr hs => exact Or.inr (Exists.intro (j+1) (And.intro (by omega) hs))

theorem oddTotient_other_blocks_disjoint (i j : Nat) (hne : Not (i=j)) :
    Disjoint (oddTotientOtherBlock i) (oddTotientOtherBlock j) := by
  apply Finset.disjoint_left.mpr
  intro d hleft hright
  have hl : d=3^(i+2) \/ d=5*3^(i+1) := by
    simpa only [oddTotientOtherBlock,Finset.mem_insert,Finset.mem_singleton] using hleft
  have hr : d=3^(j+2) \/ d=5*3^(j+1) := by
    simpa only [oddTotientOtherBlock,Finset.mem_insert,Finset.mem_singleton] using hright
  cases hl with
  | inl hi =>
    cases hr with
    | inl hj =>
      have hh := (Nat.pow_right_injective (by decide : 2<=(3 : Nat)))
        (hi.symm.trans hj)
      exact hne (by omega)
    | inr hj =>
      have heq : 1*3^(i+2)=5*3^(j+1) := by
        simpa only [one_mul] using hi.symm.trans hj
      have hh := oddTotient_prime_power_unit_injective 3 1 5 (i+2) (j+1)
        (by decide) (by decide) (by decide) (by decide) (by decide) heq
      have hhunit := hh.1
      omega
  | inr hi =>
    cases hr with
    | inl hj =>
      have heq : 5*3^(i+1)=1*3^(j+2) := by
        simpa only [one_mul] using hi.symm.trans hj
      have hh := oddTotient_prime_power_unit_injective 3 5 1 (i+1) (j+2)
        (by decide) (by decide) (by decide) (by decide) (by decide) heq
      have hhunit := hh.1
      omega
    | inr hj =>
      have hh := oddTotient_prime_power_unit_injective 3 5 5 (i+1) (j+1)
        (by decide) (by decide) (by decide) (by decide) (by decide) (hi.symm.trans hj)
      have hhindex := hh.2
      exact hne (by omega)

theorem oddTotient_base_other_block_disjoint (i : Nat) :
    Disjoint oddTotientBaseOther (oddTotientOtherBlock i) := by
  apply Finset.disjoint_left.mpr
  intro d hd hb
  have hsmall : d<=5 := by
    have hs : d=3 \/ d=5 := by
      simpa only [oddTotientBaseOther,Finset.mem_insert,Finset.mem_singleton] using hd
    omega
  have hthree : 3<=(3 : Nat)^(i+1) := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (n:=3) (i:=1) (j:=i+1) (by decide) (by omega))
  have hnine : 9<=(3 : Nat)^(i+2) := by
    simpa only [show (3 : Nat)^2=9 from rfl] using
      (Nat.pow_le_pow_right (n:=3) (i:=2) (j:=i+2) (by decide) (by omega))
  have hs : d=3^(i+2) \/ d=5*3^(i+1) := by
    simpa only [oddTotientOtherBlock,Finset.mem_insert,Finset.mem_singleton] using hb
  omega

theorem oddTotient_other_block_sum (i : Nat) :
    (oddTotientOtherBlock i).sum (fun d => d.totient/2)=7*3^i := by
  have hne : Not ((3 : Nat)^(i+2)=5*3^(i+1)) := by
    intro heq
    have hh := oddTotient_prime_power_unit_injective 3 1 5 (i+2) (i+1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [one_mul] using heq)
    have hhunit := hh.1
    omega
  rw [oddTotientOtherBlock,Finset.sum_insert (by
    simpa only [Finset.mem_singleton] using hne),Finset.sum_singleton]
  have hfirst : (3^(i+2) : Nat).totient/2=3*3^i := by
    rw [Nat.totient_prime_pow (by decide : Nat.Prime 3) (by omega : 0 < (i+2)),
      show i+2-1=i+1 by omega,show (3 : Nat)-1=2 from rfl,pow_succ]
    omega
  have hsecond := oddTotient_scaled_three_weight 5 i (by decide)
  have hphi : (5 : Nat).totient=4 := by decide
  rw [hphi] at hsecond
  rw [hfirst,hsecond]
  omega

theorem oddTotient_three_next_disjoint (j : Nat) :
    Disjoint (oddTotientThreeDegrees j) (oddTotientScaledBlock 5 (j+1)) := by
  apply Finset.disjoint_left.mpr
  intro d hold hnew
  cases oddTotient_three_mem_cases d j hold with
  | inl hb =>
    have hbase := oddTotient_base_scaled_block_disjoint oddTotientBaseThree 5 (j+1)
      (by decide) (by decide)
    exact Finset.disjoint_left.mp hbase hb hnew
  | inr hex =>
    choose i hi using hex
    have hblocks := oddTotient_scaled_blocks_disjoint 5 i (j+1) (by decide)
      (fun e he => (oddTotient_auxiliary_data e he).2.2.2.2.2.1) (by omega)
    exact Finset.disjoint_left.mp hblocks hi.2 hnew

theorem oddTotient_five_next_disjoint (j : Nat) :
    Disjoint (oddTotientFiveDegrees j) (oddTotientScaledBlock 3 (j+1)) := by
  apply Finset.disjoint_left.mpr
  intro d hold hnew
  cases oddTotient_five_mem_cases d j hold with
  | inl hb =>
    have hbase := oddTotient_base_scaled_block_disjoint oddTotientBaseFive 3 (j+1)
      (by decide) (by decide)
    exact Finset.disjoint_left.mp hbase hb hnew
  | inr hex =>
    choose i hi using hex
    have hblocks := oddTotient_scaled_blocks_disjoint 3 i (j+1) (by decide)
      (fun e he => (oddTotient_auxiliary_data e he).2.2.2.2.1) (by omega)
    exact Finset.disjoint_left.mp hblocks hi.2 hnew

theorem oddTotient_other_next_disjoint (j : Nat) :
    Disjoint (oddTotientOtherDegrees j) (oddTotientOtherBlock (j+1)) := by
  apply Finset.disjoint_left.mpr
  intro d hold hnew
  cases oddTotient_other_mem_cases d j hold with
  | inl hb =>
    exact Finset.disjoint_left.mp (oddTotient_base_other_block_disjoint (j+1)) hb hnew
  | inr hex =>
    choose i hi using hex
    exact Finset.disjoint_left.mp (oddTotient_other_blocks_disjoint i (j+1) (by omega))
      hi.2 hnew

theorem oddTotient_three_total (j : Nat) :
    (oddTotientThreeDegrees j).sum (fun d => d.totient/2)=31*5^(j+1)+2 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [oddTotientThreeDegrees,Finset.sum_union (oddTotient_three_next_disjoint j),
      oddTotient_scaled_five_block_sum,ih]
    simp only [pow_succ]
    omega

theorem oddTotient_five_total (j : Nat) :
    (oddTotientFiveDegrees j).sum (fun d => d.totient/2)=31*3^(j+1)+4 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [oddTotientFiveDegrees,Finset.sum_union (oddTotient_five_next_disjoint j),
      oddTotient_scaled_three_block_sum,ih]
    simp only [pow_succ]
    omega

theorem oddTotient_other_total (j : Nat) :
    2*(oddTotientOtherDegrees j).sum (fun d => d.totient/2)+1=7*3^(j+1) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [oddTotientOtherDegrees,Finset.sum_union (oddTotient_other_next_disjoint j),
      oddTotient_other_block_sum]
    simp only [pow_succ] at ih
    simp only [pow_succ]
    omega


theorem oddTotient_scaled_block_data (p r i d : Nat) (hr : Odd r) (hrpos : 0<r)
    (hpr : Nat.Coprime p r)
    (hpe : forall e, Membership.mem oddTotientAuxiliaryPrimes e -> Nat.Coprime p e)
    (hd : Membership.mem (oddTotientScaledBlock r i) d) :
    Odd d /\ 1<d /\ Nat.Coprime p d := by
  choose e he using Finset.mem_image.mp hd
  have hdata := oddTotient_auxiliary_data e he.1
  have hp : 0<r^(i+1) := pow_pos hrpos _
  have hlo := Nat.mul_le_mul hdata.2.2.1 (show 1<=r^(i+1) by omega)
  rw [<- he.2]
  exact And.intro (hdata.2.1.mul (Odd.pow hr))
    (And.intro (by omega) ((hpe e he.1).mul_right (Nat.Coprime.pow_right (i+1) hpr)))

theorem oddTotient_other_block_data (p i d : Nat)
    (hp3 : Nat.Coprime p 3) (hp5 : Nat.Coprime p 5)
    (hd : Membership.mem (oddTotientOtherBlock i) d) :
    Odd d /\ 1<d /\ Nat.Coprime p d := by
  have hthree : 3<=(3 : Nat)^(i+1) := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (n:=3) (i:=1) (j:=i+1) (by decide) (by omega))
  have hnine : 9<=(3 : Nat)^(i+2) := by
    simpa only [show (3 : Nat)^2=9 from rfl] using
      (Nat.pow_le_pow_right (n:=3) (i:=2) (j:=i+2) (by decide) (by omega))
  have hs : d=3^(i+2) \/ d=5*3^(i+1) := by
    simpa only [oddTotientOtherBlock,Finset.mem_insert,Finset.mem_singleton] using hd
  cases hs with
  | inl heq =>
    rw [heq]
    exact And.intro (Odd.pow (by decide : Odd (3 : Nat)))
      (And.intro (by omega) (Nat.Coprime.pow_right (i+2) hp3))
  | inr heq =>
    rw [heq]
    exact And.intro ((by decide : Odd (5 : Nat)).mul (Odd.pow (by decide : Odd (3 : Nat))))
      (And.intro (by omega) (hp5.mul_right (Nat.Coprime.pow_right (i+1) hp3)))

theorem oddTotient_three_data (d j : Nat)
    (hd : Membership.mem (oddTotientThreeDegrees j) d) :
    Odd d /\ 1<d /\ Nat.Coprime 3 d := by
  cases oddTotient_three_mem_cases d j hd with
  | inl hb =>
    have hbase : forall a, Membership.mem oddTotientBaseThree a ->
        Odd a /\ 1<a /\ Nat.Coprime 3 a := by decide
    exact hbase d hb
  | inr hex =>
    choose i hi using hex
    apply oddTotient_scaled_block_data 3 5 i d (by decide) (by decide) (by decide)
    . intro e he
      exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
        (oddTotient_auxiliary_data e he).2.2.2.2.1
    . exact hi.2

theorem oddTotient_five_data (d j : Nat)
    (hd : Membership.mem (oddTotientFiveDegrees j) d) :
    Odd d /\ 1<d /\ Nat.Coprime 5 d := by
  cases oddTotient_five_mem_cases d j hd with
  | inl hb =>
    have hbase : forall a, Membership.mem oddTotientBaseFive a ->
        Odd a /\ 1<a /\ Nat.Coprime 5 a := by decide
    exact hbase d hb
  | inr hex =>
    choose i hi using hex
    apply oddTotient_scaled_block_data 5 3 i d (by decide) (by decide) (by decide)
    . intro e he
      exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr
        (oddTotient_auxiliary_data e he).2.2.2.2.2.1
    . exact hi.2

theorem oddTotient_other_data (p d j : Nat)
    (hp3 : Nat.Coprime p 3) (hp5 : Nat.Coprime p 5)
    (hd : Membership.mem (oddTotientOtherDegrees j) d) :
    Odd d /\ 1<d /\ Nat.Coprime p d := by
  cases oddTotient_other_mem_cases d j hd with
  | inl hb =>
    have hs : d=3 \/ d=5 := by
      simpa only [oddTotientBaseOther,Finset.mem_insert,Finset.mem_singleton] using hb
    cases hs with
    | inl heq => rw [heq]; exact And.intro (by decide) (And.intro (by decide) hp3)
    | inr heq => rw [heq]; exact And.intro (by decide) (And.intro (by decide) hp5)
  | inr hex =>
    choose i hi using hex
    exact oddTotient_other_block_data p i d hp3 hp5 hi.2

theorem oddTotient_normalized_weight_double (d : Nat) (hodd : Odd d) (hd : 1<d) :
    2*(d.totient/2)=d.totient := by
  have hd3 : 2<d := by
    have hm := Nat.odd_iff.mp hodd
    omega
  choose k hk using Nat.totient_even hd3
  omega

theorem oddTotient_sum_normalized_double (D : Finset Nat)
    (hD : forall d, Membership.mem D d -> Odd d /\ 1<d) :
    D.sum Nat.totient=2*(D.sum (fun d => d.totient/2)) := by
  calc
    D.sum Nat.totient = D.sum (fun d => 2*(d.totient/2)) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact (oddTotient_normalized_weight_double d (hD d hd).1 (hD d hd).2).symm
    _ = 2*(D.sum (fun d => d.totient/2)) := (Finset.mul_sum _ _ _).symm

end Nat

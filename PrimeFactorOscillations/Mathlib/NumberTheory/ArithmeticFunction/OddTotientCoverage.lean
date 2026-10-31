/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.OddTotientFamilies

/-!
# Universal interval growth for the explicit odd-totient blocks

The list order retains the available prefix weight at every insertion. The
new-degree hypotheses are consumed from the degree-family disjointness
theorems, and the resulting steps feed the all-stage saturation horizons.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

namespace Nat

private def oddTotientScaledList (r i : Nat) : List Nat :=
  [7*r^(i+1),11*r^(i+1),13*r^(i+1),17*r^(i+1),19*r^(i+1)]

private def oddTotientOtherList (i : Nat) : List Nat :=
  [3^(i+2),5*3^(i+1)]

private theorem oddTotient_scaled_list_finset (r i : Nat) :
    (oddTotientScaledList r i).toFinset=oddTotientScaledBlock r i := by
  simp [oddTotientScaledList,oddTotientScaledBlock,oddTotientAuxiliaryPrimes]

private theorem oddTotient_scaled_list_nodup (r i : Nat) (hr : 2<=r) :
    (oddTotientScaledList r i).Nodup := by
  have hp : 0<r^(i+1) := pow_pos (by omega) _
  simp [oddTotientScaledList,List.nodup_cons]
  omega

private theorem oddTotient_five_block_values (i : Nat) :
    (7*5^(i+1)).totient/2=12*5^i /\
    (11*5^(i+1)).totient/2=20*5^i /\
    (13*5^(i+1)).totient/2=24*5^i /\
    (17*5^(i+1)).totient/2=32*5^i /\
    (19*5^(i+1)).totient/2=36*5^i := by
  have h7 := oddTotient_scaled_five_weight 7 i (by decide)
  have hp7 : (7 : Nat).totient=6 := by decide
  rw [hp7] at h7
  have h11 := oddTotient_scaled_five_weight 11 i (by decide)
  have hp11 : (11 : Nat).totient=10 := by decide
  rw [hp11] at h11
  have h13 := oddTotient_scaled_five_weight 13 i (by decide)
  have hp13 : (13 : Nat).totient=12 := by decide
  rw [hp13] at h13
  have h17 := oddTotient_scaled_five_weight 17 i (by decide)
  have hp17 : (17 : Nat).totient=16 := by decide
  rw [hp17] at h17
  have h19 := oddTotient_scaled_five_weight 19 i (by decide)
  have hp19 : (19 : Nat).totient=18 := by decide
  rw [hp19] at h19
  omega

private theorem oddTotient_three_block_values (i : Nat) :
    (7*3^(i+1)).totient/2=6*3^i /\
    (11*3^(i+1)).totient/2=10*3^i /\
    (13*3^(i+1)).totient/2=12*3^i /\
    (17*3^(i+1)).totient/2=16*3^i /\
    (19*3^(i+1)).totient/2=18*3^i := by
  have h7 := oddTotient_scaled_three_weight 7 i (by decide)
  have hp7 : (7 : Nat).totient=6 := by decide
  rw [hp7] at h7
  have h11 := oddTotient_scaled_three_weight 11 i (by decide)
  have hp11 : (11 : Nat).totient=10 := by decide
  rw [hp11] at h11
  have h13 := oddTotient_scaled_three_weight 13 i (by decide)
  have hp13 : (13 : Nat).totient=12 := by decide
  rw [hp13] at h13
  have h17 := oddTotient_scaled_three_weight 17 i (by decide)
  have hp17 : (17 : Nat).totient=16 := by decide
  rw [hp17] at h17
  have h19 := oddTotient_scaled_three_weight 19 i (by decide)
  have hp19 : (19 : Nat).totient=18 := by decide
  rw [hp19] at h19
  omega

theorem oddTotient_three_interval_step (T : Finset Nat) (i S : Nat)
    (hnew : forall d, Membership.mem (oddTotientScaledBlock 5 i) d ->
      Not (Membership.mem T d))
    (hcover : Finset.subsetSumInterval T (fun d => d.totient/2) 5 S)
    (hS : 12*5^i+10<=S+1) :
    Finset.subsetSumInterval (Union.union T (oddTotientScaledBlock 5 i))
      (fun d => d.totient/2) 5 (S+124*5^i) := by
  have hw := oddTotient_five_block_values i
  have hblock : Finset.subsetSumAdmissibleBlock (fun d : Nat => d.totient/2)
      5 S (oddTotientScaledList 5 i) := by
    dsimp only [oddTotientScaledList,Finset.subsetSumAdmissibleBlock]
    simp only [hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2]
    exact And.intro (by omega) (And.intro (by omega) (And.intro (by omega)
      (And.intro (by omega) (And.intro (by omega) True.intro))))
  have hnewL : forall d, Membership.mem (oddTotientScaledList 5 i) d ->
      Not (Membership.mem T d) := by
    intro d hd
    apply hnew d
    rw [<- oddTotient_scaled_list_finset 5 i]
    exact List.mem_toFinset.mpr hd
  have hsum : ((oddTotientScaledList 5 i).map (fun d : Nat => d.totient/2)).sum=
      124*5^i := by
    simp only [oddTotientScaledList,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2]
    omega
  have hcovered := Finset.subset_sum_interval_insert_block T
    (fun d : Nat => d.totient/2) 5 S (oddTotientScaledList 5 i)
    (oddTotient_scaled_list_nodup 5 i (by decide)) hnewL hcover hblock
  simpa only [oddTotient_scaled_list_finset,hsum] using hcovered

theorem oddTotient_five_interval_step (T : Finset Nat) (i S : Nat)
    (hnew : forall d, Membership.mem (oddTotientScaledBlock 3 i) d ->
      Not (Membership.mem T d))
    (hcover : Finset.subsetSumInterval T (fun d => d.totient/2) 3 S)
    (hS : 6*3^i+6<=S+1) :
    Finset.subsetSumInterval (Union.union T (oddTotientScaledBlock 3 i))
      (fun d => d.totient/2) 3 (S+62*3^i) := by
  have hw := oddTotient_three_block_values i
  have hblock : Finset.subsetSumAdmissibleBlock (fun d : Nat => d.totient/2)
      3 S (oddTotientScaledList 3 i) := by
    dsimp only [oddTotientScaledList,Finset.subsetSumAdmissibleBlock]
    simp only [hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2]
    exact And.intro (by omega) (And.intro (by omega) (And.intro (by omega)
      (And.intro (by omega) (And.intro (by omega) True.intro))))
  have hnewL : forall d, Membership.mem (oddTotientScaledList 3 i) d ->
      Not (Membership.mem T d) := by
    intro d hd
    apply hnew d
    rw [<- oddTotient_scaled_list_finset 3 i]
    exact List.mem_toFinset.mpr hd
  have hsum : ((oddTotientScaledList 3 i).map (fun d : Nat => d.totient/2)).sum=
      62*3^i := by
    simp only [oddTotientScaledList,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2]
    omega
  have hcovered := Finset.subset_sum_interval_insert_block T
    (fun d : Nat => d.totient/2) 3 S (oddTotientScaledList 3 i)
    (oddTotient_scaled_list_nodup 3 i (by decide)) hnewL hcover hblock
  simpa only [oddTotient_scaled_list_finset,hsum] using hcovered

private theorem oddTotient_other_list_finset (i : Nat) :
    (oddTotientOtherList i).toFinset=oddTotientOtherBlock i := by
  simp [oddTotientOtherList,oddTotientOtherBlock]

private theorem oddTotient_other_list_nodup (i : Nat) :
    (oddTotientOtherList i).Nodup := by
  have hp : 0<(3 : Nat)^(i+1) := pow_pos (by decide) _
  have hs : (3 : Nat)^(i+2)=3^(i+1)*3 := by
    rw [show i+2=(i+1)+1 by omega,pow_succ]
  simp [oddTotientOtherList,List.nodup_cons,hs]
  omega

private theorem oddTotient_other_block_values (i : Nat) :
    (3^(i+2) : Nat).totient/2=3*3^i /\
      (5*3^(i+1) : Nat).totient/2=4*3^i := by
  have hfirst : (3^(i+2) : Nat).totient/2=3*3^i := by
    rw [Nat.totient_prime_pow (by decide : Nat.Prime 3) (by omega : 0 < (i+2)),
      show i+2-1=i+1 by omega,show (3 : Nat)-1=2 from rfl,pow_succ]
    omega
  have hsecond := oddTotient_scaled_three_weight 5 i (by decide)
  have hphi : (5 : Nat).totient=4 := by decide
  rw [hphi] at hsecond
  exact And.intro hfirst hsecond

theorem oddTotient_other_interval_step (T : Finset Nat) (i S : Nat)
    (hnew : forall d, Membership.mem (oddTotientOtherBlock i) d -> Not (Membership.mem T d))
    (hcover : Finset.subsetSumInterval T (fun d => d.totient/2) 0 S)
    (hS : 3*3^i<=S+1) :
    Finset.subsetSumInterval (Union.union T (oddTotientOtherBlock i))
      (fun d => d.totient/2) 0 (S+7*3^i) := by
  have hw := oddTotient_other_block_values i
  have hblock : Finset.subsetSumAdmissibleBlock (fun d : Nat => d.totient/2)
      0 S (oddTotientOtherList i) := by
    dsimp only [oddTotientOtherList,Finset.subsetSumAdmissibleBlock]
    simp only [hw.1,hw.2]
    exact And.intro (by omega) (And.intro (by omega) True.intro)
  have hnewL : forall d, Membership.mem (oddTotientOtherList i) d ->
      Not (Membership.mem T d) := by
    intro d hd
    apply hnew d
    rw [<- oddTotient_other_list_finset i]
    exact List.mem_toFinset.mpr hd
  have hsum : ((oddTotientOtherList i).map (fun d : Nat => d.totient/2)).sum=7*3^i := by
    simp only [oddTotientOtherList,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      hw.1,hw.2]
    omega
  have hcovered := Finset.subset_sum_interval_insert_block T
    (fun d : Nat => d.totient/2) 0 S (oddTotientOtherList i)
    (oddTotient_other_list_nodup i) hnewL hcover hblock
  simpa only [oddTotient_other_list_finset,hsum] using hcovered


theorem oddTotient_three_coverage (j : Nat) :
    Finset.subsetSumInterval (oddTotientThreeDegrees j) (fun d => d.totient/2)
      5 (31*5^(j+1)+2) := by
  induction j with
  | zero =>
    change Finset.subsetSumInterval (Union.union oddTotientBaseThree (oddTotientScaledBlock 5 0))
      (fun d => d.totient/2) 5 (33+124*5^0)
    apply oddTotient_three_interval_step oddTotientBaseThree 0 33
    . intro d hd hold
      exact Finset.disjoint_left.mp (oddTotient_base_scaled_block_disjoint oddTotientBaseThree 5 0 (by decide) (by decide)) hold hd
    . exact oddTotient_base_three_interval
    . decide
  | succ j ih =>
    have hp : 0<(5 : Nat)^(j+1) := pow_pos (by decide) _
    have hnew : forall d, Membership.mem (oddTotientScaledBlock 5 (j+1)) d ->
        Not (Membership.mem (oddTotientThreeDegrees j) d) := by
      intro d hd hold
      exact Finset.disjoint_left.mp (oddTotient_three_next_disjoint j) hold hd
    have hh := oddTotient_three_interval_step (oddTotientThreeDegrees j) (j+1) (31*5^(j+1)+2)
      hnew ih (by omega)
    have hsum : (31*5^(j+1)+2)+124*5^(j+1)=(31*5^((j+1)+1)+2) := by
      simp only [pow_succ]
      omega
    simpa only [oddTotientThreeDegrees,hsum] using hh

theorem oddTotient_five_coverage (j : Nat) :
    Finset.subsetSumInterval (oddTotientFiveDegrees j) (fun d => d.totient/2)
      3 (31*3^(j+1)+4) := by
  induction j with
  | zero =>
    change Finset.subsetSumInterval (Union.union oddTotientBaseFive (oddTotientScaledBlock 3 0))
      (fun d => d.totient/2) 3 (35+62*3^0)
    apply oddTotient_five_interval_step oddTotientBaseFive 0 35
    . intro d hd hold
      exact Finset.disjoint_left.mp (oddTotient_base_scaled_block_disjoint oddTotientBaseFive 3 0 (by decide) (by decide)) hold hd
    . exact oddTotient_base_five_interval
    . decide
  | succ j ih =>
    have hp : 0<(3 : Nat)^(j+1) := pow_pos (by decide) _
    have hnew : forall d, Membership.mem (oddTotientScaledBlock 3 (j+1)) d ->
        Not (Membership.mem (oddTotientFiveDegrees j) d) := by
      intro d hd hold
      exact Finset.disjoint_left.mp (oddTotient_five_next_disjoint j) hold hd
    have hh := oddTotient_five_interval_step (oddTotientFiveDegrees j) (j+1) (31*3^(j+1)+4)
      hnew ih (by omega)
    have hsum : (31*3^(j+1)+4)+62*3^(j+1)=(31*3^((j+1)+1)+4) := by
      simp only [pow_succ]
      omega
    simpa only [oddTotientFiveDegrees,hsum] using hh

theorem oddTotient_other_coverage (j : Nat) :
    Finset.subsetSumInterval (oddTotientOtherDegrees j) (fun d => d.totient/2)
      0 ((7*3^(j+1)-1)/2) := by
  induction j with
  | zero =>
    change Finset.subsetSumInterval (Union.union oddTotientBaseOther (oddTotientOtherBlock 0))
      (fun d => d.totient/2) 0 (3+7*3^0)
    apply oddTotient_other_interval_step oddTotientBaseOther 0 3
    . intro d hd hold
      exact Finset.disjoint_left.mp (oddTotient_base_other_block_disjoint 0) hold hd
    . exact oddTotient_base_other_interval
    . decide
  | succ j ih =>
    have hp : 0<(3 : Nat)^(j+1) := pow_pos (by decide) _
    have hnew : forall d, Membership.mem (oddTotientOtherBlock (j+1)) d ->
        Not (Membership.mem (oddTotientOtherDegrees j) d) := by
      intro d hd hold
      exact Finset.disjoint_left.mp (oddTotient_other_next_disjoint j) hold hd
    have hh := oddTotient_other_interval_step (oddTotientOtherDegrees j) (j+1) ((7*3^(j+1)-1)/2)
      hnew ih (by omega)
    have hsum : ((7*3^(j+1)-1)/2)+7*3^(j+1)=((7*3^((j+1)+1)-1)/2) := by
      simp only [pow_succ]
      omega
    simpa only [oddTotientOtherDegrees,hsum] using hh

theorem oddTotient_stage_le_power (r j : Nat) (hr : 2<=r) :
    j+1<=r^j := by
  induction j with
  | zero => simp only [pow_zero]; omega
  | succ j ih =>
    have hh := Nat.mul_le_mul ih hr
    rw [pow_succ]
    omega

theorem oddTotient_three_base_subset (j : Nat) :
    forall d, Membership.mem oddTotientBaseThree d -> Membership.mem (oddTotientThreeDegrees j) d := by
  induction j with
  | zero =>
    intro d hd
    exact Finset.mem_union.mpr (Or.inl hd)
  | succ j ih =>
    intro d hd
    exact Finset.mem_union.mpr (Or.inl (ih d hd))

theorem oddTotient_five_base_subset (j : Nat) :
    forall d, Membership.mem oddTotientBaseFive d -> Membership.mem (oddTotientFiveDegrees j) d := by
  induction j with
  | zero =>
    intro d hd
    exact Finset.mem_union.mpr (Or.inl hd)
  | succ j ih =>
    intro d hd
    exact Finset.mem_union.mpr (Or.inl (ih d hd))

theorem oddTotient_other_base_subset (j : Nat) :
    forall d, Membership.mem oddTotientBaseOther d -> Membership.mem (oddTotientOtherDegrees j) d := by
  induction j with
  | zero =>
    intro d hd
    exact Finset.mem_union.mpr (Or.inl hd)
  | succ j ih =>
    intro d hd
    exact Finset.mem_union.mpr (Or.inl (ih d hd))

theorem oddTotient_three_realize_interval (j t : Nat)
    (hlo : 5<=t) (hhi : t+5<=(31*5^(j+1)+2)) :
    exists D : Finset Nat, Membership.mem (oddTotientThreeDegrees j).powerset D /\
      D.sum Nat.totient=2*t := by
  choose D hD using oddTotient_three_coverage j t
    (Finset.mem_range.mpr (by omega)) hlo hhi
  apply Exists.intro D
  apply And.intro hD.1
  have hdouble := oddTotient_sum_normalized_double D (by
    intro d hd
    have hdata := oddTotient_three_data d j ((Finset.mem_powerset.mp hD.1) hd)
    exact And.intro hdata.1 hdata.2.1)
  rw [hD.2] at hdouble
  exact hdouble

theorem oddTotient_five_realize_interval (j t : Nat)
    (hlo : 3<=t) (hhi : t+3<=(31*3^(j+1)+4)) :
    exists D : Finset Nat, Membership.mem (oddTotientFiveDegrees j).powerset D /\
      D.sum Nat.totient=2*t := by
  choose D hD using oddTotient_five_coverage j t
    (Finset.mem_range.mpr (by omega)) hlo hhi
  apply Exists.intro D
  apply And.intro hD.1
  have hdouble := oddTotient_sum_normalized_double D (by
    intro d hd
    have hdata := oddTotient_five_data d j ((Finset.mem_powerset.mp hD.1) hd)
    exact And.intro hdata.1 hdata.2.1)
  rw [hD.2] at hdouble
  exact hdouble

theorem oddTotient_other_realize_interval (j t : Nat)
    (hlo : 0<=t) (hhi : t+0<=((7*3^(j+1)-1)/2)) :
    exists D : Finset Nat, Membership.mem (oddTotientOtherDegrees j).powerset D /\
      D.sum Nat.totient=2*t := by
  choose D hD using oddTotient_other_coverage j t
    (Finset.mem_range.mpr (by omega)) hlo hhi
  apply Exists.intro D
  apply And.intro hD.1
  have hdouble := oddTotient_sum_normalized_double D (by
    intro d hd
    have hdata := oddTotient_other_data 7 d j (by decide) (by decide) ((Finset.mem_powerset.mp hD.1) hd)
    exact And.intro hdata.1 hdata.2.1)
  rw [hD.2] at hdouble
  exact hdouble

end Nat

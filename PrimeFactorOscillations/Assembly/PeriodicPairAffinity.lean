/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import PrimeFactorOscillations.Assembly.FiniteFieldPairAffinity

/-!
# Normalized affinity on incomplete periodic integer samples

A sample at least one period long has positive normalizers. Its affinity
is at most twice the complete-period affinity, uniformly in the origin.
No pointwise density cap is used: every remainder is bounded by its full
nonnegative period mass. This is an integer sampling theorem, not a
critical-height prime-pair mass estimate.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.PeriodicPairAffinity

def intervalMass (f : Nat -> Real) (A N : Nat) : Real :=
  (Finset.range N).sum (fun j => f (A+j))

def periodAffinity (M : Nat) (u v : Nat -> Real) : Real :=
  (1/(M : Real))*(Finset.range M).sum (fun j => Real.sqrt (u j*v j))

def intervalAffinity (u v : Nat -> Real) (A N : Nat) : Real :=
  intervalMass (fun j => Real.sqrt (u j*v j)) A N /
    Real.sqrt (intervalMass u A N*intervalMass v A N)

theorem shifted_period_mass (M A : Nat) (f : Nat -> Real) (mu : Real)
    (hperiod : forall n, f (n+M)=f n)
    (hmean : (Finset.range M).sum f=(M : Real)*mu) :
    intervalMass f A M=(M : Real)*mu := by
  have hs := Finset.sum_range_add f A M
  have ht : (Finset.range (A+M)).sum f =
      (M : Real)*mu+(Finset.range A).sum f := by
    rw [Nat.add_comm A M,Finset.sum_range_add,hmean]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Nat.add_comm] using hperiod j
  unfold intervalMass
  linarith only [hs,ht]

theorem whole_period_mass (M A q : Nat) (f : Nat -> Real) (mu : Real)
    (hperiod : forall n, f (n+M)=f n)
    (hmean : (Finset.range M).sum f=(M : Real)*mu) :
    intervalMass f A (q*M)=(q : Real)*(M : Real)*mu := by
  induction q with
  | zero => simp [intervalMass]
  | succ q ih =>
    have ht := shifted_period_mass M (A+q*M) f mu hperiod hmean
    calc
      _ = intervalMass f A (q*M)+intervalMass f (A+q*M) M := by
        unfold intervalMass
        rw [Nat.succ_mul,Finset.sum_range_add]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [Nat.add_assoc]
      _ = (q : Real)*(M : Real)*mu+(M : Real)*mu := by rw [ih,ht]
      _ = _ := by simp only [Nat.cast_add,Nat.cast_one]; ring

theorem partial_period_mass (M A r : Nat) (f : Nat -> Real) (mu : Real)
    (hf : forall n, 0<=f n) (hr : r<=M)
    (hperiod : forall n, f (n+M)=f n)
    (hmean : (Finset.range M).sum f=(M : Real)*mu) :
    And (0<=intervalMass f A r) (intervalMass f A r<=(M : Real)*mu) := by
  have hn : 0<=intervalMass f A r :=
    Finset.sum_nonneg (fun j _ => hf (A+j))
  have hs : intervalMass f A r<=intervalMass f A M := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hr)
    intro j _ _
    exact hf (A+j)
  rw [shifted_period_mass M A f mu hperiod hmean] at hs
  exact And.intro hn hs

theorem interval_mass_bounds (M A N : Nat) (hM : 0<M)
    (f : Nat -> Real) (mu : Real) (hf : forall n, 0<=f n)
    (hperiod : forall n, f (n+M)=f n)
    (hmean : (Finset.range M).sum f=(M : Real)*mu) :
    And
      (((N/M : Nat) : Real)*(M : Real)*mu<=intervalMass f A N)
      (intervalMass f A N<=(((N/M : Nat) : Real)+1)*(M : Real)*mu) := by
  let q := N/M
  let r := N%M
  have hr : r<=M := (Nat.mod_lt N hM).le
  have hN : N=q*M+r := by
    dsimp only [q,r]
    simpa only [Nat.add_comm,Nat.mul_comm] using (Nat.mod_add_div N M).symm
  have hb := whole_period_mass M A q f mu hperiod hmean
  have ht := partial_period_mass M (A+q*M) r f mu hf hr hperiod hmean
  have he : intervalMass f A N=
      intervalMass f A (q*M)+intervalMass f (A+q*M) r := by
    unfold intervalMass
    rw [hN,Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_assoc]
  rw [he,hb]
  change And ((q : Real)*(M : Real)*mu<=_)
    (_<=((q : Real)+1)*(M : Real)*mu)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem interval_mass_positive (M A N : Nat) (hM : 0<M) (hMN : M<=N)
    (f : Nat -> Real) (hf : forall n, 0<=f n)
    (hperiod : forall n, f (n+M)=f n)
    (hmean : (Finset.range M).sum f=(M : Real)) :
    0 < intervalMass f A N := by
  have hb := (interval_mass_bounds M A N hM f 1 hf hperiod (by simpa using hmean)).1
  have hq : 0<N/M := Nat.div_pos hMN hM
  have hqR : 0<((N/M : Nat) : Real) := by exact_mod_cast hq
  have hMR : 0<(M : Real) := by exact_mod_cast hM
  have hp := mul_pos hqR hMR
  simp only [mul_one] at hb
  exact lt_of_lt_of_le hp hb

theorem period_affinity_nonneg (M : Nat) (u v : Nat -> Real) :
    0<=periodAffinity M u v := by
  apply mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg M))
  exact Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)

theorem interval_affinity_le_twice (M A N : Nat) (hM : 0<M) (hMN : M<=N)
    (u v : Nat -> Real) (hu : forall n, 0<=u n) (hv : forall n, 0<=v n)
    (hpu : forall n, u (n+M)=u n) (hpv : forall n, v (n+M)=v n)
    (hmu : (Finset.range M).sum u=(M : Real))
    (hmv : (Finset.range M).sum v=(M : Real)) :
    And (0 < intervalMass u A N)
      (And (0 < intervalMass v A N)
        (intervalAffinity u v A N<=2*periodAffinity M u v)) := by
  let H := periodAffinity M u v
  let q := ((N/M : Nat) : Real)
  let m := (M : Real)
  let SU := intervalMass u A N
  let SV := intervalMass v A N
  let D := Real.sqrt (SU*SV)
  have hSU := interval_mass_positive M A N hM hMN u hu hpu hmu
  have hSV := interval_mass_positive M A N hM hMN v hv hpv hmv
  have hm : 0<m := by dsimp only [m]; exact_mod_cast hM
  have hqN : 0<N/M := Nat.div_pos hMN hM
  have hq : 1<=q := by dsimp only [q]; exact_mod_cast (show 1<=N/M by omega)
  have hqm : 0<q*m := mul_pos (by linarith only [hq]) hm
  have hH : 0<=H := period_affinity_nonneg M u v
  have hU := (interval_mass_bounds M A N hM u 1 hu hpu (by simpa using hmu)).1
  have hV := (interval_mass_bounds M A N hM v 1 hv hpv (by simpa using hmv)).1
  change q*m*1<=SU at hU
  change q*m*1<=SV at hV
  simp only [mul_one] at hU hV
  have hprod : (q*m)^2<=SU*SV := by
    have hh := mul_le_mul hU hV hqm.le (le_trans hqm.le hU)
    nlinarith only [hh]
  have hD : q*m<=D := by
    have ht := Real.sqrt_le_sqrt hprod
    rw [Real.sqrt_sq hqm.le] at ht
    exact ht
  have hDpos : 0<D := lt_of_lt_of_le hqm hD
  have hp (n : Nat) :
      Real.sqrt (u (n+M)*v (n+M))=Real.sqrt (u n*v n) := by rw [hpu,hpv]
  have hs : (Finset.range M).sum (fun j => Real.sqrt (u j*v j))=m*H := by
    dsimp only [m,H,periodAffinity]
    field_simp [ne_of_gt hm]
  have hc := (interval_mass_bounds M A N hM
    (fun j => Real.sqrt (u j*v j)) H (fun j => Real.sqrt_nonneg _) hp hs).2
  change intervalMass (fun j => Real.sqrt (u j*v j)) A N<=(q+1)*m*H at hc
  have hnum : intervalMass (fun j => Real.sqrt (u j*v j)) A N<=2*H*D := by
    calc
      _ <= (q+1)*m*H := hc
      _ <= 2*q*m*H := by
        have ht := mul_nonneg (sub_nonneg.mpr hq) (mul_nonneg hm.le hH)
        nlinarith only [ht]
      _ <= 2*H*D := by
        have ht : (2*H)*(q*m)<=(2*H)*D :=
          mul_le_mul_of_nonneg_left hD (mul_nonneg (by norm_num) hH)
        nlinarith only [ht]
  refine And.intro hSU (And.intro hSV ?_)
  change intervalMass (fun j => Real.sqrt (u j*v j)) A N/D<=2*H
  calc
    _ <= (2*H*D)/D := div_le_div_of_nonneg_right hnum hDpos.le
    _ = _ := by field_simp [ne_of_gt hDpos]

end PrimeFactorOscillations.PeriodicPairAffinity

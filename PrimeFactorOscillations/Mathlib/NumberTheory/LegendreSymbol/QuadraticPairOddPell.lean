/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairSquareTransport

/-!
# Odd Pell transports and their exact endpoint parameters

One coupled recurrence provides the two square multipliers for every odd
Chebyshev index. Its quadratic invariant is valid in every commutative ring.
Over a field with two nonzero, the trace input (z-1)^2/(2*z) identifies
both endpoint fibers exactly, without excluding indices divisible by the
characteristic. These algebraic inputs do not assert a finite-field mass
formula or positive mass on an incomplete integer window.
-/
set_option autoImplicit false
set_option Elab.async false

namespace FiniteField
variable {R : Type*} [CommRing R]

def oddPellPair (x : R) : Nat -> Prod R R
  | 0 => (1, 1)
  | k + 1 =>
      let v := oddPellPair x k
      ((x+1)*v.1+(x+2)*v.2, x*v.1+(x+1)*v.2)

def oddPellMap (x : R) (k : Nat) : R := x*(oddPellPair x k).1^2

theorem oddPell_pair_invariant (x : R) (k : Nat) :
    (x+2)*(oddPellPair x k).2^2-x*(oddPellPair x k).1^2=2 := by
  induction k with
  | zero =>
      dsimp [oddPellPair]
      ring
  | succ k ih =>
      change (x+2)*(x*(oddPellPair x k).1+(x+1)*(oddPellPair x k).2)^2-
        x*((x+1)*(oddPellPair x k).1+(x+2)*(oddPellPair x k).2)^2=2
      calc
        _ = (x+2)*(oddPellPair x k).2^2-x*(oddPellPair x k).1^2 := by ring
        _ = 2 := ih

theorem oddPell_shifted_square (x : R) (k : Nat) :
    oddPellMap x k+2=(x+2)*(oddPellPair x k).2^2 := by
  unfold oddPellMap
  calc
    _ = x*(oddPellPair x k).1^2+
        ((x+2)*(oddPellPair x k).2^2-x*(oddPellPair x k).1^2) := by
          rw [oddPell_pair_invariant]
    _ = _ := by ring

variable {K : Type*} [Field K]

theorem oddPell_map_reachable (x : K) (k : Nat) :
    squarePairReach x (oddPellMap x k) 2 := by
  apply Exists.intro (oddPellPair x k).1
  apply Exists.intro (oddPellPair x k).2
  exact And.intro rfl (oddPell_shifted_square x k)

theorem oddPell_pair_trace (z : K) (hz : Not (z=0))
    (htwo : Not ((2 : K)=0)) (k : Nat) :
    let x := (z-1)^2/(2*z)
    (oddPellPair x k).1*(z-1)*z^k=z^(2*k+1)-1 /\
      (oddPellPair x k).2*(z+1)*z^k=z^(2*k+1)+1 := by
  let x : K := (z-1)^2/(2*z)
  change (oddPellPair x k).1*(z-1)*z^k=z^(2*k+1)-1 /\
    (oddPellPair x k).2*(z+1)*z^k=z^(2*k+1)+1
  have hx : 2*z*x=(z-1)^2 := by
    dsimp [x]
    field_simp [htwo,hz]
  have ht : 2*z*(x+1)=z^2+1 := by
    calc
      _ = 2*z*x+2*z := by ring
      _ = _ := by rw [hx]; ring
  have hp : 2*z*(x+2)=(z+1)^2 := by
    calc
      _ = 2*z*x+4*z := by ring
      _ = _ := by rw [hx]; ring
  have cancel_two (a b : K) (he : 2*a=2*b) : a=b := by
    have he0 : 2*(a-b)=0 := by rw [mul_sub,he,sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he0).resolve_left htwo)
  induction k with
  | zero => simp [oddPellPair]
  | succ k ih =>
      have he : 2*(k+1)+1=(2*k+1)+2 := by omega
      apply And.intro
      . apply cancel_two
        change 2*(((x+1)*(oddPellPair x k).1+
          (x+2)*(oddPellPair x k).2)*(z-1)*z^(k+1))=_
        calc
          _ = (2*z*(x+1))*((oddPellPair x k).1*(z-1)*z^k)+
              (2*z*(x+2))*((oddPellPair x k).2*(z-1)*z^k) := by
                rw [pow_succ]
                ring
          _ = (z^2+1)*((oddPellPair x k).1*(z-1)*z^k)+
              (z+1)^2*((oddPellPair x k).2*(z-1)*z^k) := by rw [ht,hp]
          _ = (z^2+1)*((oddPellPair x k).1*(z-1)*z^k)+
              (z^2-1)*((oddPellPair x k).2*(z+1)*z^k) := by ring
          _ = (z^2+1)*(z^(2*k+1)-1)+(z^2-1)*(z^(2*k+1)+1) := by
                rw [ih.1,ih.2]
          _ = _ := by rw [he,pow_add]; ring
      . apply cancel_two
        change 2*((x*(oddPellPair x k).1+
          (x+1)*(oddPellPair x k).2)*(z+1)*z^(k+1))=_
        calc
          _ = (2*z*x)*((oddPellPair x k).1*(z+1)*z^k)+
              (2*z*(x+1))*((oddPellPair x k).2*(z+1)*z^k) := by
                rw [pow_succ]
                ring
          _ = (z-1)^2*((oddPellPair x k).1*(z+1)*z^k)+
              (z^2+1)*((oddPellPair x k).2*(z+1)*z^k) := by rw [hx,ht]
          _ = (z^2-1)*((oddPellPair x k).1*(z-1)*z^k)+
              (z^2+1)*((oddPellPair x k).2*(z+1)*z^k) := by ring
          _ = (z^2-1)*(z^(2*k+1)-1)+(z^2+1)*(z^(2*k+1)+1) := by
                rw [ih.1,ih.2]
          _ = _ := by rw [he,pow_add]; ring

theorem oddPell_map_trace_scaled (z : K) (hz : Not (z=0))
    (htwo : Not ((2 : K)=0)) (k : Nat) :
    2*z^(2*k+1)*oddPellMap ((z-1)^2/(2*z)) k=(z^(2*k+1)-1)^2 := by
  let x : K := (z-1)^2/(2*z)
  change 2*z^(2*k+1)*oddPellMap x k=_
  have hx : 2*z*x=(z-1)^2 := by
    dsimp [x]
    field_simp [htwo,hz]
  have hm : z^(2*k+1)=(z^k)^2*z := by
    rw [show 2*k+1=k*2+1 by omega,pow_add,pow_mul,pow_one]
  have ha := (oddPell_pair_trace z hz htwo k).1
  change (oddPellPair x k).1*(z-1)*z^k=z^(2*k+1)-1 at ha
  calc
    _ = (2*z*x)*((oddPellPair x k).1*z^k)^2 := by
      rw [hm]
      unfold oddPellMap
      ring
    _ = ((oddPellPair x k).1*(z-1)*z^k)^2 := by rw [hx]; ring
    _ = _ := by rw [ha]

theorem oddPell_map_shift_trace_scaled (z : K) (hz : Not (z=0))
    (htwo : Not ((2 : K)=0)) (k : Nat) :
    2*z^(2*k+1)*(oddPellMap ((z-1)^2/(2*z)) k+2)=(z^(2*k+1)+1)^2 := by
  calc
    _ = 2*z^(2*k+1)*oddPellMap ((z-1)^2/(2*z)) k+4*z^(2*k+1) := by ring
    _ = (z^(2*k+1)-1)^2+4*z^(2*k+1) := by
      rw [oddPell_map_trace_scaled z hz htwo k]
    _ = _ := by ring

theorem oddPell_map_eq_zero_iff (z : K) (hz : Not (z=0))
    (htwo : Not ((2 : K)=0)) (k : Nat) :
    oddPellMap ((z-1)^2/(2*z)) k=0 <-> z^(2*k+1)=1 := by
  have hscale : Not (2*z^(2*k+1)=0) := mul_ne_zero htwo (pow_ne_zero _ hz)
  constructor
  . intro he
    have hs : (z^(2*k+1)-1)^2=0 := by
      rw [<- oddPell_map_trace_scaled z hz htwo k,he,mul_zero]
    have hp : (z^(2*k+1)-1)*(z^(2*k+1)-1)=0 := by simpa only [pow_two] using hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).elim id id)
  . intro he
    have hs : (z^(2*k+1)-1)^2=0 := by simp only [he,sub_self,zero_pow (by decide : Not (2=0))]
    have hp := (oddPell_map_trace_scaled z hz htwo k).trans hs
    exact (mul_eq_zero.mp hp).resolve_left hscale

theorem oddPell_map_eq_neg_two_iff (z : K) (hz : Not (z=0))
    (htwo : Not ((2 : K)=0)) (k : Nat) :
    oddPellMap ((z-1)^2/(2*z)) k=-2 <-> z^(2*k+1)=-1 := by
  have hscale : Not (2*z^(2*k+1)=0) := mul_ne_zero htwo (pow_ne_zero _ hz)
  constructor
  . intro he
    have hs : (z^(2*k+1)+1)^2=0 := by
      rw [<- oddPell_map_shift_trace_scaled z hz htwo k,he,neg_add_cancel,mul_zero]
    have hp : (z^(2*k+1)+1)*(z^(2*k+1)+1)=0 := by simpa only [pow_two] using hs
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hp).elim id id)
  . intro he
    have hs : (z^(2*k+1)+1)^2=0 := by
      simp only [he,neg_add_cancel,zero_pow (by decide : Not (2=0))]
    have hp := (oddPell_map_shift_trace_scaled z hz htwo k).trans hs
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hp).resolve_left hscale)

end FiniteField

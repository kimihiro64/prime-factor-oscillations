/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A cubic lift of integer pairs at distance two

The classical cubic Chebyshev identity gives simultaneous square
multipliers at the two endpoints. Its iterates are unbounded composite
pairs. Seeds congruent to two modulo three have pairwise coprime new
factor blocks. These identities will be consumed by the actual
finite-field pair-count law, with every new prime mask retained.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Nat.TwinCubic

def step (n : Nat) : Nat := n*(2*n+3)^2
def endpointProduct (n : Nat) : Nat := n*(n+2)
def block (n : Nat) : Nat := (2*n+1)*(2*n+3)

def orbit (seed : Nat) : Nat -> Nat
  | 0 => seed
  | k+1 => step (orbit seed k)

def leftScale (seed : Nat) : Nat -> Nat
  | 0 => 1
  | k+1 => leftScale seed k*(2*orbit seed k+3)

def rightScale (seed : Nat) : Nat -> Nat
  | 0 => 1
  | k+1 => rightScale seed k*(2*orbit seed k+1)

theorem step_add_two (n : Nat) :
    step n+2=(n+2)*(2*n+1)^2 := by unfold step; ring

theorem step_chebyshev (n : Nat) :
    step n+1+3*(n+1)=4*(n+1)^3 := by unfold step; ring

theorem block_eq (n : Nat) :
    block n=3+4*endpointProduct n := by unfold block endpointProduct; ring

theorem endpointProduct_step (n : Nat) :
    endpointProduct (step n)=endpointProduct n*(block n)^2 := by
  unfold endpointProduct
  rw [step_add_two]
  unfold step block
  ring

theorem orbit_eq_left_square (seed k : Nat) :
    orbit seed k=seed*(leftScale seed k)^2 := by
  induction k with
  | zero => simp [orbit,leftScale]
  | succ k ih =>
    simp only [orbit,leftScale,step]
    rw [ih]
    ring

theorem orbit_add_two_eq_right_square (seed k : Nat) :
    orbit seed k+2=(seed+2)*(rightScale seed k)^2 := by
  induction k with
  | zero => simp [orbit,rightScale]
  | succ k ih =>
    simp only [orbit,rightScale]
    rw [step_add_two,ih]
    ring

theorem step_pos (n : Nat) (hn : 0<n) : 0<step n := by
  unfold step
  positivity

theorem orbit_pos (seed : Nat) (hs : 0<seed) (k : Nat) : 0<orbit seed k := by
  induction k with
  | zero => exact hs
  | succ k ih => exact step_pos _ ih

theorem lt_step (n : Nat) (hn : 0<n) : n<step n := by
  have hu : 2<=2*n+3 := by omega
  have hs : 2<=(2*n+3)^2 := by nlinarith only [hu]
  have hm := Nat.mul_le_mul_left n hs
  unfold step
  nlinarith only [hn,hm]

theorem orbit_strictMono (seed : Nat) (hs : 0<seed) : StrictMono (orbit seed) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact lt_step _ (orbit_pos seed hs k)

theorem seed_add_le_orbit (seed : Nat) (hs : 0<seed) (k : Nat) :
    seed+k<=orbit seed k := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
    have ht := lt_step _ (orbit_pos seed hs k)
    change seed+(k+1)<=step (orbit seed k)
    omega

private theorem not_prime_mul_square (a b : Nat) (ha : 0<a) (hb : 1<b) :
    Not (Nat.Prime (a*b^2)) := by
  have hd : Dvd.dvd b (a*b^2) := Exists.intro (a*b) (by ring)
  have hm : b^2<=a*b^2 := by
    simpa only [one_mul] using Nat.mul_le_mul_right (b^2) (show 1<=a from ha)
  have ht : b<a*b^2 := lt_of_lt_of_le (by nlinarith only [hb]) hm
  intro hp
  rcases (Nat.dvd_prime hp).mp hd with he | he
  . omega
  . omega

theorem step_composite_pair (n : Nat) (hn : 0<n) :
    Not (Nat.Prime (step n)) /\ Not (Nat.Prime (step n+2)) := by
  apply And.intro
  . exact not_prime_mul_square n (2*n+3) hn (by omega)
  . rw [step_add_two]
    exact not_prime_mul_square (n+2) (2*n+1) (by omega) (by omega)

theorem exists_large_composite_pair (seed : Nat) (hs : 0<seed) (X : Nat) :
    exists k : Nat, X<orbit seed (k+1) /\
      Not (Nat.Prime (orbit seed (k+1))) /\
      Not (Nat.Prime (orbit seed (k+1)+2)) := by
  have hl := seed_add_le_orbit seed hs (X+1)
  have hc := step_composite_pair (orbit seed X) (orbit_pos seed hs X)
  exact Exists.intro X (And.intro (by omega) hc)

theorem step_mod_three (n : Nat) (hn : n%3=2) : step n%3=2 := by
  simp [step,Nat.mul_mod,Nat.add_mod,Nat.pow_mod,hn]

theorem orbit_mod_three (seed : Nat) (hs : seed%3=2) (k : Nat) :
    orbit seed k%3=2 := by
  induction k with
  | zero => exact hs
  | succ k ih => exact step_mod_three _ ih

theorem orbit_mod_six (seed : Nat) (hs : seed%6=5) (k : Nat) :
    orbit seed k%6=5 := by
  induction k with
  | zero => exact hs
  | succ k ih => simpa [orbit,step,Nat.mul_mod,Nat.add_mod,Nat.pow_mod,ih]

theorem affine_factors_coprime (n : Nat) : Nat.Coprime (2*n+1) (2*n+3) := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  rw [show 2*n+3=2+(2*n+1)*1 from by ring,Nat.gcd_add_mul_left_right,
    Nat.gcd_comm,Nat.gcd_rec]
  have hm : (2*n+1)%2=1 := by omega
  rw [hm]
  norm_num

theorem block_coprime_endpointProduct (n : Nat) (hn : n%3=2) :
    Nat.Coprime (block n) (endpointProduct n) := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  rw [Nat.gcd_comm,block_eq,Nat.gcd_add_mul_right_right,Nat.gcd_comm,Nat.gcd_rec]
  have hm : endpointProduct n%3=2 := by
    simp [endpointProduct,Nat.mul_mod,Nat.add_mod,hn]
  rw [hm]
  norm_num

theorem endpointProduct_dvd_next (n : Nat) :
    Dvd.dvd (endpointProduct n) (endpointProduct (step n)) := by
  rw [endpointProduct_step]
  exact dvd_mul_right _ _

theorem endpointProduct_orbit_dvd (seed i j : Nat) (hij : i<=j) :
    Dvd.dvd (endpointProduct (orbit seed i)) (endpointProduct (orbit seed j)) := by
  induction j generalizing i with
  | zero =>
    have hi : i=0 := by omega
    subst i
    exact dvd_rfl
  | succ j ih =>
    by_cases hi : i=j+1
    . subst i
      exact dvd_rfl
    . exact dvd_trans (ih i (by omega)) (endpointProduct_dvd_next (orbit seed j))

theorem block_dvd_next (n : Nat) :
    Dvd.dvd (block n) (endpointProduct (step n)) := by
  rw [endpointProduct_step]
  exact Exists.intro (endpointProduct n*block n) (by ring)

theorem earlier_block_dvd (seed i j : Nat) (hij : i<j) :
    Dvd.dvd (block (orbit seed i)) (endpointProduct (orbit seed j)) :=
  dvd_trans (block_dvd_next (orbit seed i))
    (endpointProduct_orbit_dvd seed (i+1) j hij)

theorem blocks_coprime_of_lt (seed : Nat) (hs : seed%3=2) (i j : Nat) (hij : i<j) :
    Nat.Coprime (block (orbit seed i)) (block (orbit seed j)) := by
  have hc := block_coprime_endpointProduct (orbit seed j) (orbit_mod_three seed hs j)
  exact (Nat.Coprime.of_dvd_right (earlier_block_dvd seed i j hij) hc).symm

theorem blocks_pairwise_coprime (seed : Nat) (hs : seed%3=2) :
    Pairwise (fun i j : Nat => Nat.Coprime (block (orbit seed i)) (block (orbit seed j))) := by
  intro i j hne
  rcases lt_or_gt_of_ne hne with hij | hji
  . exact blocks_coprime_of_lt seed hs i j hij
  . exact (blocks_coprime_of_lt seed hs j i hji).symm

theorem new_prime_divisor (n p : Nat) (hn : n%3=2) (hp : Nat.Prime p)
    (hd : Dvd.dvd p (block n)) : Not (Dvd.dvd p (endpointProduct n)) := by
  intro he
  have hg := Nat.dvd_gcd hd he
  have hc := Nat.coprime_iff_gcd_eq_one.mp (block_coprime_endpointProduct n hn)
  rw [hc] at hg
  exact hp.not_dvd_one hg

end Nat.TwinCubic

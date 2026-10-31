/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairCubicRigidity
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairCubicSurvival

/-!
# Uniform survival under every compatible low-degree polynomial sequence

At the normalized shift two, each compatible polynomial is the identity
or the cubic lift. Every finite composition is therefore a cubic iterate.
The established half-scale reserve applies to the entire degree class.
The observable is the actual trace-free two-class law, not a raw count.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem cubicPair_map_dichotomy (hF : Not (ringChar F=2))
    (hq : 5<=(Fintype.card F : Int)) (a b d e : F)
    (hr : forall x : F, squarePairReach x (a*x^3+b*x^2+d*x+e) 2) :
    (fun x : F => a*x^3+b*x^2+d*x+e)=id \/
      (fun x : F => a*x^3+b*x^2+d*x+e)=cubicPairLift := by
  have htwo := two_ne_zero_of_odd hF
  have ht := cubic_squarePairReach_rigidity hF hq a b d e 2 htwo hr
  have he := ht.1
  rcases ht.2 with hi | hc
  . apply Or.inl
    funext x
    simp only [hi.1,hi.2.1,hi.2.2,he,zero_mul,zero_add,one_mul,add_zero,id_eq]
  . apply Or.inr
    have ha : a=4 := by
      have hz : (2 : F)^2*(a-4)=0 := by
        calc
          _ = a*2^2-16 := by ring
          _ = 0 := sub_eq_zero.mpr hc.1
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 htwo))
    have hb : b=12 := by
      have hz : (2 : F)*(b-12)=0 := by
        calc
          _ = b*2-24 := by ring
          _ = 0 := sub_eq_zero.mpr hc.2.1
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left htwo)
    funext x
    rw [ha,hb,hc.2.2,he]
    unfold cubicPairLift
    ring

def polynomialPairWalk (f : Nat -> F -> F) : Nat -> F -> F
  | 0, x => x
  | n+1, x => f n (polynomialPairWalk f n x)

omit [Fintype F] [DecidableEq F] in
theorem polynomialPairWalk_is_cubic_iterate (f : Nat -> F -> F)
    (hf : forall i : Nat, f i=id \/ f i=cubicPairLift) (n : Nat) :
    exists k : Nat, k<=n /\ polynomialPairWalk f n=(cubicPairLift^[k]) := by
  induction n with
  | zero => exact Exists.intro 0 (And.intro (Nat.le_refl 0) rfl)
  | succ n ih =>
    let k : Nat := Classical.choose ih
    have hk := Classical.choose_spec ih
    rcases hf n with hi | hc
    . refine Exists.intro k (And.intro (Nat.le_succ_of_le hk.1) ?_)
      funext x
      change f n (polynomialPairWalk f n x)=(cubicPairLift^[k]) x
      rw [hi,hk.2]
      rfl
    . refine Exists.intro (k+1) (And.intro (Nat.succ_le_succ hk.1) ?_)
      funext x
      change f n (polynomialPairWalk f n x)=(cubicPairLift^[k+1]) x
      rw [hc,hk.2]
      exact (Function.iterate_succ_apply' cubicPairLift k x).symm

theorem low_degree_square_transport_survival (hF : Not (ringChar F=2))
    (hq : 5<=(Fintype.card F : Real)) (a b d e : Nat -> F)
    (hr : forall i : Nat, forall x : F,
      squarePairReach x (a i*x^3+b i*x^2+d i*x+e i) 2) (n : Nat) :
    ((Fintype.card F : Real)-3)/(2*(Fintype.card F : Real)) <=
      (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F =>
        traceFreePairWeight
          (polynomialPairWalk (fun i x => a i*x^3+b i*x^2+d i*x+e i) n c) 2) := by
  have hqi : 5<=(Fintype.card F : Int) := by exact_mod_cast hq
  let f : Nat -> F -> F := fun i x => a i*x^3+b i*x^2+d i*x+e i
  have hf : forall i : Nat, f i=id \/ f i=cubicPairLift :=
    fun i => cubicPair_map_dichotomy hF hqi (a i) (b i) (d i) (e i) (hr i)
  have ht := polynomialPairWalk_is_cubic_iterate f hf n
  let k : Nat := Classical.choose ht
  have hk := Classical.choose_spec ht
  change ((Fintype.card F : Real)-3)/(2*(Fintype.card F : Real)) <=
    (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F =>
      traceFreePairWeight (polynomialPairWalk f n c) 2)
  rw [hk.2]
  exact traceFreePairWeight_cubic_iterate_mean_lower hF hq k

end FiniteField

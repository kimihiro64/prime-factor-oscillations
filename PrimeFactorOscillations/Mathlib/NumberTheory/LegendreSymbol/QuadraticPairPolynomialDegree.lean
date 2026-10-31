/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Algebra.Field.FieldFunctionPolynomial
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairSquareExtremal

/-!
# Linear polynomial complexity of optimal square-transport erasure

Equality at the sharp core mass forces every noncore image to an endpoint.
The polynomial P*(P+h) must therefore have at least three quarters of the
field as roots. The lower degree bound and an interpolated attaining map
give an attained minimum degree of linear growth in the field cardinal.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
open _root_.Polynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem square_transport_minimum_profile_iff (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 5<=(Fintype.card F : Real))
    (Phi : F -> F) (hPhi : forall c : F, squarePairReach c (Phi c) h) :
    ((1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => traceFreePairWeight (Phi c) h)=
        ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
          (4*(Fintype.card F : Real))) <->
      (forall c : F, traceFreePairWeight (Phi c) h=
        if squarePairCore c h then (1 : Real) else 0) := by
  constructor
  . intro hmean
    have hpoint (c : F) : (if squarePairCore c h then (1 : Real) else 0)<=
        traceFreePairWeight (Phi c) h := by
      by_cases hc : squarePairCore c h
      . rw [ite_eq_left hc,traceFreePairWeight_square_core c (Phi c) h hh hq hc (hPhi c)]
      . rw [ite_eq_right hc]
        exact traceFreePairWeight_nonneg_all (Phi c) h hh hq
    have hq0 : Not ((Fintype.card F : Real)=0) := ne_of_gt (by linarith only [hq])
    have hscale : Not (1/(Fintype.card F : Real)=0) := div_ne_zero one_ne_zero hq0
    have hraw :
        (Finset.univ.sum fun c : F => traceFreePairWeight (Phi c) h)=
          Finset.univ.sum (fun c : F => if squarePairCore c h then (1 : Real) else 0) := by
      have hz : (1/(Fintype.card F : Real))*
          ((Finset.univ.sum fun c : F => traceFreePairWeight (Phi c) h)-
            (Finset.univ.sum fun c : F => if squarePairCore c h then (1 : Real) else 0))=0 := by
        rw [mul_sub,hmean,squarePairCore_mass hF h hh hq,sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hscale)
    have hzero :
        (Finset.univ.sum fun c : F =>
          traceFreePairWeight (Phi c) h-(if squarePairCore c h then (1 : Real) else 0))=0 := by
      rw [Finset.sum_sub_distrib,hraw,sub_self]
    intro c
    have hle := Finset.single_le_sum
      (fun x (_ : Membership.mem (Finset.univ : Finset F) x) => sub_nonneg.mpr (hpoint x))
      (Finset.mem_univ c)
    rw [hzero] at hle
    exact sub_eq_zero.mp (le_antisymm hle (sub_nonneg.mpr (hpoint c)))
  . intro hprofile
    simp_rw [hprofile]
    exact squarePairCore_mass hF h hh hq

private theorem zero_weight_endpoints (h y : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) (hy : traceFreePairWeight y h=0) :
    y=0 \/ y= -h := by
  by_cases hz : y=0
  . exact Or.inl hz
  . by_cases hn : y= -h
    . exact Or.inr hn
    . have hp : Not (y+h=0) := fun he => hn (eq_neg_of_add_eq_zero_left he)
      have hb := (traceFreePairWeight_good_bounds y h hz hp hh hq).1
      rw [hy] at hb
      norm_num at hb

theorem square_transport_minimum_iff_endpoints (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 5<=(Fintype.card F : Real))
    (Phi : F -> F) (hPhi : forall c : F, squarePairReach c (Phi c) h) :
    ((1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => traceFreePairWeight (Phi c) h)=
        ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
          (4*(Fintype.card F : Real))) <->
      (forall c : F, Not (squarePairCore c h) -> Phi c=0 \/ Phi c= -h) := by
  rw [square_transport_minimum_profile_iff hF h hh hq Phi hPhi]
  constructor
  . intro hp c hc
    have hz : traceFreePairWeight (Phi c) h=0 := by
      rw [hp c,ite_eq_right hc]
    exact zero_weight_endpoints h (Phi c) hh hq hz
  . intro hp c
    by_cases hc : squarePairCore c h
    . rw [ite_eq_left hc]
      exact traceFreePairWeight_square_core c (Phi c) h hh hq hc (hPhi c)
    . rw [ite_eq_right hc]
      rcases hp c hc with hz | hn
      . simp only [hz,traceFreePairWeight_zero]
      . simp only [hn,traceFreePairWeight_neg_shift]

def SquareTransportMinimizer (h : F) (P : Polynomial F) : Prop :=
  (forall c : F, squarePairReach c (P.eval c) h) /\
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => traceFreePairWeight (P.eval c) h)=
        ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
          (4*(Fintype.card F : Real))

theorem square_transport_extremizer_degree_lower (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 5<=(Fintype.card F : Real))
    (P : Polynomial F) (hmin : SquareTransportMinimizer h P) :
    3*(Fintype.card F : Int)+(quadraticChar F) (-1)<=8*(P.natDegree : Int) := by
  have hend := (square_transport_minimum_iff_endpoints hF h hh hq
    (fun c : F => P.eval c) hmin.1).mp hmin.2
  have hP0 : P.eval 0=0 := by
    have ht := (Classical.choose_spec (Classical.choose_spec (hmin.1 0))).1
    simpa only [zero_mul] using ht
  have hPh : P.eval (-h)= -h := by
    have ht := (Classical.choose_spec (Classical.choose_spec (hmin.1 (-h)))).2
    apply eq_neg_of_add_eq_zero_left
    simpa only [neg_add_cancel,zero_mul] using ht
  have hP : Not (P=0) := by
    intro hz
    rw [hz,eval_zero] at hPh
    exact hh (neg_eq_zero.mp hPh.symm)
  have hS : Not (P+C h=0) := by
    intro hz
    have ht := congrArg (fun A : Polynomial F => A.eval 0) hz
    rw [eval_add,eval_C,hP0,zero_add,eval_zero] at ht
    exact hh ht
  let Q : Polynomial F := P*(P+C h)
  let core : Finset F := Finset.univ.filter (fun c : F => squarePairCore c h)
  let zeros : Finset F := Finset.univ.filter (fun c : F => Q.eval c=0)
  have hQ : Not (Q=0) := mul_ne_zero hP hS
  have hQeval (c : F) : Q.eval c=P.eval c*(P.eval c+h) := by
    simp only [Q,eval_mul,eval_add,eval_C]
  have hcover : (Finset.univ : Finset F)<=Union.union core zeros := by
    intro c _
    by_cases hc : squarePairCore c h
    . exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        (And.intro (Finset.mem_univ c) hc)))
    . have hz : Q.eval c=0 := by
        rw [hQeval]
        rcases hend c hc with h0 | hneg
        . rw [h0,zero_mul]
        . rw [hneg,neg_add_cancel,mul_zero]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        (And.intro (Finset.mem_univ c) hz)))
  have hZ : zeros.card<=Q.natDegree := card_eval_zero_le_natDegree Q hQ
  have hSdegree : (P+C h).natDegree<=P.natDegree := by
    simpa only [natDegree_C,max_eq_left (Nat.zero_le P.natDegree)] using
      natDegree_add_le P (C h)
  have hQdegree : Q.natDegree<=2*P.natDegree := by
    change (P*(P+C h)).natDegree<=2*P.natDegree
    rw [natDegree_mul hP hS]
    calc
      _ <= P.natDegree+P.natDegree := Nat.add_le_add_left hSdegree P.natDegree
      _ = 2*P.natDegree := (two_mul P.natDegree).symm
  have hc : Fintype.card F<=core.card+2*P.natDegree := by
    calc
      _ = (Finset.univ : Finset F).card := (Finset.card_univ).symm
      _ <= (Union.union core zeros).card := Finset.card_le_card hcover
      _ <= core.card+zeros.card := Finset.card_union_le core zeros
      _ <= core.card+2*P.natDegree := Nat.add_le_add_left (hZ.trans hQdegree) core.card
  have hs := sum_squarePairCore_indicator hF h hh
  have hcore :
      (Finset.univ.sum fun c : F => if squarePairCore c h then (1 : Int) else 0)=
        (core.card : Int) := by
    rw [<- Finset.sum_filter]
    simp only [core,Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [hcore] at hs
  have hci : (Fintype.card F : Int)<=(core.card : Int)+2*(P.natDegree : Int) := by
    exact_mod_cast hc
  linarith only [hci,hs]

theorem square_transport_extremizer_polynomial_exists (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 5<=(Fintype.card F : Real)) :
    exists P : Polynomial F, P.natDegree<=Fintype.card F-1 /\
      SquareTransportMinimizer h P := by
  let P : Polynomial F := fieldFunctionPolynomial (fun c : F => squarePairCollapse c h)
  have hqn : 5<=Fintype.card F := by exact_mod_cast hq
  have h2 : 2<=Fintype.card F := le_trans (by decide : 2<=5) hqn
  have he (c : F) : P.eval c=squarePairCollapse c h :=
    fieldFunctionPolynomial_eval h2 (fun c : F => squarePairCollapse c h) c
  refine Exists.intro P (And.intro (fieldFunctionPolynomial_natDegree_le _) ?_)
  constructor
  . intro c
    rw [he]
    exact squarePairCollapse_reachable c h hh
  . simp_rw [he]
    exact (traceFreePairWeight_square_minimum_attained hF h hh hq).2.2

theorem square_transport_minimum_degree (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 5<=(Fintype.card F : Real)) :
    exists P : Polynomial F, SquareTransportMinimizer h P /\
      (3*(Fintype.card F : Int)+(quadraticChar F) (-1)<=8*(P.natDegree : Int)) /\
      P.natDegree<=Fintype.card F-1 /\
      (forall Q : Polynomial F, SquareTransportMinimizer h Q -> P.natDegree<=Q.natDegree) := by
  have hu := square_transport_extremizer_polynomial_exists hF h hh hq
  let U : Polynomial F := Classical.choose hu
  have hU := Classical.choose_spec hu
  have hex : exists n : Nat, exists P : Polynomial F,
      P.natDegree=n /\ SquareTransportMinimizer h P :=
    Exists.intro U.natDegree (Exists.intro U (And.intro rfl hU.2))
  let n : Nat := Nat.find hex
  let P : Polynomial F := Classical.choose (Nat.find_spec hex)
  have hP := Classical.choose_spec (Nat.find_spec hex)
  have hleast : forall Q : Polynomial F, SquareTransportMinimizer h Q ->
      P.natDegree<=Q.natDegree := by
    intro Q hQ
    have hn : n<=Q.natDegree := Nat.find_min' hex (Exists.intro Q (And.intro rfl hQ))
    rw [hP.1]
    exact hn
  exact Exists.intro P (And.intro hP.2 (And.intro
    (square_transport_extremizer_degree_lower hF h hh hq P hP.2)
    (And.intro ((hleast U hU.2).trans hU.1) hleast)))

end FiniteField

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Proof.ProbeEuler.SelectedLocal

/-!
# Complete selected-tuple bounds with the marked correction

Extends the exact weighted tuple majorant to Re(x)>=3/4 with the same row
norm and prime-scale powers. The physical factorization separately requires
injectivity and primes outside the exclusion set. This bound alone does not
exclude a zero. Adapted from the pinned OAI weighted-slot and tuple proofs.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.SelectedTupleExtension
open scoped Classical
open OAI OAI.SevenEighths
open OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.ConcretePrimeRowBridge
open OAI.SevenEighths.ProbePrimePower OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.HeckeInverseAmplification OAI.SevenEighths.ProbePhysical
open OAI.SevenEighths.ProbeEuler OAI.SevenEighths.ProbeRow
open OAI.SevenEighths.ProbeHighRowFamily
open OAI.CanonicalQuadraticSieve OAI.CanonicalRowCompletion
local notation "O" => OAI.ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
  (hc : Not (ringChar (HasQuotient.Quotient O (Ideal.span {p} : Ideal O)) = 2))

theorem continued_selected_slot_bound_extended (eps a b r B : Real) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:Real)<=r) (hB : 0<=B) :
    Exists (fun C : Real => 0<C /\
      forall (eta : Character) (u : FreeRow) (T : Finset PrimeIdeal)
        (hT : forall P, Membership.mem T P -> Supported P.val /\ (4:Real)<=P.val.absNorm)
        (Y : Real), 1<=Y -> forall (W : Real->Complex),
        Set.Subset (Function.support W) (Set.Icc a b) ->
        (forall y, norm (W y)<=B) -> forall (x w z : Complex),
        (3/4:Real)<=x.re -> (1/2:Real)<=w.re -> z.re=r ->
        (Finset.univ.sum (fun P : T =>
          norm (W ((P.val.val.absNorm:Real)/Y)*(P.val.val.absNorm:Complex)^(z-1)*
            continuedCompensatedLocal eta u P.val (hT P.val P.property).1 x w z
              (star (idealCoeff eta P.val.val)*(P.val.val.absNorm:Complex)^x)
              ((P.val.val.absNorm:Complex)^(-w))))) <=
          C*((Ideal.span {u.val}:Ideal O).absNorm:Real)^eps*Y^r) := by
  have hh := ProbeSelectedPrimeSums.weighted_slot_bound_indexed eps a b r (1/2) B 961
    heps ha hb (by norm_num) hB (by norm_num)
  let C : Real := Classical.choose hh
  have hC : 0<C := (Classical.choose_spec hh).1
  refine Exists.intro C (And.intro hC ?_)
  intro eta u T hT Y hY W hWS hWB x w z hx hw hz
  let f : T->Ideal O := fun P=>P.val.val
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    exact Subtype.ext h
  let G : T->Complex := fun P =>
    continuedCompensatedLocal eta u P.val (hT P.val P.property).1 x w z
      (star (idealCoeff eta P.val.val)*(P.val.val.absNorm:Complex)^x)
      ((P.val.val.absNorm:Complex)^(-w))
  have hg (P : T) (_ : Membership.mem Finset.univ P) : norm (G P)<=
      961*(if Dvd.dvd (f P) (Ideal.span {u.val}:Ideal O)
        then (Ideal.absNorm (f P):Real)^(1/2:Real) else 1) := by
    have hlocal := continuedCompensatedLocal_bound_extended eta u P.val
      (hT P.val P.property).1 (hT P.val P.property).2 x w z hx hw
      (by rw [hz];exact hr)
    apply hlocal.trans
    by_cases hdiv : Dvd.dvd (f P) (Ideal.span {u.val}:Ideal O)
    . simp only [show P.val.val=f P from rfl,ite_eq_left hdiv]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le
      . have hn := (hT P.val P.property).2
        change 1 <= (P.val.val.absNorm : Real)
        linarith
      . exact max_le (by linarith) (by norm_num)
    . simp only [show P.val.val=f P from rfl,ite_eq_right hdiv,le_refl]
  exact (Classical.choose_spec hh).2 f hf (Ideal.span {u.val})
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _=>P.val.property.ne_zero) W hWS hWB G hg z hz

theorem continued_selected_tuple_bound_extended (K : Nat) (eps a b r B : Real)
    (heps : 0<eps) (ha : 0<a) (hb : 0<b) (hr : (17/50:Real)<=r) (hB : 0<=B) :
    Exists (fun C : Real => 0<C /\
      forall (eta : Character) (u : FreeRow) (T : Fin K->Finset PrimeIdeal)
        (hT : forall i P, Membership.mem (T i) P ->
          Supported P.val /\ (4:Real)<=P.val.absNorm)
        (Y : Fin K->Real), (forall i,1<=Y i) ->
        forall (W : Fin K->Real->Complex),
        (forall i,Set.Subset (Function.support (W i)) (Set.Icc a b)) ->
        (forall i y,norm (W i y)<=B) -> forall (x w z : Complex),
        (3/4:Real)<=x.re -> (1/2:Real)<=w.re -> z.re=r ->
        (Finset.univ.sum (fun P : (forall i : Fin K,T i) =>
          norm (Finset.univ.prod (fun i : Fin K =>
            W i (((P i).val.val.absNorm:Real)/Y i)*
              ((P i).val.val.absNorm:Complex)^(z-1)*
              continuedCompensatedLocal eta u (P i).val
                (hT i (P i).val (P i).property).1 x w z
                (star (idealCoeff eta (P i).val.val)*((P i).val.val.absNorm:Complex)^x)
                (((P i).val.val.absNorm:Complex)^(-w)))))) <=
          C*((Ideal.span {u.val}:Ideal O).absNorm:Real)^eps*
            Finset.univ.prod (fun i : Fin K => (Y i)^r)) := by
  let d : Real := eps/((K:Real)+1)
  have hd : 0<d := div_pos heps (by positivity)
  have hh := continued_selected_slot_bound_extended d a b r B hd ha hb hr hB
  let C : Real := Classical.choose hh
  have hC : 0<C := (Classical.choose_spec hh).1
  have hmain := (Classical.choose_spec hh).2
  refine Exists.intro (C^K) (And.intro (pow_pos hC K) ?_)
  intro eta u T hT Y hY W hWS hWB x w z hx hw hz
  let N : Real := ((Ideal.span {u.val}:Ideal O).absNorm:Real)
  have hN : 1<=N := by
    dsimp [N]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hdK : d*(K:Real)<=eps := by
    have hden : (0:Real)<(K:Real)+1 := by positivity
    have heq : d*((K:Real)+1)=eps := by
      dsimp [d]
      field_simp [ne_of_gt hden]
    nlinarith [hd]
  have hpow : (N^d)^K<=N^eps := by
    rw [<-Real.rpow_mul_natCast (by linarith : 0<=N)]
    exact Real.rpow_le_rpow_of_exponent_le hN hdK
  let F : forall i : Fin K,T i->Complex := fun i P =>
    W i ((P.val.val.absNorm:Real)/Y i)*(P.val.val.absNorm:Complex)^(z-1)*
      continuedCompensatedLocal eta u P.val (hT i P.val P.property).1 x w z
        (star (idealCoeff eta P.val.val)*(P.val.val.absNorm:Complex)^x)
        ((P.val.val.absNorm:Complex)^(-w))
  change (Finset.univ.sum (fun P : (forall i : Fin K,T i) =>
    norm (Finset.univ.prod (fun i : Fin K=>F i (P i))))) <=
      C^K*N^eps*Finset.univ.prod (fun i : Fin K=>(Y i)^r)
  simp_rw [norm_prod]
  rw [<-Fintype.prod_sum (fun i P=>norm (F i P))]
  calc
    _ <= Finset.univ.prod (fun i : Fin K=>C*N^d*(Y i)^r) := by
      gcongr with i hi
      exact hmain eta u (T i) (hT i) (Y i) (hY i) (W i) (hWS i) (hWB i)
        x w z hx hw hz
    _ = C^K*(N^d)^K*Finset.univ.prod (fun i : Fin K=>(Y i)^r) := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    _ <= C^K*N^eps*Finset.univ.prod (fun i : Fin K=>(Y i)^r) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity))
        (Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _)

theorem continued_selected_tuple_with_correction_extended
    (K : Nat) (delta a b r B : Real) (hdelta : 0<delta)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:Real)<=r) (hB : 0<=B) :
    Exists (fun C : Real => 0<C /\
      forall (eps : Real) (S : Finset (Ideal O)) (hS : SourceExclusions S)
        (_hfirst : FirstTail eps S) (eta : Character) (u : FreeRow)
        (T : Fin K->Finset PrimeIdeal)
        (hT : forall i P, Membership.mem (T i) P ->
          Supported P.val /\ (4:Real)<=P.val.absNorm)
        (Y : Fin K->Real), (forall i,1<=Y i) ->
        forall (W : Fin K->Real->Complex),
        (forall i,Set.Subset (Function.support (W i)) (Set.Icc a b)) ->
        (forall i y,norm (W i y)<=B) -> forall (x w z : Complex),
        (3/4:Real)<=x.re -> (1/2:Real)<=w.re -> z.re=r ->
        1+eps<=x.re+w.re ->
        (Finset.univ.sum (fun P : (forall i : Fin K,T i) =>
          norm (continuedCorrection
            (markExclusions S (Finset.univ.image (fun i : Fin K=>(P i).val)))
            (markedSourceExclusions S hS (Finset.univ.image (fun i : Fin K=>(P i).val)))
            eta u x w z *
            Finset.univ.prod (fun i : Fin K =>
              W i (((P i).val.val.absNorm:Real)/Y i)*
                ((P i).val.val.absNorm:Complex)^(z-1)*
                continuedCompensatedLocal eta u (P i).val
                  (hT i (P i).val (P i).property).1 x w z
                  (star (idealCoeff eta (P i).val.val)*((P i).val.val.absNorm:Complex)^x)
                  (((P i).val.val.absNorm:Complex)^(-w)))))) <=
          C*((Ideal.span {u.val}:Ideal O).absNorm:Real)^delta*
            Finset.univ.prod (fun i : Fin K=>(Y i)^r)) := by
  have hh1 := continued_selected_tuple_bound_extended K (delta/2) a b r B
    (by linarith) ha hb hr hB
  let C1 : Real := Classical.choose hh1
  have hC1 : 0<C1 := (Classical.choose_spec hh1).1
  have hmain := (Classical.choose_spec hh1).2
  have hh2 := unselectedCorrection_first_subpower (delta/2) (by linarith)
  let C2 : Real := Classical.choose hh2
  have hC2 : 0<C2 := (Classical.choose_spec hh2).1
  have hcorr := (Classical.choose_spec hh2).2
  refine Exists.intro (C2*C1) (And.intro (mul_pos hC2 hC1) ?_)
  intro eps S hS hfirst eta u T hT Y hY W hWS hWB x w z hx hw hz hxw
  let N : Real := ((Ideal.span {u.val}:Ideal O).absNorm:Real)
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  let F : (forall i : Fin K,T i)->Complex := fun P=>Finset.univ.prod (fun i : Fin K =>
    W i (((P i).val.val.absNorm:Real)/Y i)*((P i).val.val.absNorm:Complex)^(z-1)*
      continuedCompensatedLocal eta u (P i).val (hT i (P i).val (P i).property).1 x w z
        (star (idealCoeff eta (P i).val.val)*((P i).val.val.absNorm:Complex)^x)
        (((P i).val.val.absNorm:Complex)^(-w)))
  calc
    _ <= Finset.univ.sum (fun P : (forall i : Fin K,T i) =>
        (C2*N^(delta/2))*norm (F P)) := by
      apply Finset.sum_le_sum
      intro P hP
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hcorr eps S hS hfirst (Finset.univ.image (fun i : Fin K=>(P i).val))
          eta u x w z (by linarith) (by linarith) (by rw [hz];exact hr) hxw)
        (norm_nonneg _)
    _ = (C2*N^(delta/2))*Finset.univ.sum (fun P : (forall i : Fin K,T i) =>
        norm (F P)) := (Finset.mul_sum _ _ _).symm
    _ <= (C2*N^(delta/2))*
        (C1*N^(delta/2)*Finset.univ.prod (fun i : Fin K=>(Y i)^r)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hmain eta u T hT Y hY W hWS hWB x w z hx hw hz
    _ = (C2*C1)*N^delta*Finset.univ.prod (fun i : Fin K=>(Y i)^r) := by
      have hp : N^(delta/2)*N^(delta/2)=N^delta := by
        rw [<-Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = (C2*C1)*(N^(delta/2)*N^(delta/2))*
            Finset.univ.prod (fun i : Fin K=>(Y i)^r) := by ring
        _ = _ := by rw [hp]

end PrimeFactorOscillations.SelectedTupleExtension

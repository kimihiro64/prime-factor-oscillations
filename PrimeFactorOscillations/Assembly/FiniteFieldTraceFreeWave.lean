/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTraceFreeSigns

/-!
# Signed windows of the canonical actual pair-count law

Every mixed count product and covariance row is retained in the exact
signed identity. For nonnegative coefficients the negative nonoverlap
rows give an upper bound by the two-neighbor overlap graph. Injective
shifts bound its energy by twice the coefficient square sum. All averages
are complete finite-field averages; no short integer-interval supply
is inferred.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldTraceFreeWave
attribute [local instance] Classical.propDecidable
open _root_.FiniteField
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq F] in
private theorem translate_sum (f : F -> Real) (a : F) :
    (Finset.univ.sum fun c : F => f (c+a))=Finset.univ.sum f := by
  let e : Equiv F F :=
    { toFun := fun c => c+a
      invFun := fun c => c-a
      left_inv := by intro c; ring
      right_inv := by intro c; ring }
  exact Equiv.sum_comp e f

theorem centered_shift_kernel
    (hF : Not (ringChar F=2)) (h x y : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) :
    (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F =>
      (traceFreePairWeight (c+x) h-1)*(traceFreePairWeight (c+y) h-1))=
        traceFreePairCovariance h (y-x) := by
  have hm := traceFreePairWeight_mean_one hF h hh hq
  have hk := translate_sum (fun c : F => traceFreePairWeight c h) (y-x)
  have hp (c : F) :
      (traceFreePairWeight c h-1)*(traceFreePairWeight (c+(y-x)) h-1)=
      traceFreePairWeight c h*traceFreePairWeight (c+(y-x)) h-
        traceFreePairWeight c h-traceFreePairWeight (c+(y-x)) h+1 := by ring
  have hb : (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F =>
      (traceFreePairWeight c h-1)*(traceFreePairWeight (c+(y-x)) h-1))=
        traceFreePairCovariance h (y-x) := by
    simp_rw [hp]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,hk]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    have hq0 : Not ((Fintype.card F : Real)=0) := by linarith only [hq]
    have hi : (1/(Fintype.card F : Real))*(Fintype.card F : Real)=1 := by
      field_simp [hq0]
    unfold traceFreePairCovariance traceFreePairKernel
    nlinarith only [hm,hi]
  have hs := translate_sum (fun c : F =>
    (traceFreePairWeight c h-1)*(traceFreePairWeight (c+(y-x)) h-1)) x
  have he (c : F) : c+x+(y-x)=c+y := by ring
  simp_rw [he] at hs
  rw [hs]
  exact hb

def windowEnergy (h : F) (b : I -> Real) (s : I -> F) : Real :=
  (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F =>
    (Finset.univ.sum fun i : I => b i*(traceFreePairWeight (c+s i) h-1))^2)

def edgeEnergy (b : I -> Real) (s : I -> F) (a : F) : Real :=
  Finset.univ.sum fun i : I => Finset.univ.sum fun j : I =>
    if s j-s i=a then b i*b j else 0

omit [DecidableEq I] in
theorem windowEnergy_eq_covariance
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) (b : I -> Real) (s : I -> F) :
    windowEnergy h b s=Finset.univ.sum fun i : I => Finset.univ.sum fun j : I =>
      b i*b j*traceFreePairCovariance h (s j-s i) := by
  have hp (c : F) :
      (Finset.univ.sum fun i : I => b i*(traceFreePairWeight (c+s i) h-1))^2=
      Finset.univ.sum fun i : I => Finset.univ.sum fun j : I =>
        b i*b j*((traceFreePairWeight (c+s i) h-1)*
          (traceFreePairWeight (c+s j) h-1)) := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs :
      (Finset.univ.sum fun c : F => Finset.univ.sum fun i : I =>
        Finset.univ.sum fun j : I => b i*b j*((traceFreePairWeight (c+s i) h-1)*
          (traceFreePairWeight (c+s j) h-1)))=
      Finset.univ.sum fun i : I => Finset.univ.sum fun j : I =>
        b i*b j*(Finset.univ.sum fun c : F =>
          (traceFreePairWeight (c+s i) h-1)*(traceFreePairWeight (c+s j) h-1)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  unfold windowEnergy
  simp_rw [hp]
  rw [hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = b i*b j*((1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F =>
      (traceFreePairWeight (c+s i) h-1)*(traceFreePairWeight (c+s j) h-1))) := by ring
    _ = _ := by rw [centered_shift_kernel hF h (s i) (s j) hh hq]

private theorem unique_constant_sum_le (P : I -> Prop) [DecidablePred P]
    (v : Real) (hv : 0<=v)
    (hP : forall i j, P i -> P j -> i=j) :
    (Finset.univ.sum fun i : I => if P i then v else 0)<=v := by
  by_cases hex : Exists P
  . choose i hi using hex
    have he (j : I) : P j <-> j=i := by
      constructor
      . intro hj; exact hP j i hj hi
      . intro hj; rw [hj]; exact hi
    simp_rw [he]
    simp
  . have he (i : I) : Not (P i) := by intro hi; exact hex (Exists.intro i hi)
    simp only [ite_eq_right (he _),Finset.sum_const_zero]
    exact hv

omit [Fintype F] in
theorem edgeEnergy_le_square_sum (b : I -> Real) (s : I -> F)
    (hs : Function.Injective s) (a : F) :
    edgeEnergy b s a<=Finset.univ.sum fun i : I => (b i)^2 := by
  have hr (i : I) : (Finset.univ.sum fun j : I =>
      if s j-s i=a then (b i)^2 else 0)<=(b i)^2 := by
    apply unique_constant_sum_le _ _ (sq_nonneg _)
    intro j k hj hk
    apply hs
    linear_combination hj-hk
  have hc (j : I) : (Finset.univ.sum fun i : I =>
      if s j-s i=a then (b j)^2 else 0)<=(b j)^2 := by
    apply unique_constant_sum_le _ _ (sq_nonneg _)
    intro i k hi hk
    apply hs
    linear_combination hk-hi
  have hp (i j : I) :
      2*(if s j-s i=a then b i*b j else 0)<=
      (if s j-s i=a then (b i)^2 else 0)+
        (if s j-s i=a then (b j)^2 else 0) := by
    split_ifs <;> nlinarith only [sq_nonneg (b i-b j)]
  have hbound :
      2*edgeEnergy b s a<=
        (Finset.univ.sum fun i : I => (b i)^2)+(Finset.univ.sum fun j : I => (b j)^2) := by
    unfold edgeEnergy
    rw [Finset.mul_sum]
    calc
      _ <= Finset.univ.sum (fun i : I => Finset.univ.sum fun j : I =>
          (if s j-s i=a then (b i)^2 else 0)+(if s j-s i=a then (b j)^2 else 0)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun j _ => hp i j)
      _ = (Finset.univ.sum fun i : I => Finset.univ.sum fun j : I =>
          if s j-s i=a then (b i)^2 else 0)+
        (Finset.univ.sum fun j : I => Finset.univ.sum fun i : I =>
          if s j-s i=a then (b j)^2 else 0) := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j : I =>
          if s j-s i=a then (b j)^2 else 0)]
      _ <= _ := add_le_add
        (Finset.sum_le_sum (fun i _ => hr i)) (Finset.sum_le_sum (fun j _ => hc j))
  linarith only [hbound]

theorem windowEnergy_le_graph
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) (ht : (quadraticChar F) (-1)=-1)
    (b : I -> Real) (hb : forall i, 0<=b i) (s : I -> F) (hs : Function.Injective s) :
    windowEnergy h b s<=
      (2*(Finset.univ.sum fun i : I => (b i)^2)+
        edgeEnergy b s h+edgeEnergy b s (-h))/((Fintype.card F : Real)-3) := by
  have hz (i j : I) : (s j-s i=0)=(j=i) := propext (by
    constructor
    . intro he; apply hs; linear_combination he
    . intro he; rw [he,sub_self])
  have hp (i j : I) :
      b i*b j*((if s j-s i=0 then (2 : Real) else 0)+
        (if s j-s i=h then 1 else 0)+(if s j-s i=-h then 1 else 0))=
      2*(if j=i then b i*b j else 0)+
        (if s j-s i=h then b i*b j else 0)+
        (if s j-s i=-h then b i*b j else 0) := by
    simp only [hz]
    split_ifs <;> ring
  rw [windowEnergy_eq_covariance hF h hh hq]
  calc
    _ <= Finset.univ.sum (fun i : I => Finset.univ.sum fun j : I =>
        b i*b j*(((if s j-s i=0 then (2 : Real) else 0)+
          (if s j-s i=h then 1 else 0)+(if s j-s i=-h then 1 else 0))/
          ((Fintype.card F : Real)-3))) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (traceFreePairCovariance_graph_upper hF h (s j-s i) hh hq ht)
        (mul_nonneg (hb i) (hb j))
    _ = _ := by
      simp only [<- mul_div_assoc,hp,<- Finset.sum_div,Finset.sum_add_distrib,
        <- Finset.mul_sum,edgeEnergy]
      simp [pow_two]

theorem windowEnergy_le_four_square_sum
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) (ht : (quadraticChar F) (-1)=-1)
    (b : I -> Real) (hb : forall i, 0<=b i) (s : I -> F) (hs : Function.Injective s) :
    windowEnergy h b s<=
      4*(Finset.univ.sum fun i : I => (b i)^2)/((Fintype.card F : Real)-3) := by
  have hg := windowEnergy_le_graph hF h hh hq ht b hb s hs
  have hp := edgeEnergy_le_square_sum b s hs h
  have hn := edgeEnergy_le_square_sum b s hs (-h)
  have hd : 0<=(Fintype.card F : Real)-3 := by linarith only [hq]
  exact hg.trans (div_le_div_of_nonneg_right (by linarith only [hp,hn]) hd)

end PrimeFactorOscillations.FiniteFieldTraceFreeWave

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerMass
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistResonance
/-!
# Affine integer sampling with exact frozen rows

Rows where the integer progression step vanishes are retained exactly.
On every other prime row the affine map is a residue permutation, preserving
the centered correction and its variance. The incomplete-interval sieve
consumer keeps every phase and the full original local masks.
The full compensated packet satisfies an integer L1 estimate uniform in the
step and origin. Its exact frozen Euler factor is retained explicitly.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerAffine
open PrimeFactorOscillations.FiniteFieldIntegerTail
open PrimeFactorOscillations.FiniteFieldIntegerMass
attribute [local instance] Classical.propDecidable

def fieldAffineEquiv {F : Type*} [Field F] (a b : F) (hb : Not (b=0)) :
    Equiv F F :=
  { toFun := fun x => a+b*x
    invFun := fun y => (y-a)/b
    left_inv := by intro x; field_simp [hb] <;> ring
    right_inv := by intro y; field_simp [hb] <;> ring }

def affineCorrection {Q : Nat} (K : Nat) (h : Int) (a b : Nat)
    (q : BoundedModulus Q) (x : ZMod q.val) : Real :=
  if (b : ZMod q.val)=0 then 0
    else tailCorrection K h q ((a : ZMod q.val)+(b : ZMod q.val)*x)

theorem affine_correction_mean_zero {Q : Nat} (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (q : BoundedModulus Q) :
    (Finset.univ.sum fun x : ZMod q.val => affineCorrection K h a b q x)=0 := by
  by_cases hb : (b : ZMod q.val)=0
  . simp [affineCorrection,hb]
  . by_cases hp : Nat.Prime q.val
    . letI : Fact (Nat.Prime q.val) := Fact.mk hp
      let e := fieldAffineEquiv (a : ZMod q.val) (b : ZMod q.val) hb
      calc
        _ = Finset.univ.sum (fun x : ZMod q.val => tailCorrection K h q (e x)) := by
          simp only [affineCorrection,if_neg hb]
          rfl
        _ = Finset.univ.sum (fun x : ZMod q.val => tailCorrection K h q x) :=
          Equiv.sum_comp e _
        _ = 0 := tail_correction_mean_zero K h hK q
    . simp [affineCorrection,hb,tail_correction_composite K h q hp]

theorem affine_correction_composite {Q : Nat} (K : Nat) (h : Int) (a b : Nat)
    (q : BoundedModulus Q) (hp : Not (Nat.Prime q.val)) (x : ZMod q.val) :
    affineCorrection K h a b q x=0 := by
  simp [affineCorrection,tail_correction_composite K h q hp]

theorem affine_variance_le_original {Q : Nat} (K : Nat) (h : Int) (a b : Nat)
    (q : BoundedModulus Q) :
    (1/(q.val : Real))*(Finset.univ.sum fun x : ZMod q.val =>
      (affineCorrection K h a b q x)^2) <=
    (1/(q.val : Real))*(Finset.univ.sum fun x : ZMod q.val =>
      (tailCorrection K h q x)^2) := by
  by_cases hb : (b : ZMod q.val)=0
  . norm_num [affineCorrection,hb] <;> positivity
  . by_cases hp : Nat.Prime q.val
    . letI : Fact (Nat.Prime q.val) := Fact.mk hp
      let e := fieldAffineEquiv (a : ZMod q.val) (b : ZMod q.val) hb
      have he := Equiv.sum_comp e (fun x : ZMod q.val => (tailCorrection K h q x)^2)
      simp only [fieldAffineEquiv,e] at he
      simp only [affineCorrection,if_neg hb]
      exact le_of_eq (congrArg (fun z : Real => (1/(q.val : Real))*z) he)
    . simp [affineCorrection,hb,tail_correction_composite K h q hp]

theorem affine_variance_sum_le {Q : Nat} (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (hKQ : K<=Q) :
    ((Finset.Icc 1 Q).attach.sum fun q =>
      (1/(q.val : Real))*(Finset.univ.sum fun x : ZMod q.val =>
        (affineCorrection K h a b q x)^2)) <= 5/(K : Real) := by
  apply le_trans _ (tail_variance_sum_le K h hK hKQ)
  exact Finset.sum_le_sum (fun q _ => affine_variance_le_original K h a b q)

theorem affine_correction_abs_half {Q : Nat} (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (q : BoundedModulus Q) (x : ZMod q.val) :
    abs (affineCorrection K h a b q x)<=1/2 := by
  by_cases hb : (b : ZMod q.val)=0
  . simp [affineCorrection,hb]
  . simp only [affineCorrection,if_neg hb]
    exact tail_correction_abs_half K h hK q _

theorem affine_square_sum_le {Q : Nat} (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (hKQ : K<=Q) (n : Nat) :
    ((Finset.Icc 1 Q).attach.sum fun q =>
      (affineCorrection K h a b q (n : ZMod q.val))^2)<=9/(K : Real) := by
  apply le_trans _ (tail_square_sum_le K h hK hKQ (a+b*n))
  apply Finset.sum_le_sum
  intro q _
  by_cases hb : (b : ZMod q.val)=0
  . norm_num [affineCorrection,hb] <;> positivity
  . simp only [affineCorrection,if_neg hb,Nat.cast_add,Nat.cast_mul]
    exact le_refl _

def affineLinearSum (K : Nat) (h : Int) (a b Q n : Nat) : Real :=
  (Finset.Icc 1 Q).attach.sum
    (fun q => affineCorrection K h a b q (n : ZMod q.val))

def affineLogSum (K : Nat) (h : Int) (a b Q n : Nat) : Real :=
  (Finset.Icc 1 Q).attach.sum
    (fun q => Real.log (1+affineCorrection K h a b q (n : ZMod q.val)))

theorem affine_linear_interval_energy {Q N : Nat} (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat) :
    (Finset.univ.sum fun j : Fin N =>
      (affineLinearSum K h a b Q (M+1+j.val))^2) <=
        180*((N : Real)+(Q : Real)^2)/(K : Real) := by
  let f : (q : BoundedModulus Q) -> ZMod q.val -> Complex :=
    fun q x => (affineCorrection K h a b q x : Complex)
  have hm : forall q, (Finset.univ.sum (f q))=0 := by
    intro q
    dsimp only [f]
    rw [<- Complex.ofReal_sum,affine_correction_mean_zero K h a b hK q]
    rfl
  have hc : forall q, Not (Nat.Prime q.val) -> forall x, f q x=0 := by
    intro q hp x
    simp only [f,affine_correction_composite K h a b q hp x,Complex.ofReal_zero]
  have he := periodic_prime_family_interval_energy (show 0<Q from by omega)
    hN (M+1) f hm hc
  have hv := affine_variance_sum_le K h a b hK hKQ
  have hreal : forall z : Real, norm (z : Complex)^2=z^2 := by intro z; simp
  simp only [f,<- Complex.ofReal_sum,hreal] at he
  change (Finset.univ.sum fun j : Fin N =>
      (affineLinearSum K h a b Q (M+1+j.val))^2) <= _ at he
  calc
    _ <= 36*((N : Real)+(Q : Real)^2)*
      ((Finset.Icc 1 Q).attach.sum fun q =>
        (1/(q.val : Real))*(Finset.univ.sum fun x : ZMod q.val =>
          (affineCorrection K h a b q x)^2)) := he
    _ <= 36*((N : Real)+(Q : Real)^2)*(5/(K : Real)) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by ring

theorem frozen_iff_dvd {Q : Nat} (b : Nat) (q : BoundedModulus Q) :
    (b : ZMod q.val)=0 <-> Dvd.dvd q.val b :=
  CharP.cast_eq_zero_iff (ZMod q.val) q.val b

theorem affine_log_remainder_le {Q : Nat} (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (hKQ : K<=Q) (n : Nat) :
    abs (affineLogSum K h a b Q n-affineLinearSum K h a b Q n)<=18/(K : Real) := by
  unfold affineLogSum affineLinearSum
  rw [<- Finset.sum_sub_distrib]
  calc
    _ <= (Finset.Icc 1 Q).attach.sum (fun q =>
        abs (Real.log (1+affineCorrection K h a b q (n : ZMod q.val))-
          affineCorrection K h a b q (n : ZMod q.val))) := Finset.abs_sum_le_sum_abs _ _
    _ <= (Finset.Icc 1 Q).attach.sum (fun q =>
        2*(affineCorrection K h a b q (n : ZMod q.val))^2) := by
      apply Finset.sum_le_sum
      intro q _
      exact abs_log_one_add_sub_self_le _ (affine_correction_abs_half K h a b hK q _)
    _ = 2*((Finset.Icc 1 Q).attach.sum (fun q =>
        (affineCorrection K h a b q (n : ZMod q.val))^2)) := by rw [Finset.mul_sum]
    _ <= 2*(9/(K : Real)) :=
      mul_le_mul_of_nonneg_left (affine_square_sum_le K h a b hK hKQ n) (by norm_num)
    _ = _ := by ring

theorem affine_log_interval_energy {Q N : Nat} (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat) :
    (Finset.univ.sum fun j : Fin N =>
      (affineLogSum K h a b Q (M+1+j.val))^2) <=
        500*((N : Real)+(Q : Real)^2)/(K : Real) := by
  have hKr : (6 : Real)<=(K : Real) := by exact_mod_cast hK
  have hK0 : 0<(K : Real) := by linarith only [hKr]
  have he := affine_linear_interval_energy K h a b hK hKQ hN M
  have hs : (Finset.univ.sum fun j : Fin N =>
      (affineLogSum K h a b Q (M+1+j.val))^2) <=
      2*(Finset.univ.sum fun j : Fin N =>
        (affineLinearSum K h a b Q (M+1+j.val))^2)+
          (N : Real)*(648/(K : Real)^2) := by
    calc
      _ <= Finset.univ.sum (fun j : Fin N =>
          2*(affineLinearSum K h a b Q (M+1+j.val))^2+648/(K : Real)^2) := by
        apply Finset.sum_le_sum
        intro j _
        have hb := abs_le.mp (affine_log_remainder_le K h a b hK hKQ (M+1+j.val))
        have hsq : (affineLogSum K h a b Q (M+1+j.val)-
            affineLinearSum K h a b Q (M+1+j.val))^2<=(18/(K : Real))^2 := by
          nlinarith only [mul_nonneg (sub_nonneg.mpr hb.2)
            (show 0<=18/(K : Real)+(affineLogSum K h a b Q (M+1+j.val)-
              affineLinearSum K h a b Q (M+1+j.val)) from by linarith only [hb.1])]
        have hi := sq_nonneg (affineLogSum K h a b Q (M+1+j.val)-
          2*affineLinearSum K h a b Q (M+1+j.val))
        have hd : (18/(K : Real))^2=324/(K : Real)^2 := by ring
        rw [hd] at hsq
        have hd2 : 648/(K : Real)^2=2*(324/(K : Real)^2) := by ring
        rw [hd2]
        nlinarith only [hi,hsq]
      _ = _ := by rw [Finset.sum_add_distrib,<- Finset.mul_sum]; simp
  have hrem : (N : Real)*(648/(K : Real)^2)<=
      108*((N : Real)+(Q : Real)^2)/(K : Real) := by
    have hi : 648/(K : Real)^2<=108/(K : Real) := by
      calc
        _ = (648/(K : Real))/(K : Real) := by ring
        _ <= 108/(K : Real) := div_le_div_of_nonneg_right
          (calc
            _ <= (648 : Real)/6 := div_le_div_of_nonneg_left
              (by norm_num) (by norm_num) hKr
            _ = _ := by norm_num) hK0.le
    calc
      _ <= (N : Real)*(108/(K : Real)) :=
        mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg N)
      _ <= ((N : Real)+(Q : Real)^2)*(108/(K : Real)) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg (Q : Real)]) (by positivity)
      _ = _ := by ring
  have ht := mul_le_mul_of_nonneg_left he (show (0 : Real)<=2 from by norm_num)
  have hp : 0<=((N : Real)+(Q : Real)^2)/(K : Real) := by positivity
  calc
    _ <= 2*(180*((N : Real)+(Q : Real)^2)/(K : Real))+
        108*((N : Real)+(Q : Real)^2)/(K : Real) := le_trans hs (add_le_add ht hrem)
    _ = 468*(((N : Real)+(Q : Real)^2)/(K : Real)) := by ring
    _ <= 500*(((N : Real)+(Q : Real)^2)/(K : Real)) :=
      mul_le_mul_of_nonneg_right (by norm_num) hp
    _ = _ := by ring

theorem finite_l1_of_log_energy {N : Nat} (U V T : Fin N -> Real) (B E : Real)
    (hB : 0<=B) (hV : forall j, 0<=V j)
    (hfactor : forall j, U j=V j*Real.exp (T j))
    (hUcap : forall j, U j<=B) (hVcap : forall j, V j<=B)
    (henergy : (Finset.univ.sum fun j : Fin N => (T j)^2)<=E) :
    (Finset.univ.sum fun j : Fin N => abs (U j-V j))<=B*Real.sqrt ((N : Real)*E) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun _ => (1 : Real)) (fun j => abs (T j))
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one,sq_abs] at hc
  have hE : 0<=E := le_trans (Finset.sum_nonneg (fun j _ => sq_nonneg (T j))) henergy
  have hs := le_trans hc (mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg N))
  have hr : 0<=(N : Real)*E := mul_nonneg (Nat.cast_nonneg N) hE
  have hroot := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg ((N : Real)*E)
  have hsum : (Finset.univ.sum fun j : Fin N => abs (T j))<=Real.sqrt ((N : Real)*E) := by
    nlinarith only [hs,hroot,hn]
  calc
    _ <= Finset.univ.sum (fun j : Fin N => B*abs (T j)) := by
      apply Finset.sum_le_sum
      intro j _
      exact coupled_exp_difference_le (U j) (V j) B (T j) (hV j)
        (hfactor j) (hUcap j) (hVcap j)
    _ = B*(Finset.univ.sum fun j : Fin N => abs (T j)) := by rw [Finset.mul_sum]
    _ <= _ := mul_le_mul_of_nonneg_left hsum hB

def compensatedLocal {Q : Nat} (K : Nat) (h : Int) (b : Nat)
    (q : BoundedModulus Q) (c : ZMod q.val) : Real :=
  if (b : ZMod q.val)=0 then actualLocal h q c else hybridLocal K h q c

def compensatedPacket (K : Nat) (h : Int) (b Q n : Nat) : Real :=
  (Finset.Icc 1 Q).attach.prod (fun q => compensatedLocal K h b q (n : ZMod q.val))

theorem compensated_local_nonneg {Q : Nat} (K : Nat) (h : Int) (b : Nat)
    (q : BoundedModulus Q) (c : ZMod q.val) : 0<=compensatedLocal K h b q c := by
  unfold compensatedLocal
  split_ifs
  . exact actual_local_nonneg h q c
  . exact hybrid_local_nonneg K h q c

theorem compensated_local_envelope {Q : Nat} (K : Nat) (h : Int) (b : Nat)
    (hK : 6<=K) (q : BoundedModulus Q) (c : ZMod q.val) :
    compensatedLocal K h b q c<=localEnvelope q.val := by
  unfold compensatedLocal
  split_ifs
  . exact actual_local_envelope h q c
  . exact hybrid_local_envelope K h hK q c

theorem compensated_packet_nonneg (K : Nat) (h : Int) (b Q n : Nat) :
    0<=compensatedPacket K h b Q n := by
  apply Finset.prod_nonneg
  intro q _
  exact compensated_local_nonneg K h b q _

theorem compensated_packet_envelope (K : Nat) (h : Int) (b Q n : Nat)
    (hK : 6<=K) (hKQ : K<=Q) :
    compensatedPacket K h b Q n<=replacementConstant*(Real.log (Q : Real))^4 := by
  calc
    _ <= (Finset.Icc 1 Q).attach.prod (fun q => localEnvelope q.val) := by
      apply real_product_le_of_nonneg
      . intro q _
        exact compensated_local_nonneg K h b q _
      . intro q _
        exact compensated_local_envelope K h b hK q _
    _ = (Finset.Icc 1 Q).prod localEnvelope := Finset.prod_attach (Finset.Icc 1 Q) localEnvelope
    _ <= _ := envelope_product_bound Q (by omega)

theorem compensated_local_factorization {Q : Nat} (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (q : BoundedModulus Q) (x : ZMod q.val) :
    actualLocal h q ((a : ZMod q.val)+(b : ZMod q.val)*x)=
      compensatedLocal K h b q ((a : ZMod q.val)+(b : ZMod q.val)*x)*
        (1+affineCorrection K h a b q x) := by
  by_cases hb : (b : ZMod q.val)=0
  . simp [compensatedLocal,affineCorrection,hb]
  . simpa only [compensatedLocal,affineCorrection,if_neg hb] using
      full_local_factorization K h hK q ((a : ZMod q.val)+(b : ZMod q.val)*x)

theorem compensated_packet_factorization (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (Q n : Nat) :
    actualPacket h Q (a+b*n)=compensatedPacket K h b Q (a+b*n)*
      Real.exp (affineLogSum K h a b Q n) := by
  unfold actualPacket compensatedPacket affineLogSum
  simp only [Nat.cast_add,Nat.cast_mul]
  simp_rw [compensated_local_factorization K h a b hK]
  rw [Finset.prod_mul_distrib,Real.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro q _
  symm
  apply Real.exp_log
  have hb := abs_le.mp (affine_correction_abs_half K h a b hK q (n : ZMod q.val))
  linarith only [hb.1]

theorem affine_packet_l1_replacement {Q N : Nat} (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat) :
    (Finset.univ.sum fun j : Fin N =>
      abs (actualPacket h Q (a+b*(M+1+j.val))-
        compensatedPacket K h b Q (a+b*(M+1+j.val)))) <=
      replacementConstant*(Real.log (Q : Real))^4*
        Real.sqrt (500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real)) := by
  have he := affine_log_interval_energy K h a b hK hKQ hN M
  have hb : 0<=replacementConstant*(Real.log (Q : Real))^4 := by
    unfold replacementConstant
    positivity
  have hi := finite_l1_of_log_energy
    (fun j : Fin N => actualPacket h Q (a+b*(M+1+j.val)))
    (fun j : Fin N => compensatedPacket K h b Q (a+b*(M+1+j.val)))
    (fun j : Fin N => affineLogSum K h a b Q (M+1+j.val))
    (replacementConstant*(Real.log (Q : Real))^4)
    (500*((N : Real)+(Q : Real)^2)/(K : Real)) hb
    (fun j => compensated_packet_nonneg K h b Q _)
    (fun j => compensated_packet_factorization K h a b hK Q _)
    (fun j => actual_packet_envelope h Q _ (by omega))
    (fun j => compensated_packet_envelope K h b Q _ hK hKQ) he
  have hid : (N : Real)*(500*((N : Real)+(Q : Real)^2)/(K : Real))=
      500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real) := by ring
  rwa [hid] at hi

def frozenLogSum (K : Nat) (h : Int) (a b Q : Nat) : Real :=
  (Finset.Icc 1 Q).attach.sum (fun q =>
    if (b : ZMod q.val)=0
      then Real.log (1+tailCorrection K h q (a : ZMod q.val)) else 0)

theorem affine_log_frozen_decomposition (K : Nat) (h : Int) (a b Q n : Nat) :
    tailLogSum K h Q (a+b*n)=affineLogSum K h a b Q n+frozenLogSum K h a b Q := by
  unfold tailLogSum affineLogSum frozenLogSum
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hb : (b : ZMod q.val)=0
  . simp [affineCorrection,hb,Nat.cast_add,Nat.cast_mul]
  . simp [affineCorrection,hb,Nat.cast_add,Nat.cast_mul]

theorem compensated_frozen_factor (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (Q n : Nat) :
    compensatedPacket K h b Q (a+b*n)=
      hybridPacket K h Q (a+b*n)*Real.exp (frozenLogSum K h a b Q) := by
  have hU := full_packet_factorization K h hK Q (a+b*n)
  have hV := compensated_packet_factorization K h a b hK Q n
  rw [affine_log_frozen_decomposition,Real.exp_add] at hU
  have heq :
      compensatedPacket K h b Q (a+b*n)*Real.exp (affineLogSum K h a b Q n)=
      (hybridPacket K h Q (a+b*n)*Real.exp (frozenLogSum K h a b Q))*
        Real.exp (affineLogSum K h a b Q n) := by
    calc
      _ = actualPacket h Q (a+b*n) := hV.symm
      _ = hybridPacket K h Q (a+b*n)*
          (Real.exp (affineLogSum K h a b Q n)*Real.exp (frozenLogSum K h a b Q)) := hU
      _ = _ := by ring
  have hn : Not (Real.exp (affineLogSum K h a b Q n)=0) := ne_of_gt (Real.exp_pos _)
  calc
    _ = (compensatedPacket K h b Q (a+b*n)*Real.exp (affineLogSum K h a b Q n))/
        Real.exp (affineLogSum K h a b Q n) := by field_simp [hn]
    _ = ((hybridPacket K h Q (a+b*n)*Real.exp (frozenLogSum K h a b Q))*
        Real.exp (affineLogSum K h a b Q n))/Real.exp (affineLogSum K h a b Q n) := by rw [heq]
    _ = _ := by field_simp [hn]

theorem affine_packet_mass_replacement {Q N : Nat} (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat) :
    abs ((Finset.univ.sum fun j : Fin N => actualPacket h Q (a+b*(M+1+j.val)))-
      (Finset.univ.sum fun j : Fin N => compensatedPacket K h b Q (a+b*(M+1+j.val)))) <=
      replacementConstant*(Real.log (Q : Real))^4*
        Real.sqrt (500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real)) := by
  rw [<- Finset.sum_sub_distrib]
  exact le_trans (Finset.abs_sum_le_sum_abs _ _)
    (affine_packet_l1_replacement K h a b hK hKQ hN M)


theorem affine_logarithmic_cutoff_l1_replacement {Q N : Nat} (K : Nat) (h : Int) (a b : Nat)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat)
    (hcritical : (Q : Real)^2<=3*(N : Real))
    (hlogK : (Real.log (Q : Real))^10<=(K : Real)) :
    (Finset.univ.sum fun j : Fin N =>
      abs (actualPacket h Q (a+b*(M+1+j.val))-compensatedPacket K h b Q (a+b*(M+1+j.val)))) <=
      45*replacementConstant*(N : Real)/Real.log (Q : Real) := by
  have hlog : 0<Real.log (Q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1<Q from by omega))
  have hl0 : Not (Real.log (Q : Real)=0) := ne_of_gt hlog
  have hR : 500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real)<=
      2025*(N : Real)^2/(Real.log (Q : Real))^10 := by
    calc
      _ <= 500*(N : Real)*(4*(N : Real))/(K : Real) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [hcritical]) (by positivity))
          (Nat.cast_nonneg K)
      _ = 2000*(N : Real)^2/(K : Real) := by ring
      _ <= 2000*(N : Real)^2/(Real.log (Q : Real))^10 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hlog _) hlogK
      _ <= _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg (N : Real)))
        (pow_nonneg hlog.le _)
  have hid : Real.sqrt (2025*(N : Real)^2/(Real.log (Q : Real))^10)=
      45*(N : Real)/(Real.log (Q : Real))^5 := by
    have he : 2025*(N : Real)^2/(Real.log (Q : Real))^10=
        (45*(N : Real)/(Real.log (Q : Real))^5)^2 := by
      field_simp [hl0] <;> ring
    rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg (by positivity)]
  have hs := Real.sqrt_le_sqrt hR
  rw [hid] at hs
  calc
    _ <= replacementConstant*(Real.log (Q : Real))^4*
        Real.sqrt (500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real)) :=
      affine_packet_l1_replacement K h a b hK hKQ hN M
    _ <= replacementConstant*(Real.log (Q : Real))^4*
        (45*(N : Real)/(Real.log (Q : Real))^5) :=
      mul_le_mul_of_nonneg_left hs (by unfold replacementConstant; positivity)
    _ = _ := by field_simp [hl0] <;> ring


theorem prime_step_frozen_log (p : Nat) [Fact (Nat.Prime p)]
    (hp7 : 7<=p) (h : Int) (hh : Not ((h : ZMod p)=0)) (a : Nat) :
    frozenLogSum (p-1) h a p p =
      Real.log (1+_root_.FiniteField.QuadraticPairTwistLikelihood.localCorrection
        (a : ZMod p) (h : ZMod p)) := by
  let qp : BoundedModulus p := Subtype.mk p (Finset.mem_Icc.mpr (And.intro (by omega) le_rfl))
  have hpp : (p : ZMod p)=0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p p).mpr (dvd_refl p)
  have hmain : (if (p : ZMod qp.val)=0 then
      Real.log (1+tailCorrection (p-1) h qp (a : ZMod qp.val)) else 0)=
      Real.log (1+_root_.FiniteField.QuadraticPairTwistLikelihood.localCorrection
        (a : ZMod p) (h : ZMod p)) := by
    simp [qp,hpp,tailCorrection,Fact.out,hh,show p-1<p from by omega]
  unfold frozenLogSum
  rw [Finset.sum_eq_single qp]
  . exact hmain
  . intro q _ hneq
    have hv : Not (q.val=p) := by
      intro he
      apply hneq
      apply Subtype.ext
      exact he
    have hq := (Finset.mem_Icc.mp q.property).2
    have hlo : Not (p-1<q.val) := by omega
    have ha := tail_correction_abs_le (p-1) h (by omega) q (a : ZMod q.val)
    rw [if_neg hlo] at ha
    have hz : tailCorrection (p-1) h q (a : ZMod q.val)=0 :=
      abs_eq_zero.mp (le_antisymm ha (abs_nonneg _))
    simp [hz]
  . intro hn
    exact False.elim (hn (Finset.mem_attach _ qp))

theorem exists_prime_step_positive_frozen_log (p : Nat) [Fact (Nat.Prime p)]
    (hp7 : 7<=p) (h : Int) (hh : Not ((h : ZMod p)=0)) :
    exists a : Nat, a<p /\
      Real.log (1+1/(4*(p : Real)))<=frozenLogSum (p-1) h a p p /\
      0<frozenLogSum (p-1) h a p p := by
  have hF : Not (ringChar (ZMod p)=2) := by
    rw [ringChar.eq (ZMod p) p]
    omega
  have hq : (7 : Real)<=(Fintype.card (ZMod p) : Real) := by
    rw [ZMod.card]
    exact_mod_cast hp7
  have hex := _root_.FiniteField.QuadraticPairTwistResonance.exists_local_positive_crest
    hF (h : ZMod p) hh hq
  let c : ZMod p := Classical.choose hex
  have hc := Classical.choose_spec hex
  change 1/(4*(Fintype.card (ZMod p) : Real))<=
    _root_.FiniteField.QuadraticPairTwistLikelihood.localCorrection c (h : ZMod p) at hc
  rw [ZMod.card] at hc
  have hp0 : (0 : Real)<p := by exact_mod_cast (show 0<p from by omega)
  have hc0 : 0<1/(4*(p : Real)) := by positivity
  have hl : Real.log (1+1/(4*(p : Real)))<=
      Real.log (1+_root_.FiniteField.QuadraticPairTwistLikelihood.localCorrection
        c (h : ZMod p)) :=
    Real.log_le_log (by linarith only [hc0]) (by linarith only [hc])
  have hl0 : 0<Real.log (1+1/(4*(p : Real))) :=
    Real.log_pos (by linarith only [hc0])
  refine Exists.intro c.val (And.intro (ZMod.val_lt c) ?_)
  rw [prime_step_frozen_log p hp7 h hh c.val,ZMod.natCast_zmod_val]
  exact And.intro hl (lt_of_lt_of_le hl0 hl)


end PrimeFactorOscillations.FiniteFieldIntegerAffine

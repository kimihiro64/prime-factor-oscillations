/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.RamanujanIncidenceEstimate

/-!
# RamanujanIncidenceOperator

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

set_option maxHeartbeats 2000000

noncomputable section
namespace OAI.SevenEighths.RamanujanIncidenceGram
open scoped Classical BigOperators
open IdealMobiusDivisorSum CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem finite_normalized_energy (R C : Finset Id) (M Q Dr Dc : Real)
    (hM : 1<=M)
    (hR0 : forall A, Membership.mem R A -> Not (A=0))
    (hR : forall A, Membership.mem R A -> (A.absNorm:Real)<=M)
    (hC0 : forall I, Membership.mem C I -> Not (I=0))
    (hC : forall I, Membership.mem C I -> (I.absNorm:Real)<=Q)
    (hDr : 0<=Dr) (hDc : 0<=Dc)
    (hrdiv : forall A, Membership.mem R A -> ((idealDivisors A).card:Real)<=Dr)
    (hcdiv : forall I, Membership.mem C I -> ((idealDivisors I).card:Real)<=Dc)
    (G : Id -> Id -> Complex)
    (hG : forall A, Membership.mem R A -> forall I, Membership.mem C I ->
      norm (G A I)<=sharedMass A I/Real.sqrt (I.absNorm:Real))
    (b : Id -> Complex) :
    (R.sum fun A=>norm (C.sum fun I=>b I*G A I)^2)<=
      32768*M*Dr*Dc*(columnDyadicLength Q+1:Real)*
        (C.sum fun I=>norm (b I)^2) := by
  let k := fun A I=>sharedMass A I/Real.sqrt (I.absNorm:Real)
  let w := fun I:Id=>1/Real.sqrt (I.absNorm:Real)
  have hn (I : Id) (hI : Membership.mem C I) : 0<(I.absNorm:Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hC0 I hI))
  have hs (I : Id) (hI : Membership.mem C I) : 0<Real.sqrt (I.absNorm:Real) :=
    Real.sqrt_pos.mpr (hn I hI)
  have hk (A : Id) (hA : Membership.mem R A) (I : Id) (hI : Membership.mem C I) :
      0<=k A I := div_nonneg (sharedMass_nonneg A I) (hs I hI).le
  have hrow (A : Id) (hA : Membership.mem R A) :
      (C.sum fun I=>k A I*w I)<=Dr*(256*(columnDyadicLength Q+1:Real)) := by
    have he (I : Id) (hI : Membership.mem C I) :
        k A I*w I=sharedMass A I/(I.absNorm:Real) := by
      have hsq := Real.sq_sqrt (hn I hI).le
      have hsn := ne_of_gt (hs I hI)
      have hnn := ne_of_gt (hn I hI)
      dsimp [k,w]
      field_simp
      rw [hsq]
    rw [Finset.sum_congr rfl he]
    exact (sharedMass_row C Q hC0 hC A (hR0 A hA)).trans
      (mul_le_mul_of_nonneg_right (hrdiv A hA) (by positivity))
  have hcol (I : Id) (hI : Membership.mem C I) :
      (R.sum fun A=>k A I/w I)<=128*M*Dc := by
    have he (A : Id) : k A I/w I=sharedMass A I := by
      have hsn := ne_of_gt (hs I hI)
      dsimp [k,w]
      field_simp
    rw [Finset.sum_congr rfl (fun A _=>he A)]
    exact (sharedMass_column R M hM hR0 hR I (hC0 I hI)).trans
      (mul_le_mul_of_nonneg_left (hcdiv I hI) (by positivity))
  have hb := weighted_schur R C k w (fun I=>norm (b I))
    (Dr*(256*(columnDyadicLength Q+1:Real))) (128*M*Dc) hk
    (fun I hI=>one_div_pos.mpr (hs I hI)) (fun I _=>norm_nonneg _)
    (by positivity) hrow hcol
  have hp (A : Id) (hA : Membership.mem R A) :
      norm (C.sum fun I=>b I*G A I)<=(C.sum fun I=>norm (b I)*k A I) := by
    exact (norm_sum_le C (fun I=>b I*G A I)).trans
      (Finset.sum_le_sum fun I hI=>by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hG A hA I hI) (norm_nonneg _))
  calc
    _ <= R.sum (fun A=>(C.sum fun I=>norm (b I)*k A I)^2) := by
      apply Finset.sum_le_sum
      intro A hA
      have hh := hp A hA
      have hn0 := norm_nonneg (C.sum fun I=>b I*G A I)
      nlinarith
    _ <= _ := by
      convert hb using 1 <;> ring

theorem normalized_energy (eps : Real) (heps : 0<eps) :
    Exists fun K : Real => 0<K /\
    forall (R C : Finset Id) (M Q : Real), 1<=M -> 1<=Q ->
    (forall A, Membership.mem R A -> Not (A=0) /\ (A.absNorm:Real)<=M) ->
    (forall I, Membership.mem C I -> Not (I=0) /\ (I.absNorm:Real)<=Q) ->
    forall G : Id -> Id -> Complex,
    (forall A, Membership.mem R A -> forall I, Membership.mem C I ->
      norm (G A I)<=sharedMass A I/Real.sqrt (I.absNorm:Real)) ->
    forall b : Id -> Complex,
    (R.sum fun A=>norm (C.sum fun I=>b I*G A I)^2)<=
      K*M*(M*Q)^eps*(C.sum fun I=>norm (b I)^2) := by
  let delta := eps/2
  have hd : 0<delta := by dsimp [delta];positivity
  have ex := IdealDivisorBound.ideal_divisor_small_power delta hd
  choose D hD hdiv using ex
  let H : Real := 2+1/(delta*Real.log 2)
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hH : 0<H := by dsimp [H];positivity
  let K : Real := 32768*D^2*H
  refine Exists.intro K (And.intro (by dsimp [K];positivity) ?_)
  intro R C M Q hM hQ hR hC G hG b
  have hMp : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hQp : 0<Q := lt_of_lt_of_le zero_lt_one hQ
  have hdr : forall A, Membership.mem R A -> ((idealDivisors A).card:Real)<=D*M^delta := by
    intro A hA
    exact (hdiv A (hR A hA).1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hR A hA).2 hd.le) hD.le)
  have hdc : forall I, Membership.mem C I -> ((idealDivisors I).card:Real)<=D*Q^delta := by
    intro I hI
    exact (hdiv I (hC I hI).1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hC I hI).2 hd.le) hD.le)
  have he := finite_normalized_energy R C M Q (D*M^delta) (D*Q^delta) hM
    (fun A hA=>(hR A hA).1) (fun A hA=>(hR A hA).2)
    (fun I hI=>(hC I hI).1) (fun I hI=>(hC I hI).2)
    (by positivity) (by positivity) hdr hdc G hG b
  have hh : (columnDyadicLength Q+1:Real)<=H*Q^delta :=
    columnDyadicLength_small_power delta hd Q hQ
  have hpower : M^delta*Q^delta*Q^delta<=(M*Q)^eps := by
    have hm : M^delta<=M^eps := Real.rpow_le_rpow_of_exponent_le hM (by dsimp [delta];linarith)
    have heq : Q^delta*Q^delta=Q^eps := by
      rw [<-Real.rpow_add hQp]
      congr 1
      dsimp [delta]
      ring
    rw [mul_assoc,heq,Real.mul_rpow hMp.le hQp.le]
    exact mul_le_mul_of_nonneg_right hm (by positivity)
  calc
    _ <= 32768*M*(D*M^delta)*(D*Q^delta)*(H*Q^delta)*
        (C.sum fun I=>norm (b I)^2) := by
      apply he.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh (by positivity))
        (Finset.sum_nonneg fun I _=>sq_nonneg _)
    _ = K*M*(M^delta*Q^delta*Q^delta)*(C.sum fun I=>norm (b I)^2) := by
      dsimp [K]
      ring
    _ <= _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower (by dsimp [K];positivity))
      (Finset.sum_nonneg fun I _=>sq_nonneg _)

end OAI.SevenEighths.RamanujanIncidenceGram

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Proof.LargeSieve.CharacterReduction
import PrimeFactorOscillations.Helpers.CharacterProbability
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistLikelihood
/-!
# Integer interval energy for finite-field pair packets

Finite Fourier inversion and the unconditional additive large sieve give
integer interval energy for prime-modulus periodic functions, with the
complete family of Fourier phases retained. A second-order logarithm
bound gives explicit 180 and 500 interval energy constants, including the
critical Q^2 <= 3*N range. The full actual/flat product comparison retains
the weighted exceptional-set subtraction. The existing character
probability export is preserved through this owner to keep the probability
facade within its import budget. No prime-pair positivity is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerTail
open BombieriVinogradov.LargeSieve
attribute [local instance] Classical.propDecidable
theorem shifted_farey_dual_energy {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (M : Nat) (b : FareyIndex Q -> Complex) :
    (Finset.univ.sum fun n : Fin N => norm (fareyDualSample b (M+n.val))^2) <=
      36*((N : Real)+(Q : Real)^2)*
        ((fareyIndices Q).sum fun i => norm (b i)^2) := by
  let c : FareyIndex Q -> Complex :=
    fun i => additivePhase ((M : Real)*(fareyValue i : Real))*b i
  have hs (n : Nat) : fareyDualSample c n=fareyDualSample b (M+n) := by
    unfold fareyDualSample
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [c]
    rw [Nat.cast_add,add_mul,additivePhase_add]
    ring
  have hc : ((fareyIndices Q).sum fun i => norm (c i)^2) =
      ((fareyIndices Q).sum fun i => norm (b i)^2) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [c,norm_mul,norm_additivePhase,one_mul]
  have hp := fareyDualEnergy hQ hN c
  simp_rw [hs] at hp
  rw [hc] at hp
  exact hp


theorem finite_fourier_inversion {q : Nat} [NeZero q]
    (f : ZMod q -> Complex) (n : ZMod q) :
    (1/(q : Complex))*(Finset.univ.sum fun k : ZMod q =>
      additiveTransform f (-k)*ZMod.stdAddChar (n*k))=f n := by
  have hq : Not ((q : Complex)=0) := by exact_mod_cast (NeZero.ne q)
  have hs : (Finset.univ.sum fun k : ZMod q =>
      additiveTransform f (-k)*ZMod.stdAddChar (n*k))=f n*(q : Complex) := by
    calc
      _ = Finset.univ.sum (fun k : ZMod q =>
          Finset.univ.sum (fun x : ZMod q =>
            f x*ZMod.stdAddChar (x*(-k))*ZMod.stdAddChar (n*k))) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [additiveTransform,Finset.sum_mul]
      _ = Finset.univ.sum (fun x : ZMod q =>
          Finset.univ.sum (fun k : ZMod q =>
            f x*(ZMod.stdAddChar (x*(-k))*ZMod.stdAddChar (n*k)))) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = Finset.univ.sum (fun x : ZMod q =>
          f x*(Finset.univ.sum fun k : ZMod q =>
            ZMod.stdAddChar (k*(n-x)))) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        have he : ZMod.stdAddChar (x*(-k))*ZMod.stdAddChar (n*k) =
            ZMod.stdAddChar (k*(n-x)) := by
          rw [<- AddChar.map_add_eq_mul]
          congr 1
          ring
        rw [he]
      _ = Finset.univ.sum (fun x : ZMod q =>
          f x*(if x=n then (q : Complex) else 0)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [AddChar.sum_mulShift (n-x) (ZMod.isPrimitive_stdAddChar q)]
        by_cases hx : x=n
        . subst x
          simp
        . have hn : Not (n-x=0) := fun he => hx (sub_eq_zero.mp he).symm
          simp [hn,hx]
      _ = _ := by simp
  rw [hs]
  field_simp [hq]

theorem abs_log_one_add_sub_self_le (x : Real) (hx : abs x <= 1/2) :
    abs (Real.log (1+x)-x) <= 2*x^2 := by
  have hb := abs_le.mp hx
  have hp : 0 < 1+x := by linarith only [hb.1]
  have hu : Real.log (1+x) <= x := by
    have he := Real.log_le_sub_one_of_pos hp
    linarith only [he]
  have hInv := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hInv
  have he : x+Inv.inv (1+x)-1=x^2/(1+x) := by
    field_simp [ne_of_gt hp] <;> ring
  have hhalf : (1/2 : Real) <= 1+x := by linarith only [hb.1]
  have hd : x^2/(1+x) <= 2*x^2 := by
    calc
      _ <= x^2/(1/2) := div_le_div_of_nonneg_left (sq_nonneg x)
        (by norm_num : (0 : Real)<1/2) hhalf
      _ = _ := by ring
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  calc
    _ = x-Real.log (1+x) := by ring
    _ <= x+Inv.inv (1+x)-1 := by linarith only [hInv]
    _ = x^2/(1+x) := he
    _ <= 2*x^2 := hd

def primeFourierCoeff {q : Nat} [NeZero q]
    (f : ZMod q -> Complex) (u : Units (ZMod q)) : Complex :=
  (1/(q : Complex))*additiveTransform f (-(u : ZMod q))

theorem prime_fourier_reconstruction {q : Nat} [NeZero q] [Fact (Nat.Prime q)]
    (f : ZMod q -> Complex) (hf : (Finset.univ.sum f)=0) (n : Nat) :
    (Finset.univ.sum fun u : Units (ZMod q) =>
      additivePhase ((n : Real)*(unitFraction u : Real))*primeFourierCoeff f u) =
        f (n : ZMod q) := by
  let term : ZMod q -> Complex := fun k =>
    ZMod.stdAddChar ((n : ZMod q)*k)*
      ((1/(q : Complex))*additiveTransform f (-k))
  have hzero : term 0=0 := by
    simp [term,additiveTransform,hf]
  have hu : (Finset.univ.sum fun u : Units (ZMod q) => term (u : ZMod q)) =
      ((Finset.univ : Finset (ZMod q)).erase 0).sum term := by
    refine Finset.sum_bij (fun u _ => (u : ZMod q)) ?_ ?_ ?_ ?_
    . intro u _
      exact Finset.mem_erase.mpr
        (And.intro (Units.ne_zero u) (Finset.mem_univ _))
    . intro u _ v _ huv
      exact Units.val_injective huv
    . intro k hk
      let u : Units (ZMod q) := Units.mk0 k (Finset.mem_erase.mp hk).1
      exact Exists.intro u (Exists.intro (Finset.mem_univ _) rfl)
    . intro u _
      rfl
  have hs : ((Finset.univ : Finset (ZMod q)).erase 0).sum term =
      Finset.univ.sum term := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k hk hnot
    have hk0 : k=0 := by
      by_contra hz
      exact hnot (Finset.mem_erase.mpr (And.intro hz hk))
    rw [hk0]
    exact hzero
  calc
    _ = Finset.univ.sum (fun u : Units (ZMod q) => term (u : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro u _
      have hp := additivePhase_int_unitFraction (n : Int) u
      simpa only [Int.cast_natCast,term,primeFourierCoeff] using
        congrArg (fun z : Complex => z*primeFourierCoeff f u) hp
    _ = ((Finset.univ : Finset (ZMod q)).erase 0).sum term := hu
    _ = Finset.univ.sum term := hs
    _ = (1/(q : Complex))*(Finset.univ.sum fun k : ZMod q =>
        additiveTransform f (-k)*ZMod.stdAddChar ((n : ZMod q)*k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [term]
      ring
    _ = f (n : ZMod q) := finite_fourier_inversion f (n : ZMod q)

theorem prime_fourier_coeff_energy {q : Nat} [NeZero q]
    (f : ZMod q -> Complex) :
    (Finset.univ.sum fun u : Units (ZMod q) => norm (primeFourierCoeff f u)^2) <=
      (1/(q : Real))*(Finset.univ.sum fun x : ZMod q => norm (f x)^2) := by
  let e : Function.Embedding (Units (ZMod q)) (ZMod q) :=
    { toFun := fun u => -(u : ZMod q)
      inj' := by
        intro u v huv
        exact Units.val_injective (neg_injective huv) }
  have hsum : (Finset.univ.sum fun u : Units (ZMod q) =>
      norm (additiveTransform f (-(u : ZMod q)))^2) <=
      (Finset.univ.sum fun k : ZMod q => norm (additiveTransform f k)^2) := by
    calc
      _ = ((Finset.univ : Finset (Units (ZMod q))).map e).sum
          (fun k : ZMod q => norm (additiveTransform f k)^2) := by
        rw [Finset.sum_map]
        rfl
      _ <= _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
  have hn (u : Units (ZMod q)) : norm (primeFourierCoeff f u)^2 =
      (1/(q : Real))^2*norm (additiveTransform f (-(u : ZMod q)))^2 := by
    simp [primeFourierCoeff,norm_mul,norm_div,mul_pow]
  simp_rw [hn]
  rw [<- Finset.mul_sum]
  have hq : Not ((q : Real)=0) := by exact_mod_cast (NeZero.ne q)
  calc
    _ <= (1/(q : Real))^2*
        (Finset.univ.sum fun k : ZMod q => norm (additiveTransform f k)^2) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by
      rw [additiveParseval_normSq]
      field_simp [hq] <;> ring

abbrev BoundedModulus (Q : Nat) :=
  Subtype (fun q : Nat => Membership.mem (Finset.Icc 1 Q) q)

private instance boundedModulus_neZero {Q : Nat} (q : BoundedModulus Q) :
    NeZero q.val :=
  NeZero.mk (by
    have hq := (Finset.mem_Icc.mp q.property).1
    omega)

def familyCoefficient {Q : Nat}
    (f : (q : BoundedModulus Q) -> ZMod q.val -> Complex)
    (i : FareyIndex Q) : Complex :=
  primeFourierCoeff (f i.fst) i.snd

theorem family_coefficient_energy {Q : Nat}
    (f : (q : BoundedModulus Q) -> ZMod q.val -> Complex) :
    ((fareyIndices Q).sum fun i => norm (familyCoefficient f i)^2) <=
      ((Finset.Icc 1 Q).attach.sum fun q =>
        (1/(q.val : Real))*(Finset.univ.sum fun x : ZMod q.val => norm (f q x)^2)) := by
  unfold familyCoefficient fareyIndices
  rw [Finset.sum_sigma]
  apply Finset.sum_le_sum
  intro q _
  convert prime_fourier_coeff_energy (f q) using 1
  congr 1 <;> ext u <;> simp

theorem family_reconstruction {Q : Nat}
    (f : (q : BoundedModulus Q) -> ZMod q.val -> Complex)
    (hmean : forall q, (Finset.univ.sum (f q))=0)
    (hcomposite : forall q, Not (Nat.Prime q.val) -> forall x, f q x=0)
    (n : Nat) :
    fareyDualSample (familyCoefficient f) n =
      ((Finset.Icc 1 Q).attach.sum fun q => f q (n : ZMod q.val)) := by
  unfold fareyDualSample fareyIndices familyCoefficient
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : Nat.Prime q.val
  . letI : Fact (Nat.Prime q.val) := Fact.mk hp
    convert prime_fourier_reconstruction (f q) (hmean q) n using 1
    congr 1 <;> ext u <;> simp [fareyValue]
  . have he : f q=(fun _ : ZMod q.val => (0 : Complex)) := funext (hcomposite q hp)
    simp [primeFourierCoeff,additiveTransform,he]

theorem periodic_prime_family_interval_energy {Q N : Nat}
    (hQ : 0 < Q) (hN : 0 < N) (M : Nat)
    (f : (q : BoundedModulus Q) -> ZMod q.val -> Complex)
    (hmean : forall q, (Finset.univ.sum (f q))=0)
    (hcomposite : forall q, Not (Nat.Prime q.val) -> forall x, f q x=0) :
    (Finset.univ.sum fun n : Fin N =>
      norm ((Finset.Icc 1 Q).attach.sum fun q =>
        f q ((M+n.val : Nat) : ZMod q.val))^2) <=
      36*((N : Real)+(Q : Real)^2)*
        ((Finset.Icc 1 Q).attach.sum fun q =>
          (1/(q.val : Real))*(Finset.univ.sum fun x : ZMod q.val => norm (f q x)^2)) := by
  have hp := shifted_farey_dual_energy hQ hN M (familyCoefficient f)
  simp_rw [family_reconstruction f hmean hcomposite] at hp
  have he := family_coefficient_energy f
  have hc : 0 <= 36*((N : Real)+(Q : Real)^2) :=
    mul_nonneg (by norm_num) (add_nonneg (Nat.cast_nonneg N) (sq_nonneg _))
  exact le_trans hp (mul_le_mul_of_nonneg_left he hc)

def tailCorrection {Q : Nat} (K : Nat) (h : Int)
    (q : BoundedModulus Q) (c : ZMod q.val) : Real :=
  if hp : Nat.Prime q.val then
    letI : Fact (Nat.Prime q.val) := Fact.mk hp
    if K<q.val /\ Not ((h : ZMod q.val)=0)
      then _root_.FiniteField.QuadraticPairTwistLikelihood.localCorrection c (h : ZMod q.val)
      else 0
  else 0

def tailLinearSum (K : Nat) (h : Int) (Q n : Nat) : Real :=
  (Finset.Icc 1 Q).attach.sum
    (fun q => tailCorrection K h q (n : ZMod q.val))

theorem tail_correction_mean_zero {Q : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (q : BoundedModulus Q) :
    (Finset.univ.sum fun c : ZMod q.val => tailCorrection K h q c)=0 := by
  by_cases hp : Nat.Prime q.val
  . letI : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hg : K<q.val /\ Not ((h : ZMod q.val)=0)
    . have hp7 : 7<=q.val := by omega
      have hF : Not (ringChar (ZMod q.val)=2) := by
        rw [ringChar.eq (ZMod q.val) q.val]
        omega
      have hq7 : (7 : Real)<=(Fintype.card (ZMod q.val) : Real) := by
        rw [ZMod.card]
        exact_mod_cast hp7
      simp only [tailCorrection,dif_pos hp,if_pos hg]
      exact _root_.FiniteField.QuadraticPairTwistLikelihood.local_correction_mean_zero
        hF (h : ZMod q.val) hg.2 hq7
    . simp [tailCorrection,hp,hg]
  . simp [tailCorrection,hp]

theorem tail_correction_composite {Q : Nat} (K : Nat) (h : Int)
    (q : BoundedModulus Q) (hp : Not (Nat.Prime q.val)) (c : ZMod q.val) :
    tailCorrection K h q c=0 := by
  simp [tailCorrection,hp]

theorem tail_correction_variance_le {Q : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (q : BoundedModulus Q) :
    (1/(q.val : Real))*(Finset.univ.sum fun c : ZMod q.val =>
      (tailCorrection K h q c)^2) <=
        if K<q.val then 5/(q.val : Real)^2 else 0 := by
  by_cases hp : Nat.Prime q.val
  . letI : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hg : K<q.val /\ Not ((h : ZMod q.val)=0)
    . have hp7 : 7<=q.val := by omega
      have hF : Not (ringChar (ZMod q.val)=2) := by
        rw [ringChar.eq (ZMod q.val) q.val]
        omega
      have hq7 : (7 : Real)<=(Fintype.card (ZMod q.val) : Real) := by
        rw [ZMod.card]
        exact_mod_cast hp7
      simp only [tailCorrection,dif_pos hp,if_pos hg,if_pos hg.1]
      simpa only [ZMod.card] using
        _root_.FiniteField.QuadraticPairTwistLikelihood.local_correction_variance_le
          hF (h : ZMod q.val) hg.2 hq7
    . simp only [tailCorrection,dif_pos hp,if_neg hg,zero_pow,
        Finset.sum_const_zero,mul_zero]
      split_ifs <;> norm_num <;> positivity
  . simp only [tailCorrection,dif_neg hp,zero_pow,Finset.sum_const_zero,mul_zero]
    split_ifs <;> norm_num <;> positivity

theorem tail_variance_sum_le {Q : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) :
    ((Finset.Icc 1 Q).attach.sum fun q =>
      (1/(q.val : Real))*(Finset.univ.sum fun c : ZMod q.val =>
        (tailCorrection K h q c)^2)) <= 5/(K : Real) := by
  calc
    _ <= (Finset.Icc 1 Q).attach.sum
        (fun q => if K<q.val then 5/(q.val : Real)^2 else 0) := by
      apply Finset.sum_le_sum
      intro q _
      exact tail_correction_variance_le K h hK q
    _ = 5*((Finset.Ico (K+1) (Q+1)).sum fun p => (1 : Real)/(p : Real)^2) := by
      rw [show (Finset.Icc 1 Q).attach.sum
          (fun q => if K<q.val then (5 : Real)/(q.val : Real)^2 else 0) =
          (Finset.Icc 1 Q).sum (fun p => if K<p then (5 : Real)/(p : Real)^2 else 0)
        from Finset.sum_attach (Finset.Icc 1 Q)
          (fun p : Nat => if K<p then (5 : Real)/(p : Real)^2 else 0)]
      rw [<- Finset.sum_filter]
      have he : (Finset.Icc 1 Q).filter (fun p => K<p)=Finset.Ico (K+1) (Q+1) := by
        ext p
        simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ico]
        omega
      rw [he,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ <= 5*(1/(K : Real)) := mul_le_mul_of_nonneg_left
      (_root_.FiniteField.QuadraticPairEuler.sum_inverse_square_tail K Q
        (by omega) hKQ (Finset.Ico (K+1) (Q+1)) (le_refl _)) (by norm_num)
    _ = _ := by ring

theorem tail_linear_interval_energy {Q N : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat) :
    (Finset.univ.sum fun j : Fin N =>
      (tailLinearSum K h Q (M+1+j.val))^2) <=
        180*((N : Real)+(Q : Real)^2)/(K : Real) := by
  let f : (q : BoundedModulus Q) -> ZMod q.val -> Complex :=
    fun q c => (tailCorrection K h q c : Complex)
  have hm : forall q, (Finset.univ.sum (f q))=0 := by
    intro q
    dsimp only [f]
    rw [<- Complex.ofReal_sum,tail_correction_mean_zero K h hK q]
    rfl
  have hc : forall q, Not (Nat.Prime q.val) -> forall c, f q c=0 := by
    intro q hp c
    simp only [f,tail_correction_composite K h q hp c,Complex.ofReal_zero]
  have he := periodic_prime_family_interval_energy (show 0<Q from by omega)
    hN (M+1) f hm hc
  have hv := tail_variance_sum_le K h hK hKQ
  have hreal : forall z : Real, norm (z : Complex)^2=z^2 := by
    intro z
    simp
  simp only [f,<- Complex.ofReal_sum,hreal] at he
  change (Finset.univ.sum fun j : Fin N =>
      (tailLinearSum K h Q (M+1+j.val))^2) <= _ at he
  calc
    _ <= 36*((N : Real)+(Q : Real)^2)*
      ((Finset.Icc 1 Q).attach.sum fun q =>
        (1/(q.val : Real))*(Finset.univ.sum fun c : ZMod q.val =>
          (tailCorrection K h q c)^2)) := he
    _ <= 36*((N : Real)+(Q : Real)^2)*(5/(K : Real)) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by ring

theorem tail_correction_abs_le {Q : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (q : BoundedModulus Q) (c : ZMod q.val) :
    abs (tailCorrection K h q c) <= if K<q.val then 3/(q.val : Real) else 0 := by
  by_cases hp : Nat.Prime q.val
  . letI : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hg : K<q.val /\ Not ((h : ZMod q.val)=0)
    . have hq7 : (7 : Real)<=(Fintype.card (ZMod q.val) : Real) := by
        rw [ZMod.card]
        exact_mod_cast (show 7<=q.val from by omega)
      simp only [tailCorrection,dif_pos hp,if_pos hg,if_pos hg.1]
      simpa only [ZMod.card] using
        _root_.FiniteField.QuadraticPairTwistLikelihood.local_correction_abs_le
          c (h : ZMod q.val) hg.2 hq7
    . simp only [tailCorrection,dif_pos hp,if_neg hg]
      split_ifs <;> norm_num <;> positivity
  . simp only [tailCorrection,dif_neg hp]
    split_ifs <;> norm_num <;> positivity

theorem tail_correction_abs_half {Q : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (q : BoundedModulus Q) (c : ZMod q.val) :
    abs (tailCorrection K h q c)<=1/2 := by
  have ha := tail_correction_abs_le K h hK q c
  by_cases hp : K<q.val
  . rw [if_pos hp] at ha
    have hq : (7 : Real)<=(q.val : Real) := by exact_mod_cast (show 7<=q.val from by omega)
    calc
      _ <= 3/(q.val : Real) := ha
      _ <= (3 : Real)/7 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq
      _ <= _ := by norm_num
  . rw [if_neg hp] at ha
    linarith only [ha]

theorem tail_envelope_sum_le {Q : Nat} (K : Nat) (hK : 6<=K)
    (hKQ : K<=Q) (B : Real) (hB : 0<=B) :
    ((Finset.Icc 1 Q).attach.sum fun q =>
      if K<q.val then B/(q.val : Real)^2 else 0) <= B/(K : Real) := by
  calc
    _ = B*((Finset.Ico (K+1) (Q+1)).sum fun p => (1 : Real)/(p : Real)^2) := by
      rw [show (Finset.Icc 1 Q).attach.sum
          (fun q => if K<q.val then B/(q.val : Real)^2 else 0) =
          (Finset.Icc 1 Q).sum (fun p => if K<p then B/(p : Real)^2 else 0)
        from Finset.sum_attach (Finset.Icc 1 Q)
          (fun p : Nat => if K<p then B/(p : Real)^2 else 0)]
      rw [<- Finset.sum_filter]
      have he : (Finset.Icc 1 Q).filter (fun p => K<p)=Finset.Ico (K+1) (Q+1) := by
        ext p
        simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ico]
        omega
      rw [he,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ <= B*(1/(K : Real)) := mul_le_mul_of_nonneg_left
      (_root_.FiniteField.QuadraticPairEuler.sum_inverse_square_tail K Q
        (by omega) hKQ (Finset.Ico (K+1) (Q+1)) (le_refl _)) hB
    _ = _ := by ring

theorem tail_square_sum_le {Q : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) (n : Nat) :
    ((Finset.Icc 1 Q).attach.sum fun q =>
      (tailCorrection K h q (n : ZMod q.val))^2) <= 9/(K : Real) := by
  apply le_trans _ (tail_envelope_sum_le K hK hKQ 9 (by norm_num))
  apply Finset.sum_le_sum
  intro q _
  have ha := tail_correction_abs_le K h hK q (n : ZMod q.val)
  by_cases hp : K<q.val
  . rw [if_pos hp] at ha
    rw [if_pos hp]
    have hr : 0<=3/(q.val : Real) := by positivity
    have hab := abs_le.mp ha
    have hs : (tailCorrection K h q (n : ZMod q.val))^2<=(3/(q.val : Real))^2 := by
      nlinarith only [hab.1,hab.2,mul_nonneg
        (sub_nonneg.mpr hab.2) (show 0<=3/(q.val : Real)+
          tailCorrection K h q (n : ZMod q.val) from by linarith only [hab.1])]
    calc
      _ <= (3/(q.val : Real))^2 := hs
      _ = _ := by ring
  . rw [if_neg hp] at ha
    rw [if_neg hp]
    have hz := abs_eq_zero.mp (le_antisymm ha (abs_nonneg _))
    rw [hz]
    norm_num

def tailLogSum (K : Nat) (h : Int) (Q n : Nat) : Real :=
  (Finset.Icc 1 Q).attach.sum
    (fun q => Real.log (1+tailCorrection K h q (n : ZMod q.val)))

def tailRatio (K : Nat) (h : Int) (Q n : Nat) : Real :=
  (Finset.Icc 1 Q).attach.prod
    (fun q => 1+tailCorrection K h q (n : ZMod q.val))

theorem tail_ratio_exp_log (K : Nat) (h : Int) (hK : 6<=K) (Q n : Nat) :
    tailRatio K h Q n=Real.exp (tailLogSum K h Q n) := by
  unfold tailRatio tailLogSum
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro q _
  symm
  apply Real.exp_log
  have hb := abs_le.mp (tail_correction_abs_half K h hK q (n : ZMod q.val))
  linarith only [hb.1]

theorem tail_log_remainder_le {Q : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) (n : Nat) :
    abs (tailLogSum K h Q n-tailLinearSum K h Q n)<=18/(K : Real) := by
  unfold tailLogSum tailLinearSum
  rw [<- Finset.sum_sub_distrib]
  calc
    _ <= (Finset.Icc 1 Q).attach.sum
        (fun q => abs (Real.log (1+tailCorrection K h q (n : ZMod q.val))-
          tailCorrection K h q (n : ZMod q.val))) := Finset.abs_sum_le_sum_abs _ _
    _ <= (Finset.Icc 1 Q).attach.sum
        (fun q => 2*(tailCorrection K h q (n : ZMod q.val))^2) := by
      apply Finset.sum_le_sum
      intro q _
      exact abs_log_one_add_sub_self_le _ (tail_correction_abs_half K h hK q _)
    _ = 2*((Finset.Icc 1 Q).attach.sum
        (fun q => (tailCorrection K h q (n : ZMod q.val))^2)) := by
      rw [Finset.mul_sum]
    _ <= 2*(9/(K : Real)) :=
      mul_le_mul_of_nonneg_left (tail_square_sum_le K h hK hKQ n) (by norm_num)
    _ = _ := by ring

theorem tail_log_interval_energy {Q N : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat) :
    (Finset.univ.sum fun j : Fin N =>
      (tailLogSum K h Q (M+1+j.val))^2) <=
        500*((N : Real)+(Q : Real)^2)/(K : Real) := by
  have hKr : (6 : Real)<=(K : Real) := by exact_mod_cast hK
  have hK0 : 0<(K : Real) := by linarith only [hKr]
  have he := tail_linear_interval_energy K h hK hKQ hN M
  have hs : (Finset.univ.sum fun j : Fin N =>
      (tailLogSum K h Q (M+1+j.val))^2) <=
      2*(Finset.univ.sum fun j : Fin N =>
        (tailLinearSum K h Q (M+1+j.val))^2)+
          (N : Real)*(648/(K : Real)^2) := by
    calc
      _ <= Finset.univ.sum (fun j : Fin N =>
          2*(tailLinearSum K h Q (M+1+j.val))^2+648/(K : Real)^2) := by
        apply Finset.sum_le_sum
        intro j _
        have hb := abs_le.mp (tail_log_remainder_le K h hK hKQ (M+1+j.val))
        have hr : 0<=18/(K : Real) := by positivity
        have hsq : (tailLogSum K h Q (M+1+j.val)-
            tailLinearSum K h Q (M+1+j.val))^2<=(18/(K : Real))^2 := by
          nlinarith only [mul_nonneg
            (sub_nonneg.mpr hb.2) (show 0<=18/(K : Real)+
              (tailLogSum K h Q (M+1+j.val)-
              tailLinearSum K h Q (M+1+j.val)) from by linarith only [hb.1])]
        have hi := sq_nonneg (tailLogSum K h Q (M+1+j.val)-
          2*tailLinearSum K h Q (M+1+j.val))
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
        108*((N : Real)+(Q : Real)^2)/(K : Real) :=
      le_trans hs (add_le_add ht hrem)
    _ = 468*(((N : Real)+(Q : Real)^2)/(K : Real)) := by ring
    _ <= 500*(((N : Real)+(Q : Real)^2)/(K : Real)) :=
      mul_le_mul_of_nonneg_right (by norm_num) hp
    _ = _ := by ring

def tailBadIndices {N : Nat} (K : Nat) (h : Int) (Q M : Nat)
    (epsilon : Real) : Finset (Fin N) :=
  Finset.univ.filter (fun j => epsilon<abs (tailLogSum K h Q (M+1+j.val)))

theorem tail_bad_card_bound {Q N : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat)
    (epsilon : Real) (heps : 0<epsilon) :
    ((tailBadIndices (N:=N) K h Q M epsilon).card : Real)*epsilon^2 <=
      500*((N : Real)+(Q : Real)^2)/(K : Real) := by
  apply le_trans _ (tail_log_interval_energy K h hK hKQ hN M)
  calc
    _ = (tailBadIndices (N:=N) K h Q M epsilon).sum
        (fun _ => epsilon^2) := by simp
    _ <= (tailBadIndices (N:=N) K h Q M epsilon).sum
        (fun j => (tailLogSum K h Q (M+1+j.val))^2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hh : epsilon<abs (tailLogSum K h Q (M+1+j.val)) :=
        (Finset.mem_filter.mp hj).2
      nlinarith only [sq_abs (tailLogSum K h Q (M+1+j.val)),
        mul_nonneg (sub_nonneg.mpr (le_of_lt hh))
          (show 0<=abs (tailLogSum K h Q (M+1+j.val))+epsilon from by positivity)]
    _ <= _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      . exact Finset.filter_subset _ _
      . intro j _ _
        exact sq_nonneg _

theorem tail_ratio_bounds (K : Nat) (h : Int) (hK : 6<=K) (Q n : Nat)
    (epsilon : Real) (hg : abs (tailLogSum K h Q n)<=epsilon) :
    Real.exp (-epsilon)<=tailRatio K h Q n /\
      tailRatio K h Q n<=Real.exp epsilon := by
  rw [tail_ratio_exp_log K h hK Q n]
  exact And.intro (Real.exp_le_exp.mpr (abs_le.mp hg).1)
    (Real.exp_le_exp.mpr (abs_le.mp hg).2)

def tailActualLocal {Q : Nat} (K : Nat) (h : Int)
    (q : BoundedModulus Q) (c : ZMod q.val) : Real :=
  if hp : Nat.Prime q.val then
    letI : Fact (Nat.Prime q.val) := Fact.mk hp
    if K<q.val /\ Not ((h : ZMod q.val)=0)
      then _root_.FiniteField.traceFreePairWeight c (h : ZMod q.val)
      else 1
  else 1

def tailFlatLocal {Q : Nat} (K : Nat) (h : Int)
    (q : BoundedModulus Q) (c : ZMod q.val) : Real :=
  if hp : Nat.Prime q.val then
    letI : Fact (Nat.Prime q.val) := Fact.mk hp
    if K<q.val /\ Not ((h : ZMod q.val)=0)
      then _root_.FiniteField.QuadraticPairTwistLikelihood.flatPairWeight c (h : ZMod q.val)
      else 1
  else 1

theorem tail_local_factorization {Q : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (q : BoundedModulus Q) (c : ZMod q.val) :
    tailActualLocal K h q c=tailFlatLocal K h q c*(1+tailCorrection K h q c) := by
  by_cases hp : Nat.Prime q.val
  . letI : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hg : K<q.val /\ Not ((h : ZMod q.val)=0)
    . have hq7 : (7 : Real)<=(Fintype.card (ZMod q.val) : Real) := by
        rw [ZMod.card]
        exact_mod_cast (show 7<=q.val from by omega)
      simp only [tailActualLocal,tailFlatLocal,tailCorrection,dif_pos hp,if_pos hg]
      exact _root_.FiniteField.QuadraticPairTwistLikelihood.local_factorization c
        (h : ZMod q.val) hq7
    . simp [tailActualLocal,tailFlatLocal,tailCorrection,hp,hg]
  . simp [tailActualLocal,tailFlatLocal,tailCorrection,hp]

theorem tail_flat_local_nonneg {Q : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (q : BoundedModulus Q) (c : ZMod q.val) :
    0<=tailFlatLocal K h q c := by
  by_cases hp : Nat.Prime q.val
  . letI : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hg : K<q.val /\ Not ((h : ZMod q.val)=0)
    . have hq7 : (7 : Real)<=(Fintype.card (ZMod q.val) : Real) := by
        rw [ZMod.card]
        exact_mod_cast (show 7<=q.val from by omega)
      simp only [tailFlatLocal,dif_pos hp,if_pos hg]
      unfold _root_.FiniteField.QuadraticPairTwistLikelihood.flatPairWeight
      apply mul_nonneg
      . apply div_nonneg (Nat.cast_nonneg _)
        linarith only [hq7]
      . unfold _root_.FiniteField.QuadraticPairTwistLikelihood.admissibilityMask
        split_ifs <;> norm_num
    . simp [tailFlatLocal,hp,hg]
  . simp [tailFlatLocal,hp]

def tailActualPacket (K : Nat) (h : Int) (Q n : Nat) : Real :=
  (Finset.Icc 1 Q).attach.prod
    (fun q => tailActualLocal K h q (n : ZMod q.val))

def tailFlatPacket (K : Nat) (h : Int) (Q n : Nat) : Real :=
  (Finset.Icc 1 Q).attach.prod
    (fun q => tailFlatLocal K h q (n : ZMod q.val))

theorem tail_packet_factorization (K : Nat) (h : Int) (hK : 6<=K) (Q n : Nat) :
    tailActualPacket K h Q n=tailFlatPacket K h Q n*tailRatio K h Q n := by
  unfold tailActualPacket tailFlatPacket tailRatio
  simp_rw [tail_local_factorization K h hK]
  rw [Finset.prod_mul_distrib]

theorem tail_flat_packet_nonneg (K : Nat) (h : Int) (hK : 6<=K) (Q n : Nat) :
    0<=tailFlatPacket K h Q n := by
  apply Finset.prod_nonneg
  intro q _
  exact tail_flat_local_nonneg K h hK q _

theorem full_packet_comparison (K : Nat) (h : Int) (hK : 6<=K) (Q n : Nat)
    (epsilon A : Real) (hA : 0<=A)
    (hg : abs (tailLogSum K h Q n)<=epsilon) :
    Real.exp (-epsilon)*(A*tailFlatPacket K h Q n)<=A*tailActualPacket K h Q n /\
      A*tailActualPacket K h Q n<=Real.exp epsilon*(A*tailFlatPacket K h Q n) := by
  have hb := tail_ratio_bounds K h hK Q n epsilon hg
  have hn : 0<=A*tailFlatPacket K h Q n :=
    mul_nonneg hA (tail_flat_packet_nonneg K h hK Q n)
  rw [tail_packet_factorization K h hK Q n]
  constructor
  . calc
      _ = (A*tailFlatPacket K h Q n)*Real.exp (-epsilon) := by ring
      _ <= (A*tailFlatPacket K h Q n)*tailRatio K h Q n :=
        mul_le_mul_of_nonneg_left hb.1 hn
      _ = _ := by ring
  . calc
      _ = (A*tailFlatPacket K h Q n)*tailRatio K h Q n := by ring
      _ <= (A*tailFlatPacket K h Q n)*Real.exp epsilon :=
        mul_le_mul_of_nonneg_left hb.2 hn
      _ = _ := by ring

theorem full_packet_mass_lower {N : Nat} (K : Nat) (h : Int) (hK : 6<=K)
    (Q M : Nat) (epsilon : Real) (A : Fin N -> Real)
    (hA : forall j, 0<=A j) :
    Real.exp (-epsilon)*
      ((Finset.univ.sum fun j : Fin N => A j*tailFlatPacket K h Q (M+1+j.val))-
       ((tailBadIndices (N:=N) K h Q M epsilon).sum fun j =>
         A j*tailFlatPacket K h Q (M+1+j.val))) <=
      (Finset.univ.sum fun j : Fin N => A j*tailActualPacket K h Q (M+1+j.val)) := by
  have hp : forall j : Fin N,
      Real.exp (-epsilon)*(A j*tailFlatPacket K h Q (M+1+j.val))-
        (if epsilon<abs (tailLogSum K h Q (M+1+j.val))
          then Real.exp (-epsilon)*(A j*tailFlatPacket K h Q (M+1+j.val)) else 0) <=
      A j*tailActualPacket K h Q (M+1+j.val) := by
    intro j
    by_cases hb : epsilon<abs (tailLogSum K h Q (M+1+j.val))
    . rw [if_pos hb,sub_self,tail_packet_factorization K h hK,
        tail_ratio_exp_log K h hK]
      exact mul_nonneg (hA j) (mul_nonneg
        (tail_flat_packet_nonneg K h hK Q _) (Real.exp_pos _).le)
    . rw [if_neg hb,sub_zero]
      exact (full_packet_comparison K h hK Q _ epsilon (A j) (hA j)
        (le_of_not_gt hb)).1
  have hs := Finset.sum_le_sum (fun j (_ : Membership.mem (Finset.univ : Finset (Fin N)) j) => hp j)
  rw [Finset.sum_sub_distrib,<- Finset.mul_sum] at hs
  have hf :
      (Finset.univ.sum fun j : Fin N =>
        if epsilon<abs (tailLogSum K h Q (M+1+j.val))
          then Real.exp (-epsilon)*(A j*tailFlatPacket K h Q (M+1+j.val)) else 0)=
      Real.exp (-epsilon)*((tailBadIndices (N:=N) K h Q M epsilon).sum fun j =>
        A j*tailFlatPacket K h Q (M+1+j.val)) := by
    rw [<- Finset.sum_filter,Finset.mul_sum]
    rfl
  rw [hf] at hs
  calc
    _ = Real.exp (-epsilon)*(Finset.univ.sum fun j : Fin N =>
        A j*tailFlatPacket K h Q (M+1+j.val))-
        Real.exp (-epsilon)*((tailBadIndices (N:=N) K h Q M epsilon).sum fun j =>
          A j*tailFlatPacket K h Q (M+1+j.val)) := by ring
    _ <= _ := hs

theorem tail_bad_card_bound_div {Q N : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat)
    (epsilon : Real) (heps : 0<epsilon) :
    ((tailBadIndices (N:=N) K h Q M epsilon).card : Real) <=
      (500*((N : Real)+(Q : Real)^2)/(K : Real))/epsilon^2 := by
  have hb := tail_bad_card_bound K h hK hKQ hN M epsilon heps
  have he2 : 0<epsilon^2 := sq_pos_of_pos heps
  have he0 : Not (epsilon^2=0) := ne_of_gt he2
  have hid : ((500*((N : Real)+(Q : Real)^2)/(K : Real))/epsilon^2)*epsilon^2 =
      500*((N : Real)+(Q : Real)^2)/(K : Real) := by field_simp
  have hm : ((tailBadIndices (N:=N) K h Q M epsilon).card : Real)*epsilon^2 <=
      ((500*((N : Real)+(Q : Real)^2)/(K : Real))/epsilon^2)*epsilon^2 := by
    rw [hid]
    exact hb
  by_contra hn
  have ht : 0<(((tailBadIndices (N:=N) K h Q M epsilon).card : Real)-
      (500*((N : Real)+(Q : Real)^2)/(K : Real))/epsilon^2)*epsilon^2 :=
    mul_pos (sub_pos.mpr (lt_of_not_ge hn)) he2
  nlinarith only [ht,hm]

theorem critical_tail_log_interval_energy {Q N : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat)
    (hcritical : (Q : Real)^2<=3*(N : Real)) :
    (Finset.univ.sum fun j : Fin N =>
      (tailLogSum K h Q (M+1+j.val))^2) <= 2000*(N : Real)/(K : Real) := by
  calc
    _ <= 500*((N : Real)+(Q : Real)^2)/(K : Real) :=
      tail_log_interval_energy K h hK hKQ hN M
    _ <= 500*((N : Real)+3*(N : Real))/(K : Real) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (show (N : Real)+(Q : Real)^2<=(N : Real)+3*(N : Real) from by linarith only [hcritical]) (by norm_num))
        (Nat.cast_nonneg K)
    _ = _ := by ring

end PrimeFactorOscillations.FiniteFieldIntegerTail

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFSieveLocal

/-! # Coprime CRT frequencies for products of local sieve certificates -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def sieveFrequencyEquiv {m n : Nat} (h : Nat.Coprime m n) :
    Equiv (Prod (ZMod m) (ZMod n)) (ZMod (m * n)) :=
  let e := ZMod.chineseRemainder h
  let u := ZMod.unitOfCoprime n h.symm
  let v := ZMod.unitOfCoprime m h
  { toFun := fun x => e.symm ((u : ZMod m) * x.1, (v : ZMod n) * x.2)
    invFun := fun y =>
      (((Inv.inv u : Units (ZMod m)) : ZMod m) * (e y).1,
       ((Inv.inv v : Units (ZMod n)) : ZMod n) * (e y).2)
    left_inv := by
      intro x
      simp [<- mul_assoc]
    right_inv := by
      intro y
      apply e.injective
      simp [<- mul_assoc] }

theorem sieveFrequencyEquiv_crt {m n : Nat} (h : Nat.Coprime m n)
    (a : ZMod m) (b : ZMod n) :
    ZMod.chineseRemainder h (sieveFrequencyEquiv h (a, b)) =
      ((n : ZMod m) * a, (m : ZMod n) * b) := by
  change ZMod.chineseRemainder h ((ZMod.chineseRemainder h).symm
    (((ZMod.unitOfCoprime n h.symm : Units (ZMod m)) : ZMod m) * a,
     ((ZMod.unitOfCoprime m h : Units (ZMod n)) : ZMod n) * b)) = _
  rw [(ZMod.chineseRemainder h).apply_symm_apply]
  rfl

theorem sieveFrequencyEquiv_apply_nat {m n : Nat} [NeZero m] [NeZero n]
    (h : Nat.Coprime m n) (a : ZMod m) (b : ZMod n) :
    sieveFrequencyEquiv h (a, b) = ((a.val * n + b.val * m : Nat) : ZMod (m * n)) := by
  apply (ZMod.chineseRemainder h).injective
  rw [sieveFrequencyEquiv_crt, map_natCast]
  apply Prod.ext <;> simp [mul_comm]

private theorem stdAddChar_nat {q : Nat} [NeZero q] (j : Nat) :
    ZMod.stdAddChar (j : ZMod q) =
      Complex.exp (2 * (Real.pi : Complex) * Complex.I * (j : Complex) / (q : Complex)) := by
  simpa only [Int.cast_natCast] using (ZMod.stdAddChar_coe (N := q) (j : Int))

private theorem stdAddChar_mul_nat {q : Nat} [NeZero q] (a : ZMod q) (k : Nat) :
    ZMod.stdAddChar (a * (k : ZMod q)) =
      Complex.exp (2 * (Real.pi : Complex) * Complex.I * (a.val : Complex) *
        (k : Complex) / (q : Complex)) := by
  have h := stdAddChar_nat (q := q) (a.val * k)
  simpa only [Nat.cast_mul, ZMod.natCast_zmod_val, mul_assoc] using h

theorem sieveFrequencyEquiv_phase {m n : Nat} [NeZero m] [NeZero n]
    (h : Nat.Coprime m n) (a : ZMod m) (b : ZMod n) (k : Nat) :
    ZMod.stdAddChar (sieveFrequencyEquiv h (a, b) * (k : ZMod (m * n))) =
      ZMod.stdAddChar (a * (k : ZMod m)) * ZMod.stdAddChar (b * (k : ZMod n)) := by
  have hm : Not ((m : Complex) = 0) := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hn : Not ((n : Complex) = 0) := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [sieveFrequencyEquiv_apply_nat, <- Nat.cast_mul, stdAddChar_nat,
    stdAddChar_mul_nat, stdAddChar_mul_nat, <- Complex.exp_add]
  congr 1
  push_cast
  field_simp <;> ring

private theorem isUnit_unit_mul_iff {R : Type*} [CommMonoid R] (u : Units R) (a : R) :
    IsUnit ((u : R) * a) <-> IsUnit a := by
  constructor
  next =>
    intro ha
    choose b hb using (isUnit_iff_exists_inv.mp ha)
    apply isUnit_iff_exists_inv.mpr
    refine Exists.intro ((u : R) * b) ?_
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
  next =>
    intro ha
    exact (show IsUnit (u : R) from Exists.intro u rfl).mul ha

theorem sieveFrequencyEquiv_isUnit {m n : Nat} (h : Nat.Coprime m n)
    (a : ZMod m) (b : ZMod n) :
    IsUnit (sieveFrequencyEquiv h (a, b)) <-> And (IsUnit a) (IsUnit b) := by
  rw [<- MulEquiv.isUnit_map (ZMod.chineseRemainder h), sieveFrequencyEquiv_crt, Prod.isUnit_iff]
  exact and_congr (isUnit_unit_mul_iff (ZMod.unitOfCoprime n h.symm) a)
    (isUnit_unit_mul_iff (ZMod.unitOfCoprime m h) b)

noncomputable def sieveTensorCoefficient {m n : Nat} (h : Nat.Coprime m n)
    (c : ZMod m -> Complex) (d : ZMod n -> Complex) (a : ZMod (m * n)) : Complex :=
  let x := (sieveFrequencyEquiv h).symm a
  c x.1 * d x.2

theorem sieveTensorCoefficient_reconstruct {m n : Nat} [NeZero m] [NeZero n]
    (h : Nat.Coprime m n) (c : ZMod m -> Complex) (d : ZMod n -> Complex) (k : Nat) :
    Finset.sum Finset.univ (fun a => sieveTensorCoefficient h c d a *
      ZMod.stdAddChar (a * (k : ZMod (m * n)))) =
        (Finset.sum Finset.univ (fun a => c a * ZMod.stdAddChar (a * (k : ZMod m)))) *
        (Finset.sum Finset.univ (fun b => d b * ZMod.stdAddChar (b * (k : ZMod n)))) := by
  classical
  calc
    _ = Finset.sum Finset.univ (fun x : Prod (ZMod m) (ZMod n) =>
        sieveTensorCoefficient h c d (sieveFrequencyEquiv h x) *
          ZMod.stdAddChar (sieveFrequencyEquiv h x * (k : ZMod (m * n)))) :=
      (Equiv.sum_comp (sieveFrequencyEquiv h) _).symm
    _ = _ := by
      simp only [sieveTensorCoefficient, Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type]
      simp only [sieveFrequencyEquiv_phase]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

theorem sieveTensorCoefficient_normSq_sum {m n : Nat} [NeZero m] [NeZero n]
    (h : Nat.Coprime m n) (c : ZMod m -> Complex) (d : ZMod n -> Complex) :
    Finset.sum Finset.univ (fun a => Complex.normSq (sieveTensorCoefficient h c d a)) =
      (Finset.sum Finset.univ (fun a => Complex.normSq (c a))) *
      (Finset.sum Finset.univ (fun b => Complex.normSq (d b))) := by
  classical
  calc
    _ = Finset.sum Finset.univ (fun x : Prod (ZMod m) (ZMod n) =>
        Complex.normSq (sieveTensorCoefficient h c d (sieveFrequencyEquiv h x))) :=
      (Equiv.sum_comp (sieveFrequencyEquiv h) _).symm
    _ = _ := by
      simp only [sieveTensorCoefficient, Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type]
      simp only [Complex.normSq_eq_norm_sq, norm_mul, mul_pow]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]

theorem sieveTensorCoefficient_eq_zero_of_not_isUnit {m n : Nat}
    (h : Nat.Coprime m n) (c : ZMod m -> Complex) (d : ZMod n -> Complex)
    (hc : forall a, Not (IsUnit a) -> c a = 0)
    (hd : forall b, Not (IsUnit b) -> d b = 0)
    (a : ZMod (m * n)) (ha : Not (IsUnit a)) : sieveTensorCoefficient h c d a = 0 := by
  let x := (sieveFrequencyEquiv h).symm a
  have hNotBoth : Not (And (IsUnit x.1) (IsUnit x.2)) := by
    intro hBoth
    have hUnit := (sieveFrequencyEquiv_isUnit h x.1 x.2).mpr hBoth
    have hEq : sieveFrequencyEquiv h (x.1, x.2) = a := by
      change sieveFrequencyEquiv h ((sieveFrequencyEquiv h).symm a) = a
      exact (sieveFrequencyEquiv h).apply_symm_apply a
    rw [hEq] at hUnit
    exact ha hUnit
  change c x.1 * d x.2 = 0
  by_cases hFirst : IsUnit x.1
  next =>
    have hSecond : Not (IsUnit x.2) := fun hb => hNotBoth (And.intro hFirst hb)
    rw [hd x.2 hSecond, mul_zero]
  next => rw [hc x.1 hFirst, zero_mul]

private theorem localSieve_full_certificate {q : Nat} [NeZero q]
    (A : Finset (ZMod q)) (hA : 0 < A.card) (k : Nat)
    (hk : Not (Membership.mem A (k : ZMod q))) :
    Finset.sum Finset.univ (fun a => localSieveCoefficient A a *
      ZMod.stdAddChar (a * (k : ZMod q))) = 1 := by
  classical
  have h := Finset.sum_erase_add Finset.univ
    (fun a => localSieveCoefficient A a * ZMod.stdAddChar (a * (k : ZMod q)))
    (Finset.mem_univ (0 : ZMod q))
  rw [localSieveCoefficient_zero A hA, zero_mul, add_zero] at h
  exact h.symm.trans (localSieveCertificate A hA (k : ZMod q) hk)

/-- A constructed certificate for every finite set of distinct prime moduli.
Its support is primitive even at a composite product; the empty product is 1. -/
theorem exists_sieveProductCertificate (P : Finset Nat) (A : (p : Nat) -> Finset (ZMod p)) :
    forall [NeZero (Finset.prod P (fun p => p))],
    (forall p, Membership.mem P p -> Nat.Prime p) ->
    (forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p)) ->
    exists c : ZMod (Finset.prod P (fun p => p)) -> Complex,
      And (forall a, Not (IsUnit a) -> c a = 0)
        (And (Finset.sum Finset.univ (fun a => Complex.normSq (c a)) =
          Finset.prod P (fun p => ((p : Real) - ((A p).card : Real)) / ((A p).card : Real)))
          (forall k : Nat, (forall p, Membership.mem P p -> Not (Membership.mem (A p) (k : ZMod p))) ->
            Finset.sum Finset.univ (fun a => c a *
              ZMod.stdAddChar (a * (k : ZMod (Finset.prod P (fun p => p))))) = 1)) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro hNZ hPrime hA
    revert hNZ
    rw [Finset.prod_empty]
    intro hNZ
    refine Exists.intro (fun _ => (1 : Complex)) (And.intro ?_ (And.intro ?_ ?_))
    next =>
      intro a ha
      have ha1 : a = 1 := Subsingleton.elim _ _
      rw [ha1] at ha
      exact (ha isUnit_one).elim
    next => simp [Finset.card_univ, ZMod.card]
    next =>
      intro k hk
      have hZero : forall a : ZMod 1, a * (k : ZMod 1) = 0 := fun _ => Subsingleton.elim _ _
      simp [hZero, Finset.card_univ, ZMod.card]
  | @insert p P hpNot ih =>
    intro hNZ hPrime hA
    have hpPrime := hPrime p (Finset.mem_insert_self p P)
    have hpA := hA p (Finset.mem_insert_self p P)
    have hOldPrime : forall q, Membership.mem P q -> Nat.Prime q :=
      fun q hq => hPrime q (Finset.mem_insert_of_mem hq)
    have hOldA : forall q, Membership.mem P q -> And (0 < (A q).card) ((A q).card < q) :=
      fun q hq => hA q (Finset.mem_insert_of_mem hq)
    letI : NeZero p := NeZero.mk hpPrime.ne_zero
    have hProd : Not (Finset.prod P (fun q => q) = 0) :=
      Finset.prod_ne_zero_iff.mpr (fun q hq => (hOldPrime q hq).ne_zero)
    letI : NeZero (Finset.prod P (fun q => q)) := NeZero.mk hProd
    choose c hcUnit hcNorm hcReconstruct using ih hOldPrime hOldA
    have hCoprime : Nat.Coprime p (Finset.prod P (fun q => q)) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply (Nat.coprime_primes hpPrime (hOldPrime q hq)).mpr
      intro he
      apply hpNot
      rwa [he]
    revert hNZ
    rw [Finset.prod_insert hpNot]
    intro hNZ
    refine Exists.intro (sieveTensorCoefficient hCoprime (localSieveCoefficient (A p)) c)
      (And.intro ?_ (And.intro ?_ ?_))
    next =>
      intro a ha
      exact sieveTensorCoefficient_eq_zero_of_not_isUnit hCoprime _ _
        (localSieveCoefficient_eq_zero_of_not_isUnit hpPrime (A p) hpA.1) hcUnit a ha
    next =>
      rw [sieveTensorCoefficient_normSq_sum, localSieveCoefficient_normSq_sum (A p) hpA.1,
        hcNorm, Finset.prod_insert hpNot]
    next =>
      intro k hk
      rw [sieveTensorCoefficient_reconstruct,
        localSieve_full_certificate (A p) hpA.1 k (hk p (Finset.mem_insert_self p P)),
        hcReconstruct k (fun q hq => hk q (Finset.mem_insert_of_mem hq)), one_mul]

private theorem sum_units_eq_sum {q : Nat} [NeZero q] {R : Type*} [AddCommMonoid R]
    (f : ZMod q -> R) (hf : forall a, Not (IsUnit a) -> f a = 0) :
    Finset.sum (Finset.univ.filter (fun a : ZMod q => IsUnit a)) f = Finset.sum Finset.univ f := by
  classical
  apply Finset.sum_subset (fun a _ => Finset.mem_univ a)
  intro a ha hNot
  apply hf a
  intro hUnit
  exact hNot (Finset.mem_filter.mpr (And.intro (Finset.mem_univ a) hUnit))

private theorem primitive_energy_of_certificate {q : Nat} [NeZero q]
    (c : ZMod q -> Complex) (X : Finset Nat)
    (hc : forall a, Not (IsUnit a) -> c a = 0)
    (hCertificate : forall k, Membership.mem X k ->
      Finset.sum Finset.univ (fun a => c a * ZMod.stdAddChar (a * (k : ZMod q))) = 1) :
    (X.card : Real) ^ 2 <=
      (Finset.sum Finset.univ (fun a => Complex.normSq (c a))) *
      Finset.sum (Finset.univ.filter (fun a : ZMod q => IsUnit a))
        (fun a => norm (localSieveSample X a) ^ 2) := by
  classical
  let F : Finset (ZMod q) := Finset.univ.filter (fun a => IsUnit a)
  have hMass : Finset.sum F (fun a => c a * localSieveSample X a) = (X.card : Complex) := by
    simp only [localSieveSample, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = Finset.sum X (fun _ => (1 : Complex)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have h := sum_units_eq_sum (fun a : ZMod q => c a * ZMod.stdAddChar (a * (k : ZMod q)))
          (fun a ha => by rw [hc a ha, zero_mul])
        exact h.trans (hCertificate k hk)
      _ = _ := by simp
  have hTriangle : (X.card : Real) <= Finset.sum F
      (fun a => norm (c a) * norm (localSieveSample X a)) := by
    have h := norm_sum_le F (fun a => c a * localSieveSample X a)
    rw [hMass] at h
    simpa [norm_mul] using h
  have hNonneg : 0 <= Finset.sum F (fun a => norm (c a) * norm (localSieveSample X a)) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hSquare : (X.card : Real) ^ 2 <=
      (Finset.sum F (fun a => norm (c a) * norm (localSieveSample X a))) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hTriangle hTriangle (Nat.cast_nonneg X.card) hNonneg
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq F
    (fun a => norm (c a)) (fun a => norm (localSieveSample X a))
  have hNorm : Finset.sum F (fun a => norm (c a) ^ 2) =
      Finset.sum Finset.univ (fun a => Complex.normSq (c a)) := by
    have h := sum_units_eq_sum (fun a => Complex.normSq (c a))
      (fun a ha => by rw [hc a ha]; simp)
    simpa only [Complex.normSq_eq_norm_sq] using h
  rw [hNorm] at hCS
  exact hSquare.trans hCS

/-- Every squarefree product receives its full local sieve weight, with primitive support. -/
theorem sieveProduct_primitive_energy_lower_bound (P : Finset Nat)
    [NeZero (Finset.prod P (fun p => p))] (A : (p : Nat) -> Finset (ZMod p))
    (hPrime : forall p, Membership.mem P p -> Nat.Prime p)
    (hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p))
    (X : Finset Nat) (hAvoid : forall k, Membership.mem X k ->
      forall p, Membership.mem P p -> Not (Membership.mem (A p) (k : ZMod p))) :
    (Finset.prod P (fun p => ((A p).card : Real) / ((p : Real) - ((A p).card : Real)))) *
      (X.card : Real) ^ 2 <=
        Finset.sum (Finset.univ.filter (fun a : ZMod (Finset.prod P (fun p => p)) => IsUnit a))
          (fun a => norm (localSieveSample X a) ^ 2) := by
  classical
  choose c hcUnit hcNorm hcReconstruct using exists_sieveProductCertificate P A hPrime hA
  have hRaw := primitive_energy_of_certificate c X hcUnit
    (fun k hk => hcReconstruct k (hAvoid k hk))
  rw [hcNorm] at hRaw
  let H : Real := Finset.prod P (fun p => ((A p).card : Real) / ((p : Real) - ((A p).card : Real)))
  let E : Real := Finset.prod P (fun p => ((p : Real) - ((A p).card : Real)) / ((A p).card : Real))
  have hH : 0 <= H := by
    apply Finset.prod_nonneg
    intro p hp
    have hlt : ((A p).card : Real) < (p : Real) := by exact_mod_cast (hA p hp).2
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hCancel : H * E = 1 := by
    dsimp [H, E]
    rw [<- Finset.prod_mul_distrib]
    calc
      _ = Finset.prod P (fun _ => (1 : Real)) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hpos : (0 : Real) < ((A p).card : Real) := by exact_mod_cast (hA p hp).1
        have hlt : ((A p).card : Real) < (p : Real) := by exact_mod_cast (hA p hp).2
        have hdiff : 0 < (p : Real) - ((A p).card : Real) := by linarith
        field_simp
      _ = _ := by simp
  have hScaled := mul_le_mul_of_nonneg_left hRaw hH
  change H * (X.card : Real) ^ 2 <= _
  calc
    _ <= H * (E * Finset.sum
        (Finset.univ.filter (fun a : ZMod (Finset.prod P (fun p => p)) => IsUnit a))
          (fun a => norm (localSieveSample X a) ^ 2)) := hScaled
    _ = (H * E) * Finset.sum
        (Finset.univ.filter (fun a : ZMod (Finset.prod P (fun p => p)) => IsUnit a))
          (fun a => norm (localSieveSample X a) ^ 2) := by ring
    _ = _ := by rw [hCancel, one_mul]

end PrimeFactorOscillations.LPF

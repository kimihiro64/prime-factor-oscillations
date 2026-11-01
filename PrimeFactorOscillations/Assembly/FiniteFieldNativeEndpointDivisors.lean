/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeAgreementGeometry

/-!
# Prime-divisor support of exceptional native agreement

Each positive matching row forces its candidate endpoint prime to divide the
fixed reference invariant. An unbounded pairwise exceptional family therefore
uses the lower row and a finite set of lower endpoint primes.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_square_cross_rows_endpoint_divisors (n h m k : Nat)
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k)) (hk : 0 < k) :
    And
      (IsSquare (h * k * n * m) -> Dvd.dvd m (h * n))
      (IsSquare (h * k * (n + h) * (m + k)) ->
        Dvd.dvd (m + k) (h * (n + h))) := by
  have factor (A p g : Nat) (hp : Nat.Prime p) (hpg : Not (Dvd.dvd p g))
      (hs : IsSquare (A * g * p)) : Dvd.dvd p A := by
    let r := Classical.choose hs
    have hr : A * g * p = r * r := Classical.choose_spec hs
    have hpr2 : Dvd.dvd p (r * r) := by
      refine Exists.intro (A * g) ?_
      rw [<- hr]
      ring
    have hpr : Dvd.dvd p r := by
      rcases hp.dvd_mul.mp hpr2 with hpr | hpr
      . exact hpr
      . exact hpr
    let s := Classical.choose hpr
    have hrs : r = p * s := Classical.choose_spec hpr
    have hmul : p * (A * g) = p * (p * (s * s)) := by
      calc
        p * (A * g) = A * g * p := by ring
        _ = r * r := hr
        _ = p * (p * (s * s)) := by rw [hrs]; ring
    have hAg : A * g = p * (s * s) :=
      Nat.eq_of_mul_eq_mul_left hp.pos hmul
    have hpAg : Dvd.dvd p (A * g) := Exists.intro (s * s) hAg
    exact (hp.dvd_mul.mp hpAg).resolve_right hpg
  have hcop : Nat.Coprime m (m + k) :=
    (Nat.coprime_primes hm hmk).mpr (by omega)
  have hnotLower : Not (Dvd.dvd m k) :=
    hm.coprime_iff_not_dvd.mp (Nat.coprime_self_add_right.mp hcop)
  have hnotUpper : Not (Dvd.dvd (m + k) k) :=
    Nat.not_dvd_of_pos_of_lt hk (by have hm0 := hm.pos; omega)
  constructor
  . intro hs
    apply factor (h * n) m k hm hnotLower
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
  . intro hs
    apply factor (h * (n + h)) (m + k) k hmk hnotUpper
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hs

theorem native_half_agreement_endpoint_divisor_cover (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hneq : Not (And (n = m) (h = k)))
    (hrate : nativeAgreementRate n h m k = 1 / 2) :
    Or (Dvd.dvd m (h * n)) (Dvd.dvd (m + k) (h * (n + h))) := by
  have hdiv := native_square_cross_rows_endpoint_divisors n h m k hm hmk hk
  rcases (native_agreement_arithmetic_classification
    n h m k hn hnh hm hmk hh hk hneq).1.mp hrate with hl | hu
  . exact Or.inl (hdiv.1 hl)
  . exact Or.inr (hdiv.2 hu)

theorem native_half_agreement_unbounded_family_rigidity
    {I : Type*} (n h : I -> Nat)
    (hn : forall i, Nat.Prime (n i))
    (hnh : forall i, Nat.Prime (n i + h i))
    (hh : forall i, 0 < h i)
    (hinj : Function.Injective (fun i => Prod.mk (n i) (h i)))
    (hPairs : forall i j, Not (i = j) ->
      nativeAgreementRate (n i) (h i) (n j) (h j) = 1 / 2)
    (hUnbounded : forall Q : Nat, exists i, Q < n i + h i) :
    And
      (forall i j, IsSquare ((h i * n i) * (h j * n j)))
      (forall i j, Dvd.dvd (n j) (h i * n i)) := by
  have hLower : forall i j, IsSquare ((h i * n i) * (h j * n j)) := by
    rcases (native_half_agreement_family_rigidity n h hn hnh hh hinj).mp hPairs
      with hl | hu
    . exact hl
    . let a := Classical.choose (hUnbounded 0)
      choose b hb using hUnbounded (h a * (n a + h a))
      have hs : IsSquare (h a * h b * (n a + h a) * (n b + h b)) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hu a b
      have hdiv := (native_square_cross_rows_endpoint_divisors
        (n a) (h a) (n b) (h b) (hn b) (hnh b) (hh b)).2 hs
      have hle : n b + h b <= h a * (n a + h a) :=
        Nat.le_of_dvd (Nat.mul_pos (hh a) (hnh a).pos) hdiv
      exact False.elim (not_lt_of_ge hle hb)
  refine And.intro hLower ?_
  intro i j
  apply (native_square_cross_rows_endpoint_divisors
    (n i) (h i) (n j) (h j) (hn j) (hnh j) (hh j)).1
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hLower i j

end PrimeFactorOscillations.FiniteFieldIntegerSignature

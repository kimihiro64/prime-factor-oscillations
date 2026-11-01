/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeArithmeticAgreement

/-!
# Global rigidity of exceptional native agreement

Pairwise agreement one half in an arbitrary injective family of actual prime
pairs forces one common row of the two positive squareclass invariants.
Every compared pair is fixed before its field-scale limit.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_half_agreement_family_rigidity
    {I : Type*} (n h : I -> Nat)
    (hn : forall i, Nat.Prime (n i))
    (hnh : forall i, Nat.Prime (n i + h i))
    (hh : forall i, 0 < h i)
    (hinj : Function.Injective (fun i => Prod.mk (n i) (h i))) :
    (forall i j, Not (i = j) ->
      nativeAgreementRate (n i) (h i) (n j) (h j) = 1 / 2) <->
    Or
      (forall i j, IsSquare ((h i * n i) * (h j * n j)))
      (forall i j, IsSquare ((h i * (n i + h i)) * (h j * (n j + h j)))) := by
  classical
  let L : I -> I -> Prop := fun i j => IsSquare ((h i * n i) * (h j * n j))
  let U : I -> I -> Prop := fun i j =>
    IsSquare ((h i * (n i + h i)) * (h j * (n j + h j)))
  have square_trans (a b c : Nat) (hb : 0 < b)
      (hab : IsSquare (a * b)) (hbc : IsSquare (b * c)) : IsSquare (a * c) := by
    have hsq : IsSquare ((b * b) * (a * c)) := by
      convert hab.mul hbc using 1
      ring
    let r := Classical.choose hsq
    have hr : (b * b) * (a * c) = r * r := Classical.choose_spec hsq
    have hdiv : Dvd.dvd (b ^ 2) (r ^ 2) := by
      refine Exists.intro (a * c) ?_
      simpa only [pow_two] using hr.symm
    have hbr : Dvd.dvd b r :=
      (Nat.pow_dvd_pow_iff (by decide : Not ((2 : Nat) = 0))).mp hdiv
    let t := Classical.choose hbr
    have ht : r = b * t := Classical.choose_spec hbr
    refine Exists.intro t ?_
    have hmul : (b * b) * (a * c) = (b * b) * (t * t) := by
      rw [hr, ht]
      ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hb hb) hmul
  have lrefl (i : I) : L i i := IsSquare.mul_self _
  have urefl (i : I) : U i i := IsSquare.mul_self _
  have usymm {i j : I} (hij : U i j) : U j i := by
    dsimp only [U] at *
    simpa only [mul_comm] using hij
  have ltrans {i j k : I} (hij : L i j) (hjk : L j k) : L i k :=
    square_trans _ _ _ (Nat.mul_pos (hh j) (hn j).pos) hij hjk
  have utrans {i j k : I} (hij : U i j) (hjk : U j k) : U i k :=
    square_trans _ _ _ (Nat.mul_pos (hh j) (hnh j).pos) hij hjk
  have hclass (i j : I) (hij : Not (i = j)) :
      (nativeAgreementRate (n i) (h i) (n j) (h j) = 1 / 2) <->
        Or (L i j) (U i j) := by
    have hneq : Not (And (n i = n j) (h i = h j)) := by
      intro heq
      exact hij (hinj (Prod.ext heq.1 heq.2))
    simpa only [L, U, mul_assoc, mul_comm, mul_left_comm] using
      (native_agreement_arithmetic_classification (n i) (h i) (n j) (h j)
        (hn i) (hnh i) (hn j) (hnh j) (hh i) (hh j) hneq).1
  have hno (i j : I) (hij : Not (i = j)) : Not (And (L i j) (U i j)) := by
    intro hboth
    have hrate := (hclass i j hij).mpr (Or.inl hboth.1)
    have hs1 : IsSquare (h i * h j * n i * n j) := by
      simpa only [L, mul_assoc, mul_comm, mul_left_comm] using hboth.1
    have hs2 : IsSquare (h i * h j * (n i + h i) * (n j + h j)) := by
      simpa only [U, mul_assoc, mul_comm, mul_left_comm] using hboth.2
    have hformula := native_agreement_rate_eq_square_test
      (n i) (h i) (n j) (h j) (hn i).pos (hh i) (hn j).pos (hh j)
    have hbad : nativeAgreementRate (n i) (h i) (n j) (h j) = 5 / 8 := by
      rw [hformula, ite_eq_left hs1, ite_eq_left hs2]
      norm_num
    linarith only [hrate, hbad]
  constructor
  . intro hHalf
    by_cases hLower : forall i j, L i j
    . exact Or.inl hLower
    . apply Or.inr
      have hex : exists i j, Not (L i j) := by
        simpa only [not_forall] using hLower
      choose i j hijLower using hex
      have hij : Not (i = j) := by
        intro heq
        subst j
        exact hijLower (lrefl i)
      have hijU : U i j := by
        rcases (hclass i j hij).mp (hHalf i j hij) with hl | hu
        . exact False.elim (hijLower hl)
        . exact hu
      have hAnchor (t : I) : U i t := by
        by_cases hit : i = t
        . subst t
          exact urefl i
        by_cases hjt : j = t
        . subst t
          exact hijU
        rcases (hclass i t hit).mp (hHalf i t hit) with hLit | hUit
        . have htj : Not (t = j) := fun heq => hjt heq.symm
          rcases (hclass t j htj).mp (hHalf t j htj) with hLtj | hUtj
          . exact False.elim (hijLower (ltrans hLit hLtj))
          . have hUit := utrans hijU (usymm hUtj)
            exact False.elim (hno i t hit (And.intro hLit hUit))
        . exact hUit
      intro s t
      exact utrans (usymm (hAnchor s)) (hAnchor t)
  . intro hRows i j hij
    apply (hclass i j hij).mpr
    rcases hRows with hl | hu
    . exact Or.inl (hl i j)
    . exact Or.inr (hu i j)

end PrimeFactorOscillations.FiniteFieldIntegerSignature

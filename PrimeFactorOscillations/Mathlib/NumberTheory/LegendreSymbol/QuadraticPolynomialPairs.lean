/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairs

/-!
# Irreducible monic quadratic pairs over odd finite fields

The common nonsquare-discriminant formula is transferred to actual
irreducible monic polynomials. The point trace is the trace of the explicit
split cubic, including square-scaling invariance. Both inadmissible constant
terms vanish, and the total count over all constants is evaluated exactly.

No Hasse estimate or assertion about integer prime pairs is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open scoped BigOperators

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def monicQuadratic (b c : F) : Polynomial F :=
  Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c

theorem monicQuadratic_natDegree (b c : F) :
    (monicQuadratic b c).natDegree = 2 := by
  simpa only [monicQuadratic, Polynomial.C_1, one_mul] using
    Polynomial.natDegree_quadratic (a := (1 : F)) (b := b) (c := c) one_ne_zero

theorem monicQuadratic_irreducible_iff_noRoot (b c : F) :
    Irreducible (monicQuadratic b c) <->
      forall x : F, Not (x ^ 2 + b * x + c = 0) := by
  let P := monicQuadratic b c
  have hd : P.natDegree = 2 := monicQuadratic_natDegree b c
  have hp0 : Not (P = 0) := by
    intro h
    simp [h] at hd
  have hdeg : P.degree = 2 := by
    simpa [hd] using Polynomial.degree_eq_natDegree hp0
  have hpu : Not (IsUnit P) := by
    intro h
    have hz := Polynomial.isUnit_iff_degree_eq_zero.mp h
    rw [hdeg] at hz
    norm_num at hz
  constructor
  . intro hirr x hx
    have hr := Polynomial.roots_eq_zero_of_irreducible_of_natDegree_ne_one hirr
      (by change Not (P.natDegree = 1); rw [hd]; norm_num)
    have hroot : P.IsRoot x := by
      simpa [P, Polynomial.IsRoot, monicQuadratic] using hx
    have hmem := (Polynomial.mem_roots hp0).mpr hroot
    rw [hr] at hmem
    simpa using hmem
  . intro hno
    apply (Polynomial.irreducible_iff_lt_natDegree_lt hp0 hpu).mpr
    intro q hmon hq hdiv
    have hqn : q.natDegree = 1 := by
      simp only [hd, Nat.reduceDiv, Finset.mem_Ioc] at hq
      exact Nat.le_antisymm hq.2 (Nat.succ_le_iff.mpr hq.1)
    have hqd : q.degree = 1 := by
      simpa [hqn] using Polynomial.degree_eq_natDegree hmon.ne_zero
    choose x hx using Polynomial.exists_root_of_degree_eq_one hqd
    apply hno x
    have hroot : P.IsRoot x := by
      choose s hs using hdiv
      change Polynomial.eval x P = 0
      change Polynomial.eval x q = 0 at hx
      rw [hs, Polynomial.eval_mul, hx, zero_mul]
    simpa [P, Polynomial.IsRoot, monicQuadratic] using hroot

theorem two_ne_zero_of_odd (hF : Not (ringChar F = 2)) : Not ((2 : F) = 0) := by
  intro h
  have hsum : (1 : F) + 1 = 0 := by
    calc
      (1 : F) + 1 = 2 := by ring
      _ = 0 := h
  exact (Ring.neg_one_ne_one_of_char_ne_two hF)
    ((eq_neg_iff_add_eq_zero.mpr hsum).symm)

theorem monicQuadratic_irreducible_iff_nonsquare (hF : Not (ringChar F = 2))
    (b c : F) :
    Irreducible (monicQuadratic b c) <-> Not (IsSquare (b ^ 2 - 4 * c)) := by
  have htwo := two_ne_zero_of_odd hF
  letI : NeZero (2 : F) := NeZero.mk htwo
  rw [monicQuadratic_irreducible_iff_noRoot]
  constructor
  . intro hno hs
    choose y hy using hs
    let x := (y - b) / 2
    have hx : 2 * x + b = y := by
      dsimp [x]
      field_simp [htwo]
      <;> ring
    apply hno x
    have hdisc : discrim (1 : F) b c = (2 * (1 : F) * x + b) ^ 2 := by
      simpa [discrim, hx, pow_two] using hy
    have hz := (quadratic_eq_zero_iff_discrim_eq_sq (a := (1 : F))
      (b := b) (c := c) one_ne_zero x).mpr hdisc
    simpa only [one_mul, pow_two] using hz
  . intro hno x hx
    apply hno
    have hz := (quadratic_eq_zero_iff_discrim_eq_sq (a := (1 : F))
      (b := b) (c := c) one_ne_zero x).mp (by simpa only [one_mul, pow_two] using hx)
    refine Exists.intro (2 * x + b) ?_
    simpa [discrim, pow_two] using hz


theorem splitCubicPointTrace_square_scale (hF : Not (ringChar F = 2))
    (s : F) (hs : Not (s = 0)) (a b : F) :
    splitCubicPointTrace (s ^ 2 * a) (s ^ 2 * b) = splitCubicPointTrace a b := by
  rw [splitCubicPointTrace_eq hF, splitCubicPointTrace_eq hF]
  congr 1
  have hs2 : Not (s ^ 2 = 0) := pow_ne_zero 2 hs
  let e : Equiv F F :=
    { toFun := fun x => s ^ 2 * x
      invFun := fun x => x / s ^ 2
      left_inv := by intro x; field_simp [hs2]
      right_inv := by intro x; field_simp [hs2] }
  calc
    (Finset.univ.sum fun x : F =>
        (quadraticChar F) (x * (x - s ^ 2 * a) * (x - s ^ 2 * b))) =
      Finset.univ.sum (fun x : F =>
        (quadraticChar F) ((e x) * (e x - s ^ 2 * a) * (e x - s ^ 2 * b))) :=
      (Equiv.sum_comp e _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      change (quadraticChar F)
        ((s ^ 2 * x) * (s ^ 2 * x - s ^ 2 * a) * (s ^ 2 * x - s ^ 2 * b)) = _
      have heq :
          (s ^ 2 * x) * (s ^ 2 * x - s ^ 2 * a) * (s ^ 2 * x - s ^ 2 * b) =
            (s ^ 3) ^ 2 * (x * (x - a) * (x - b)) := by ring
      rw [heq, map_mul, map_pow, quadraticChar_sq_one (pow_ne_zero 3 hs), one_mul]

noncomputable def monicQuadraticPairCount (c h : F) : Int := by
  classical
  exact Finset.univ.sum (fun b : F =>
    if Irreducible (monicQuadratic b c) /\ Irreducible (monicQuadratic b (c + h))
      then 1 else 0)

theorem monicQuadraticPairCount_eq_discriminant (hF : Not (ringChar F = 2))
    (c h : F) :
    monicQuadraticPairCount c h = nonsquarePairCount (4 * c) (4 * (c + h)) := by
  classical
  unfold monicQuadraticPairCount nonsquarePairCount
  simp_rw [monicQuadratic_irreducible_iff_nonsquare hF]

theorem monicQuadraticPairCount_eq_trace (hF : Not (ringChar F = 2))
    (c h : F) (hc : Not (c = 0)) (hch : Not (c + h = 0)) (hh : Not (h = 0)) :
    4 * monicQuadraticPairCount c h =
      (Fintype.card F : Int) + 1 - splitCubicPointTrace c (c + h) -
        (1 + (quadraticChar F) c) * (1 - (quadraticChar F) (-h)) -
        (1 + (quadraticChar F) (c + h)) * (1 - (quadraticChar F) h) := by
  have htwo := two_ne_zero_of_odd hF
  have hfourEq : (4 : F) = (2 : F) ^ 2 := by ring
  have hfour : Not ((4 : F) = 0) := by
    rw [hfourEq]
    exact pow_ne_zero 2 htwo
  have hab : Not ((4 : F) * c = 4 * (c + h)) := by
    intro heq
    have hz : (4 : F) * (-h) = 0 := by
      calc
        _ = 4 * c - 4 * (c + h) := by ring
        _ = 0 := sub_eq_zero.mpr heq
    exact (mul_ne_zero hfour (neg_ne_zero.mpr hh)) hz
  have ht : splitCubicPointTrace ((4 : F) * c) (4 * (c + h)) =
      splitCubicPointTrace c (c + h) := by
    simpa only [<- hfourEq] using
      splitCubicPointTrace_square_scale hF (2 : F) htwo c (c + h)
  have hchi : (quadraticChar F) (4 : F) = 1 := by
    rw [hfourEq, map_pow, quadraticChar_sq_one htwo]
  have hm : (4 : F) * c - 4 * (c + h) = 4 * (-h) := by ring
  have hp : (4 : F) * (c + h) - 4 * c = 4 * h := by ring
  have he := nonsquarePairCount_eq_trace hF ((4 : F) * c) (4 * (c + h))
    (mul_ne_zero hfour hc) (mul_ne_zero hfour hch) hab
  rw [hm, hp, ht] at he
  simp only [map_mul, hchi, one_mul] at he
  rw [monicQuadraticPairCount_eq_discriminant hF]
  exact he

noncomputable def linearNonsquarePairCount (t : F) : Int := by
  classical
  exact Finset.univ.sum (fun a : F =>
    if Not (IsSquare a) /\ Not (IsSquare (a - t)) then 1 else 0)

theorem linearNonsquarePairCount_eq (hF : Not (ringChar F = 2))
    (t : F) (ht : Not (t = 0)) :
    4 * linearNonsquarePairCount t =
      (Fintype.card F : Int) - 3 + (quadraticChar F) t +
        (quadraticChar F) (-t) := by
  classical
  let e : Equiv F F :=
    { toFun := fun a => a - t
      invFun := fun a => a + t
      left_inv := by intro a; ring
      right_inv := by intro a; ring }
  have hz : (Finset.univ.sum fun a : F =>
      (quadraticChar F) (a - t)) = 0 := by
    calc
      _ = Finset.univ.sum (fun a : F => (quadraticChar F) a) :=
        Equiv.sum_comp e (quadraticChar F)
      _ = 0 := quadraticChar_sum_zero hF
  have hcross : (Finset.univ.sum fun a : F =>
      (quadraticChar F) a * (quadraticChar F) (a - t)) = -1 := by
    simpa only [sub_zero, map_mul] using
      quadraticChar_sum_mul_sub hF (0 : F) t (Ne.symm ht)
  have hjoint : (Finset.univ.sum fun a : F =>
      if a = 0 /\ a - t = 0 then (1 : Int) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have hn : Not (a = 0 /\ a - t = 0) := by
      intro h
      apply ht
      calc
        t = a := (sub_eq_zero.mp h.2).symm
        _ = 0 := h.1
    simp only [hn, ite_false]
  have hpoint (a : F) :
      (1 - (quadraticChar F) a) * (1 - (quadraticChar F) (a - t)) =
        1 - (quadraticChar F) a - (quadraticChar F) (a - t) +
          (quadraticChar F) a * (quadraticChar F) (a - t) := by ring
  have hrow0 : (Finset.univ.sum fun a : F =>
      if a = 0 then 1 - (quadraticChar F) (a - t) else 0) =
        1 - (quadraticChar F) (-t) := by simp
  have hrowt : (Finset.univ.sum fun a : F =>
      if a - t = 0 then 1 - (quadraticChar F) a else 0) =
        1 - (quadraticChar F) t := by
    simp only [sub_eq_zero]
    simp
  calc
    4 * linearNonsquarePairCount t =
        Finset.univ.sum (fun a : F =>
          (1 - (quadraticChar F) a) * (1 - (quadraticChar F) (a - t)) -
            (if a = 0 then 1 - (quadraticChar F) (a - t) else 0) -
            (if a - t = 0 then 1 - (quadraticChar F) a else 0) +
            (if a = 0 /\ a - t = 0 then 1 else 0)) := by
      unfold linearNonsquarePairCount
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact four_nonsquare_pair_indicator a (a - t)
    _ = _ := by
      simp_rw [hpoint]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hjoint, hcross, hz, quadraticChar_sum_zero hF, hrow0, hrowt]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      ring

theorem sum_monicQuadraticPairCount_eq_linear (hF : Not (ringChar F = 2))
    (h : F) :
    (Finset.univ.sum fun c : F => monicQuadraticPairCount c h) =
      (Fintype.card F : Int) * linearNonsquarePairCount (4 * h) := by
  classical
  have htwo := two_ne_zero_of_odd hF
  have hfour : Not ((4 : F) = 0) := by
    have he : (4 : F) = 2 ^ 2 := by ring
    rw [he]
    exact pow_ne_zero 2 htwo
  have hcol (b : F) :
      (Finset.univ.sum fun c : F =>
        if Irreducible (monicQuadratic b c) /\
            Irreducible (monicQuadratic b (c + h)) then (1 : Int) else 0) =
          linearNonsquarePairCount (4 * h) := by
    let e : Equiv F F :=
      { toFun := fun c => b ^ 2 - 4 * c
        invFun := fun a => (b ^ 2 - a) / 4
        left_inv := by intro c; field_simp [hfour] <;> ring
        right_inv := by intro a; field_simp [hfour] <;> ring }
    simp_rw [monicQuadratic_irreducible_iff_nonsquare hF]
    have heq (c : F) : b ^ 2 - 4 * (c + h) = e c - 4 * h := by
      change b ^ 2 - 4 * (c + h) = (b ^ 2 - 4 * c) - 4 * h
      ring
    simp_rw [heq]
    exact Equiv.sum_comp e (fun a : F =>
      if Not (IsSquare a) /\ Not (IsSquare (a - 4 * h)) then (1 : Int) else 0)
  unfold monicQuadraticPairCount
  rw [Finset.sum_comm]
  simp_rw [hcol]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem sum_monicQuadraticPairCount_eq (hF : Not (ringChar F = 2))
    (h : F) (hh : Not (h = 0)) :
    4 * (Finset.univ.sum fun c : F => monicQuadraticPairCount c h) =
      (Fintype.card F : Int) *
        ((Fintype.card F : Int) - 3 + (quadraticChar F) h +
          (quadraticChar F) (-h)) := by
  have htwo := two_ne_zero_of_odd hF
  have he : (4 : F) = 2 ^ 2 := by ring
  have hfour : Not ((4 : F) = 0) := by
    rw [he]
    exact pow_ne_zero 2 htwo
  have hchi : (quadraticChar F) (4 : F) = 1 := by
    rw [he, map_pow, quadraticChar_sq_one htwo]
  have hn : -(4 * h) = (4 : F) * (-h) := by ring
  have hr := linearNonsquarePairCount_eq hF (4 * h) (mul_ne_zero hfour hh)
  rw [hn] at hr
  simp only [map_mul, hchi, one_mul] at hr
  rw [sum_monicQuadraticPairCount_eq_linear hF]
  calc
    _ = (Fintype.card F : Int) * (4 * linearNonsquarePairCount (4 * h)) := by ring
    _ = _ := by rw [hr]

theorem monicQuadraticPairCount_zero (hF : Not (ringChar F = 2)) (h : F) :
    monicQuadraticPairCount 0 h = 0 := by
  classical
  unfold monicQuadraticPairCount
  apply Finset.sum_eq_zero
  intro b _
  have hs : IsSquare (b ^ 2 - 4 * (0 : F)) := Exists.intro b (by ring)
  have hn : Not (Irreducible (monicQuadratic b (0 : F))) := by
    intro hi
    exact (monicQuadratic_irreducible_iff_nonsquare hF b 0).mp hi hs
  simp only [hn, false_and, ite_false]

theorem monicQuadraticPairCount_neg_shift (hF : Not (ringChar F = 2)) (h : F) :
    monicQuadraticPairCount (-h) h = 0 := by
  classical
  unfold monicQuadraticPairCount
  apply Finset.sum_eq_zero
  intro b _
  have hs : IsSquare (b ^ 2 - 4 * (0 : F)) := Exists.intro b (by ring)
  have hn : Not (Irreducible (monicQuadratic b (0 : F))) := by
    intro hi
    exact (monicQuadratic_irreducible_iff_nonsquare hF b 0).mp hi hs
  simp only [neg_add_cancel, hn, and_false, ite_false]

end FiniteField

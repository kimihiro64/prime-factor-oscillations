/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.Tactic.Ring

/-!
# Fixed-root characters and the rank-one determinant probe

The two fixed Sp4 root values leave a quadratic character on the product
of the square-torus coordinates. Quartic determinant twists realize this
kernel. These are algebraic inputs, not an automorphic factorization.

The final theorem rejects a bare determinant-character model for a
rank-one Whittaker probe: every weight depending only on the last diagonal
coordinate has zero total when the character square is nontrivial.
The Levi Whittaker factor therefore cannot be erased from that model.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Metaplectic.Sp4FixedSpectrum

section Characters

variable {A C : Type*} [CommGroup A] [CommGroup C]

def determinantCharacter (k : MonoidHom A C) : MonoidHom (Prod A A) C where
  toFun := fun p => k (p.1 * p.2)
  map_one' := by simp
  map_mul' := by
    intro p q
    change k ((p.1 * q.1) * (p.2 * q.2)) = k (p.1 * p.2) * k (q.1 * q.2)
    rw [<- map_mul]
    congr 1
    ac_rfl

theorem fixed_roots_iff_quadratic (f : MonoidHom (Prod A A) C) :
    And (forall a : A, f (a, a ^ (-1 : Int)) = 1)
        (forall a : A, f (1, a ^ 2) = 1) <->
      exists k : MonoidHom A C,
        And (forall a : A, k a ^ 2 = 1) (f = determinantCharacter k) := by
  constructor
  . intro h
    let k : MonoidHom A C :=
      { toFun := fun a => f (1, a)
        map_one' := f.map_one
        map_mul' := by
          intro a b
          simpa only [Prod.mk_mul_mk, one_mul] using f.map_mul (1, a) (1, b) }
    refine Exists.intro k (And.intro ?_ ?_)
    . intro a
      change f (1, a) ^ 2 = 1
      have hm := f.map_mul (1, a) (1, a)
      have hp : ((1 : A), a) * ((1 : A), a) = ((1 : A), a ^ 2) := by
        simp only [Prod.mk_mul_mk, one_mul, pow_two]
      rw [hp] at hm
      rw [pow_two, <- hm]
      exact h.2 a
    . apply DFunLike.ext
      intro p
      change f p = k (p.1 * p.2)
      have hp : p = (p.1, p.1 ^ (-1 : Int)) * (1, p.1 * p.2) := by
        apply Prod.ext <;> simp
      calc
        f p = f (p.1, p.1 ^ (-1 : Int)) * f (1, p.1 * p.2) := by
          rw [<- map_mul, <- hp]
        _ = k (p.1 * p.2) := by
          rw [h.1, one_mul]
          rfl
  . intro h
    cases h with
    | intro k hk =>
      rw [hk.2]
      constructor
      . intro a
        change k (a * a ^ (-1 : Int)) = 1
        simp only [zpow_neg_one, mul_inv_cancel, map_one]
      . intro a
        change k (1 * a ^ 2) = 1
        rw [one_mul, map_pow]
        exact hk.1 a

theorem square_torus_twist_eq_iff (tau sigma : MonoidHom A C) :
    (forall a b : A, tau (a ^ 2 * b ^ 2) = sigma (a ^ 2 * b ^ 2)) <->
      forall a : A, tau a ^ 2 = sigma a ^ 2 := by
  constructor
  . intro h a
    simpa only [one_pow, mul_one, map_pow] using h a 1
  . intro h a b
    simp only [map_mul, map_pow, h a, h b]

theorem quartic_twist_fixed_roots (tau : MonoidHom A C)
    (hfour : forall a : A, tau a ^ 4 = 1) :
    And (forall a : A, determinantCharacter (tau ^ 2) (a, a ^ (-1 : Int)) = 1)
        (forall a : A, determinantCharacter (tau ^ 2) (1, a ^ 2) = 1) := by
  apply (fixed_roots_iff_quadratic _).mpr
  refine Exists.intro (tau ^ 2) (And.intro ?_ rfl)
  intro a
  change (tau a ^ 2) ^ 2 = 1
  rw [<- pow_mul]
  exact hfour a

end Characters

section FiniteDeterminant

variable {K C : Type*} [Field K] [Fintype K] [Field C]

noncomputable def rankOneProbe (chi : MulChar K C) (w : K -> C) : C :=
  Finset.univ.sum (fun p : Prod K K =>
    Finset.univ.sum (fun c : K => chi (p.1 * c - p.2 ^ 2) * w c))

theorem rank_one_probe_eq_zero (chi : MulChar K C) (u : Units K)
    (hchi : Not (chi (u : K) ^ 2 = 1)) (w : K -> C) :
    rankOneProbe chi w = 0 := by
  classical
  let x : K := u
  have hx : Not (x = 0) := Units.ne_zero u
  let e : Equiv (Prod K K) (Prod K K) :=
    { toFun := fun p => (x ^ 2 * p.1, x * p.2)
      invFun := fun p => ((x ^ (-1 : Int)) ^ 2 * p.1, x ^ (-1 : Int) * p.2)
      left_inv := by
        intro p
        apply Prod.ext <;> simp [hx]
      right_inv := by
        intro p
        apply Prod.ext <;> simp [hx] }
  let g : Prod K K -> C := fun p =>
    Finset.univ.sum (fun c : K => chi (p.1 * c - p.2 ^ 2) * w c)
  have hscale (p : Prod K K) : g (e p) = chi x ^ 2 * g p := by
    change Finset.univ.sum (fun c : K =>
      chi ((x ^ 2 * p.1) * c - (x * p.2) ^ 2) * w c) = _
    have hd (c : K) : (x ^ 2 * p.1) * c - (x * p.2) ^ 2 =
        x ^ 2 * (p.1 * c - p.2 ^ 2) := by ring
    simp_rw [hd, map_mul, map_pow, mul_assoc]
    exact (Finset.mul_sum Finset.univ (fun c : K =>
      chi (p.1 * c - p.2 ^ 2) * w c) (chi x ^ 2)).symm
  have hperm : Finset.univ.sum (fun p => g (e p)) = Finset.univ.sum g :=
    Fintype.sum_equiv e (fun p => g (e p)) g (fun _ => rfl)
  have heq : chi x ^ 2 * rankOneProbe chi w = rankOneProbe chi w := by
    change chi x ^ 2 * Finset.univ.sum g = Finset.univ.sum g
    rw [Finset.mul_sum]
    calc
      _ = Finset.univ.sum (fun p => g (e p)) :=
        Finset.sum_congr rfl (fun p _ => (hscale p).symm)
      _ = _ := hperm
  have hz : (chi x ^ 2 - 1) * rankOneProbe chi w = 0 := by
    rw [sub_mul, one_mul, heq, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hchi)

end FiniteDeterminant

end Metaplectic.Sp4FixedSpectrum

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Taylor coefficients of finite linear products

Normalized derivatives at zero recover existing elementary symmetric sums.
Ring homomorphisms preserve the same multiset coefficients.
-/

set_option autoImplicit false
set_option Elab.async false

namespace RingHom

theorem map_multiset_esymm {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : RingHom R S) (s : Multiset R) (r : Nat) :
    f (s.esymm r) = (s.map f).esymm r := by
  simp only [Multiset.esymm, map_multiset_sum, Multiset.powersetCard_map,
    Multiset.map_map, Function.comp_def, map_multiset_prod]

end RingHom

namespace Finset

theorem normalized_iteratedDeriv_prod_linear_zero {I : Type*} [DecidableEq I]
    (s : Finset I) (a : I -> Complex) (r : Nat) :
    iteratedDeriv r (fun z : Complex => s.prod (fun i => 1 + a i * z)) 0 /
      (r.factorial : Complex) = (s.val.map a).esymm r := by
  classical
  have hprod : (fun z : Complex => s.prod (fun i => 1 + a i * z)) =
      fun z : Complex => s.powerset.sum (fun t => t.prod a * z ^ t.card) := by
    funext z
    simp_rw [add_comm (1 : Complex)]
    rw [Finset.prod_add]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const]
  rw [hprod, iteratedDeriv_fun_sum (fun t _ => by fun_prop), Finset.sum_div,
    Finset.esymm_map_val]
  have hterm (t : Finset I) :
      iteratedDeriv r (fun z : Complex => t.prod a * z ^ t.card) 0 /
        (r.factorial : Complex) = if t.card = r then t.prod a else 0 := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
    by_cases ht : t.card = r
    next =>
      rw [ht]
      have hf : Not ((r.factorial : Complex) = 0) := by
        exact_mod_cast Nat.factorial_ne_zero r
      simp [hf]
    next => simp [ht, Ne.symm ht]
  simp_rw [hterm]
  rw [<- Finset.sum_filter]
  have hfilter : s.powerset.filter (fun t => t.card = r) = s.powersetCard r := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
  rw [hfilter]

end Finset


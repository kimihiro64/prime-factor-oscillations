/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ArithmeticFunctionDirichletL1

/-!
# Dilation by four as a Dirichlet point mass

Convolution with the point mass at four preserves both signed mass and
absolute mass. Its output vanishes outside the multiples of four.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.ArithmeticFunctionL1

noncomputable def fourAtom : ArithmeticFunction Real where
  toFun n := if n = 4 then 1 else 0
  map_zero' := by norm_num

theorem fourAtom_hasSum_one : HasSum (fun n : Nat => fourAtom n) 1 :=
  hasSum_ite_eq 4 1

theorem fourAtom_nonneg (n : Nat) : 0 <= fourAtom n := by
  change 0 <= if n = 4 then (1 : Real) else 0
  split_ifs <;> norm_num

theorem fourAtom_norm_hasSum_one : HasSum (fun n : Nat => norm (fourAtom n)) 1 := by
  have heq : (fun n : Nat => norm (fourAtom n)) = (fun n : Nat => fourAtom n) := by
    funext n
    rw [Real.norm_eq_abs, abs_of_nonneg (fourAtom_nonneg n)]
  rw [heq]
  exact fourAtom_hasSum_one

theorem fourAtom_mul_apply (f : ArithmeticFunction Real) (n : Nat) :
    (fourAtom * f) n = if Dvd.dvd 4 n then f (n / 4) else 0 := by
  classical
  by_cases hn : n = 0
  . subst n
    simp
  . rw [ArithmeticFunction.mul_apply]
    by_cases hd : Dvd.dvd 4 n
    . rw [ite_eq_left hd]
      calc
        n.divisorsAntidiagonal.sum (fun x => fourAtom x.1 * f x.2) =
            fourAtom 4 * f (n / 4) := by
          apply Finset.sum_eq_single (4, n / 4)
          . intro x hx hne
            by_cases hfirst : x.1 = 4
            . have hprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
              rw [hfirst] at hprod
              have hsecond : x.2 = n / 4 :=
                Nat.eq_of_mul_eq_mul_left (by norm_num)
                  (hprod.trans (Nat.mul_div_cancel' hd).symm)
              exact False.elim (hne (Prod.ext hfirst hsecond))
            . simp [fourAtom, hfirst]
          . intro hnot
            exact False.elim (hnot (Nat.mem_divisorsAntidiagonal.mpr
              (And.intro (Nat.mul_div_cancel' hd) hn)))
        _ = f (n / 4) := by simp [fourAtom]
    . rw [ite_eq_right hd]
      apply Finset.sum_eq_zero
      intro x hx
      have hfirst : Not (x.1 = 4) := by
        intro heq
        have hprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
        rw [heq] at hprod
        exact hd (Exists.intro x.2 hprod.symm)
      simp [fourAtom, hfirst]

theorem fourAtom_norm_mul_apply (f : ArithmeticFunction Real) (n : Nat) :
    norm ((fourAtom * f) n) = (fourAtom * absolute f) n := by
  rw [fourAtom_mul_apply, fourAtom_mul_apply]
  by_cases hd : Dvd.dvd 4 n
  . rw [ite_eq_left hd, ite_eq_left hd]
    rfl
  . simp only [ite_eq_right hd, norm_zero]

theorem fourAtom_mul_hasSum (f : ArithmeticFunction Real)
    (hf : Summable (fun n : Nat => norm (f n))) :
    HasSum (fun n : Nat => (fourAtom * f) n) (tsum (fun n : Nat => f n)) := by
  have h := convolution_hasSum fourAtom f fourAtom_norm_hasSum_one.summable hf
  rw [fourAtom_hasSum_one.tsum_eq, one_mul] at h
  exact h

theorem fourAtom_norm_mul_hasSum (f : ArithmeticFunction Real)
    (hf : Summable (fun n : Nat => norm (f n))) :
    HasSum (fun n : Nat => norm ((fourAtom * f) n))
      (tsum (fun n : Nat => norm (f n))) := by
  have hf' : Summable (fun n : Nat => norm (absolute f n)) := by
    change Summable (fun n : Nat => norm (norm (f n)))
    simpa only [norm_norm] using hf
  have h := convolution_hasSum fourAtom (absolute f) fourAtom_norm_hasSum_one.summable hf'
  rw [fourAtom_hasSum_one.tsum_eq, one_mul] at h
  have heq : (fun n : Nat => norm ((fourAtom * f) n)) =
      (fun n : Nat => (fourAtom * absolute f) n) :=
    funext (fourAtom_norm_mul_apply f)
  rw [<- heq] at h
  exact h

end PrimeFactorOscillations.ArithmeticFunctionL1

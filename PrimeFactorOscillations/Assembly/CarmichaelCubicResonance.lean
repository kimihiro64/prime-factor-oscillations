/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelLargeSquareRemainder

/-!
# Exact cubic resonance in the retained signed native core

For a cubic Dirichlet character, the square-part companion is the conjugate
of the plain companion. All companion ratio classes retain their complete
coefficients and arbitrary complex kernels. Unit square-part indices have
unique residue representatives and signed integer shifts, giving exact cubic
input polynomials. Nonunit zeros and every compensation factor are retained.
No nonresonant partner is discarded and no signed core bound is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelCubicResonance
open scoped Classical
open CarmichaelNativeSquarepart CarmichaelNativeLowSector

private theorem minus_three_real :
    star OAI.ShortDraftHeckeBridge.chiMinusThree =
      OAI.ShortDraftHeckeBridge.chiMinusThree := by
  ext a
  rw [MulChar.star_apply]
  change star (((quadraticChar (ZMod 3)) a : Int) : Complex) =
    (((quadraticChar (ZMod 3)) a : Int) : Complex)
  simp

/-- The two actual companion characters are conjugates, including nonunits. -/
theorem cubic_squarepart_conjugacy {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1) :
    OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2) =
      star (OAI.ShortDraftHeckeBridge.baseChangeChar chi) := by
  have hc : chi ^ 2 = Inv.inv chi := by
    calc
      _ = (chi ^ 2 * chi) * Inv.inv chi := by
        simp only [mul_assoc, mul_inv_cancel, mul_one]
      _ = Inv.inv chi := by rw [<- pow_succ, hchi, one_mul]
  have h3 : Inv.inv OAI.ShortDraftHeckeBridge.chiMinusThree =
      OAI.ShortDraftHeckeBridge.chiMinusThree :=
    (MulChar.star_eq_inv _).symm.trans minus_three_real
  let f : MonoidHom (DirichletCharacter Complex q) (DirichletCharacter Complex (q * 3)) :=
    DirichletCharacter.changeLevel (R := Complex)
      (Exists.intro 3 rfl : Dvd.dvd q (q * 3))
  let g : MonoidHom (DirichletCharacter Complex 3) (DirichletCharacter Complex (q * 3)) :=
    DirichletCharacter.changeLevel (R := Complex)
      (Exists.intro q (Nat.mul_comm q 3) : Dvd.dvd 3 (q * 3))
  change f (chi ^ 2) * g OAI.ShortDraftHeckeBridge.chiMinusThree =
    star (f chi * g OAI.ShortDraftHeckeBridge.chiMinusThree)
  rw [MulChar.star_eq_inv]
  have hg : Inv.inv (g OAI.ShortDraftHeckeBridge.chiMinusThree) =
      g OAI.ShortDraftHeckeBridge.chiMinusThree := by
    rw [<- map_inv, h3]
  calc
    _ = Inv.inv (f chi) * g OAI.ShortDraftHeckeBridge.chiMinusThree := by
      rw [hc, map_inv]
    _ = Inv.inv (g OAI.ShortDraftHeckeBridge.chiMinusThree) * Inv.inv (f chi) := by
      rw [hg]
      exact mul_comm _ _
    _ = _ := (mul_inv_rev _ _).symm

/-- The product is the principal character, retaining its zeros on nonunits. -/
theorem cubic_phase_product {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1) :
    OAI.ShortDraftHeckeBridge.baseChangeChar chi *
      OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2) = 1 := by
  rw [cubic_squarepart_conjugacy chi hchi, MulChar.star_eq_inv, mul_inv_cancel]

/-- Complete coefficient on the cubic companion slice, with both local masks. -/
def cubicResonanceCoefficient {q : Nat}
    (chi : DirichletCharacter Complex q) (r s : Nat) : Complex :=
  if Nat.Coprime r s then
    nativeCoefficient chi r * (ArithmeticFunction.moebius s : Complex) ^ 2 *
      (1 : DirichletCharacter Complex (q * 3)) (s : ZMod (q * 3))
  else 0

/-- Equal native and plain companion indices retain the full cubic coefficient. -/
theorem cubic_companion_resonance {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1) (r s : Nat) :
    squarepartCoefficient chi r s *
      OAI.ShortDraftHeckeBridge.baseChangeChar chi (s : ZMod (q * 3)) =
        cubicResonanceCoefficient chi r s := by
  have he := congrArg (fun xi : DirichletCharacter Complex (q * 3) =>
    xi (s : ZMod (q * 3))) (cubic_phase_product chi hchi)
  change OAI.ShortDraftHeckeBridge.baseChangeChar chi (s : ZMod (q * 3)) *
    OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2) (s : ZMod (q * 3)) =
    (1 : DirichletCharacter Complex (q * 3)) (s : ZMod (q * 3)) at he
  unfold squarepartCoefficient cubicResonanceCoefficient
  by_cases hcop : Nat.Coprime r s
  . rw [ite_eq_left hcop, ite_eq_left hcop]
    calc
      _ = (nativeCoefficient chi r * (ArithmeticFunction.moebius s : Complex) ^ 2) *
          (OAI.ShortDraftHeckeBridge.baseChangeChar chi (s : ZMod (q * 3)) *
            OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2) (s : ZMod (q * 3))) := by
        dsimp only [nativeCoefficient]
        ring
      _ = _ := by rw [he]
  . rw [ite_eq_right hcop, ite_eq_right hcop, zero_mul]

/-- The coupled cubic slice preserves an arbitrary complex kernel and every cross term. -/
theorem cubic_resonance_pair {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1)
    (r u s t : Nat) (K : Nat -> Nat -> Complex) :
    (OAI.ShortDraftHeckeBridge.baseChangeChar chi (s : ZMod (q * 3)) *
      star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (t : ZMod (q * 3)))) *
      (squarepartCoefficient chi r s * star (squarepartCoefficient chi u t)) *
        K ((r * s ^ 2) * s) ((u * t ^ 2) * t) =
    cubicResonanceCoefficient chi r s * star (cubicResonanceCoefficient chi u t) *
      K (r * s ^ 3) (u * t ^ 3) := by
  have hs : (r * s ^ 2) * s = r * s ^ 3 := by ring
  have ht : (u * t ^ 2) * t = u * t ^ 3 := by ring
  rw [hs, ht]
  calc
    _ = (squarepartCoefficient chi r s *
        OAI.ShortDraftHeckeBridge.baseChangeChar chi (s : ZMod (q * 3))) *
        star (squarepartCoefficient chi u t *
          OAI.ShortDraftHeckeBridge.baseChangeChar chi (t : ZMod (q * 3))) *
        K (r * s ^ 3) (u * t ^ 3) := by
      rw [star_mul]
      ring
    _ = _ := by
      rw [cubic_companion_resonance chi hchi, cubic_companion_resonance chi hchi]

/-- Every companion ratio class has its exact phase, including all zero masks. -/
theorem cubic_companion_ratio {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1)
    (r s b a : Nat)
    (hbs : (b : ZMod (q * 3)) = (a : ZMod (q * 3)) * (s : ZMod (q * 3))) :
    squarepartCoefficient chi r s *
      OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) =
    OAI.ShortDraftHeckeBridge.baseChangeChar chi (a : ZMod (q * 3)) *
      cubicResonanceCoefficient chi r s := by
  have he := congrArg (fun xi : DirichletCharacter Complex (q * 3) =>
    xi (s : ZMod (q * 3))) (cubic_phase_product chi hchi)
  change OAI.ShortDraftHeckeBridge.baseChangeChar chi (s : ZMod (q * 3)) *
    OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2) (s : ZMod (q * 3)) =
    (1 : DirichletCharacter Complex (q * 3)) (s : ZMod (q * 3)) at he
  unfold squarepartCoefficient cubicResonanceCoefficient
  by_cases hcop : Nat.Coprime r s
  . rw [ite_eq_left hcop, ite_eq_left hcop, hbs, map_mul]
    calc
      _ = OAI.ShortDraftHeckeBridge.baseChangeChar chi (a : ZMod (q * 3)) *
          ((nativeCoefficient chi r * (ArithmeticFunction.moebius s : Complex) ^ 2) *
            (OAI.ShortDraftHeckeBridge.baseChangeChar chi (s : ZMod (q * 3)) *
              OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2) (s : ZMod (q * 3)))) := by
        dsimp only [nativeCoefficient]
        ring
      _ = _ := by rw [he]
  . rw [ite_eq_right hcop, ite_eq_right hcop, zero_mul, mul_zero]

/-- All ratio classes stay coupled in an arbitrary complex kernel. -/
theorem cubic_ratio_pair {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1)
    (r u s t b d a c : Nat) (K : Nat -> Nat -> Complex)
    (hbs : (b : ZMod (q * 3)) = (a : ZMod (q * 3)) * (s : ZMod (q * 3)))
    (hdt : (d : ZMod (q * 3)) = (c : ZMod (q * 3)) * (t : ZMod (q * 3))) :
    (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
      star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3)))) *
      (squarepartCoefficient chi r s * star (squarepartCoefficient chi u t)) *
        K ((r * s ^ 2) * b) ((u * t ^ 2) * d) =
    (OAI.ShortDraftHeckeBridge.baseChangeChar chi (a : ZMod (q * 3)) *
      star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (c : ZMod (q * 3)))) *
      (cubicResonanceCoefficient chi r s * star (cubicResonanceCoefficient chi u t)) *
        K ((r * s ^ 2) * b) ((u * t ^ 2) * d) := by
  calc
    _ = (squarepartCoefficient chi r s *
        OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3))) *
        star (squarepartCoefficient chi u t *
          OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3))) *
        K ((r * s ^ 2) * b) ((u * t ^ 2) * d) := by
      rw [star_mul]
      ring
    _ = _ := by
      rw [cubic_companion_ratio chi hchi r s b a hbs,
        cubic_companion_ratio chi hchi u t d c hdt, star_mul]
      ring

private theorem shifted_input_mod (q a s b : Nat) (k : Int)
    (hb : (b : Int) = (a : Int) * (s : Int) + k * ((q * 3 : Nat) : Int)) :
    (b : ZMod (q * 3)) = (a : ZMod (q * 3)) * (s : ZMod (q * 3)) := by
  have h := congrArg (fun z : Int => (z : ZMod (q * 3))) hb
  simpa only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self,
    mul_zero, add_zero] using h

/-- The physical input on every signed-shift family is exactly a cubic polynomial. -/
theorem shifted_cubic_input (q r s b a : Nat) (k : Int)
    (hb : (b : Int) = (a : Int) * (s : Int) + k * ((q * 3 : Nat) : Int)) :
    (((r * s ^ 2) * b : Nat) : Int) =
      (r : Int) * (a : Int) * (s : Int) ^ 3 +
        (r : Int) * k * ((q * 3 : Nat) : Int) * (s : Int) ^ 2 := by
  push_cast
  rw [hb]
  push_cast
  ring

/-- Negative and positive integer shifts have the same complete coefficient transfer. -/
theorem shifted_cubic_companion {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1)
    (r s b a : Nat) (k : Int)
    (hb : (b : Int) = (a : Int) * (s : Int) + k * ((q * 3 : Nat) : Int)) :
    squarepartCoefficient chi r s *
      OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) =
    OAI.ShortDraftHeckeBridge.baseChangeChar chi (a : ZMod (q * 3)) *
      cubicResonanceCoefficient chi r s :=
  cubic_companion_ratio chi hchi r s b a (shifted_input_mod q a s b k hb)

/-- Every unit square-part index admits the full signed-shift parametrization. -/
theorem shifted_cubic_parameters_exist {q : Nat} [NeZero q]
    (s b : Nat) (hcop : Nat.Coprime s (q * 3)) :
    exists a : Nat, a < q * 3 /\ exists k : Int,
      (b : Int) = (a : Int) * (s : Int) + k * ((q * 3 : Nat) : Int) := by
  let v : Units (ZMod (q * 3)) := ZMod.unitOfCoprime s hcop
  let x : ZMod (q * 3) := (b : ZMod (q * 3)) *
    ((Inv.inv v : Units (ZMod (q * 3))) : ZMod (q * 3))
  have hv : ((Inv.inv v : Units (ZMod (q * 3))) : ZMod (q * 3)) *
      (s : ZMod (q * 3)) = 1 := by
    change ((Inv.inv v : Units (ZMod (q * 3))) : ZMod (q * 3)) *
      (v : ZMod (q * 3)) = 1
    exact congrArg (fun w : Units (ZMod (q * 3)) => (w : ZMod (q * 3)))
      (inv_mul_cancel v)
  have hx : (b : ZMod (q * 3)) = (x.val : ZMod (q * 3)) * (s : ZMod (q * 3)) := by
    rw [ZMod.natCast_zmod_val]
    dsimp only [x]
    rw [mul_assoc, hv, mul_one]
  have hz : (((b : Int) - (x.val : Int) * (s : Int) : Int) : ZMod (q * 3)) = 0 := by
    push_cast
    rw [hx]
    ring
  have hd : Dvd.dvd ((q * 3 : Nat) : Int) ((b : Int) - (x.val : Int) * (s : Int)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  let k : Int := Classical.choose hd
  have hk : (b : Int) - (x.val : Int) * (s : Int) = ((q * 3 : Nat) : Int) * k :=
    Classical.choose_spec hd
  refine Exists.intro x.val (And.intro x.val_lt (Exists.intro k ?_))
  nlinarith only [hk]

/-- The residue representative and signed shift are unique on the full unit domain. -/
theorem shifted_cubic_parameters_unique {q : Nat} [NeZero q]
    (s b a c : Nat) (k l : Int) (hcop : Nat.Coprime s (q * 3))
    (ha : a < q * 3) (hc : c < q * 3)
    (hb1 : (b : Int) = (a : Int) * (s : Int) + k * ((q * 3 : Nat) : Int))
    (hb2 : (b : Int) = (c : Int) * (s : Int) + l * ((q * 3 : Nat) : Int)) :
    a = c /\ k = l := by
  let v : Units (ZMod (q * 3)) := ZMod.unitOfCoprime s hcop
  have hv : (s : ZMod (q * 3)) *
      ((Inv.inv v : Units (ZMod (q * 3))) : ZMod (q * 3)) = 1 := by
    change (v : ZMod (q * 3)) *
      ((Inv.inv v : Units (ZMod (q * 3))) : ZMod (q * 3)) = 1
    exact congrArg (fun w : Units (ZMod (q * 3)) => (w : ZMod (q * 3)))
      (mul_inv_cancel v)
  have he := (shifted_input_mod q a s b k hb1).symm.trans
    (shifted_input_mod q c s b l hb2)
  have hZ : (a : ZMod (q * 3)) = (c : ZMod (q * 3)) := by
    calc
      _ = ((a : ZMod (q * 3)) * (s : ZMod (q * 3))) *
          ((Inv.inv v : Units (ZMod (q * 3))) : ZMod (q * 3)) := by
        rw [mul_assoc, hv, mul_one]
      _ = ((c : ZMod (q * 3)) * (s : ZMod (q * 3))) *
          ((Inv.inv v : Units (ZMod (q * 3))) : ZMod (q * 3)) :=
        congrArg (fun z : ZMod (q * 3) =>
          z * ((Inv.inv v : Units (ZMod (q * 3))) : ZMod (q * 3))) he
      _ = _ := by rw [mul_assoc, hv, mul_one]
  have hac : a = c := by
    have heq := congrArg (fun z : ZMod (q * 3) => z.val) hZ
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] using heq
  refine And.intro hac ?_
  have hprod : k * ((q * 3 : Nat) : Int) = l * ((q * 3 : Nat) : Int) := by
    rw [hac] at hb1
    nlinarith only [hb1, hb2]
  have hM : (0 : Int) < ((q * 3 : Nat) : Int) :=
    Nat.cast_pos.mpr (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne q)) (by decide))
  rcases lt_trichotomy k l with hlt | heq | hgt
  . exact False.elim ((ne_of_lt (mul_lt_mul_of_pos_right hlt hM)) hprod)
  . exact heq
  . exact False.elim ((ne_of_lt (mul_lt_mul_of_pos_right hgt hM)) hprod.symm)

end PrimeFactorOscillations.CarmichaelCubicResonance

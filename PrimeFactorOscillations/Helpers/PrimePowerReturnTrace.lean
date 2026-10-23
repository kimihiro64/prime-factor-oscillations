/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimePowerReturnSpectrum

/-!
# Exact last-layer cancellation in the native return law

The actual last-layer units permute the power kernel when the conductor
prime divides the exponent. Their complete phase sum is retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

open scoped BigOperators

theorem square_zero_one_add_pow {R : Type*} [CommRing R]
    (t : R) (ht : t * t = 0) (k : Nat) :
    (1 + t) ^ k = 1 + (k : R) * t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Nat.cast_add, Nat.cast_one]
    calc
      (1 + (k : R) * t) * (1 + t) =
          1 + ((k : R) + 1) * t + (k : R) * (t * t) := by ring
      _ = 1 + ((k : R) + 1) * t := by rw [ht, mul_zero, add_zero]

def squareZeroUnit {R : Type*} [CommRing R] (t : R) (ht : t * t = 0) :
    Units R where
  val := 1 + t
  inv := 1 - t
  val_inv := by
    calc
      (1 + t) * (1 - t) = 1 - t * t := by ring
      _ = 1 := by rw [ht, sub_zero]
  inv_val := by
    calc
      (1 - t) * (1 + t) = 1 - t * t := by ring
      _ = 1 := by rw [ht, sub_zero]

def lastLayer (p a : Nat) [NeZero p] : ZMod (p ^ (a + 2)) :=
  ((p ^ (a + 1) : Nat) : ZMod (p ^ (a + 2)))

theorem prime_mul_last_layer (p a : Nat) [NeZero p] :
    (p : ZMod (p ^ (a + 2))) * lastLayer p a = 0 := by
  simp only [lastLayer, <- Nat.cast_mul, <- pow_succ', CharP.cast_eq_zero]

theorem last_layer_square_zero (p a : Nat) [NeZero p] :
    lastLayer p a * lastLayer p a = 0 := by
  have hn : p ^ (a + 1) * p ^ (a + 1) = p ^ (a + 2) * p ^ a := by
    rw [<- pow_add, <- pow_add]
    congr 1
    omega
  unfold lastLayer
  rw [<- Nat.cast_mul, hn, Nat.cast_mul]
  simp only [CharP.cast_eq_zero, zero_mul]

theorem last_layer_nonzero (p a : Nat) [NeZero p] (hp : Nat.Prime p) :
    Not (lastLayer p a = 0) := by
  have hlt : p ^ (a + 1) < p ^ (a + 2) := by
    calc
      p ^ (a + 1) = p ^ (a + 1) * 1 := (mul_one _).symm
      _ < p ^ (a + 1) * p := Nat.mul_lt_mul_of_pos_left hp.one_lt (pow_pos hp.pos _)
      _ = p ^ (a + 2) := (pow_succ _ _).symm
  intro hz
  have hd : Dvd.dvd (p ^ (a + 2)) (p ^ (a + 1)) :=
    (CharP.cast_eq_zero_iff (ZMod (p ^ (a + 2))) (p ^ (a + 2)) _).mp hz
  exact Nat.not_le_of_gt hlt (Nat.le_of_dvd (pow_pos hp.pos _) hd)

def lastLayerReturn (p a k : Nat) [NeZero p] (hpk : Dvd.dvd p k)
    (j : Fin p) : powerKernel (p ^ (a + 2)) k := by
  have hsq : (lastLayer p a * (j.val : ZMod (p ^ (a + 2)))) *
      (lastLayer p a * (j.val : ZMod (p ^ (a + 2)))) = 0 := by
    calc
      _ = (lastLayer p a * lastLayer p a) * (j.val : ZMod (p ^ (a + 2))) ^ 2 := by ring
      _ = 0 := by rw [last_layer_square_zero, zero_mul]
  refine Subtype.mk (squareZeroUnit _ hsq) ?_
  change (squareZeroUnit _ hsq) ^ k = 1
  apply Units.ext
  change (1 + lastLayer p a * (j.val : ZMod (p ^ (a + 2)))) ^ k = 1
  rw [square_zero_one_add_pow _ hsq]
  choose d hd using hpk
  rw [hd, Nat.cast_mul]
  calc
    _ = 1 + (d : ZMod (p ^ (a + 2))) * j.val *
        ((p : ZMod (p ^ (a + 2))) * lastLayer p a) := by ring
    _ = 1 := by rw [prime_mul_last_layer, mul_zero, add_zero]

theorem last_layer_return_value (p a k : Nat) [NeZero p] (hpk : Dvd.dvd p k)
    (j : Fin p) :
    ((lastLayerReturn p a k hpk j).val : ZMod (p ^ (a + 2))) =
      1 + lastLayer p a * (j.val : ZMod (p ^ (a + 2))) := rfl

theorem last_layer_phase_sum (p a h : Nat) [NeZero p] (hp : Nat.Prime p)
    (hh : Nat.Coprime h (p ^ (a + 2))) (x : Units (ZMod (p ^ (a + 2)))) :
    Finset.univ.sum (fun j : Fin p => ZMod.stdAddChar
      ((h : ZMod (p ^ (a + 2))) *
        ((x : ZMod (p ^ (a + 2))) * (1 + lastLayer p a * (j.val : ZMod (p ^ (a + 2))))))) = 0 := by
  let b : ZMod (p ^ (a + 2)) := (h : ZMod (p ^ (a + 2))) * x
  let z : Complex := ZMod.stdAddChar (b * lastLayer p a)
  have hb : IsUnit b := ((ZMod.isUnit_iff_coprime h _).mpr hh).mul x.isUnit
  have hnz : Not (z = 1) := by
    intro hz
    have hzero : b * lastLayer p a = 0 := by
      apply ZMod.injective_stdAddChar
      simpa only [z, AddChar.map_zero_eq_one] using hz
    have heq : b * lastLayer p a = b * 0 := by simpa only [mul_zero] using hzero
    exact last_layer_nonzero p a hp (hb.mul_right_inj.mp heq)
  have hpow : z ^ p = 1 := by
    rw [<- AddChar.map_nsmul_eq_pow]
    have heq : HSMul.hSMul p (b * lastLayer p a) = 0 := by
      rw [nsmul_eq_mul]
      calc
        _ = b * ((p : ZMod (p ^ (a + 2))) * lastLayer p a) := by ring
        _ = 0 := by rw [prime_mul_last_layer, mul_zero]
    rw [heq, AddChar.map_zero_eq_one]
  have hgeom := geom_sum_mul z p
  rw [hpow, sub_self] at hgeom
  have hsum : Finset.univ.sum (fun j : Fin p => z ^ j.val) = 0 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hnz)
  have hchar (j : Fin p) : ZMod.stdAddChar
      ((h : ZMod (p ^ (a + 2))) *
        ((x : ZMod (p ^ (a + 2))) * (1 + lastLayer p a * (j.val : ZMod (p ^ (a + 2)))))) =
      ZMod.stdAddChar b * z ^ j.val := by
    rw [<- mul_assoc]
    change ZMod.stdAddChar (b * (1 + lastLayer p a * (j.val : ZMod (p ^ (a + 2))))) = _
    rw [mul_add, mul_one, AddChar.map_add_eq_mul]
    have he := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := p ^ (a + 2)))
      j.val (b * lastLayer p a)
    have hnat : HSMul.hSMul j.val (b * lastLayer p a) =
        b * (lastLayer p a * (j.val : ZMod (p ^ (a + 2)))) := by
      rw [nsmul_eq_mul]
      ring
    rw [hnat] at he
    exact congrArg (fun w : Complex => ZMod.stdAddChar b * w) he
  simp_rw [hchar]
  rw [<- Finset.mul_sum, hsum, mul_zero]

/-- The complete return trace cancels when the prime divides the power. -/
theorem primitive_return_zero (p a k h : Nat) [NeZero p] (hp : Nat.Prime p)
    (hpk : Dvd.dvd p k) (hh : Nat.Coprime h (p ^ (a + 2))) :
    returnTransform (p ^ (a + 2)) k h = 0 := by
  classical
  have hperm (j : Fin p) : Finset.univ.sum
      (fun u : powerKernel (p ^ (a + 2)) k => ZMod.stdAddChar
        ((h : ZMod (p ^ (a + 2))) *
          ((u * lastLayerReturn p a k hpk j).val : ZMod (p ^ (a + 2))))) =
      returnTransform (p ^ (a + 2)) k h :=
    _root_.Equiv.sum_comp (Equiv.mulRight (lastLayerReturn p a k hpk j))
      (fun u : powerKernel (p ^ (a + 2)) k =>
        ZMod.stdAddChar ((h : ZMod (p ^ (a + 2))) * (u.val : ZMod (p ^ (a + 2)))))
  have hsum : Finset.univ.sum
      (fun _ : Fin p => returnTransform (p ^ (a + 2)) k h) = 0 := by
    calc
      _ = Finset.univ.sum (fun j : Fin p => Finset.univ.sum
          (fun u : powerKernel (p ^ (a + 2)) k => ZMod.stdAddChar
            ((h : ZMod (p ^ (a + 2))) *
              ((u * lastLayerReturn p a k hpk j).val : ZMod (p ^ (a + 2)))))) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hperm j).symm
      _ = Finset.univ.sum (fun u : powerKernel (p ^ (a + 2)) k =>
          Finset.univ.sum (fun j : Fin p => ZMod.stdAddChar
            ((h : ZMod (p ^ (a + 2))) *
              ((u * lastLayerReturn p a k hpk j).val : ZMod (p ^ (a + 2)))))) :=
        Finset.sum_comm
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro u _
        simpa only [Subgroup.coe_mul, Units.val_mul, last_layer_return_value] using
          (last_layer_phase_sum p a h hp hh u.val)
  have hm : (p : Complex) * returnTransform (p ^ (a + 2)) k h = 0 := by
    simpa [nsmul_eq_mul] using hsum
  exact (mul_eq_zero.mp hm).resolve_left (by exact_mod_cast hp.ne_zero)

theorem primitive_centered_zero_iff (p a k h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (hh : Nat.Coprime h (p ^ (a + 2))) :
    centeredTransform (p ^ (a + 2)) k h = 0 <-> Dvd.dvd p k := by
  constructor
  { intro hz
    by_contra hpk
    exact primitive_centered_nonzero p a k h hp hp2 hpk hh hz }
  { intro hpk
    rw [centeredTransform, primitive_return_zero p a k h hp hpk hh,
      primitive_unit_mask p a h hp hh, mul_zero, mul_zero, sub_self] }

end PrimeFactorOscillations.PrimePowerReturnSpectrum

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRationalModelBlocks

/-! # Exact constant and parity identification of the two exceptional modes

The complete denominator-one/two operator is the constant kernel minus
the parity kernel. The auxiliary grid disappears from its entries.
No numerical root-of-unity approximation is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_half_grid_character {R : Nat} [NeZero R] (hEven : Dvd.dvd 2 R) :
    ZMod.stdAddChar (N := R) (-((R / 2 : Nat) : ZMod R)) = (-1 : Complex) := by
  let c : ZMod R := ((R / 2 : Nat) : ZMod R)
  let z : Complex := ZMod.stdAddChar (-c)
  have hR : 0 < R := NeZero.pos R
  have hR2 : 2 <= R := Nat.le_of_dvd hR hEven
  have hProduct : (R / 2) * 2 = R := Nat.div_mul_cancel hEven
  have hDouble : (2 : ZMod R) * c = 0 := by
    have h : (((R / 2) * 2 : Nat) : ZMod R) = 0 := by rw [hProduct]; simp
    push_cast at h
    simpa only [mul_comm] using h
  have hC : Not (c = 0) := by
    have hPos : 0 < R / 2 := Nat.div_pos hR2 (by decide)
    have hLt : R / 2 < R := Nat.div_lt_self hR (by decide)
    intro hZero
    have h := congrArg (fun x : ZMod R => x.val) hZero
    simp only [c, ZMod.val_natCast_of_lt hLt, ZMod.val_zero] at h
    omega
  have hArg : (2 : Nat) * (-c) = (0 : ZMod R) := by
    change (2 : ZMod R) * (-c) = 0
    rw [mul_neg, hDouble, neg_zero]
  have hSquare : z ^ 2 = 1 := by
    dsimp [z]
    rw [<- AddChar.map_nsmul_eq_pow]
    simp only [nsmul_eq_mul, hArg, AddChar.map_zero_eq_one]
  have hNotOne : Not (z = 1) := by
    intro hOne
    have hZero : -c = (0 : ZMod R) := ZMod.injective_stdAddChar
      (by simpa only [z, AddChar.map_zero_eq_one] using hOne)
    exact hC (neg_eq_zero.mp hZero)
  have hProductZero : (z - 1) * (z + 1) = 0 := by
    calc
      _ = z ^ 2 - 1 := by ring
      _ = 0 := by rw [hSquare]; ring
  have hAdd : z + 1 = 0 := (mul_eq_zero.mp hProductZero).resolve_left (sub_ne_zero.mpr hNotOne)
  change z = -1
  calc
    _ = (z + 1) - 1 := by ring
    _ = _ := by rw [hAdd]; ring

theorem hamiltonian_half_grid_power {R : Nat} [NeZero R] (hEven : Dvd.dvd 2 R) (t : Nat) :
    ZMod.stdAddChar (N := R) (-((R / 2 : Nat) : ZMod R) * (t : ZMod R)) =
      (-1 : Complex) ^ t := by
  have hArg : -((R / 2 : Nat) : ZMod R) * (t : ZMod R) =
      t * (-((R / 2 : Nat) : ZMod R)) := by ring
  rw [hArg, <- nsmul_eq_mul, AddChar.map_nsmul_eq_pow, hamiltonian_half_grid_character hEven]

theorem hamiltonian_rational_low_term_one {R : Nat} [NeZero R]
    (Q t : Nat) (u : lpfRationalCenters Q) (hDen : u.1.val + 1 = 1) :
    hamiltonianRationalLowCoefficient Q u *
      ZMod.stdAddChar ((-hamiltonianRationalCenter R Q u) * (t : ZMod R)) = 1 := by
  have hVal : (u.2 : ZMod (u.1.val + 1)).val = 0 := by
    have h := ZMod.val_lt (u.2 : ZMod (u.1.val + 1))
    omega
  have hCenter : hamiltonianRationalCenter R Q u = 0 := by
    simp only [hamiltonianRationalCenter, lpfRationalGridPoint, hVal,
      Nat.mul_zero, Nat.cast_zero, Int.cast_zero, zero_add]
  have hRho : lpfRationalCoefficient 1 = (1 : Complex) := by norm_num [lpfRationalCoefficient]
  unfold hamiltonianRationalLowCoefficient
  rw [if_pos (Or.inl hDen), hDen, hRho, hCenter]
  simp

theorem hamiltonian_rational_low_term_two {R : Nat} [NeZero R]
    (hEven : Dvd.dvd 2 R) (Q t : Nat) (u : lpfRationalCenters Q)
    (hDen : u.1.val + 1 = 2) :
    hamiltonianRationalLowCoefficient Q u *
      ZMod.stdAddChar ((-hamiltonianRationalCenter R Q u) * (t : ZMod R)) =
        -((-1 : Complex) ^ t) := by
  have hCoprime := ZMod.val_coe_unit_coprime u.2
  have hLt : (u.2 : ZMod (u.1.val + 1)).val < 2 := by
    have h := ZMod.val_lt (u.2 : ZMod (u.1.val + 1))
    omega
  have hNotZero : Not ((u.2 : ZMod (u.1.val + 1)).val = 0) := by
    intro hZero
    have h : Nat.Coprime 0 2 := by simpa only [hZero, hDen] using hCoprime
    norm_num at h
  have hVal : (u.2 : ZMod (u.1.val + 1)).val = 1 := by omega
  have hCenter : hamiltonianRationalCenter R Q u = ((R / 2 : Nat) : ZMod R) := by
    simp only [hamiltonianRationalCenter, lpfRationalGridPoint, hVal, hDen,
      Nat.mul_one, Int.cast_zero, add_zero]
  have hRho : lpfRationalCoefficient 2 = (-1 : Complex) := by
    norm_num [lpfRationalCoefficient, ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      Nat.totient_two]
  unfold hamiltonianRationalLowCoefficient
  rw [if_pos (Or.inr hDen), hDen, hRho, hCenter, hamiltonian_half_grid_power hEven]
  ring

theorem hamiltonian_rational_low_sum {R : Nat} [NeZero R]
    (Q t : Nat) (hQ : 2 <= Q) (hEven : Dvd.dvd 2 R) :
    Finset.univ.sum (fun u : lpfRationalCenters Q =>
      hamiltonianRationalLowCoefficient Q u *
        ZMod.stdAddChar ((-hamiltonianRationalCenter R Q u) * (t : ZMod R))) =
      1 - (-1 : Complex) ^ t := by
  classical
  let q0 : Fin Q := Fin.mk 0 (by omega)
  let q1 : Fin Q := Fin.mk 1 (by omega)
  let f := fun q : Fin Q => Finset.univ.sum (fun a : Units (ZMod (q.val + 1)) =>
    hamiltonianRationalLowCoefficient Q (Sigma.mk q a) *
      ZMod.stdAddChar ((-hamiltonianRationalCenter R Q (Sigma.mk q a)) * (t : ZMod R)))
  have h01 : Not (q0 = q1) := by
    intro h
    have hVal := congrArg Fin.val h
    norm_num [q0, q1] at hVal
  have h0 : f q0 = 1 := by
    have hTerm (a : Units (ZMod (q0.val + 1))) :=
      hamiltonian_rational_low_term_one (R := R) Q t (Sigma.mk q0 a) (by rfl)
    dsimp only [f]
    simp_rw [hTerm]
    simp [q0, ZMod.card_units_eq_totient]
  have h1 : f q1 = -((-1 : Complex) ^ t) := by
    have hTerm (a : Units (ZMod (q1.val + 1))) :=
      hamiltonian_rational_low_term_two hEven Q t (Sigma.mk q1 a) (by rfl)
    dsimp only [f]
    simp_rw [hTerm]
    simp [q1, ZMod.card_units_eq_totient, Nat.totient_two]
  have hOther (q : Fin Q) (h0q : Not (q = q0)) (h1q : Not (q = q1)) : f q = 0 := by
    have hNot0 : Not (q.val + 1 = 1) := by
      intro h
      apply h0q
      apply Fin.ext
      dsimp [q0]
      omega
    have hNot1 : Not (q.val + 1 = 2) := by
      intro h
      apply h1q
      apply Fin.ext
      dsimp [q1]
      omega
    have hNot : Not (Or (q.val + 1 = 1) (q.val + 1 = 2)) := by
      intro h
      exact h.elim hNot0 hNot1
    dsimp only [f]
    apply Finset.sum_eq_zero
    intro a ha
    simp only [hamiltonianRationalLowCoefficient, hNot, ite_false, zero_mul]
  have hTerm (q : Fin Q) : f q =
      (if q = q0 then 1 else 0) + (if q = q1 then -((-1 : Complex) ^ t) else 0) := by
    by_cases hq0 : q = q0
    . subst q
      simp only [h0, ite_true, h01, ite_false, add_zero]
    . by_cases hq1 : q = q1
      . subst q
        simp only [h1, hq0, ite_false, ite_true, zero_add]
      . simp only [hOther q hq0 hq1, hq0, hq1, ite_false, add_zero]
  rw [Fintype.sum_sigma]
  change Finset.univ.sum f = _
  simp_rw [hTerm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

def hamiltonianConstantParityMatrix (n : Nat) : Matrix (Fin n) (Fin n) Complex :=
  fun i j => (1 - (-1 : Complex) ^ ((i.val + 1) + (j.val + 1))) / (n : Complex)

theorem hamiltonian_rational_low_operator_eq {R : Nat} [NeZero R]
    (n Q : Nat) (hQ : 2 <= Q) (hEven : Dvd.dvd 2 R) :
    hamiltonianRationalOperator n R Q (hamiltonianRationalLowCoefficient Q) =
      hamiltonianConstantParityMatrix n := by
  ext i j
  rw [hamiltonian_rational_operator_apply, hamiltonian_rational_low_sum Q _ hQ hEven]
  rfl

end PrimeFactorOscillations.LPF

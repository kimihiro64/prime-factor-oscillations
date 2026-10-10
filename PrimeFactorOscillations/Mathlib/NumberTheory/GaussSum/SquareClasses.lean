/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.DiscriminantSupport
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.QuadraticEnergy

/-!
# Square classes in finite quadratic cusp packets

Over a finite residue-local ring of odd characteristic with a quartic residue
character, the complete quadratic Gauss factor is globally either constant
or quadratic on units. The shared Fourier packet consequently has either a
quadratic-character branch or an unweighted unit-sum branch. Its zero-frequency
energy retains the exceptional full unit-count contribution.

These are exact complete-sum identities, not estimates for incomplete sums.
The parity of the prime-power depth and concrete Gaussian quotient instances
are not asserted here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace RingHom

variable {R F : Type*} [CommRing R] [Fintype R] [Field F]

/-- A square residue of a unit lifts to a unit square over a finite odd residue-local ring. -/
theorem exists_unit_sq_of_isSquare_residue (rho : RingHom R F)
    (hsurj : Function.Surjective rho)
    (hunit : forall x : R, Not (rho x = 0) -> IsUnit x)
    (h2 : Not ((2 : F) = 0)) (u : Units R) (hsq : IsSquare (rho u)) :
    exists v : Units R, v ^ 2 = u := by
  classical
  let z := Classical.choose hsq
  have hz : rho u = z * z := Classical.choose_spec hsq
  have hz0 : Not (z = 0) := by
    intro h
    apply (u.isUnit.map rho).ne_zero
    rw [hz, h, zero_mul]
  let v := Classical.choose (hsurj z)
  have hv : rho v = z := Classical.choose_spec (hsurj z)
  have huv : IsUnit v := hunit v (by rw [hv]; exact hz0)
  let vu : Units R := huv.unit
  have hvu : (vu : R) = v := IsUnit.unit_spec huv
  have hfirst : rho u = (rho vu) ^ 2 := by rw [hvu, hv, pow_two]; exact hz
  have hratio : rho ((u * (Inv.inv vu) ^ 2 : Units R) : R) = 1 := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hfirst]
    rw [<- mul_pow, <- rho.map_mul]
    simp
  have hex := exists_sq_eq_of_residue_one rho hunit h2
    ((u * (Inv.inv vu) ^ 2 : Units R) : R) hratio
  let w := Classical.choose hex
  have hw := Classical.choose_spec hex
  have huw : IsUnit w := hunit w (by rw [hw.1]; exact one_ne_zero)
  let wu : Units R := huw.unit
  have hwu : wu ^ 2 = u * (Inv.inv vu) ^ 2 := by
    apply Units.ext
    simpa only [wu, w, Units.val_pow_eq_pow_val, IsUnit.unit_spec] using hw.2
  refine Exists.intro (vu * wu) ?_
  rw [mul_pow, hwu]
  simp [mul_left_comm]

end RingHom

namespace AddChar

variable {R : Type*} [CommRing R] [Fintype R]

/-- Changing a unit coefficient by a square preserves its complete quadratic sum. -/
theorem sum_quadraticPhase_mul_unit_sq (psi : AddChar R Complex) (a v : Units R) :
    Finset.sum Finset.univ (fun r : R => psi (((a * v ^ 2 : Units R) : R) * r ^ 2)) =
      Finset.sum Finset.univ (fun r : R => psi ((a : R) * r ^ 2)) := by
  classical
  calc
    _ = Finset.sum Finset.univ (fun r : R => psi ((a : R) * ((v : R) * r) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      congr 1
      ring
    _ = _ := Fintype.sum_bijective _ v.mulLeft_bijective _ _ (fun _ => rfl)

/-- If minus one is a unit square, every complete quadratic sum is real. -/
theorem conj_sum_quadraticPhase_of_unit_sq_neg_one
    (psi : AddChar R Complex) (v : Units R) (hv : v ^ 2 = -1) (h : Units R) :
    (starRingEnd Complex) (Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2))) =
      Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2)) := by
  classical
  calc
    _ = Finset.sum Finset.univ (fun r : R => psi (-((h : R) * r ^ 2))) := by
      rw [map_sum]
      simp_rw [<- AddChar.map_neg_eq_conj]
    _ = Finset.sum Finset.univ (fun r : R => psi (((h * v ^ 2 : Units R) : R) * r ^ 2)) := by
      rw [hv]
      simp
    _ = _ := sum_quadraticPhase_mul_unit_sq psi h v

/-- In the real quadratic-sum case, its square is exactly the finite-ring size. -/
theorem sq_sum_quadraticPhase_of_unit_sq_neg_one
    (psi : AddChar R Complex) (hpsi : psi.IsPrimitive) (h2 : IsUnit (2 : R))
    (v : Units R) (hv : v ^ 2 = -1) (h : Units R) :
    (Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2))) ^ 2 =
      (Fintype.card R : Complex) := by
  have hn := normSq_quadraticPhase_unit psi hpsi h2 h (0 : R)
  simp only [zero_mul, add_zero] at hn
  have heq := Complex.mul_conj (Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2)))
  rw [conj_sum_quadraticPhase_of_unit_sq_neg_one psi v hv h, <- pow_two, hn] at heq
  simpa only [Complex.ofReal_natCast] using heq

variable {F : Type*} [Field F] [Fintype F]

/-- Quadratic Gauss factors agree whenever their unit residues have the same square class. -/
theorem sum_quadraticPhase_eq_of_quadraticChar_eq [DecidableEq F]
    (rho : RingHom R F) (hsurj : Function.Surjective rho)
    (hunit : forall x : R, Not (rho x = 0) -> IsUnit x)
    (hF : Not (ringChar F = 2)) (psi : AddChar R Complex)
    (a b : Units R) (hab : quadraticChar F (rho a) = quadraticChar F (rho b)) :
    Finset.sum Finset.univ (fun r : R => psi ((a : R) * r ^ 2)) =
      Finset.sum Finset.univ (fun r : R => psi ((b : R) * r ^ 2)) := by
  classical
  let u : Units R := a * Inv.inv b
  have hinv : rho (Inv.inv b : Units R) = Inv.inv (rho b) := by
    change Units.val ((Units.map rho.toMonoidHom) (Inv.inv b)) = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    rfl
  have hq : quadraticChar F (rho u) = 1 := by
    simp only [u, Units.val_mul, map_mul, hinv]
    rw [<- MulChar.inv_apply', (quadraticChar_isQuadratic F).inv, hab,
      <- pow_two, quadraticChar_sq_one (b.isUnit.map rho).ne_zero]
  have hsquare : IsSquare (rho u) :=
    (quadraticChar_one_iff_isSquare (u.isUnit.map rho).ne_zero).mp hq
  have hex := RingHom.exists_unit_sq_of_isSquare_residue rho hsurj hunit
    (Ring.two_ne_zero hF) u hsquare
  let v := Classical.choose hex
  have hv : v ^ 2 = u := Classical.choose_spec hex
  have ha : a = b * v ^ 2 := by rw [hv]; simp [u, mul_left_comm]
  rw [ha]
  exact sum_quadraticPhase_mul_unit_sq psi b v

/-- The Gauss factor is either constant or quadratic on every unit residue class at once. -/
theorem quadraticGauss_residue_dichotomy [DecidableEq F]
    (rho : RingHom R F) (hsurj : Function.Surjective rho)
    (hunit : forall x : R, Not (rho x = 0) -> IsUnit x)
    (hF : Not (ringChar F = 2)) (hneg : IsSquare (-1 : F))
    (psi : AddChar R Complex) (hpsi : psi.IsPrimitive) :
    let G : Units R -> Complex := fun h =>
      Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2))
    Or (forall h : Units R, G h = G 1)
      (forall h : Units R, G h = (quadraticChar F (rho h) : Complex) * G 1) := by
  classical
  let G : Units R -> Complex := fun h =>
    Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2))
  change Or (forall h : Units R, G h = G 1)
    (forall h : Units R, G h = (quadraticChar F (rho h) : Complex) * G 1)
  have h2R : IsUnit (2 : R) := hunit 2 (by simpa only [map_ofNat] using Ring.two_ne_zero hF)
  have hnegRes : IsSquare (rho ((-1 : Units R) : R)) := by
    simpa only [Units.coe_neg_one, map_neg, map_one] using hneg
  have hex := RingHom.exists_unit_sq_of_isSquare_residue rho hsurj hunit
    (Ring.two_ne_zero hF) (-1 : Units R) hnegRes
  let v := Classical.choose hex
  have hv : v ^ 2 = -1 := Classical.choose_spec hex
  have hGs (h : Units R) : G h ^ 2 = (Fintype.card R : Complex) :=
    sq_sum_quadraticPhase_of_unit_sq_neg_one psi hpsi h2R v hv h
  let z := Classical.choose (FiniteField.exists_nonsquare hF)
  have hz : Not (IsSquare z) := Classical.choose_spec (FiniteField.exists_nonsquare hF)
  have hz0 : Not (z = 0) := by intro h; apply hz; rw [h]; exact IsSquare.zero
  let c0 := Classical.choose (hsurj z)
  have hc0 : rho c0 = z := Classical.choose_spec (hsurj z)
  have huc : IsUnit c0 := hunit c0 (by rw [hc0]; exact hz0)
  let c : Units R := huc.unit
  have hc : quadraticChar F (rho c) = -1 := by
    apply quadraticChar_neg_one_iff_not_isSquare.mpr
    simpa only [c, IsUnit.unit_spec, hc0] using hz
  have hsame (h : Units R) (hh : quadraticChar F (rho h) = 1) : G h = G 1 := by
    apply sum_quadraticPhase_eq_of_quadraticChar_eq rho hsurj hunit hF psi
    simpa only [Units.val_one, map_one] using hh
  have hother (h : Units R) (hh : quadraticChar F (rho h) = -1) : G h = G c := by
    apply sum_quadraticPhase_eq_of_quadraticChar_eq rho hsurj hunit hF psi
    exact hh.trans hc.symm
  have hsign : Or (G c = G 1) (G c = -G 1) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp ((hGs c).trans (hGs 1).symm)
  rcases hsign with hplus | hminus
  . left
    intro h
    rcases quadraticChar_dichotomy (h.isUnit.map rho).ne_zero with hh | hh
    . exact hsame h hh
    . exact (hother h hh).trans hplus
  . right
    intro h
    rcases quadraticChar_dichotomy (h.isUnit.map rho).ne_zero with hh | hh
    . rw [hh, Int.cast_one, one_mul]
      exact hsame h hh
    . rw [hh, Int.cast_neg, Int.cast_one, neg_one_mul]
      exact (hother h hh).trans hminus

end AddChar

namespace MulChar

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A nontrivial quartic character forces minus one into the square class. -/
theorem isSquare_neg_one_of_quartic (hF : Not (ringChar F = 2))
    (chi : MulChar F Complex) (hfour : chi ^ 4 = 1) (htwo : Not (chi ^ 2 = 1)) :
    IsSquare (-1 : F) := by
  have hval : (chi ^ 2) (-1 : F) = 1 := by
    rw [MulChar.pow_apply' chi (by decide : Not ((2 : Nat) = 0)), <- map_pow]
    simp
  rw [quartic_sq_eq_quadraticChar hF chi hfour htwo] at hval
  change (quadraticChar F (-1 : F) : Complex) = 1 at hval
  have hq : quadraticChar F (-1 : F) = 1 := by exact_mod_cast hval
  exact (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (one_ne_zero : Not ((1 : F) = 0)))).mp hq

/-- A quartic residue character supplies every square-class hypothesis of the Gauss dichotomy. -/
theorem quartic_quadraticGauss_dichotomy {R : Type*} [CommRing R] [Fintype R]
    (rho : RingHom R F) (hsurj : Function.Surjective rho)
    (hunit : forall x : R, Not (rho x = 0) -> IsUnit x)
    (hF : Not (ringChar F = 2)) (chi : MulChar F Complex)
    (hfour : chi ^ 4 = 1) (htwo : Not (chi ^ 2 = 1))
    (psi : AddChar R Complex) (hpsi : psi.IsPrimitive) :
    let G : Units R -> Complex := fun h =>
      Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2))
    Or (forall h : Units R, G h = G 1)
      (forall h : Units R, G h = (chi ^ 2) (rho h) * G 1) := by
  have hc := AddChar.quadraticGauss_residue_dichotomy rho hsurj hunit hF
    (isSquare_neg_one_of_quartic hF chi hfour htwo) psi hpsi
  rw [quartic_sq_eq_quadraticChar hF chi hfour htwo]
  exact hc

/-- The shared packet is globally in the quadratic-Gauss branch or the unit-sum branch. -/
theorem quartic_jointFourier_dichotomy {R : Type*} [CommRing R] [Fintype R]
    [Fintype (Units R)] (rho : RingHom R F) (hsurj : Function.Surjective rho)
    (hunit : forall x : R, Not (rho x = 0) -> IsUnit x)
    (hF : Not (ringChar F = 2)) (chi : MulChar F Complex)
    (hfour : chi ^ 4 = 1) (htwo : Not (chi ^ 2 = 1))
    (psi : AddChar R Complex) (hpsi : psi.IsPrimitive) :
    let G : Units R -> Complex := fun h =>
      Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2))
    Or
      (forall A : R,
        Finset.sum Finset.univ (fun h : Units R =>
          (chi ^ 2) (rho h) * G h * psi (A * (h : R))) =
          G 1 * Finset.sum Finset.univ (fun h : Units R => (chi ^ 2) (rho h) * psi (A * (h : R))))
      (forall A : R,
        Finset.sum Finset.univ (fun h : Units R =>
          (chi ^ 2) (rho h) * G h * psi (A * (h : R))) =
          G 1 * Finset.sum Finset.univ (fun h : Units R => psi (A * (h : R)))) := by
  classical
  let G : Units R -> Complex := fun h =>
    Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2))
  have hd := quartic_quadraticGauss_dichotomy rho hsurj hunit hF chi hfour htwo psi hpsi
  change Or (forall h : Units R, G h = G 1)
    (forall h : Units R, G h = (chi ^ 2) (rho h) * G 1) at hd
  change Or (forall A : R, Finset.sum Finset.univ (fun h : Units R =>
      (chi ^ 2) (rho h) * G h * psi (A * (h : R))) =
        G 1 * Finset.sum Finset.univ (fun h : Units R => (chi ^ 2) (rho h) * psi (A * (h : R))))
    (forall A : R, Finset.sum Finset.univ (fun h : Units R =>
      (chi ^ 2) (rho h) * G h * psi (A * (h : R))) =
        G 1 * Finset.sum Finset.univ (fun h : Units R => psi (A * (h : R))))
  rcases hd with hconst | hquad
  . left
    intro A
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [hconst h]
    ring
  . right
    intro A
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [hquad h]
    have hsq : ((chi ^ 2) (rho h)) ^ 2 = 1 := by
      rw [<- MulChar.pow_apply' (chi ^ 2) (by decide : Not ((2 : Nat) = 0)), <- pow_mul]
      change (chi ^ 4) (rho h) = 1
      rw [hfour, MulChar.one_apply (h.isUnit.map rho)]
    calc
      _ = ((chi ^ 2) (rho h)) ^ 2 * (G 1 * psi (A * (h : R))) := by ring
      _ = _ := by rw [hsq, one_mul]

omit [Fintype F] [DecidableEq F] in
/-- A nontrivial residue character has zero total over the lifted unit group. -/
theorem sum_unit_residue_eq_zero {R : Type*} [CommRing R] [Fintype R] [Fintype (Units R)]
    (rho : RingHom R F) (hsurj : Function.Surjective rho)
    (hunit : forall x : R, Not (rho x = 0) -> IsUnit x)
    (delta : MulChar F Complex) (hdelta : Not (delta = 1)) :
    Finset.sum Finset.univ (fun h : Units R => delta (rho h)) = 0 := by
  classical
  have hex := MulChar.ne_one_iff.mp hdelta
  let z : Units F := Classical.choose hex
  have hz : Not (delta z = 1) := Classical.choose_spec hex
  let x := Classical.choose (hsurj (z : F))
  have hx : rho x = z := Classical.choose_spec (hsurj (z : F))
  have hux : IsUnit x := hunit x (by rw [hx]; exact z.ne_zero)
  let v : Units R := hux.unit
  have hv : Not (delta (rho v) = 1) := by simpa only [v, IsUnit.unit_spec, hx] using hz
  have hs : delta (rho v) * Finset.sum Finset.univ (fun h : Units R => delta (rho h)) =
      Finset.sum Finset.univ (fun h : Units R => delta (rho h)) := by
    rw [Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.mulLeft v)
    intro h
    change delta (rho v) * delta (rho h) = delta (rho ((v * h : Units R) : R))
    simp only [Units.val_mul, map_mul]
  exact eq_zero_of_mul_eq_self_left hv hs

/-- At zero frequency the whole shared packet either vanishes or has the full unit-count size. -/
theorem quartic_jointFourier_zero_energy {R : Type*} [CommRing R] [Fintype R]
    [Fintype (Units R)] (rho : RingHom R F) (hsurj : Function.Surjective rho)
    (hunit : forall x : R, Not (rho x = 0) -> IsUnit x)
    (hF : Not (ringChar F = 2)) (chi : MulChar F Complex)
    (hfour : chi ^ 4 = 1) (htwo : Not (chi ^ 2 = 1))
    (psi : AddChar R Complex) (hpsi : psi.IsPrimitive) :
    let G : Units R -> Complex := fun h =>
      Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2))
    let E := Complex.normSq (Finset.sum Finset.univ (fun h : Units R => (chi ^ 2) (rho h) * G h))
    Or (E = 0) (E = (Fintype.card R : Real) * (Fintype.card (Units R) : Real) ^ 2) := by
  classical
  let G : Units R -> Complex := fun h =>
    Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2))
  have hd := quartic_jointFourier_dichotomy rho hsurj hunit hF chi hfour htwo psi hpsi
  have h2R : IsUnit (2 : R) := hunit 2 (by simpa only [map_ofNat] using Ring.two_ne_zero hF)
  have hG : Complex.normSq (G 1) = (Fintype.card R : Real) := by
    simpa only [G, zero_mul, add_zero] using
      AddChar.normSq_quadraticPhase_unit psi hpsi h2R (1 : Units R) (0 : R)
  change Or
    (Complex.normSq (Finset.sum Finset.univ (fun h : Units R => (chi ^ 2) (rho h) * G h)) = 0)
    (Complex.normSq (Finset.sum Finset.univ (fun h : Units R => (chi ^ 2) (rho h) * G h)) =
      (Fintype.card R : Real) * (Fintype.card (Units R) : Real) ^ 2)
  rcases hd with hquad | hplain
  . left
    have h0 := hquad (0 : R)
    simp only [zero_mul, AddChar.map_zero_eq_one, mul_one] at h0
    rw [sum_unit_residue_eq_zero rho hsurj hunit (chi ^ 2) htwo, mul_zero] at h0
    change Finset.sum Finset.univ (fun h : Units R => (chi ^ 2) (rho h) * G h) = 0 at h0
    rw [h0, map_zero]
  . right
    have h0 := hplain (0 : R)
    simp only [zero_mul, AddChar.map_zero_eq_one, mul_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h0
    change Finset.sum Finset.univ (fun h : Units R => (chi ^ 2) (rho h) * G h) =
      G 1 * (Fintype.card (Units R) : Complex) at h0
    rw [h0, map_mul, hG, Complex.normSq_natCast]
    ring

end MulChar

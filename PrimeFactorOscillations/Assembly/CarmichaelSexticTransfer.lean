/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCarrierVariation

/-!
# Sextic residual phases and all signed cubic-shift clocks

The complete resonance phase is retained for arbitrary Dirichlet base
characters. For a sextic base character its residual is quadratic, with
the principal residual kept explicitly. All signed integer shifts have
uniform actual-carrier variation after the exact positive-input extension.
The unrestricted Gauss row has a complete local neutral classification,
including imprimitive sixth powers and their nonunit-zero masks.
No moving Hecke/norm identification, principal-core estimate or improved
complete zero-free boundary is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelSexticTransfer
open scoped Classical
open CarmichaelNativeSquarepart CarmichaelNativeLowSector
open CarmichaelCarrierVariation CarmichaelCompanionCancellation
open CubicReciprocalGaussian

def residualCharacter {q : Nat} (chi : DirichletCharacter Complex q) :
    DirichletCharacter Complex (q * 3) :=
  OAI.ShortDraftHeckeBridge.baseChangeChar chi *
    OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2)

def residualCoefficient {q : Nat} (chi : DirichletCharacter Complex q)
    (r s : Nat) : Complex :=
  if Nat.Coprime r s then
    nativeCoefficient chi r * (ArithmeticFunction.moebius s : Complex) ^ 2 *
      residualCharacter chi (s : ZMod (q * 3))
  else 0

/-- Resonance reduces the character order by three; its phase is never silently erased. -/
theorem residual_as_cube {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) :
    residualCharacter chi =
      (DirichletCharacter.changeLevel (R := Complex)
        (Exists.intro 3 rfl : Dvd.dvd q (q * 3))) (chi ^ 3) := by
  let f : MonoidHom (DirichletCharacter Complex q) (DirichletCharacter Complex (q * 3)) :=
    DirichletCharacter.changeLevel (R := Complex)
      (Exists.intro 3 rfl : Dvd.dvd q (q * 3))
  let g : MonoidHom (DirichletCharacter Complex 3) (DirichletCharacter Complex (q * 3)) :=
    DirichletCharacter.changeLevel (R := Complex)
      (Exists.intro q (Nat.mul_comm q 3) : Dvd.dvd 3 (q * 3))
  let E := g OAI.ShortDraftHeckeBridge.chiMinusThree
  have hone := CarmichaelCubicResonance.cubic_squarepart_conjugacy
    (1 : DirichletCharacter Complex q) (by simp)
  have hstar : E = star E := by
    change f ((1 : DirichletCharacter Complex q) ^ 2) * E =
      star (f (1 : DirichletCharacter Complex q) * E) at hone
    simpa only [one_pow, map_one, one_mul] using hone
  have hinv : Inv.inv E = E := (MulChar.star_eq_inv E).symm.trans hstar.symm
  have hEE : E * E = 1 := by
    calc
      _ = E * Inv.inv E := congrArg (fun z => E * z) hinv.symm
      _ = 1 := mul_inv_cancel E
  change (f chi * E) * (f (chi ^ 2) * E) = f (chi ^ 3)
  simp only [map_pow]
  calc
    _ = (f chi * (f chi) ^ 2) * (E * E) := by ac_rfl
    _ = (f chi) ^ 3 := by rw [<- pow_succ', hEE, mul_one]

/-- A sextic base character leaves a quadratic residual, including the principal case. -/
theorem sextic_residual_quadratic {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 6 = 1) :
    residualCharacter chi ^ 2 = 1 := by
  rw [residual_as_cube, <- map_pow, <- pow_mul]
  norm_num only [show (3 : Nat) * 2 = 6 by decide]
  rw [hchi, map_one]

/-- The retained quadratic residual is real as a character, not merely bounded in modulus. -/
theorem sextic_residual_real {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 6 = 1) :
    star (residualCharacter chi) = residualCharacter chi := by
  have h := sextic_residual_quadratic chi hchi
  have hh : residualCharacter chi * residualCharacter chi = 1 := by
    simpa only [pow_two] using h
  rw [MulChar.star_eq_inv]
  calc
    _ = Inv.inv (residualCharacter chi) * 1 := (mul_one _).symm
    _ = Inv.inv (residualCharacter chi) *
        (residualCharacter chi * residualCharacter chi) := by rw [hh]
    _ = residualCharacter chi := by rw [<- mul_assoc, inv_mul_cancel, one_mul]

/-- Every ratio class retains its exact residual phase for arbitrary base characters. -/
theorem general_companion_ratio {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (r s b a : Nat)
    (hbs : (b : ZMod (q * 3)) = (a : ZMod (q * 3)) * (s : ZMod (q * 3))) :
    squarepartCoefficient chi r s *
      OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) =
      OAI.ShortDraftHeckeBridge.baseChangeChar chi (a : ZMod (q * 3)) *
        residualCoefficient chi r s := by
  unfold squarepartCoefficient residualCoefficient
  by_cases hcop : Nat.Coprime r s
  . rw [ite_eq_left hcop, ite_eq_left hcop, hbs, map_mul]
    simp only [residualCharacter, MulChar.mul_apply]
    dsimp only [nativeCoefficient]
    ring
  . rw [ite_eq_right hcop, ite_eq_right hcop, zero_mul, mul_zero]

/-- Both residual phases stay coupled with an arbitrary complex physical kernel. -/
theorem general_ratio_pair {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (r u s t b d a c : Nat) (K : Nat -> Nat -> Complex)
    (hbs : (b : ZMod (q * 3)) = (a : ZMod (q * 3)) * (s : ZMod (q * 3)))
    (hdt : (d : ZMod (q * 3)) = (c : ZMod (q * 3)) * (t : ZMod (q * 3))) :
    (squarepartCoefficient chi r s * star (squarepartCoefficient chi u t)) *
      (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
        star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3)))) *
          K (r * s ^ 2 * b) (u * t ^ 2 * d) =
      (OAI.ShortDraftHeckeBridge.baseChangeChar chi (a : ZMod (q * 3)) *
        star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (c : ZMod (q * 3)))) *
      (residualCoefficient chi r s * star (residualCoefficient chi u t)) *
        K (r * s ^ 2 * b) (u * t ^ 2 * d) := by
  have hl := general_companion_ratio chi r s b a hbs
  have hr := congrArg star (general_companion_ratio chi u t d c hdt)
  simp only [star_mul] at hr
  calc
    _ = (squarepartCoefficient chi r s *
        OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3))) *
      (star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3))) *
        star (squarepartCoefficient chi u t)) *
          K (r * s ^ 2 * b) (u * t ^ 2 * d) := by ring
    _ = _ := by rw [hl, hr]; ring

def shiftedNormClock (r a Q : Nat) (k : Int) (s : Nat) : Nat :=
  r * s ^ 2 * Int.toNat ((a : Int) * (s : Int) + k * (Q : Int))

/-- All signed shifts have an increasing nonnegative positive-input clock. -/
theorem shifted_norm_clock_monotone (r a Q : Nat) (k : Int) :
    Monotone (shiftedNormClock r a Q k) := by
  intro i j hij
  have hsq : i ^ 2 <= j ^ 2 := by nlinarith
  have hijZ : (i : Int) <= (j : Int) := by exact_mod_cast hij
  have ha : (0 : Int) <= (a : Int) := by omega
  have hlin : (a : Int) * (i : Int) + k * (Q : Int) <=
      (a : Int) * (j : Int) + k * (Q : Int) := by nlinarith
  exact Nat.mul_le_mul (Nat.mul_le_mul_left r hsq) (Int.toNat_le_toNat hlin)

/-- The extended clock equals the exact original physical input whenever that input is admissible. -/
theorem shifted_norm_clock_input (r a Q s b : Nat) (k : Int)
    (hbs : (b : Int) = (a : Int) * (s : Int) + k * (Q : Int)) :
    shiftedNormClock r a Q k s = r * s ^ 2 * b := by
  unfold shiftedNormClock
  rw [<- hbs]
  simp

/-- Nonpositive affine inputs are exactly zero in the extended physical clock. -/
theorem shifted_norm_clock_nonpositive (r a Q s : Nat) (k : Int)
    (hbad : (a : Int) * (s : Int) + k * (Q : Int) <= 0) :
    shiftedNormClock r a Q k s = 0 := by
  rw [shiftedNormClock, Int.toNat_eq_zero.mpr hbad, mul_zero]

/-- Zero extension does not insert a boundary wave: both actual compensation windows vanish there. -/
theorem shifted_carrier_zero_nonpositive (r a Q s D : Nat) (k : Int)
    (hbad : (a : Int) * (s : Int) + k * (Q : Int) <= 0) :
    quarticCarrierWindow D ((shiftedNormClock r a Q k s : Real) / (D : Real)) = 0 := by
  rw [shifted_norm_clock_nonpositive r a Q s k hbad]
  simp only [Nat.cast_zero, zero_div, quarticCarrierWindow, carrierProfile_zero,
    mul_zero, sub_self]

/-- The full compensated shifted-cubic family has the same uniform budget, even for negative shifts. -/
theorem shifted_carrier_rescaled_variation
    (r a Q D B l : Nat) (k : Int) (hD : 0 < D) :
    windowVariation (fun i => quarticCarrierWindow D
      ((shiftedNormClock r a Q k (l * (i + 1)) : Real) / (D : Real))) B <=
      (21 / 4 : Real) := by
  let P : Nat -> Real := fun i =>
    (shiftedNormClock r a Q k (l * (i + 1)) : Real) / (D : Real)
  have hP : Monotone P := by
    intro i j hij
    have ht := shifted_norm_clock_monotone r a Q k
      (Nat.mul_le_mul_left l (Nat.succ_le_succ hij))
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr ht) (Nat.cast_nonneg D)
  have hP0 : 0 <= P 0 := by dsimp only [P]; positivity
  have hQ : Monotone (fun i => P i / (D : Real) ^ 3) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (hP hij) (by positivity)
  have hQ0 : 0 <= P 0 / (D : Real) ^ 3 := by positivity
  have hv := compensated_carrier_clock_variation P
    (fun i => P i / (D : Real) ^ 3) hP hQ hP0 hQ0
    ((D : Complex) ^ (-3 : Complex)) B
  change windowVariation (fun i => carrierProfile (P i) -
    (D : Complex) ^ (-3 : Complex) * carrierProfile (P i / (D : Real) ^ 3)) B <= _
  calc
    _ <= (21 / 8 : Real) * (1 + norm ((D : Complex) ^ (-3 : Complex))) := hv
    _ <= (21 / 8 : Real) * (1 + 1) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (1 : Real)) (quartic_compensation_norm_le_one D hD))
        (by norm_num)
    _ = _ := by norm_num


/-- Odd base characters discharge residual nonprincipality; cubic principal residuals are not included. -/
theorem residual_nonprincipal_of_odd {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hodd : chi (-1 : ZMod q) = -1) :
    Not (residualCharacter chi = 1) := by
  have hcop : IsCoprime (-1 : Int) ((q * 3 : Nat) : Int) :=
    Exists.intro (-1) (Exists.intro 0 (by ring))
  have hl := DirichletCharacter.changeLevel_eq_cast_of_dvd' (chi ^ 3)
    (Exists.intro 3 rfl : Dvd.dvd q (q * 3)) hcop
  simp only [Int.cast_neg, Int.cast_one] at hl
  have hvalue : residualCharacter chi (-1 : ZMod (q * 3)) = -1 := by
    rw [residual_as_cube, hl]
    rw [pow_succ, MulChar.mul_apply, pow_two, MulChar.mul_apply]
    norm_num [hodd]
  intro h
  rw [h, MulChar.one_apply (isUnit_one.neg)] at hvalue
  norm_num at hvalue


/-- Exact good-prime neutrality forces equal squarefree supports and an even cube exponent. -/
theorem neutral_exponents (c s n : Nat) (hc : c <= 1) (hs : s <= 1) :
    Dvd.dvd 6 (c + 3 * n + 5 * s) <-> c = s /\ Even n := by
  constructor
  . intro h
    cases h with
    | intro k hk =>
      have hcs : c = s := by omega
      refine And.intro hcs (Exists.intro (k - s) ?_)
      omega
  . intro h
    choose k hk using h.2
    rw [h.1, hk]
    exact Exists.intro (s + k) (by ring)

/-- Neutrality at every prime, with no restricted prime subset, has a complete exponent-vector classification. -/
theorem neutral_factorization {iota : Type} (c s n : Finsupp iota Nat)
    (hc : forall p, c p <= 1) (hs : forall p, s p <= 1) :
    (forall p, Dvd.dvd 6 (c p + 3 * n p + 5 * s p)) <->
      c = s /\ exists h : Finsupp iota Nat, n = h + h := by
  constructor
  . intro h
    have hlocal (p : iota) : c p = s p /\ Even (n p) :=
      (neutral_exponents (c p) (s p) (n p) (hc p) (hs p)).mp (h p)
    have hcs : c = s := by
      ext p
      exact (hlocal p).1
    let a : Finsupp iota Nat := Finsupp.mapRange (fun v : Nat => v / 2) (by decide) n
    refine And.intro hcs (Exists.intro a ?_)
    ext p
    simp only [a, Finsupp.add_apply, Finsupp.mapRange_apply]
    have he := Classical.choose_spec (hlocal p).2
    omega
  . intro h
    choose a ha using h.2
    intro p
    apply (neutral_exponents (c p) (s p) (n p) (hc p) (hs p)).mpr
    refine And.intro (by rw [h.1]) (Exists.intro (a p) ?_)
    simpa only [Finsupp.add_apply] using congrArg (fun v : Finsupp iota Nat => v p) ha

/-- Even sixth-power rows keep their full nonunit-zero mask; only its support is compressed. -/
theorem neutral_mask_support {iota : Type} (c s n h : Finsupp iota Nat)
    (hcs : c = s) (hn : n = h + h) :
    (c + (n + n + n) + s).support = (c + h).support := by
  rw [<- hcs, hn]
  ext p
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply]
  omega

/-- The full neutral Gauss row allows sixth-power moduli and retains the frequency zero mask. -/
theorem gauss_neutral_exponents (c s n m : Nat) (hc : c <= 1)
    (hfrequency : s - 1 <= m) (hmask : 0 < c + 3 * n -> m = 0) :
    Dvd.dvd 6 (c + 3 * n + 5 * s) <->
      exists v h : Nat, s = c + 6 * v /\ n = h + h /\
        (0 < c + n -> v = 0) := by
  constructor
  . intro hneutral
    by_cases hpositive : 0 < c + 3 * n
    . have hm : m = 0 := hmask hpositive
      have hs : s <= 1 := by omega
      have hlocal := (neutral_exponents c s n hc hs).mp hneutral
      cases hlocal.2 with
      | intro h hh =>
        refine Exists.intro 0 (Exists.intro h ?_)
        exact And.intro (by omega) (And.intro hh (by intro _; rfl))
    . cases hneutral with
      | intro k hk =>
        refine Exists.intro (s / 6) (Exists.intro 0 ?_)
        exact And.intro (by omega) (And.intro (by omega) (by omega))
  . intro h
    cases h with
    | intro v hv =>
      cases hv with
      | intro a ha =>
        refine Exists.intro (c + a + 5 * v) ?_
        rw [ha.1, ha.2.1]
        ring

/-- All prime valuations of a nonzero Gauss row, including every imprimitive sixth power, are classified. -/
theorem gauss_neutral_factorization {iota : Type} (c s n m : Finsupp iota Nat)
    (hc : forall p, c p <= 1)
    (hfrequency : forall p, s p - 1 <= m p)
    (hmask : forall p, 0 < c p + 3 * n p -> m p = 0) :
    (forall p, Dvd.dvd 6 (c p + 3 * n p + 5 * s p)) <->
      exists v h : Finsupp iota Nat,
        s = c + (v + v + v + v + v + v) /\ n = h + h /\
          forall p, 0 < v p -> c p + h p = 0 := by
  constructor
  . intro hneutral
    have hlocal (p : iota) :=
      (gauss_neutral_exponents (c p) (s p) (n p) (m p)
        (hc p) (hfrequency p) (hmask p)).mp (hneutral p)
    let v : Finsupp iota Nat := Finsupp.mapRange (fun a : Nat => a / 6) (by decide) s
    let h : Finsupp iota Nat := Finsupp.mapRange (fun a : Nat => a / 2) (by decide) n
    refine Exists.intro v (Exists.intro h (And.intro ?_ (And.intro ?_ ?_)))
    . ext p
      simp only [v, Finsupp.add_apply, Finsupp.mapRange_apply]
      cases hlocal p with
      | intro a ha =>
        cases ha with
        | intro b hb =>
          have hcp := hc p
          omega
    . ext p
      simp only [h, Finsupp.add_apply, Finsupp.mapRange_apply]
      cases hlocal p with
      | intro a ha =>
        cases ha with
        | intro b hb => omega
    . intro p hp
      simp only [v, Finsupp.mapRange_apply] at hp
      simp only [h, Finsupp.add_apply, Finsupp.mapRange_apply]
      cases hlocal p with
      | intro a ha =>
        cases ha with
        | intro b hb =>
          have hcp := hc p
          by_cases hpositive : 0 < c p + n p
          . have ha0 := hb.2.2 hpositive
            omega
          . omega
  . intro h
    cases h with
    | intro v hv =>
      cases hv with
      | intro a ha =>
        intro p
        apply (gauss_neutral_exponents (c p) (s p) (n p) (m p)
          (hc p) (hfrequency p) (hmask p)).mpr
        refine Exists.intro (v p) (Exists.intro (a p) ?_)
        have hs := congrArg (fun b : Finsupp iota Nat => b p) ha.1
        have hn := congrArg (fun b : Finsupp iota Nat => b p) ha.2.1
        simp only [Finsupp.add_apply] at hs hn
        refine And.intro (by omega) (And.intro hn ?_)
        intro hpositive
        by_contra hnonzero
        have hz := ha.2.2 p (by omega)
        omega

/-- Sixth powers retain their prime support even when their unit character phase is neutral. -/
theorem gauss_neutral_mask_support {iota : Type} (c s n v h : Finsupp iota Nat)
    (hs : s = c + (v + v + v + v + v + v)) (hn : n = h + h) :
    (c + (n + n + n) + s).support = (c + v + h).support := by
  rw [hs, hn]
  ext p
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply]
  omega

end PrimeFactorOscillations.CarmichaelSexticTransfer

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelWindowTransfer
import PrimeFactorOscillations.Helpers.CubicCompensatedWindow

/-!
# Finite signed native packets and their physical Mellin transforms

Transfers fixed positive finite supports to Mellin space, retaining both
quartic window factors and the native principal character. Infinite supports,
carrier identification and new arithmetic estimates are not asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelPhysicalPacket
open MeasureTheory
open scoped Classical

def physicalPacket (T : Finset Nat) (a : Nat -> Complex)
    (W : Real -> Complex) (t : Real) : Complex :=
  T.sum (fun n => a n * W ((n : Real) / t))

def dirichletPacket (T : Finset Nat) (a : Nat -> Complex) (s : Complex) : Complex :=
  T.sum (fun n => a n * (n : Complex) ^ (-s))

theorem scaledWindow_hasMellin (W : Real -> Complex) (s M : Complex)
    (hW : HasMellin W s M) (y : Real) (hy : 0 < y) :
    HasMellin (fun t : Real => W (y / t)) (-s) ((y : Complex) ^ (-s) * M) := by
  have hconv : MellinConvergent (fun t : Real => W (y * t)) s :=
    (MellinConvergent.comp_mul_left hy).2 hW.1
  have hinv : MellinConvergent (fun t : Real => W (y * t ^ (-1 : Real))) (-s) :=
    (MellinConvergent.comp_rpow (f := fun t : Real => W (y * t))
      (s := -s) (a := (-1 : Real)) (by norm_num : Not ((-1 : Real) = 0))).2
      (by simpa only [Complex.ofReal_neg, Complex.ofReal_one, div_neg,
        div_one, neg_neg] using hconv)
  constructor
  . simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hinv
  . have hi := mellin_comp_inv (fun t : Real => W (y * t)) (-s)
    rw [neg_neg, mellin_comp_mul_left W s hy, hW.2] at hi
    simpa only [div_eq_mul_inv, smul_eq_mul] using hi

theorem physicalPacket_hasMellin (T : Finset Nat) (a : Nat -> Complex)
    (W : Real -> Complex) (s M : Complex) (hW : HasMellin W s M)
    (hpos : forall n : Nat, Membership.mem T n -> 0 < n) :
    HasMellin (physicalPacket T a W) (-s) (M * dirichletPacket T a s) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp [physicalPacket, dirichletPacket, HasMellin, MellinConvergent, mellin]
  | @insert n T hn ih =>
    have hnpos : (0 : Real) < n := by exact_mod_cast hpos n (Finset.mem_insert_self n T)
    have hsmall : HasMellin (physicalPacket T a W) (-s)
        (M * dirichletPacket T a s) :=
      ih (fun k hk => hpos k (Finset.mem_insert_of_mem hk))
    have hterm := hasMellin_const_smul (scaledWindow_hasMellin W s M hW n hnpos).1 (a n)
    have htermEq : HasMellin (fun t : Real => a n * W ((n : Real) / t)) (-s)
        (a n * ((n : Complex) ^ (-s) * M)) := by
      simpa only [smul_eq_mul, (scaledWindow_hasMellin W s M hW n hnpos).2,
        Complex.ofReal_natCast] using hterm
    have hadd := hasMellin_add htermEq.1 hsmall.1
    rw [htermEq.2, hsmall.2] at hadd
    have he : physicalPacket (insert n T) a W =
        (fun t : Real => a n * W ((n : Real) / t) + physicalPacket T a W t) := by
      funext t
      simp only [physicalPacket, Finset.sum_insert hn]
    rw [he]
    simpa only [dirichletPacket, Finset.sum_insert hn,
      mul_add, mul_left_comm, mul_comm, mul_assoc] using hadd

def windowMultiplier (d s : Complex) : Complex :=
  HSMul.hSMul (Inv.inv (2 : Real))
    (CubicCompensatedWindow.rootPolynomial d s * Complex.Gamma (s / 2))

theorem primeWindow_packet_hasMellin (T : Finset Nat) (a : Nat -> Complex)
    (d s : Complex) (hs : 0 < s.re)
    (hpos : forall n : Nat, Membership.mem T n -> 0 < n) :
    HasMellin (physicalPacket T a (CubicCompensatedWindow.primeWindow d))
      (-s) (windowMultiplier d s * dirichletPacket T a s) :=
  physicalPacket_hasMellin T a _ s _ (CubicCompensatedWindow.primeWindow_hasMellin d s hs)
    hpos

theorem quartic_packet_mellin (T : Finset Nat) (a : Nat -> Complex)
    (W : Real -> Complex) (s M R : Complex) (hW : HasMellin W s M)
    (hRef : HasMellin W (DirichletCompensatedProbe.quarticMap s) R)
    (hpos : forall n : Nat, Membership.mem T n -> 0 < n) :
    mellin (CarmichaelWindowTransfer.quarticPhysicalProbe (physicalPacket T a W)) (-s) =
      M * dirichletPacket T a s -
        HSMul.hSMul ((4 : Real) ^ (-1 : Int))
          (R * dirichletPacket T a (DirichletCompensatedProbe.quarticMap s)) := by
  have hMain := physicalPacket_hasMellin T a W s M hW hpos
  have hReference := physicalPacket_hasMellin T a W _ R hRef hpos
  have h := CarmichaelWindowTransfer.quarticPhysicalProbe_mellin
    (physicalPacket T a W) s hMain.1 hReference.1
  rw [hMain.2, hReference.2] at h
  exact h

theorem primeWindow_quartic_packet_mellin (T : Finset Nat) (a : Nat -> Complex)
    (d s : Complex) (hs : 0 < s.re)
    (hpos : forall n : Nat, Membership.mem T n -> 0 < n) :
    mellin (CarmichaelWindowTransfer.quarticPhysicalProbe
        (physicalPacket T a (CubicCompensatedWindow.primeWindow d))) (-s) =
      windowMultiplier d s * dirichletPacket T a s -
        HSMul.hSMul ((4 : Real) ^ (-1 : Int))
          (windowMultiplier d (DirichletCompensatedProbe.quarticMap s) *
            dirichletPacket T a (DirichletCompensatedProbe.quarticMap s)) := by
  have hq : 0 < (DirichletCompensatedProbe.quarticMap s).re := by
    dsimp [DirichletCompensatedProbe.quarticMap]
    simp only [Complex.div_ofNat_re, Complex.add_re]
    norm_num
    linarith
  exact quartic_packet_mellin T a _ s _ _
    (CubicCompensatedWindow.primeWindow_hasMellin d s hs)
    (CubicCompensatedWindow.primeWindow_hasMellin d _ hq) hpos

open CarmichaelIntegralSpectrum CarmichaelCorrelationSpectrum

theorem native_dirichlet_expansion {q : Nat} [NeZero q]
    (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (T : Finset Nat) (a : Nat -> Complex) (s : Complex) :
    (multiplicity S (1 : DirichletCharacter Complex q) : Complex) *
        dirichletPacket T (fun n => (carmichaelPrimeWeight q S n : Complex) * a n) s =
      Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (multiplicity S chi : Complex) *
          dirichletPacket T (fun n => chi (n : ZMod q) * a n) s) := by
  have h := signed_finite_packet S hDiv T (fun n => a n * (n : Complex) ^ (-s))
  rw [multiplicity_principal S hDiv]
  unfold dirichletPacket
  rw [Finset.mul_sum]
  simpa only [mul_assoc] using h

theorem native_principal_separation {q : Nat} [NeZero q]
    (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (T : Finset Nat) (a : Nat -> Complex) (s : Complex)
    (hunit : forall n : Nat, Membership.mem T n -> IsUnit (n : ZMod q)) :
    (multiplicity S (1 : DirichletCharacter Complex q) : Complex) *
        dirichletPacket T (fun n => (carmichaelPrimeWeight q S n : Complex) * a n) s =
      (multiplicity S (1 : DirichletCharacter Complex q) : Complex) *
        dirichletPacket T a s +
      (Finset.univ.erase (1 : DirichletCharacter Complex q)).sum (fun chi =>
        (multiplicity S chi : Complex) *
          dirichletPacket T (fun n => chi (n : ZMod q) * a n) s) := by
  classical
  rw [native_dirichlet_expansion S hDiv]
  have hp : dirichletPacket T
      (fun n => (1 : DirichletCharacter Complex q) (n : ZMod q) * a n) s =
      dirichletPacket T a s := by
    apply Finset.sum_congr rfl
    intro n hn
    change (1 : DirichletCharacter Complex q) (n : ZMod q) * a n *
      (n : Complex) ^ (-s) = _
    rw [MulChar.one_apply (hunit n hn), one_mul]
  have h := Finset.sum_erase_add Finset.univ
    (fun chi : DirichletCharacter Complex q =>
      (multiplicity S chi : Complex) *
        dirichletPacket T (fun n => chi (n : ZMod q) * a n) s)
    (Finset.mem_univ (1 : DirichletCharacter Complex q))
  rw [hp] at h
  exact h.symm.trans (add_comm _ _)

end PrimeFactorOscillations.CarmichaelPhysicalPacket

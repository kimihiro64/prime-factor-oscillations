/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CarrierAmplifiedMoment
import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianRamanujanStrata

/-!
# GaussianTwoDiagonal

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# The two physical diagonals of the amplified moment

The signed remainder retains both centered row factors. The diagonal
bounds are finite deterministic transfers from the same character array
to its separate row energies. No analytic sieve estimate is assumed or
asserted by this module.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianTwoDiagonal

variable {R I J : Type}

def amplitude (s : Finset I) (f : I -> R -> Complex) (r : R) : Complex :=
  s.sum fun i => f i r

def diagonal (s : Finset I) (f : I -> R -> Complex) (r : R) : Real :=
  s.sum fun i => Complex.normSq (f i r)

def energy (rows : Finset R) (s : Finset I) (t : Finset J)
    (f : I -> R -> Complex) (g : J -> R -> Complex) (w : R -> Real) : Real :=
  rows.sum fun r =>
    w r * Complex.normSq (amplitude s f r) * Complex.normSq (amplitude t g r)

def cofactorDiagonal (rows : Finset R) (s : Finset I) (t : Finset J)
    (f : I -> R -> Complex) (g : J -> R -> Complex) (w : R -> Real) : Real :=
  rows.sum fun r => w r * diagonal s f r * Complex.normSq (amplitude t g r)

def primeDiagonal (rows : Finset R) (s : Finset I) (t : Finset J)
    (f : I -> R -> Complex) (g : J -> R -> Complex) (w : R -> Real) : Real :=
  rows.sum fun r => w r * Complex.normSq (amplitude s f r) * diagonal t g r

def bothDiagonal (rows : Finset R) (s : Finset I) (t : Finset J)
    (f : I -> R -> Complex) (g : J -> R -> Complex) (w : R -> Real) : Real :=
  rows.sum fun r => w r * diagonal s f r * diagonal t g r

def crossPacket (rows : Finset R) (s : Finset I) (t : Finset J)
    (f : I -> R -> Complex) (g : J -> R -> Complex) (w : R -> Real) : Real :=
  rows.sum fun r => w r *
    (Complex.normSq (amplitude s f r) - diagonal s f r) *
    (Complex.normSq (amplitude t g r) - diagonal t g r)

theorem diagonal_nonneg (s : Finset I) (f : I -> R -> Complex) (r : R) :
    0 <= diagonal s f r :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (f i r)

theorem bothDiagonal_nonneg (rows : Finset R) (s : Finset I) (t : Finset J)
    (f : I -> R -> Complex) (g : J -> R -> Complex) (w : R -> Real)
    (hw : forall r, Membership.mem rows r -> 0 <= w r) :
    0 <= bothDiagonal rows s t f g w := by
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg (mul_nonneg (hw r hr) (diagonal_nonneg s f r))
    (diagonal_nonneg t g r)

theorem energy_decomposition (rows : Finset R) (s : Finset I) (t : Finset J)
    (f : I -> R -> Complex) (g : J -> R -> Complex) (w : R -> Real) :
    energy rows s t f g w =
      cofactorDiagonal rows s t f g w + primeDiagonal rows s t f g w -
        bothDiagonal rows s t f g w + crossPacket rows s t f g w := by
  unfold energy cofactorDiagonal primeDiagonal bothDiagonal crossPacket
  simp only [<- Finset.sum_add_distrib, <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem energy_le_two_diagonals_add_cross (rows : Finset R)
    (s : Finset I) (t : Finset J)
    (f : I -> R -> Complex) (g : J -> R -> Complex) (w : R -> Real)
    (hw : forall r, Membership.mem rows r -> 0 <= w r) :
    energy rows s t f g w <=
      cofactorDiagonal rows s t f g w + primeDiagonal rows s t f g w +
        crossPacket rows s t f g w := by
  rw [energy_decomposition]
  linarith [bothDiagonal_nonneg rows s t f g w hw]

theorem cofactorDiagonal_le (rows : Finset R) (s : Finset I) (t : Finset J)
    (f : I -> R -> Complex) (g : J -> R -> Complex) (w : R -> Real)
    (mass : I -> Real)
    (hw : forall r, Membership.mem rows r -> 0 <= w r)
    (hm : forall i, Membership.mem s i -> forall r, Membership.mem rows r ->
      Complex.normSq (f i r) <= mass i) :
    cofactorDiagonal rows s t f g w <=
      (s.sum mass) * rows.sum (fun r => w r * Complex.normSq (amplitude t g r)) := by
  have hd : forall r, Membership.mem rows r -> diagonal s f r <= s.sum mass := by
    intro r hr
    exact Finset.sum_le_sum fun i hi => hm i hi r hr
  unfold cofactorDiagonal
  calc
    _ <= rows.sum (fun r => w r * (s.sum mass) *
        Complex.normSq (amplitude t g r)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hd r hr) (hw r hr))
        (Complex.normSq_nonneg (amplitude t g r))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

theorem primeDiagonal_le (rows : Finset R) (s : Finset I) (t : Finset J)
    (f : I -> R -> Complex) (g : J -> R -> Complex) (w : R -> Real)
    (mass : J -> Real)
    (hw : forall r, Membership.mem rows r -> 0 <= w r)
    (hm : forall j, Membership.mem t j -> forall r, Membership.mem rows r ->
      Complex.normSq (g j r) <= mass j) :
    primeDiagonal rows s t f g w <=
      (t.sum mass) * rows.sum (fun r => w r * Complex.normSq (amplitude s f r)) := by
  calc
    _ = cofactorDiagonal rows t s g f w := by
      unfold primeDiagonal cofactorDiagonal
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ <= _ := cofactorDiagonal_le rows t s g f w mass hw hm

/-- The quartic detector error stays below both endpoint budgets
for an arbitrary amplifier scale Y, including Y = D ^ 4. -/
theorem carrier_quartic_arbitrary_amplifier (rows : Finset R) (s : Finset I)
    (a f : I -> Complex) (K : R -> I -> Complex) (P : R -> Complex)
    (D Y Crows Ccols Camp Cerr : Real) (hD : 0 < D) (hY : 0 <= Y)
    (hRows : 0 <= Crows) (hCols : 0 <= Ccols)
    (hAmp : 0 <= Camp) (hErr : 0 <= Cerr)
    (hS : (s.card : Real) <= Ccols * D)
    (hT : (rows.card : Real) <= Crows * D ^ 4)
    (herr : forall n, Membership.mem s n -> norm (f n - a n) <= Cerr / D ^ 3)
    (hK : forall r, Membership.mem rows r ->
      forall n, Membership.mem s n -> norm (K r n) <= 1)
    (hP : forall r, Membership.mem rows r -> norm (P r) <= Camp * Y) :
    UniformCarrier.AmplifiedMoment.energy rows s f K P <=
      2 * UniformCarrier.AmplifiedMoment.energy rows s a K P +
        2 * Crows * Ccols ^ 2 * Camp ^ 2 * Cerr ^ 2 * Y ^ 2 := by
  have heps : 0 <= Cerr / D ^ 3 := div_nonneg hErr (pow_nonneg hD.le _)
  have hbase := UniformCarrier.AmplifiedMoment.energy_transfer rows s a f K P
    (Cerr / D ^ 3) (Camp * Y) heps (mul_nonneg hAmp hY) herr hK hP
  calc
    _ <= 2 * UniformCarrier.AmplifiedMoment.energy rows s a K P +
        2 * (rows.card : Real) *
          ((s.card : Real) * (Cerr / D ^ 3) * (Camp * Y)) ^ 2 := hbase
    _ <= 2 * UniformCarrier.AmplifiedMoment.energy rows s a K P +
        2 * (Crows * D ^ 4) *
          ((Ccols * D) * (Cerr / D ^ 3) * (Camp * Y)) ^ 2 := by
      gcongr
    _ = _ := by
      field_simp [hD.ne'] <;> ring

end PrimeFactorOscillations.GaussianTwoDiagonal


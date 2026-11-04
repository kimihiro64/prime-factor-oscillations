/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenFourier

/-!
# Signed cubic frequency projections in the sevenfold model

The residue and nonresidue supports retain exactly their six resonant
ordered triples. The constant amplitude is arbitrary, so all principal
and compensation cross terms remain in the calculation.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Metaplectic.G2Seven.Cubic

noncomputable def mean (F : ZMod 7 -> Complex) : Complex :=
  Finset.univ.sum F / 7

def residueFrequency (i : Fin 4) : ZMod 7 :=
  match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 4

def nonresidueFrequency (i : Fin 4) : ZMod 7 :=
  match i.val with
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | _ => 6

def coefficient (u A B C : Complex) (i : Fin 4) : Complex :=
  match i.val with
  | 0 => u
  | 1 => A
  | 2 => B
  | _ => C

noncomputable def carrier (f : Fin 4 -> ZMod 7) (u A B C : Complex)
    (a : ZMod 7) : Complex :=
  Finset.univ.sum (fun i : Fin 4 =>
    ZMod.stdAddChar (a * f i) * coefficient u A B C i)

private theorem character_frequency_sum (r : ZMod 7) :
    Finset.univ.sum (fun a : ZMod 7 => ZMod.stdAddChar (r * a)) =
      if r = 0 then 7 else 0 := by
  by_cases hz : r = 0
  case pos => simp [hz]
  case neg =>
    rw [if_neg hz]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 7 hz)

/-- Complete cubic orthogonality, including repeated and zero frequencies. -/
theorem cubic_sum (f : Fin 4 -> ZMod 7) (u A B C : Complex) :
    Finset.univ.sum (fun a : ZMod 7 => (carrier f u A B C a) ^ 3) =
      7 * Finset.univ.sum (fun r : Fin 4 => Finset.univ.sum (fun s : Fin 4 =>
        Finset.univ.sum (fun k : Fin 4 =>
          if f r + f s + f k = 0 then
            coefficient u A B C r * coefficient u A B C s * coefficient u A B C k
          else 0))) := by
  have hc (a : ZMod 7) (r s k : Fin 4) :
      ZMod.stdAddChar (a * f r) * ZMod.stdAddChar (a * f s) *
          ZMod.stdAddChar (a * f k) =
        ZMod.stdAddChar ((f r + f s + f k) * a) := by
    rw [<- AddChar.map_add_eq_mul, <- AddChar.map_add_eq_mul]
    congr 1
    ring
  have hp (a : ZMod 7) :
      (carrier f u A B C a) ^ 3 =
        Finset.univ.sum (fun r : Fin 4 => Finset.univ.sum (fun s : Fin 4 =>
          Finset.univ.sum (fun k : Fin 4 =>
            ZMod.stdAddChar ((f r + f s + f k) * a) *
              (coefficient u A B C r * coefficient u A B C s * coefficient u A B C k)))) := by
    simp only [carrier, pow_succ, pow_zero, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro k _
    calc
      _ = (ZMod.stdAddChar (a * f r) * ZMod.stdAddChar (a * f s) *
          ZMod.stdAddChar (a * f k)) *
          (coefficient u A B C r * coefficient u A B C s * coefficient u A B C k) := by ring
      _ = _ := by rw [hc]
  simp_rw [hp]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext r
    rw [Finset.sum_comm]
    arg 2
    ext s
    rw [Finset.sum_comm]
  simp_rw [<- Finset.sum_mul, character_frequency_sum]
  simp [ite_mul, Finset.mul_sum]

def tripleResonant (r s k : Fin 4) : Prop :=
  (match r.val, s.val, k.val with
   | 0, 0, 0 => true
   | 1, 2, 3 => true
   | 1, 3, 2 => true
   | 2, 1, 3 => true
   | 2, 3, 1 => true
   | 3, 1, 2 => true
   | 3, 2, 1 => true
   | _, _, _ => false) = true

instance (r s k : Fin 4) : Decidable (tripleResonant r s k) := by
  unfold tripleResonant
  infer_instance

/-- Seven resonant ordered triples: one principal and six fully nonzero. -/
theorem residue_resonance : forall r s k : Fin 4,
    (residueFrequency r + residueFrequency s + residueFrequency k = 0) <->
      tripleResonant r s k := by decide

theorem nonresidue_resonance : forall r s k : Fin 4,
    (nonresidueFrequency r + nonresidueFrequency s + nonresidueFrequency k = 0) <->
      tripleResonant r s k := by decide

private theorem residue_cubic_sum (u A B C : Complex) :
    Finset.univ.sum (fun a : ZMod 7 =>
      (carrier residueFrequency u A B C a) ^ 3) = 7 * (u ^ 3 + 6 * A * B * C) := by
  rw [cubic_sum]
  simp_rw [residue_resonance]
  norm_num [Fin.sum_univ_succ, tripleResonant, coefficient]
  ring

private theorem nonresidue_cubic_sum (u A B C : Complex) :
    Finset.univ.sum (fun a : ZMod 7 =>
      (carrier nonresidueFrequency u A B C a) ^ 3) = 7 * (u ^ 3 + 6 * A * B * C) := by
  rw [cubic_sum]
  simp_rw [nonresidue_resonance]
  norm_num [Fin.sum_univ_succ, tripleResonant, coefficient]
  ring

theorem residue_cubic_mean (u A B C : Complex) :
    mean (fun a => (carrier residueFrequency u A B C a) ^ 3) =
      u ^ 3 + 6 * A * B * C := by
  unfold mean
  rw [residue_cubic_sum]
  ring

theorem nonresidue_cubic_mean (u A B C : Complex) :
    mean (fun a => (carrier nonresidueFrequency u A B C a) ^ 3) =
      u ^ 3 + 6 * A * B * C := by
  unfold mean
  rw [nonresidue_cubic_sum]
  ring

noncomputable def compensatedCarrier (f : Fin 4 -> ZMod 7)
    (u A B C : Complex) (a : ZMod 7) : Complex :=
  1 + ((carrier f u (-A) (-B) (-C) a) ^ 3 - u ^ 3) / 6

/-- The complete principal channel cancels explicitly; the selected unit stays one. -/
theorem residue_compensated_mean (u A B C : Complex) :
    mean (compensatedCarrier residueFrequency u A B C) = 1 - A * B * C := by
  unfold mean compensatedCarrier
  rw [Finset.sum_add_distrib, <- Finset.sum_div, Finset.sum_sub_distrib]
  rw [residue_cubic_sum]
  norm_num
  ring

theorem nonresidue_compensated_mean (u A B C : Complex) :
    mean (compensatedCarrier nonresidueFrequency u A B C) = 1 - A * B * C := by
  unfold mean compensatedCarrier
  rw [Finset.sum_add_distrib, <- Finset.sum_div, Finset.sum_sub_distrib]
  rw [nonresidue_cubic_sum]
  norm_num
  ring

end Metaplectic.G2Seven.Cubic

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelResidueAscent
import PrimeFactorOscillations.Assembly.PrimeConstellationRH

/-!
# Exact native mask covers on arithmetic progression constellations

Three odd progression positions suffice to meet both actual native zero-mask
channels when the even step is not divisible by eight. Four positions balance
each original kernel exactly. Every modulus and signed common signal remains.
Prime-shape recurrence remains a separate hypothesis of the RH transport.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelProgressionMasks

open CarmichaelComplementaryAscent CarmichaelResidueAscent

def progressionWeight (r : Nat) (phase : Bool) (n d length : Nat) : Real :=
  (Finset.range length).sum (fun i => primeMask r phase (n + i * d))

def residueProgressionWeight (phase : Bool) (n d length : Nat) : Real :=
  (Finset.range length).sum (fun i => residueWeight phase (n + i * d))

theorem odd_progression_position (n d i : Nat)
    (hn : Nat.Coprime n 2) (hd : Dvd.dvd 2 d) :
    Nat.Coprime (n + i * d) 2 := by
  apply Nat.Coprime.symm
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro hDiv
  have hMod := Nat.mod_eq_zero_of_dvd hDiv
  have hdMod := Nat.mod_eq_zero_of_dvd hd
  simp only [Nat.add_mod, Nat.mul_mod, hdMod, mul_zero, Nat.zero_mod,
    add_zero, Nat.mod_mod] at hMod
  exact (Nat.prime_two.coprime_iff_not_dvd.mp hn.symm)
    (Nat.dvd_of_mod_eq_zero hMod)

theorem progressionWeight_eq_residue (r : Nat) (phase : Bool) (n d length : Nat)
    (hn : Nat.Coprime n 2) (hd : Dvd.dvd 2 d) :
    progressionWeight r phase n d length = residueProgressionWeight phase n d length := by
  apply Finset.sum_congr rfl
  intro i _
  exact primeMask_eq_residueWeight r _ phase (odd_progression_position n d i hn hd)

theorem odd_start_residues (n : Nat) (hn : Nat.Coprime n 2) :
    Or (n % 8 = 1) (Or (n % 8 = 3) (Or (n % 8 = 5) (n % 8 = 7))) := by
  have hNot : Not (n % 2 = 0) := by
    intro h
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hn.symm)
      (Nat.dvd_of_mod_eq_zero h)
  omega

theorem nonzero_even_step_residues (d : Nat) (hd : Dvd.dvd 2 d)
    (hEight : Not (Dvd.dvd 8 d)) :
    Or (d % 8 = 2) (Or (d % 8 = 4) (d % 8 = 6)) := by
  have hEven := Nat.mod_eq_zero_of_dvd hd
  have hNot : Not (d % 8 = 0) := by
    intro h
    exact hEight (Nat.dvd_of_mod_eq_zero h)
  omega

theorem three_term_two_or_four (r : Nat) (phase : Bool) (n d : Nat)
    (hn : Nat.Coprime n 2) (hd : Dvd.dvd 2 d) (hEight : Not (Dvd.dvd 8 d)) :
    Or (progressionWeight r phase n d 3 = 2) (progressionWeight r phase n d 3 = 4) := by
  rw [progressionWeight_eq_residue r phase n d 3 hn hd]
  rcases odd_start_residues n hn with hN | hN | hN | hN <;>
    rcases nonzero_even_step_residues d hd hEight with hD | hD | hD <;>
    cases phase <;>
    norm_num [residueProgressionWeight, Finset.sum_range_succ, residueWeight,
      Nat.add_mod, Nat.mul_mod, hN, hD]

theorem three_term_weight_bounds (r : Nat) (phase : Bool) (n d : Nat)
    (hn : Nat.Coprime n 2) (hd : Dvd.dvd 2 d) (hEight : Not (Dvd.dvd 8 d)) :
    And (2 <= progressionWeight r phase n d 3)
      (progressionWeight r phase n d 3 <= 4) := by
  rcases three_term_two_or_four r phase n d hn hd hEight with h | h <;>
    rw [h] <;> norm_num

theorem two_term_exact_balance_of_four_step (r : Nat) (phase : Bool) (n d : Nat)
    (hn : Nat.Coprime n 2) (hd : Dvd.dvd 2 d) (hFour : d % 8 = 4) :
    progressionWeight r phase n d 2 = 2 := by
  rw [progressionWeight_eq_residue r phase n d 2 hn hd]
  rcases odd_start_residues n hn with hN | hN | hN | hN <;>
    cases phase <;>
    norm_num [residueProgressionWeight, Finset.sum_range_succ, residueWeight,
      Nat.add_mod, Nat.mul_mod, hN, hFour]

theorem four_term_exact_balance (r : Nat) (phase : Bool) (n d : Nat)
    (hn : Nat.Coprime n 2) (hd : Dvd.dvd 2 d) (hEight : Not (Dvd.dvd 8 d)) :
    progressionWeight r phase n d 4 = 4 := by
  rw [progressionWeight_eq_residue r phase n d 4 hn hd]
  rcases odd_start_residues n hn with hN | hN | hN | hN <;>
    rcases nonzero_even_step_residues d hd hEight with hD | hD | hD <;>
    cases phase <;>
    norm_num [residueProgressionWeight, Finset.sum_range_succ, residueWeight,
      Nat.add_mod, Nat.mul_mod, hN, hD]

theorem four_term_signed_identity (r : Nat) (phase : Bool) (n d : Nat) (B : Real)
    (hn : Nat.Coprime n 2) (hd : Dvd.dvd 2 d) (hEight : Not (Dvd.dvd 8 d)) :
    (Finset.range 4).sum (fun i => primeMask r phase (n + i * d) * B) = 4 * B := by
  rw [<- Finset.sum_mul]
  change progressionWeight r phase n d 4 * B = 4 * B
  rw [four_term_exact_balance r phase n d hn hd hEight]

def blindStart (phase : Bool) : Nat := if phase then 7 else 3

theorem blindStart_prime (phase : Bool) : Nat.Prime (blindStart phase) := by
  cases phase <;> decide

theorem blindStart_coprime (phase : Bool) : Nat.Coprime (blindStart phase) 2 := by
  cases phase <;> decide

theorem eight_step_blind (r : Nat) (phase : Bool) (d length : Nat)
    (hd : Dvd.dvd 8 d) :
    progressionWeight r phase (blindStart phase) d length = 0 := by
  rw [progressionWeight_eq_residue r phase _ d length (blindStart_coprime phase)
    (dvd_trans (by decide : Dvd.dvd 2 8) hd)]
  apply Finset.sum_eq_zero
  intro i _
  have hMod := Nat.mod_eq_zero_of_dvd hd
  cases phase <;>
    norm_num [residueWeight, blindStart, Nat.add_mod, Nat.mul_mod, hMod]

theorem three_term_uniform_cover_iff (r d : Nat) (hd : Dvd.dvd 2 d) :
    (forall phase : Bool, forall n : Nat, Nat.Coprime n 2 ->
      2 <= progressionWeight r phase n d 3) <-> Not (Dvd.dvd 8 d) := by
  constructor
  . intro h hEight
    have hLower := h false 3 (by decide)
    have hZero := eight_step_blind r false d 3 hEight
    change progressionWeight r false 3 d 3 = 0 at hZero
    rw [hZero] at hLower
    norm_num at hLower
  . intro hEight phase n hn
    exact (three_term_weight_bounds r phase n d hn hd hEight).1

theorem two_terms_can_be_blind (r : Nat) :
    progressionWeight r false 3 2 2 = 0 := by
  rw [progressionWeight_eq_residue r false 3 2 2 (by decide) (by decide)]
  norm_num [residueProgressionWeight, Finset.sum_range_succ, residueWeight]

def fourProgressionShape (d : Nat) : Fin 4 -> Nat := fun i => i.val * d

theorem fourProgressionShape_injective (d : Nat) (hEight : Not (Dvd.dvd 8 d)) :
    Function.Injective (fourProgressionShape d) := by
  have hd0 : Not (d = 0) := by
    intro h
    apply hEight
    rw [h]
    exact dvd_zero 8
  have hdPos := Nat.pos_of_ne_zero hd0
  intro i j h
  apply Fin.ext
  change i.val * d = j.val * d at h
  by_contra hNe
  rcases lt_or_gt_of_ne hNe with hLt | hGt
  . have hMul := Nat.mul_lt_mul_of_pos_right hLt hdPos
    omega
  . have hMul := Nat.mul_lt_mul_of_pos_right hGt hdPos
    omega

theorem fourProgressionShape_bound (d : Nat) (i : Fin 4) :
    fourProgressionShape d i <= 3 * d :=
  Nat.mul_le_mul_right d (by omega : i.val <= 3)

theorem actual_four_prime_cycle_balanced (d : Nat)
    (hd : Dvd.dvd 2 d) (hEight : Not (Dvd.dvd 8 d))
    (sigma : Equiv.Perm Nat.Primes) (q : Nat) (hq : 3 <= q)
    (hc : PrimeShapeCycleAt (fourProgressionShape d) sigma q)
    (r : Nat) (phase : Bool) :
    progressionWeight r phase q d 4 = 4 := by
  have hPrime : Nat.Prime q := by
    simpa [fourProgressionShape] using hc.prime_offsets (0 : Fin 4)
  have hNot : Not (Dvd.dvd q 2) := by
    intro h
    have hLe := Nat.le_of_dvd (by decide : 0 < 2) h
    omega
  have hOdd : Nat.Coprime q 2 := hPrime.coprime_iff_not_dvd.mpr hNot
  exact four_term_exact_balance r phase q d hOdd hd hEight

/-- The recurrence premise is retained: RH alone does not supply the prime shape. -/
theorem recurrent_four_prime_progression_and_rh_iff_balanced_transport
    (d : Nat) (hd : Dvd.dvd 2 d) (hEight : Not (Dvd.dvd 8 d))
    (alpha : Real) (ha : 0 < alpha) :
    (RiemannHypothesis /\ RecurrentPrimeShape (fourProgressionShape d)) <->
      (exists sigma : Equiv.Perm Nat.Primes,
        exists hdispl : forall p : Nat.Primes,
          abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (3 * d : Nat),
        (forall N : Nat, exists q : Nat, N <= q /\
          PrimeShapeCycleAt (fourProgressionShape d) sigma q /\
          forall (r : Nat) (phase : Bool), progressionWeight r phase q d 4 = 4) /\
        Filter.Eventually (fun N : Nat =>
          let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
          (boundedPrimePermutationLaw sigma (3 * d) hdispl).densityRatio N r <
            canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N))
          Filter.atTop) := by
  have hOriginal := recurrent_prime_shape_and_rh_iff_canonical_cycle_transport
    (fourProgressionShape d) (fourProgressionShape_injective d hEight)
    (3 * d) (fourProgressionShape_bound d) alpha ha
  constructor
  . intro hBoth
    choose sigma hdispl hCycles hSign using hOriginal.mp hBoth
    refine Exists.intro sigma (Exists.intro hdispl (And.intro ?_ hSign))
    intro N
    choose q hq hc using hCycles (max N 3)
    refine Exists.intro q (And.intro ((le_max_left N 3).trans hq)
      (And.intro hc ?_))
    intro r phase
    exact actual_four_prime_cycle_balanced d hd hEight sigma q
      ((le_max_right N 3).trans hq) hc r phase
  . intro hBalanced
    choose sigma hdispl hCycles hSign using hBalanced
    apply hOriginal.mpr
    refine Exists.intro sigma (Exists.intro hdispl (And.intro ?_ hSign))
    intro N
    choose q hq hc hBalance using hCycles N
    exact Exists.intro q (And.intro hq hc)

end PrimeFactorOscillations.CarmichaelProgressionMasks

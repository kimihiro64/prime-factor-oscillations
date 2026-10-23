/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CarmichaelProfileCriterion
import PrimeFactorOscillations.Helpers.PrimeOrderReturnKernel

/-!
# Full conditional profile transitions under arbitrary coprime extensions

Each prime-label bit is gated by exponent growth or its old return.
Auxiliary return events then give the exact joint law on the entire
actual reduction fiber. No separated congruence or squarefree condition
is imposed, and all failure events remain in the product formula.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelProfileKernel

open FiniteHomProbability PrimeOrderReturnLaw PrimeOrderReturnKernel
  CarmichaelProfileLifts CarmichaelProfileCriterion CarmichaelEvenThinning

/-- Exponent growth opens a gate regardless of the old bit. -/
def returnGate (m B : Nat) (a : Units (ZMod m)) (l : Nat) : Bool := by
  classical
  exact decide (Or
    (Dvd.dvd l (Monoid.exponent (Units (ZMod (m * B))) /
      Monoid.exponent (Units (ZMod m))))
    (a ^ (Monoid.exponent (Units (ZMod m)) / l) = 1))

theorem returnGate_eq_true (m B : Nat) (a : Units (ZMod m)) (l : Nat) :
    returnGate m B a l = true <->
      Or (Dvd.dvd l (Monoid.exponent (Units (ZMod (m * B))) /
        Monoid.exponent (Units (ZMod m))))
        (a ^ (Monoid.exponent (Units (ZMod m)) / l) = 1) := by
  classical
  simp [returnGate]

theorem reduction_return_gate (m B : Nat) (hCoprime : Nat.Coprime m B)
    (l : Nat.Primes)
    (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod m))))
    (u : Units (ZMod (m * B))) :
    u ^ (Monoid.exponent (Units (ZMod (m * B))) / (l : Nat)) = 1 <->
      And
        (Or (Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (m * B))) /
          Monoid.exponent (Units (ZMod m))))
          ((unitReduction (dvd_mul_right m B) u) ^
            (Monoid.exponent (Units (ZMod m)) / (l : Nat)) = 1))
        ((unitReduction (dvd_mul_left B m) u) ^
          (Monoid.exponent (Units (ZMod (m * B))) / (l : Nat)) = 1) := by
  classical
  let L := Monoid.exponent (Units (ZMod m))
  let E := Monoid.exponent (Units (ZMod (m * B)))
  let K := E / L
  have hLE : Dvd.dvd L E := old_exponent_dvd m B hCoprime
  have hE : E = L * K := (Nat.mul_div_cancel' hLE).symm
  have hQuot : E / (l : Nat) = (L / (l : Nat)) * K := by
    rw [hE, Nat.mul_comm L K, Nat.mul_div_assoc K hl,
      Nat.mul_comm K (L / (l : Nat))]
  have hOld :
      (unitReduction (dvd_mul_right m B) u) ^ (E / (l : Nat)) = 1 <->
        Or (Dvd.dvd (l : Nat) K)
          ((unitReduction (dvd_mul_right m B) u) ^ (L / (l : Nat)) = 1) := by
    by_cases hDiv : Dvd.dvd (l : Nat) K
    { choose t ht using hDiv
      have hOldDiv : Dvd.dvd L (E / (l : Nat)) := by
        rw [hQuot, ht, <- Nat.mul_assoc, Nat.div_mul_cancel hl]
        exact dvd_mul_right L t
      have hAnn := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hOldDiv
      constructor
      { intro _
        exact Or.inl (Exists.intro t ht) }
      { intro _
        exact hAnn _ } }
    { have hCop : Nat.Coprime K (l : Nat) :=
        (l.property.coprime_iff_not_dvd.mpr hDiv).symm
      have hPeriod :
          ((unitReduction (dvd_mul_right m B) u) ^ (L / (l : Nat))) ^ (l : Nat) = 1 := by
        rw [<- pow_mul, Nat.div_mul_cancel hl]
        exact Monoid.pow_exponent_eq_one _
      rw [hQuot, pow_mul]
      simpa only [hDiv, false_or] using
        pow_coprime_period_eq_one
          ((unitReduction (dvd_mul_right m B) u) ^ (L / (l : Nat)))
          K (l : Nat) hPeriod hCop }
  rw [crt_power_eq_one m B hCoprime u (E / (l : Nat)), hOld]

theorem reduction_return_gate_all_labels (m B : Nat) (hCoprime : Nat.Coprime m B)
    (l : Nat.Primes)
    (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (m * B)))))
    (u : Units (ZMod (m * B))) :
    u ^ (Monoid.exponent (Units (ZMod (m * B))) / (l : Nat)) = 1 <->
      And
        (Or (Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (m * B))) /
          Monoid.exponent (Units (ZMod m))))
          ((unitReduction (dvd_mul_right m B) u) ^
            (Monoid.exponent (Units (ZMod m)) / (l : Nat)) = 1))
        ((unitReduction (dvd_mul_left B m) u) ^
          (Monoid.exponent (Units (ZMod (m * B))) / (l : Nat)) = 1) := by
  by_cases hOld : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod m)))
  { exact reduction_return_gate m B hCoprime l hOld u }
  { let L := Monoid.exponent (Units (ZMod m))
    let E := Monoid.exponent (Units (ZMod (m * B)))
    let K := E / L
    have hLE : Dvd.dvd L E := old_exponent_dvd m B hCoprime
    have hE : E = L * K := (Nat.mul_div_cancel' hLE).symm
    have hK : Dvd.dvd (l : Nat) K := by
      have h : Dvd.dvd (l : Nat) (L * K) := by
        rw [<- hE]
        exact hl
      exact (l.property.dvd_mul.mp h).resolve_left hOld
    have hOldDiv : Dvd.dvd L (E / (l : Nat)) := by
      rw [hE, Nat.mul_div_assoc L hK]
      exact dvd_mul_right L (K / (l : Nat))
    have hAnn := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hOldDiv
    rw [crt_power_eq_one m B hCoprime u (E / (l : Nat))]
    constructor
    { intro h
      exact And.intro (Or.inl hK) h.2 }
    { intro h
      exact And.intro (hAnn _) h.2 } }

/-- Uniform probability of a full binary profile among all lifts of a fixed base. -/
def fiberProfileProbability (m B : Nat) (a : Units (ZMod m))
    (S : Finset Nat.Primes) (bits : S -> Bool) : Real :=
  uniformProbability
    (fun u : {u : Units (ZMod (m * B)) // unitReduction (dvd_mul_right m B) u = a} =>
      matchesPattern (m * B) S bits u.val)

/-- Complete conditional product kernel for arbitrary coprime modular extensions. -/
theorem fiberProfileProbability_eq_product (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (m * B)))))
    (bits : S -> Bool) :
    fiberProfileProbability m B a S bits =
      Finset.univ.prod (fun l : S =>
        if returnGate m B a (l.val : Nat) then
          if bits l then
            1 / (returnIndex (G := Units (ZMod B))
              (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) : Real)
          else 1 - 1 / (returnIndex (G := Units (ZMod B))
              (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) : Real)
        else if bits l then 0 else 1) := by
  classical
  let E := Monoid.exponent (Units (ZMod (m * B)))
  let e := unitLiftFiberEquiv m B hCoprime a
  let gates : S -> Bool := fun l => returnGate m B a (l.val : Nat)
  let P : Units (ZMod B) -> Prop := fun b =>
    forall l : S, if bits l then And (gates l = true) (b ^ (E / (l.val : Nat)) = 1)
    else Not (And (gates l = true) (b ^ (E / (l.val : Nat)) = 1))
  have hPred :
      (fun u : {u : Units (ZMod (m * B)) // unitReduction (dvd_mul_right m B) u = a} =>
        matchesPattern (m * B) S bits u.val) =
      (fun u => P (e u)) := by
    funext u
    apply propext
    change
      (forall l : S, if bits l then u.val ^ (E / (l.val : Nat)) = 1
        else Not (u.val ^ (E / (l.val : Nat)) = 1)) <->
      (forall l : S, if bits l then And (gates l = true) ((e u) ^ (E / (l.val : Nat)) = 1)
        else Not (And (gates l = true) ((e u) ^ (E / (l.val : Nat)) = 1)))
    apply forall_congr'
    intro l
    have h := reduction_return_gate_all_labels m B hCoprime l.val (hDiv l) u.val
    rw [u.property] at h
    have hAux : e u = unitReduction (dvd_mul_left B m) u.val :=
      unitProductEquiv_snd m B hCoprime u.val
    have hGate : gates l = true <->
        Or (Dvd.dvd (l.val : Nat) (E / Monoid.exponent (Units (ZMod m))))
          (a ^ (Monoid.exponent (Units (ZMod m)) / (l.val : Nat)) = 1) :=
      returnGate_eq_true m B a (l.val : Nat)
    have hReturn : u.val ^ (E / (l.val : Nat)) = 1 <->
        And (gates l = true) ((e u) ^ (E / (l.val : Nat)) = 1) :=
      h.trans (and_congr hGate.symm (by rw [hAux]))
    cases bits l
    { exact not_congr hReturn }
    { exact hReturn }
  unfold fiberProfileProbability
  rw [hPred, uniformProbability_equiv e P]
  change gatedPatternProbability (G := Units (ZMod B)) E S gates bits = _
  exact gatedPatternProbability_eq_product E S
    hDiv
    (auxiliary_exponent_annihilates m B hCoprime) gates bits

end PrimeFactorOscillations.CarmichaelProfileKernel

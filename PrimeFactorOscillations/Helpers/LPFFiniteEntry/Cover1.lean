/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.SieveCoverCore

/-! Bounded component of the inclusive finite orbit certificate. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace PrimeFactorOscillations.LPF

def lpfEntry10000WitnessDivisors20 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 43, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 29,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval20_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 2000 lpfEntry10000WitnessDivisors20 = true := by decide

def lpfEntry10000WitnessDivisors21 : List Nat :=
  [
    2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 13,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 41, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3
  ]

theorem lpfEntry10000WitnessInterval21_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 2100 lpfEntry10000WitnessDivisors21 = true := by decide

def lpfEntry10000WitnessDivisors22 : List Nat :=
  [
    2, 31, 2, 0, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 7, 2, 31, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 11
  ]

theorem lpfEntry10000WitnessInterval22_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 2200 lpfEntry10000WitnessDivisors22 = true := by decide

def lpfEntry10000WitnessDivisors23 : List Nat :=
  [
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 11, 2, 23, 2, 3, 2, 13, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval23_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 2300 lpfEntry10000WitnessDivisors23 = true := by decide

def lpfEntry10000WitnessDivisors24 : List Nat :=
  [
    2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 41,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0,
    2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 37,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 47, 2, 3, 2, 5, 2, 11, 2, 3
  ]

theorem lpfEntry10000WitnessInterval24_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 2400 lpfEntry10000WitnessDivisors24 = true := by decide

def lpfEntry10000WitnessDivisors25 : List Nat :=
  [
    2, 41, 2, 0, 2, 3, 2, 23, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 43, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 13, 2, 11, 2, 3, 2, 17, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0,
    2, 29, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 23
  ]

theorem lpfEntry10000WitnessInterval25_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 2500 lpfEntry10000WitnessDivisors25 = true := by decide

def lpfEntry10000WitnessDivisors26 : List Nat :=
  [
    2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 43, 2, 3, 2, 37, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval26_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 2600 lpfEntry10000WitnessDivisors26 = true := by decide

def lpfEntry10000WitnessDivisors27 : List Nat :=
  [
    2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 41, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 47, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval27_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 2700 lpfEntry10000WitnessDivisors27 = true := by decide

def lpfEntry10000WitnessDivisors28 : List Nat :=
  [
    2, 0, 2, 0, 2, 3, 2, 7, 2, 53, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 47, 2, 19, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0,
    2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 13
  ]

theorem lpfEntry10000WitnessInterval28_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 2800 lpfEntry10000WitnessDivisors28 = true := by decide

def lpfEntry10000WitnessDivisors29 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 23, 2, 37, 2, 3, 2, 0, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 11, 2, 19, 2, 3, 2, 29, 2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval29_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 2900 lpfEntry10000WitnessDivisors29 = true := by decide

def lpfEntry10000WitnessDivisors30 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 23, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 17, 2, 3, 2, 11, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 7, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3
  ]

theorem lpfEntry10000WitnessInterval30_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 3000 lpfEntry10000WitnessDivisors30 = true := by decide

def lpfEntry10000WitnessDivisors31 : List Nat :=
  [
    2, 7, 2, 29, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 53, 2, 3, 2, 31, 2, 13, 2, 3, 2, 0, 2, 43,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 47, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 29, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 31, 2, 3, 2, 23, 2, 7
  ]

theorem lpfEntry10000WitnessInterval31_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 3100 lpfEntry10000WitnessDivisors31 = true := by decide

def lpfEntry10000WitnessDivisors32 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 41,
    2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval32_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 3200 lpfEntry10000WitnessDivisors32 = true := by decide

def lpfEntry10000WitnessDivisors33 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 31, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 47, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 31,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 43, 2, 3
  ]

theorem lpfEntry10000WitnessInterval33_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 3300 lpfEntry10000WitnessDivisors33 = true := by decide

def lpfEntry10000WitnessDivisors34 : List Nat :=
  [
    2, 19, 2, 41, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13,
    2, 11, 2, 3, 2, 5, 2, 23, 2, 3, 2, 47, 2, 0, 2, 3, 2, 7, 2, 19,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7,
    2, 59, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 0
  ]

theorem lpfEntry10000WitnessInterval34_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 3400 lpfEntry10000WitnessDivisors34 = true := by decide

def lpfEntry10000WitnessDivisors35 : List Nat :=
  [
    2, 3, 2, 31, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53, 2, 11, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 17, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 59
  ]

theorem lpfEntry10000WitnessInterval35_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 3500 lpfEntry10000WitnessDivisors35 = true := by decide

def lpfEntry10000WitnessDivisors36 : List Nat :=
  [
    2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 7, 2, 41, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval36_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 3600 lpfEntry10000WitnessDivisors36 = true := by decide

def lpfEntry10000WitnessDivisors37 : List Nat :=
  [
    2, 0, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0,
    2, 61, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 0,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 0, 2, 53, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 29
  ]

theorem lpfEntry10000WitnessInterval37_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 3700 lpfEntry10000WitnessDivisors37 = true := by decide

def lpfEntry10000WitnessDivisors38 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 37, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 43, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11,
    2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7
  ]

theorem lpfEntry10000WitnessInterval38_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 3800 lpfEntry10000WitnessDivisors38 = true := by decide

def lpfEntry10000WitnessDivisors39 : List Nat :=
  [
    2, 47, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 59, 2, 5, 2, 3, 2, 37,
    2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 29, 2, 3, 2, 41, 2, 23,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3
  ]

theorem lpfEntry10000WitnessInterval39_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 3900 lpfEntry10000WitnessDivisors39 = true := by decide

end PrimeFactorOscillations.LPF

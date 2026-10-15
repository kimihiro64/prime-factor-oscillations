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

def lpfEntry10000WitnessDivisors40 : List Nat :=
  [
    2, 0, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 37, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 31, 2, 17, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 61, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 0
  ]

theorem lpfEntry10000WitnessInterval40_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 4000 lpfEntry10000WitnessDivisors40 = true := by decide

def lpfEntry10000WitnessDivisors41 : List Nat :=
  [
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 41, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 11, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 37, 2, 47, 2, 3, 2, 53, 2, 59, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13
  ]

theorem lpfEntry10000WitnessInterval41_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 4100 lpfEntry10000WitnessDivisors41 = true := by decide

def lpfEntry10000WitnessDivisors42 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 31, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval42_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 4200 lpfEntry10000WitnessDivisors42 = true := by decide

def lpfEntry10000WitnessDivisors43 : List Nat :=
  [
    2, 11, 2, 13, 2, 3, 2, 59, 2, 31, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7,
    2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 61, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 43, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29,
    2, 13, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 53
  ]

theorem lpfEntry10000WitnessInterval43_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 4300 lpfEntry10000WitnessDivisors43 = true := by decide

def lpfEntry10000WitnessDivisors44 : List Nat :=
  [
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 19, 2, 43, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 61, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11
  ]

theorem lpfEntry10000WitnessInterval44_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 4400 lpfEntry10000WitnessDivisors44 = true := by decide

def lpfEntry10000WitnessDivisors45 : List Nat :=
  [
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 47,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 23, 2, 19,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval45_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 4500 lpfEntry10000WitnessDivisors45 = true := by decide

def lpfEntry10000WitnessDivisors46 : List Nat :=
  [
    2, 43, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 41, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 59, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 31, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 37
  ]

theorem lpfEntry10000WitnessInterval46_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 4600 lpfEntry10000WitnessDivisors46 = true := by decide

def lpfEntry10000WitnessDivisors47 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 53, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0, 2, 7, 2, 3, 2, 67, 2, 0,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval47_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 4700 lpfEntry10000WitnessDivisors47 = true := by decide

def lpfEntry10000WitnessDivisors48 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 61,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 47, 2, 29, 2, 3, 2, 37, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 43,
    2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 59, 2, 3
  ]

theorem lpfEntry10000WitnessInterval48_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 4800 lpfEntry10000WitnessDivisors48 = true := by decide

def lpfEntry10000WitnessDivisors49 : List Nat :=
  [
    2, 13, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13,
    2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 0
  ]

theorem lpfEntry10000WitnessInterval49_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 4900 lpfEntry10000WitnessDivisors49 = true := by decide

def lpfEntry10000WitnessDivisors50 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 11, 2, 47, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 71, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 61, 2, 5, 2, 3, 2, 37, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval50_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 5000 lpfEntry10000WitnessDivisors50 = true := by decide

def lpfEntry10000WitnessDivisors51 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 47, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 53, 2, 37, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 31, 2, 0,
    2, 3, 2, 71, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval51_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 5100 lpfEntry10000WitnessDivisors51 = true := by decide

def lpfEntry10000WitnessDivisors52 : List Nat :=
  [
    2, 7, 2, 11, 2, 3, 2, 41, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 17,
    2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 59, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 19, 2, 3, 2, 23, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 67, 2, 3, 2, 0, 2, 7
  ]

theorem lpfEntry10000WitnessInterval52_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 5200 lpfEntry10000WitnessDivisors52 = true := by decide

def lpfEntry10000WitnessDivisors53 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 47, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 7, 2, 73, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 53, 2, 3, 2, 11, 2, 23,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 41, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval53_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 5300 lpfEntry10000WitnessDivisors53 = true := by decide

def lpfEntry10000WitnessDivisors54 : List Nat :=
  [
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 61, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 53,
    2, 43, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 23, 2, 3
  ]

theorem lpfEntry10000WitnessInterval54_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 5400 lpfEntry10000WitnessDivisors54 = true := by decide

def lpfEntry10000WitnessDivisors55 : List Nat :=
  [
    2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 29,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 67, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 7, 2, 3, 2, 29, 2, 11
  ]

theorem lpfEntry10000WitnessInterval55_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 5500 lpfEntry10000WitnessDivisors55 = true := by decide

def lpfEntry10000WitnessDivisors56 : List Nat :=
  [
    2, 3, 2, 13, 2, 5, 2, 3, 2, 71, 2, 31, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 17, 2, 13, 2, 3, 2, 43, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41
  ]

theorem lpfEntry10000WitnessInterval56_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 5600 lpfEntry10000WitnessDivisors56 = true := by decide

def lpfEntry10000WitnessDivisors57 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 59, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 29, 2, 23, 2, 3, 2, 53, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3
  ]

theorem lpfEntry10000WitnessInterval57_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 5700 lpfEntry10000WitnessDivisors57 = true := by decide

def lpfEntry10000WitnessDivisors58 : List Nat :=
  [
    2, 0, 2, 7, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2, 71, 2, 3, 2, 0, 2, 17
  ]

theorem lpfEntry10000WitnessInterval58_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 5800 lpfEntry10000WitnessDivisors58 = true := by decide

def lpfEntry10000WitnessDivisors59 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 23, 2, 3, 2, 5, 2, 61, 2, 3,
    2, 31, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 59,
    2, 3, 2, 67, 2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 43, 2, 3,
    2, 0, 2, 31, 2, 3, 2, 0, 2, 53, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7
  ]

theorem lpfEntry10000WitnessInterval59_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 5900 lpfEntry10000WitnessDivisors59 = true := by decide

end PrimeFactorOscillations.LPF

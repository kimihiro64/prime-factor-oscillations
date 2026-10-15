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

def lpfEntry10000WitnessDivisors60 : List Nat :=
  [
    2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 13,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 73,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 59, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3
  ]

theorem lpfEntry10000WitnessInterval60_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 6000 lpfEntry10000WitnessDivisors60 = true := by decide

def lpfEntry10000WitnessDivisors61 : List Nat :=
  [
    2, 0, 2, 17, 2, 3, 2, 31, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 47, 2, 3,
    2, 61, 2, 0, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37,
    2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 41, 2, 11, 2, 3, 2, 0, 2, 0
  ]

theorem lpfEntry10000WitnessInterval61_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 6100 lpfEntry10000WitnessDivisors61 = true := by decide

def lpfEntry10000WitnessDivisors62 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 17,
    2, 79, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 61, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval62_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 6200 lpfEntry10000WitnessDivisors62 = true := by decide

def lpfEntry10000WitnessDivisors63 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 59, 2, 3, 2, 0, 2, 71,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval63_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 6300 lpfEntry10000WitnessDivisors63 = true := by decide

def lpfEntry10000WitnessDivisors64 : List Nat :=
  [
    2, 37, 2, 19, 2, 3, 2, 43, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 7, 2, 3, 2, 41, 2, 47,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 43, 2, 3, 2, 73, 2, 67
  ]

theorem lpfEntry10000WitnessInterval64_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 6400 lpfEntry10000WitnessDivisors64 = true := by decide

def lpfEntry10000WitnessDivisors65 : List Nat :=
  [
    2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 61, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 13,
    2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 79, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 29, 2, 3, 2, 7, 2, 11, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval65_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 6500 lpfEntry10000WitnessDivisors65 = true := by decide

def lpfEntry10000WitnessDivisors66 : List Nat :=
  [
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 29, 2, 7, 2, 3, 2, 17, 2, 61, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 59, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3
  ]

theorem lpfEntry10000WitnessInterval66_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 6600 lpfEntry10000WitnessDivisors66 = true := by decide

def lpfEntry10000WitnessDivisors67 : List Nat :=
  [
    2, 0, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 53, 2, 0, 2, 3, 2, 0, 2, 23,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 43, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 67, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 13
  ]

theorem lpfEntry10000WitnessInterval67_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 6700 lpfEntry10000WitnessDivisors67 = true := by decide

def lpfEntry10000WitnessDivisors68 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 19, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 19,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 71, 2, 83, 2, 3, 2, 61, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval68_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 6800 lpfEntry10000WitnessDivisors68 = true := by decide

def lpfEntry10000WitnessDivisors69 : List Nat :=
  [
    2, 67, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 31, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 11, 2, 53, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval69_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 6900 lpfEntry10000WitnessDivisors69 = true := by decide

def lpfEntry10000WitnessDivisors70 : List Nat :=
  [
    2, 0, 2, 47, 2, 3, 2, 7, 2, 43, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 79, 2, 13, 2, 3, 2, 31, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 23, 2, 7, 2, 3, 2, 37, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0,
    2, 73, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 41, 2, 3, 2, 47, 2, 31
  ]

theorem lpfEntry10000WitnessInterval70_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 7000 lpfEntry10000WitnessDivisors70 = true := by decide

def lpfEntry10000WitnessDivisors71 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 0, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 67, 2, 71, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 43, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23
  ]

theorem lpfEntry10000WitnessInterval71_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 7100 lpfEntry10000WitnessDivisors71 = true := by decide

def lpfEntry10000WitnessDivisors72 : List Nat :=
  [
    2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 53, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 19, 2, 29,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval72_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 7200 lpfEntry10000WitnessDivisors72 = true := by decide

def lpfEntry10000WitnessDivisors73 : List Nat :=
  [
    2, 7, 2, 67, 2, 3, 2, 0, 2, 0, 2, 3, 2, 71, 2, 5, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 41,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 17, 2, 37, 2, 3, 2, 53, 2, 0, 2, 3, 2, 73, 2, 5, 2, 3, 2, 47,
    2, 11, 2, 3, 2, 5, 2, 83, 2, 3, 2, 19, 2, 0, 2, 3, 2, 13, 2, 7
  ]

theorem lpfEntry10000WitnessInterval73_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 7300 lpfEntry10000WitnessDivisors73 = true := by decide

def lpfEntry10000WitnessDivisors74 : List Nat :=
  [
    2, 3, 2, 11, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 41, 2, 13, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 59, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval74_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 7400 lpfEntry10000WitnessDivisors74 = true := by decide

def lpfEntry10000WitnessDivisors75 : List Nat :=
  [
    2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 73,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 67, 2, 0, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 71, 2, 3
  ]

theorem lpfEntry10000WitnessInterval75_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 7500 lpfEntry10000WitnessDivisors75 = true := by decide

def lpfEntry10000WitnessDivisors76 : List Nat :=
  [
    2, 11, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 19,
    2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 17, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 47, 2, 79, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 43, 2, 0
  ]

theorem lpfEntry10000WitnessInterval76_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 7600 lpfEntry10000WitnessDivisors76 = true := by decide

def lpfEntry10000WitnessDivisors77 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 59, 2, 3, 2, 11, 2, 5, 2, 3, 2, 71,
    2, 0, 2, 3, 2, 5, 2, 61, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 31, 2, 43, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11
  ]

theorem lpfEntry10000WitnessInterval77_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 7700 lpfEntry10000WitnessDivisors77 = true := by decide

def lpfEntry10000WitnessDivisors78 : List Nat :=
  [
    2, 29, 2, 3, 2, 5, 2, 37, 2, 3, 2, 73, 2, 13, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 7, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 53, 2, 3
  ]

theorem lpfEntry10000WitnessInterval78_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 7800 lpfEntry10000WitnessDivisors78 = true := by decide

def lpfEntry10000WitnessDivisors79 : List Nat :=
  [
    2, 0, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0,
    2, 89, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 73, 2, 3,
    2, 19, 2, 0, 2, 3, 2, 31, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 79,
    2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 61, 2, 0, 2, 3, 2, 11, 2, 19
  ]

theorem lpfEntry10000WitnessInterval79_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 7900 lpfEntry10000WitnessDivisors79 = true := by decide

end PrimeFactorOscillations.LPF

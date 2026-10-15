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

def lpfEntry10000WitnessDivisors0 : List Nat :=
  [
    0, 0, 0, 0, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval0_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 0 lpfEntry10000WitnessDivisors0 = true := by decide

def lpfEntry10000WitnessDivisors1 : List Nat :=
  [
    2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0
  ]

theorem lpfEntry10000WitnessInterval1_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 100 lpfEntry10000WitnessDivisors1 = true := by decide

def lpfEntry10000WitnessDivisors2 : List Nat :=
  [
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13
  ]

theorem lpfEntry10000WitnessInterval2_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 200 lpfEntry10000WitnessDivisors2 = true := by decide

def lpfEntry10000WitnessDivisors3 : List Nat :=
  [
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval3_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 300 lpfEntry10000WitnessDivisors3 = true := by decide

def lpfEntry10000WitnessDivisors4 : List Nat :=
  [
    2, 0, 2, 13, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 0
  ]

theorem lpfEntry10000WitnessInterval4_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 400 lpfEntry10000WitnessDivisors4 = true := by decide

def lpfEntry10000WitnessDivisors5 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 17, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval5_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 500 lpfEntry10000WitnessDivisors5 = true := by decide

def lpfEntry10000WitnessDivisors6 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3
  ]

theorem lpfEntry10000WitnessInterval6_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 600 lpfEntry10000WitnessDivisors6 = true := by decide

def lpfEntry10000WitnessDivisors7 : List Nat :=
  [
    2, 0, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 17
  ]

theorem lpfEntry10000WitnessInterval7_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 700 lpfEntry10000WitnessDivisors7 = true := by decide

def lpfEntry10000WitnessDivisors8 : List Nat :=
  [
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 29
  ]

theorem lpfEntry10000WitnessInterval8_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 800 lpfEntry10000WitnessDivisors8 = true := by decide

def lpfEntry10000WitnessDivisors9 : List Nat :=
  [
    2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 23, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval9_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 900 lpfEntry10000WitnessDivisors9 = true := by decide

def lpfEntry10000WitnessDivisors10 : List Nat :=
  [
    2, 7, 2, 17, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 13,
    2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7
  ]

theorem lpfEntry10000WitnessInterval10_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 1000 lpfEntry10000WitnessDivisors10 = true := by decide

def lpfEntry10000WitnessDivisors11 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 19, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 19,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11
  ]

theorem lpfEntry10000WitnessInterval11_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 1100 lpfEntry10000WitnessDivisors11 = true := by decide

def lpfEntry10000WitnessDivisors12 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 23,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 17, 2, 11, 2, 3, 2, 29, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 19, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval12_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 1200 lpfEntry10000WitnessDivisors12 = true := by decide

def lpfEntry10000WitnessDivisors13 : List Nat :=
  [
    2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 31, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 0, 2, 29, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 0
  ]

theorem lpfEntry10000WitnessInterval13_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 1300 lpfEntry10000WitnessDivisors13 = true := by decide

def lpfEntry10000WitnessDivisors14 : List Nat :=
  [
    2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval14_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 1400 lpfEntry10000WitnessDivisors14 = true := by decide

def lpfEntry10000WitnessDivisors15 : List Nat :=
  [
    2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 17, 2, 3, 2, 37, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval15_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 1500 lpfEntry10000WitnessDivisors15 = true := by decide

def lpfEntry10000WitnessDivisors16 : List Nat :=
  [
    2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23,
    2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 0
  ]

theorem lpfEntry10000WitnessInterval16_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 1600 lpfEntry10000WitnessDivisors16 = true := by decide

def lpfEntry10000WitnessDivisors17 : List Nat :=
  [
    2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 41, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7
  ]

theorem lpfEntry10000WitnessInterval17_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 1700 lpfEntry10000WitnessDivisors17 = true := by decide

def lpfEntry10000WitnessDivisors18 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 17,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 0, 2, 43, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3
  ]

theorem lpfEntry10000WitnessInterval18_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 1800 lpfEntry10000WitnessDivisors18 = true := by decide

def lpfEntry10000WitnessDivisors19 : List Nat :=
  [
    2, 0, 2, 11, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19,
    2, 17, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 37, 2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 0
  ]

theorem lpfEntry10000WitnessInterval19_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 1900 lpfEntry10000WitnessDivisors19 = true := by decide

end PrimeFactorOscillations.LPF

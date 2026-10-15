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

def lpfEntry10000WitnessDivisors80 : List Nat :=
  [
    2, 3, 2, 53, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 13, 2, 71, 2, 3, 2, 23, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 83, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 0, 2, 59, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7
  ]

theorem lpfEntry10000WitnessInterval80_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 8000 lpfEntry10000WitnessDivisors80 = true := by decide

def lpfEntry10000WitnessDivisors81 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 23,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 47, 2, 3, 2, 5, 2, 79, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 0, 2, 29, 2, 3, 2, 31, 2, 5, 2, 3, 2, 41,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3
  ]

theorem lpfEntry10000WitnessInterval81_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 8100 lpfEntry10000WitnessDivisors81 = true := by decide

def lpfEntry10000WitnessDivisors82 : List Nat :=
  [
    2, 59, 2, 13, 2, 3, 2, 29, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 73, 2, 37, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 43
  ]

theorem lpfEntry10000WitnessInterval82_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 8200 lpfEntry10000WitnessDivisors82 = true := by decide

def lpfEntry10000WitnessDivisors83 : List Nat :=
  [
    2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 53, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 31,
    2, 19, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 61, 2, 13,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 17, 2, 83, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 37
  ]

theorem lpfEntry10000WitnessInterval83_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 8300 lpfEntry10000WitnessDivisors83 = true := by decide

def lpfEntry10000WitnessDivisors84 : List Nat :=
  [
    2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 47, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 79, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 37, 2, 3, 2, 7, 2, 61,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3
  ]

theorem lpfEntry10000WitnessInterval84_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 8400 lpfEntry10000WitnessDivisors84 = true := by decide

def lpfEntry10000WitnessDivisors85 : List Nat :=
  [
    2, 0, 2, 11, 2, 3, 2, 47, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 83, 2, 17, 2, 3, 2, 5, 2, 43, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23,
    2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 0
  ]

theorem lpfEntry10000WitnessInterval85_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 8500 lpfEntry10000WitnessDivisors85 = true := by decide

def lpfEntry10000WitnessDivisors86 : List Nat :=
  [
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 79, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 37, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 89, 2, 5, 2, 3, 2, 53,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 41, 2, 17, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval86_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 8600 lpfEntry10000WitnessDivisors86 = true := by decide

def lpfEntry10000WitnessDivisors87 : List Nat :=
  [
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 23, 2, 0,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 31, 2, 3, 2, 67, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 59, 2, 3, 2, 5, 2, 19, 2, 3
  ]

theorem lpfEntry10000WitnessInterval87_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 8700 lpfEntry10000WitnessDivisors87 = true := by decide

def lpfEntry10000WitnessDivisors88 : List Nat :=
  [
    2, 13, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13,
    2, 83, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 11
  ]

theorem lpfEntry10000WitnessInterval88_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 8800 lpfEntry10000WitnessDivisors88 = true := by decide

def lpfEntry10000WitnessDivisors89 : List Nat :=
  [
    2, 3, 2, 29, 2, 5, 2, 3, 2, 59, 2, 7, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 79, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 17,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 47, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 11, 2, 89, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0
  ]

theorem lpfEntry10000WitnessInterval89_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 8900 lpfEntry10000WitnessDivisors89 = true := by decide

def lpfEntry10000WitnessDivisors90 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 71, 2, 29,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 83, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 43, 2, 3, 2, 29, 2, 7,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 61, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3
  ]

theorem lpfEntry10000WitnessInterval90_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 9000 lpfEntry10000WitnessDivisors90 = true := by decide

def lpfEntry10000WitnessDivisors91 : List Nat :=
  [
    2, 19, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 89, 2, 53, 2, 3, 2, 0, 2, 5, 2, 3, 2, 67,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 29, 2, 3, 2, 17, 2, 0
  ]

theorem lpfEntry10000WitnessInterval91_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 9100 lpfEntry10000WitnessDivisors91 = true := by decide

def lpfEntry10000WitnessDivisors92 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 61, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 0, 2, 23, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 19, 2, 3, 2, 0, 2, 47,
    2, 3, 2, 59, 2, 5, 2, 3, 2, 13, 2, 73, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 37, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17
  ]

theorem lpfEntry10000WitnessInterval92_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 9200 lpfEntry10000WitnessDivisors92 = true := by decide

def lpfEntry10000WitnessDivisors93 : List Nat :=
  [
    2, 71, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 67, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 83,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 41, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval93_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 9300 lpfEntry10000WitnessDivisors93 = true := by decide

def lpfEntry10000WitnessDivisors94 : List Nat :=
  [
    2, 7, 2, 0, 2, 3, 2, 23, 2, 97, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 19, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7
  ]

theorem lpfEntry10000WitnessInterval94_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 9400 lpfEntry10000WitnessDivisors94 = true := by decide

def lpfEntry10000WitnessDivisors95 : List Nat :=
  [
    2, 3, 2, 13, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 0, 2, 89, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 41, 2, 3, 2, 19, 2, 11,
    2, 3, 2, 73, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 61, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 0, 2, 43, 2, 3, 2, 53, 2, 5, 2, 3, 2, 29
  ]

theorem lpfEntry10000WitnessInterval95_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 9500 lpfEntry10000WitnessDivisors95 = true := by decide

def lpfEntry10000WitnessDivisors96 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 59, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 31, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 17, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3
  ]

theorem lpfEntry10000WitnessInterval96_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 9600 lpfEntry10000WitnessDivisors96 = true := by decide

def lpfEntry10000WitnessDivisors97 : List Nat :=
  [
    2, 89, 2, 31, 2, 3, 2, 17, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 71, 2, 3, 2, 37, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 43, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 97, 2, 41
  ]

theorem lpfEntry10000WitnessInterval97_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 9700 lpfEntry10000WitnessDivisors97 = true := by decide

def lpfEntry10000WitnessDivisors98 : List Nat :=
  [
    2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 59, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 71, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 41, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19
  ]

theorem lpfEntry10000WitnessInterval98_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 9800 lpfEntry10000WitnessDivisors98 = true := by decide

def lpfEntry10000WitnessDivisors99 : List Nat :=
  [
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 23, 2, 3, 2, 47, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 0, 2, 61, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 17,
    2, 3, 2, 67, 2, 5, 2, 3, 2, 7, 2, 97, 2, 3, 2, 5, 2, 13, 2, 3
  ]

theorem lpfEntry10000WitnessInterval99_check :
    orbitTreeSieveIntervalCheck lpfEntry10000WitnessTree 9 9900 lpfEntry10000WitnessDivisors99 = true := by decide

end PrimeFactorOscillations.LPF

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.Cover0
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.SieveCoverConcat

/-! Composition of independently checked finite coverage packets. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def lpfEntry10000WitnessPacket0 : TreeSievePacket lpfEntry10000WitnessTree 9 0 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors0 rfl lpfEntry10000WitnessInterval0_check

def lpfEntry10000WitnessPacket1 : TreeSievePacket lpfEntry10000WitnessTree 9 100 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors1 rfl lpfEntry10000WitnessInterval1_check

def lpfEntry10000WitnessPacket2 : TreeSievePacket lpfEntry10000WitnessTree 9 200 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors2 rfl lpfEntry10000WitnessInterval2_check

def lpfEntry10000WitnessPacket3 : TreeSievePacket lpfEntry10000WitnessTree 9 300 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors3 rfl lpfEntry10000WitnessInterval3_check

def lpfEntry10000WitnessPacket4 : TreeSievePacket lpfEntry10000WitnessTree 9 400 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors4 rfl lpfEntry10000WitnessInterval4_check

def lpfEntry10000WitnessPacket5 : TreeSievePacket lpfEntry10000WitnessTree 9 500 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors5 rfl lpfEntry10000WitnessInterval5_check

def lpfEntry10000WitnessPacket6 : TreeSievePacket lpfEntry10000WitnessTree 9 600 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors6 rfl lpfEntry10000WitnessInterval6_check

def lpfEntry10000WitnessPacket7 : TreeSievePacket lpfEntry10000WitnessTree 9 700 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors7 rfl lpfEntry10000WitnessInterval7_check

def lpfEntry10000WitnessPacket8 : TreeSievePacket lpfEntry10000WitnessTree 9 800 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors8 rfl lpfEntry10000WitnessInterval8_check

def lpfEntry10000WitnessPacket9 : TreeSievePacket lpfEntry10000WitnessTree 9 900 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors9 rfl lpfEntry10000WitnessInterval9_check

def lpfEntry10000WitnessPacket10 : TreeSievePacket lpfEntry10000WitnessTree 9 1000 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors10 rfl lpfEntry10000WitnessInterval10_check

def lpfEntry10000WitnessPacket11 : TreeSievePacket lpfEntry10000WitnessTree 9 1100 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors11 rfl lpfEntry10000WitnessInterval11_check

def lpfEntry10000WitnessPacket12 : TreeSievePacket lpfEntry10000WitnessTree 9 1200 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors12 rfl lpfEntry10000WitnessInterval12_check

def lpfEntry10000WitnessPacket13 : TreeSievePacket lpfEntry10000WitnessTree 9 1300 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors13 rfl lpfEntry10000WitnessInterval13_check

def lpfEntry10000WitnessPacket14 : TreeSievePacket lpfEntry10000WitnessTree 9 1400 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors14 rfl lpfEntry10000WitnessInterval14_check

def lpfEntry10000WitnessPacket15 : TreeSievePacket lpfEntry10000WitnessTree 9 1500 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors15 rfl lpfEntry10000WitnessInterval15_check

def lpfEntry10000WitnessPacket16 : TreeSievePacket lpfEntry10000WitnessTree 9 1600 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors16 rfl lpfEntry10000WitnessInterval16_check

def lpfEntry10000WitnessPacket17 : TreeSievePacket lpfEntry10000WitnessTree 9 1700 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors17 rfl lpfEntry10000WitnessInterval17_check

def lpfEntry10000WitnessPacket18 : TreeSievePacket lpfEntry10000WitnessTree 9 1800 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors18 rfl lpfEntry10000WitnessInterval18_check

def lpfEntry10000WitnessPacket19 : TreeSievePacket lpfEntry10000WitnessTree 9 1900 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors19 rfl lpfEntry10000WitnessInterval19_check

def lpfEntry10000WitnessPacketBlock0 : TreeSievePacket lpfEntry10000WitnessTree 9 0 2000 :=
  (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket0
  lpfEntry10000WitnessPacket1)
  (TreeSievePacket.append lpfEntry10000WitnessPacket2
  (TreeSievePacket.append lpfEntry10000WitnessPacket3
  lpfEntry10000WitnessPacket4)))
  (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket5
  lpfEntry10000WitnessPacket6)
  (TreeSievePacket.append lpfEntry10000WitnessPacket7
  (TreeSievePacket.append lpfEntry10000WitnessPacket8
  lpfEntry10000WitnessPacket9))))
  (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket10
  lpfEntry10000WitnessPacket11)
  (TreeSievePacket.append lpfEntry10000WitnessPacket12
  (TreeSievePacket.append lpfEntry10000WitnessPacket13
  lpfEntry10000WitnessPacket14)))
  (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket15
  lpfEntry10000WitnessPacket16)
  (TreeSievePacket.append lpfEntry10000WitnessPacket17
  (TreeSievePacket.append lpfEntry10000WitnessPacket18
  lpfEntry10000WitnessPacket19)))))

end PrimeFactorOscillations.LPF

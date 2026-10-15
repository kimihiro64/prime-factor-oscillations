/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.Cover2
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.SieveCoverConcat

/-! Composition of independently checked finite coverage packets. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def lpfEntry10000WitnessPacket40 : TreeSievePacket lpfEntry10000WitnessTree 9 4000 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors40 rfl lpfEntry10000WitnessInterval40_check

def lpfEntry10000WitnessPacket41 : TreeSievePacket lpfEntry10000WitnessTree 9 4100 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors41 rfl lpfEntry10000WitnessInterval41_check

def lpfEntry10000WitnessPacket42 : TreeSievePacket lpfEntry10000WitnessTree 9 4200 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors42 rfl lpfEntry10000WitnessInterval42_check

def lpfEntry10000WitnessPacket43 : TreeSievePacket lpfEntry10000WitnessTree 9 4300 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors43 rfl lpfEntry10000WitnessInterval43_check

def lpfEntry10000WitnessPacket44 : TreeSievePacket lpfEntry10000WitnessTree 9 4400 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors44 rfl lpfEntry10000WitnessInterval44_check

def lpfEntry10000WitnessPacket45 : TreeSievePacket lpfEntry10000WitnessTree 9 4500 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors45 rfl lpfEntry10000WitnessInterval45_check

def lpfEntry10000WitnessPacket46 : TreeSievePacket lpfEntry10000WitnessTree 9 4600 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors46 rfl lpfEntry10000WitnessInterval46_check

def lpfEntry10000WitnessPacket47 : TreeSievePacket lpfEntry10000WitnessTree 9 4700 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors47 rfl lpfEntry10000WitnessInterval47_check

def lpfEntry10000WitnessPacket48 : TreeSievePacket lpfEntry10000WitnessTree 9 4800 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors48 rfl lpfEntry10000WitnessInterval48_check

def lpfEntry10000WitnessPacket49 : TreeSievePacket lpfEntry10000WitnessTree 9 4900 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors49 rfl lpfEntry10000WitnessInterval49_check

def lpfEntry10000WitnessPacket50 : TreeSievePacket lpfEntry10000WitnessTree 9 5000 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors50 rfl lpfEntry10000WitnessInterval50_check

def lpfEntry10000WitnessPacket51 : TreeSievePacket lpfEntry10000WitnessTree 9 5100 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors51 rfl lpfEntry10000WitnessInterval51_check

def lpfEntry10000WitnessPacket52 : TreeSievePacket lpfEntry10000WitnessTree 9 5200 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors52 rfl lpfEntry10000WitnessInterval52_check

def lpfEntry10000WitnessPacket53 : TreeSievePacket lpfEntry10000WitnessTree 9 5300 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors53 rfl lpfEntry10000WitnessInterval53_check

def lpfEntry10000WitnessPacket54 : TreeSievePacket lpfEntry10000WitnessTree 9 5400 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors54 rfl lpfEntry10000WitnessInterval54_check

def lpfEntry10000WitnessPacket55 : TreeSievePacket lpfEntry10000WitnessTree 9 5500 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors55 rfl lpfEntry10000WitnessInterval55_check

def lpfEntry10000WitnessPacket56 : TreeSievePacket lpfEntry10000WitnessTree 9 5600 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors56 rfl lpfEntry10000WitnessInterval56_check

def lpfEntry10000WitnessPacket57 : TreeSievePacket lpfEntry10000WitnessTree 9 5700 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors57 rfl lpfEntry10000WitnessInterval57_check

def lpfEntry10000WitnessPacket58 : TreeSievePacket lpfEntry10000WitnessTree 9 5800 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors58 rfl lpfEntry10000WitnessInterval58_check

def lpfEntry10000WitnessPacket59 : TreeSievePacket lpfEntry10000WitnessTree 9 5900 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors59 rfl lpfEntry10000WitnessInterval59_check

def lpfEntry10000WitnessPacketBlock2 : TreeSievePacket lpfEntry10000WitnessTree 9 4000 2000 :=
  (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket40
  lpfEntry10000WitnessPacket41)
  (TreeSievePacket.append lpfEntry10000WitnessPacket42
  (TreeSievePacket.append lpfEntry10000WitnessPacket43
  lpfEntry10000WitnessPacket44)))
  (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket45
  lpfEntry10000WitnessPacket46)
  (TreeSievePacket.append lpfEntry10000WitnessPacket47
  (TreeSievePacket.append lpfEntry10000WitnessPacket48
  lpfEntry10000WitnessPacket49))))
  (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket50
  lpfEntry10000WitnessPacket51)
  (TreeSievePacket.append lpfEntry10000WitnessPacket52
  (TreeSievePacket.append lpfEntry10000WitnessPacket53
  lpfEntry10000WitnessPacket54)))
  (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket55
  lpfEntry10000WitnessPacket56)
  (TreeSievePacket.append lpfEntry10000WitnessPacket57
  (TreeSievePacket.append lpfEntry10000WitnessPacket58
  lpfEntry10000WitnessPacket59)))))

end PrimeFactorOscillations.LPF

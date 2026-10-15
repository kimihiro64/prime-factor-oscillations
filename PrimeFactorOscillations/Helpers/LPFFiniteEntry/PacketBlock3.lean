/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.Cover3
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.SieveCoverConcat

/-! Composition of independently checked finite coverage packets. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def lpfEntry10000WitnessPacket60 : TreeSievePacket lpfEntry10000WitnessTree 9 6000 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors60 rfl lpfEntry10000WitnessInterval60_check

def lpfEntry10000WitnessPacket61 : TreeSievePacket lpfEntry10000WitnessTree 9 6100 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors61 rfl lpfEntry10000WitnessInterval61_check

def lpfEntry10000WitnessPacket62 : TreeSievePacket lpfEntry10000WitnessTree 9 6200 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors62 rfl lpfEntry10000WitnessInterval62_check

def lpfEntry10000WitnessPacket63 : TreeSievePacket lpfEntry10000WitnessTree 9 6300 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors63 rfl lpfEntry10000WitnessInterval63_check

def lpfEntry10000WitnessPacket64 : TreeSievePacket lpfEntry10000WitnessTree 9 6400 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors64 rfl lpfEntry10000WitnessInterval64_check

def lpfEntry10000WitnessPacket65 : TreeSievePacket lpfEntry10000WitnessTree 9 6500 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors65 rfl lpfEntry10000WitnessInterval65_check

def lpfEntry10000WitnessPacket66 : TreeSievePacket lpfEntry10000WitnessTree 9 6600 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors66 rfl lpfEntry10000WitnessInterval66_check

def lpfEntry10000WitnessPacket67 : TreeSievePacket lpfEntry10000WitnessTree 9 6700 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors67 rfl lpfEntry10000WitnessInterval67_check

def lpfEntry10000WitnessPacket68 : TreeSievePacket lpfEntry10000WitnessTree 9 6800 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors68 rfl lpfEntry10000WitnessInterval68_check

def lpfEntry10000WitnessPacket69 : TreeSievePacket lpfEntry10000WitnessTree 9 6900 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors69 rfl lpfEntry10000WitnessInterval69_check

def lpfEntry10000WitnessPacket70 : TreeSievePacket lpfEntry10000WitnessTree 9 7000 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors70 rfl lpfEntry10000WitnessInterval70_check

def lpfEntry10000WitnessPacket71 : TreeSievePacket lpfEntry10000WitnessTree 9 7100 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors71 rfl lpfEntry10000WitnessInterval71_check

def lpfEntry10000WitnessPacket72 : TreeSievePacket lpfEntry10000WitnessTree 9 7200 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors72 rfl lpfEntry10000WitnessInterval72_check

def lpfEntry10000WitnessPacket73 : TreeSievePacket lpfEntry10000WitnessTree 9 7300 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors73 rfl lpfEntry10000WitnessInterval73_check

def lpfEntry10000WitnessPacket74 : TreeSievePacket lpfEntry10000WitnessTree 9 7400 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors74 rfl lpfEntry10000WitnessInterval74_check

def lpfEntry10000WitnessPacket75 : TreeSievePacket lpfEntry10000WitnessTree 9 7500 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors75 rfl lpfEntry10000WitnessInterval75_check

def lpfEntry10000WitnessPacket76 : TreeSievePacket lpfEntry10000WitnessTree 9 7600 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors76 rfl lpfEntry10000WitnessInterval76_check

def lpfEntry10000WitnessPacket77 : TreeSievePacket lpfEntry10000WitnessTree 9 7700 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors77 rfl lpfEntry10000WitnessInterval77_check

def lpfEntry10000WitnessPacket78 : TreeSievePacket lpfEntry10000WitnessTree 9 7800 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors78 rfl lpfEntry10000WitnessInterval78_check

def lpfEntry10000WitnessPacket79 : TreeSievePacket lpfEntry10000WitnessTree 9 7900 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors79 rfl lpfEntry10000WitnessInterval79_check

def lpfEntry10000WitnessPacketBlock3 : TreeSievePacket lpfEntry10000WitnessTree 9 6000 2000 :=
  (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket60
  lpfEntry10000WitnessPacket61)
  (TreeSievePacket.append lpfEntry10000WitnessPacket62
  (TreeSievePacket.append lpfEntry10000WitnessPacket63
  lpfEntry10000WitnessPacket64)))
  (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket65
  lpfEntry10000WitnessPacket66)
  (TreeSievePacket.append lpfEntry10000WitnessPacket67
  (TreeSievePacket.append lpfEntry10000WitnessPacket68
  lpfEntry10000WitnessPacket69))))
  (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket70
  lpfEntry10000WitnessPacket71)
  (TreeSievePacket.append lpfEntry10000WitnessPacket72
  (TreeSievePacket.append lpfEntry10000WitnessPacket73
  lpfEntry10000WitnessPacket74)))
  (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket75
  lpfEntry10000WitnessPacket76)
  (TreeSievePacket.append lpfEntry10000WitnessPacket77
  (TreeSievePacket.append lpfEntry10000WitnessPacket78
  lpfEntry10000WitnessPacket79)))))

end PrimeFactorOscillations.LPF

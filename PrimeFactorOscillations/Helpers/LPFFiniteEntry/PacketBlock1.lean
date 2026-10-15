/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.Cover1
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.SieveCoverConcat

/-! Composition of independently checked finite coverage packets. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def lpfEntry10000WitnessPacket20 : TreeSievePacket lpfEntry10000WitnessTree 9 2000 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors20 rfl lpfEntry10000WitnessInterval20_check

def lpfEntry10000WitnessPacket21 : TreeSievePacket lpfEntry10000WitnessTree 9 2100 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors21 rfl lpfEntry10000WitnessInterval21_check

def lpfEntry10000WitnessPacket22 : TreeSievePacket lpfEntry10000WitnessTree 9 2200 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors22 rfl lpfEntry10000WitnessInterval22_check

def lpfEntry10000WitnessPacket23 : TreeSievePacket lpfEntry10000WitnessTree 9 2300 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors23 rfl lpfEntry10000WitnessInterval23_check

def lpfEntry10000WitnessPacket24 : TreeSievePacket lpfEntry10000WitnessTree 9 2400 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors24 rfl lpfEntry10000WitnessInterval24_check

def lpfEntry10000WitnessPacket25 : TreeSievePacket lpfEntry10000WitnessTree 9 2500 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors25 rfl lpfEntry10000WitnessInterval25_check

def lpfEntry10000WitnessPacket26 : TreeSievePacket lpfEntry10000WitnessTree 9 2600 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors26 rfl lpfEntry10000WitnessInterval26_check

def lpfEntry10000WitnessPacket27 : TreeSievePacket lpfEntry10000WitnessTree 9 2700 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors27 rfl lpfEntry10000WitnessInterval27_check

def lpfEntry10000WitnessPacket28 : TreeSievePacket lpfEntry10000WitnessTree 9 2800 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors28 rfl lpfEntry10000WitnessInterval28_check

def lpfEntry10000WitnessPacket29 : TreeSievePacket lpfEntry10000WitnessTree 9 2900 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors29 rfl lpfEntry10000WitnessInterval29_check

def lpfEntry10000WitnessPacket30 : TreeSievePacket lpfEntry10000WitnessTree 9 3000 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors30 rfl lpfEntry10000WitnessInterval30_check

def lpfEntry10000WitnessPacket31 : TreeSievePacket lpfEntry10000WitnessTree 9 3100 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors31 rfl lpfEntry10000WitnessInterval31_check

def lpfEntry10000WitnessPacket32 : TreeSievePacket lpfEntry10000WitnessTree 9 3200 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors32 rfl lpfEntry10000WitnessInterval32_check

def lpfEntry10000WitnessPacket33 : TreeSievePacket lpfEntry10000WitnessTree 9 3300 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors33 rfl lpfEntry10000WitnessInterval33_check

def lpfEntry10000WitnessPacket34 : TreeSievePacket lpfEntry10000WitnessTree 9 3400 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors34 rfl lpfEntry10000WitnessInterval34_check

def lpfEntry10000WitnessPacket35 : TreeSievePacket lpfEntry10000WitnessTree 9 3500 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors35 rfl lpfEntry10000WitnessInterval35_check

def lpfEntry10000WitnessPacket36 : TreeSievePacket lpfEntry10000WitnessTree 9 3600 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors36 rfl lpfEntry10000WitnessInterval36_check

def lpfEntry10000WitnessPacket37 : TreeSievePacket lpfEntry10000WitnessTree 9 3700 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors37 rfl lpfEntry10000WitnessInterval37_check

def lpfEntry10000WitnessPacket38 : TreeSievePacket lpfEntry10000WitnessTree 9 3800 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors38 rfl lpfEntry10000WitnessInterval38_check

def lpfEntry10000WitnessPacket39 : TreeSievePacket lpfEntry10000WitnessTree 9 3900 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors39 rfl lpfEntry10000WitnessInterval39_check

def lpfEntry10000WitnessPacketBlock1 : TreeSievePacket lpfEntry10000WitnessTree 9 2000 2000 :=
  (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket20
  lpfEntry10000WitnessPacket21)
  (TreeSievePacket.append lpfEntry10000WitnessPacket22
  (TreeSievePacket.append lpfEntry10000WitnessPacket23
  lpfEntry10000WitnessPacket24)))
  (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket25
  lpfEntry10000WitnessPacket26)
  (TreeSievePacket.append lpfEntry10000WitnessPacket27
  (TreeSievePacket.append lpfEntry10000WitnessPacket28
  lpfEntry10000WitnessPacket29))))
  (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket30
  lpfEntry10000WitnessPacket31)
  (TreeSievePacket.append lpfEntry10000WitnessPacket32
  (TreeSievePacket.append lpfEntry10000WitnessPacket33
  lpfEntry10000WitnessPacket34)))
  (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket35
  lpfEntry10000WitnessPacket36)
  (TreeSievePacket.append lpfEntry10000WitnessPacket37
  (TreeSievePacket.append lpfEntry10000WitnessPacket38
  lpfEntry10000WitnessPacket39)))))

end PrimeFactorOscillations.LPF

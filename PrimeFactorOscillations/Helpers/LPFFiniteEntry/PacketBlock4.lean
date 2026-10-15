/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.Cover4
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.SieveCoverConcat

/-! Composition of independently checked finite coverage packets. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def lpfEntry10000WitnessPacket80 : TreeSievePacket lpfEntry10000WitnessTree 9 8000 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors80 rfl lpfEntry10000WitnessInterval80_check

def lpfEntry10000WitnessPacket81 : TreeSievePacket lpfEntry10000WitnessTree 9 8100 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors81 rfl lpfEntry10000WitnessInterval81_check

def lpfEntry10000WitnessPacket82 : TreeSievePacket lpfEntry10000WitnessTree 9 8200 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors82 rfl lpfEntry10000WitnessInterval82_check

def lpfEntry10000WitnessPacket83 : TreeSievePacket lpfEntry10000WitnessTree 9 8300 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors83 rfl lpfEntry10000WitnessInterval83_check

def lpfEntry10000WitnessPacket84 : TreeSievePacket lpfEntry10000WitnessTree 9 8400 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors84 rfl lpfEntry10000WitnessInterval84_check

def lpfEntry10000WitnessPacket85 : TreeSievePacket lpfEntry10000WitnessTree 9 8500 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors85 rfl lpfEntry10000WitnessInterval85_check

def lpfEntry10000WitnessPacket86 : TreeSievePacket lpfEntry10000WitnessTree 9 8600 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors86 rfl lpfEntry10000WitnessInterval86_check

def lpfEntry10000WitnessPacket87 : TreeSievePacket lpfEntry10000WitnessTree 9 8700 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors87 rfl lpfEntry10000WitnessInterval87_check

def lpfEntry10000WitnessPacket88 : TreeSievePacket lpfEntry10000WitnessTree 9 8800 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors88 rfl lpfEntry10000WitnessInterval88_check

def lpfEntry10000WitnessPacket89 : TreeSievePacket lpfEntry10000WitnessTree 9 8900 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors89 rfl lpfEntry10000WitnessInterval89_check

def lpfEntry10000WitnessPacket90 : TreeSievePacket lpfEntry10000WitnessTree 9 9000 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors90 rfl lpfEntry10000WitnessInterval90_check

def lpfEntry10000WitnessPacket91 : TreeSievePacket lpfEntry10000WitnessTree 9 9100 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors91 rfl lpfEntry10000WitnessInterval91_check

def lpfEntry10000WitnessPacket92 : TreeSievePacket lpfEntry10000WitnessTree 9 9200 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors92 rfl lpfEntry10000WitnessInterval92_check

def lpfEntry10000WitnessPacket93 : TreeSievePacket lpfEntry10000WitnessTree 9 9300 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors93 rfl lpfEntry10000WitnessInterval93_check

def lpfEntry10000WitnessPacket94 : TreeSievePacket lpfEntry10000WitnessTree 9 9400 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors94 rfl lpfEntry10000WitnessInterval94_check

def lpfEntry10000WitnessPacket95 : TreeSievePacket lpfEntry10000WitnessTree 9 9500 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors95 rfl lpfEntry10000WitnessInterval95_check

def lpfEntry10000WitnessPacket96 : TreeSievePacket lpfEntry10000WitnessTree 9 9600 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors96 rfl lpfEntry10000WitnessInterval96_check

def lpfEntry10000WitnessPacket97 : TreeSievePacket lpfEntry10000WitnessTree 9 9700 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors97 rfl lpfEntry10000WitnessInterval97_check

def lpfEntry10000WitnessPacket98 : TreeSievePacket lpfEntry10000WitnessTree 9 9800 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors98 rfl lpfEntry10000WitnessInterval98_check

def lpfEntry10000WitnessPacket99 : TreeSievePacket lpfEntry10000WitnessTree 9 9900 100 :=
  TreeSievePacket.mk lpfEntry10000WitnessDivisors99 rfl lpfEntry10000WitnessInterval99_check

def lpfEntry10000WitnessPacketBlock4 : TreeSievePacket lpfEntry10000WitnessTree 9 8000 2000 :=
  (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket80
  lpfEntry10000WitnessPacket81)
  (TreeSievePacket.append lpfEntry10000WitnessPacket82
  (TreeSievePacket.append lpfEntry10000WitnessPacket83
  lpfEntry10000WitnessPacket84)))
  (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket85
  lpfEntry10000WitnessPacket86)
  (TreeSievePacket.append lpfEntry10000WitnessPacket87
  (TreeSievePacket.append lpfEntry10000WitnessPacket88
  lpfEntry10000WitnessPacket89))))
  (TreeSievePacket.append (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket90
  lpfEntry10000WitnessPacket91)
  (TreeSievePacket.append lpfEntry10000WitnessPacket92
  (TreeSievePacket.append lpfEntry10000WitnessPacket93
  lpfEntry10000WitnessPacket94)))
  (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacket95
  lpfEntry10000WitnessPacket96)
  (TreeSievePacket.append lpfEntry10000WitnessPacket97
  (TreeSievePacket.append lpfEntry10000WitnessPacket98
  lpfEntry10000WitnessPacket99)))))

end PrimeFactorOscillations.LPF

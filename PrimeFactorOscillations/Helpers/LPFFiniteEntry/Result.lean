/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.PacketBlock0
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.PacketBlock1
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.PacketBlock2
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.PacketBlock3
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.PacketBlock4
import PrimeFactorOscillations.Helpers.LPFJointTransfer

/-! Composition of independently checked finite coverage packets. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def lpfEntry10000WitnessFullPacket : TreeSievePacket lpfEntry10000WitnessTree 9 0 10000 :=
  (TreeSievePacket.append (TreeSievePacket.append lpfEntry10000WitnessPacketBlock0
  lpfEntry10000WitnessPacketBlock1)
  (TreeSievePacket.append lpfEntry10000WitnessPacketBlock2
  (TreeSievePacket.append lpfEntry10000WitnessPacketBlock3
  lpfEntry10000WitnessPacketBlock4)))

theorem prime_le_10000_mem_fullOrbit_two_9 (p : Nat) (hp : Nat.Prime p) (hle : p <= 10000) :
    Membership.mem (fullOrbit {2} 9) p := by
  have hpLt : p < 10000 := by
    by_contra h
    have hEq : p = 10000 := by omega
    subst p
    norm_num at hp
  have hEnd : p < 0 + lpfEntry10000WitnessFullPacket.divisors.length := by
    rw [lpfEntry10000WitnessFullPacket.length_eq]
    omega
  exact orbitTreeSieveIntervalCheck_reachable lpfEntry10000WitnessTree lpfEntry10000WitnessTree_check
    9 lpfEntry10000WitnessFullPacket.divisors 0 lpfEntry10000WitnessFullPacket.checked p hp
    (Nat.zero_le p) hEnd



theorem inputPrimePrefix_10000_subset_fullOrbit_two_9 :
    inputPrimePrefix 10000 <= fullOrbit {2} 9 := by
  intro p hp
  have h := Finset.mem_filter.mp hp
  have hBounds := Finset.mem_Icc.mp h.1
  exact prime_le_10000_mem_fullOrbit_two_9 p h.2 hBounds.2

theorem inputPrimePrefix_10000_fullOrbit_two_9_defect_zero :
    (SDiff.sdiff (inputPrimePrefix 10000) (fullOrbit {2} 9)).card = 0 := by
  by_contra h
  have hPos : 0 < (SDiff.sdiff (inputPrimePrefix 10000) (fullOrbit {2} 9)).card := by omega
  choose p hp using Finset.card_pos.mp hPos
  have hMem := Finset.mem_sdiff.mp hp
  exact hMem.2 (inputPrimePrefix_10000_subset_fullOrbit_two_9 hMem.1)

end PrimeFactorOscillations.LPF

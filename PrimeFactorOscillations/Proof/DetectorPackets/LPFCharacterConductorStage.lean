/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.LPFPrincipalCharacter
import PrimeFactorOscillations.Helpers.LPFPrincipalPrefix
import PrimeFactorOscillations.Helpers.QRHCharacterChebyshev

/-!
# LPFCharacterConductorStage

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# The principal character in the uniform LPF character-prefix input

The modulus-one character sum is the actual Chebyshev psi. The existing
finite Euler correction is reused for the principal character as well.
-/


namespace PrimeFactorOscillations.QRH

open BombieriVinogradov.SiegelWalfisz Robin1984

theorem principal_primitive_character_sum_identity
    {N x : Nat} [NeZero N] :
    characterChebyshevSum x (1 : DirichletCharacter Complex N).primitiveCharacter =
      (Chebyshev.psi (x : Real) : Complex) := by
  have hLevel : (1 : DirichletCharacter Complex N).conductor = 1 :=
    @DirichletCharacter.conductor_one Complex inferInstance N inferInstance
  rw [@DirichletCharacter.primitiveCharacter_one Complex inferInstance N inferInstance,
    hLevel]
  exact characterChebyshevSum_one_level_one x

end PrimeFactorOscillations.QRH

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenUniformCertificateBlocksHigh
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenUniformCertificateBlocksLow

/-!
# Assembly of the polynomial certificate columns

The sixteen bounded expansion modules give every column of the exact signed
certificate. This file performs only the exhaustive finite-index assembly.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Uniform.Certificate

/-- All polynomial columns of the exact stability certificate. -/
theorem column_expansion (y : Fin 6 -> Real) (j : Fin 79) :
    column y j = Finset.univ.sum (fun i : Fin 80 =>
      (coefficient j i : Real) * orbitBasis y i) := by
  refine Fin.cases (Block00.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block00.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block00.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block00.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block00.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block01.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block01.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block01.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block01.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block01.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block02.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block02.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block02.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block02.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block02.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block03.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block03.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block03.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block03.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block03.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block04.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block04.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block04.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block04.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block04.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block05.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block05.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block05.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block05.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block05.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block06.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block06.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block06.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block06.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block06.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block07.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block07.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block07.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block07.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block07.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block08.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block08.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block08.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block08.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block08.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block09.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block09.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block09.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block09.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block09.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block10.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block10.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block10.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block10.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block10.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block11.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block11.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block11.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block11.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block11.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block12.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block12.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block12.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block12.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block12.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block13.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block13.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block13.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block13.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block13.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block14.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block14.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block14.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block14.expansion y 3) ?_ j
  intro j
  refine Fin.cases (Block14.expansion y 4) ?_ j
  intro j
  refine Fin.cases (Block15.expansion y 0) ?_ j
  intro j
  refine Fin.cases (Block15.expansion y 1) ?_ j
  intro j
  refine Fin.cases (Block15.expansion y 2) ?_ j
  intro j
  refine Fin.cases (Block15.expansion y 3) ?_ j
  intro j
  exact Fin.elim0 j

end Metaplectic.G2Seven.Uniform.Certificate

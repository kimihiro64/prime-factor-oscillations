/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandau.lean
Original source lines 1664-1701. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauZetaPole

/-!
# The shifted Nicolas transform and positive-tail startup

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Asymptotics Filter MeasureTheory Set

noncomputable section

/-- The exact integrand in the shifted representation of `nicolasJMellin`. -/
def nicolasJMellinShiftIntegrand (z : Complex) (u : Real) : Complex :=
  ((u + 1 : Real) : Complex) *
    ((nicolasPsiMellinTailContinuation 3
          (((u + 1 : Real) : Complex) - z) -
        (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3
          ((u + 1 : Real) : Complex)) / z)


/-- Negating the required negative excursion gives the exact eventual
one-sided bound used by Landau's positivity argument. -/
theorem eventually_nicolasJ_add_rpow_pos_of_not_omegaMinus
    {b : Real}
    (hNot : Not (AtTopOmegaMinus nicolasJ (fun x : Real => x ^ (-b)))) :
    Filter.Eventually
      (fun x : Real => 0 < nicolasJ x + x ^ (-b)) atTop := by
  unfold AtTopOmegaMinus AtTopOmegaPlus at hNot
  push Not at hNot
  specialize hNot 1 zero_lt_one
  choose X hX using hNot
  filter_upwards [eventually_ge_atTop X] with x hx
  have hStrict := hX x hx
  linarith

/-- The eventual Landau sign can be represented by one finite startup
frontier, chosen beyond the fixed Mellin startup at three. -/
theorem exists_nicolasLandauPositiveTail_start
    {b : Real}
    (hNot : Not (AtTopOmegaMinus nicolasJ (fun x : Real => x ^ (-b)))) :
    Exists fun X : Real => And (3 <= X)
      (forall x : Real, X < x -> 0 <= nicolasJ x + x ^ (-b)) := by
  have hEventually :=
    eventually_nicolasJ_add_rpow_pos_of_not_omegaMinus hNot
  choose X hX using eventually_atTop.1 hEventually
  refine Exists.intro (max 3 X) (And.intro (le_max_left 3 X) ?_)
  intro x hx
  exact (hX x ((le_max_right 3 X).trans hx.le)).le

end

end Robin1984


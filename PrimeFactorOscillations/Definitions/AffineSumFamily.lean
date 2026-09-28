import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Fixed integer affine families and their actual local residue counts -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- A fixed nonempty family c_i*s+d_i with positive integer coefficients and
distinct rational roots. Repeated proportional forms are excluded explicitly. -/
structure AffineSumFamily where
  arity : Nat
  arity_pos : 0 < arity
  coeff : Fin arity -> Int
  shift : Fin arity -> Int
  coeff_pos : forall i : Fin arity, 0 < coeff i
  distinct_roots : forall i j : Fin arity, Not (i = j) ->
    Not (coeff i * shift j = coeff j * shift i)

namespace AffineSumFamily

/-- Evaluate the product in any commutative ring, including the integers and
prime residue fields. -/
def eval (F : AffineSumFamily) {R : Type*} [CommRing R] (s : R) : R :=
  Finset.univ.prod (fun i : Fin F.arity => (F.coeff i : R) * s + (F.shift i : R))

/-- The actual integer output on an ordered pair of prime candidates.
Primality and input cutoffs belong to the sampling theorem. -/
def value (F : AffineSumFamily) (p q : Nat) : Int :=
  F.eval ((p : Int) + q)

/-- Exact pair count among nonzero residues. At prime moduli these are exactly
the two reduced input residue classes used by prime-pair sampling. -/
noncomputable def nonzeroResidueCount (F : AffineSumFamily) (p : Nat) [NeZero p] : Nat := by
  classical
  exact (((Finset.univ.erase (0 : ZMod p)).product (Finset.univ.erase (0 : ZMod p))).filter
    (fun ab : Prod (ZMod p) (ZMod p) => F.eval (ab.1 + ab.2) = 0)).card

/-- The local divisibility probability is defined by the exact finite residue
count at every prime, including all forced, excluded and colliding cases. -/
noncomputable def localProbability (F : AffineSumFamily) (p : Nat) : Real :=
  if hp : Nat.Prime p then
    letI : NeZero p := NeZero.mk hp.ne_zero
    (F.nonzeroResidueCount p : Real) / ((p : Real) - 1) ^ 2
  else 0

/-- The residue-count definition supplies a probability at every prime,
without discarding bad coefficients or coincident roots. -/
theorem localProbability_bounds (F : AffineSumFamily) (p : Nat) (hp : Nat.Prime p) :
    0 <= F.localProbability p /\ F.localProbability p <= 1 := by
  classical
  let : NeZero p := NeZero.mk hp.ne_zero
  have hp1 : 1 <= p := hp.one_lt.le
  have hpR : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hd : 0 < ((p : Real) - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hcount : F.nonzeroResidueCount p <= (p - 1) * (p - 1) := by
    have hfilter := Finset.card_filter_le
      ((Finset.univ.erase (0 : ZMod p)).product (Finset.univ.erase (0 : ZMod p)))
      (fun ab : Prod (ZMod p) (ZMod p) => F.eval (ab.1 + ab.2) = 0)
    have hprod : ((Finset.univ.erase (0 : ZMod p)).product
        (Finset.univ.erase (0 : ZMod p))).card = (p - 1) * (p - 1) := by
      calc
        _ = (Finset.univ.erase (0 : ZMod p)).card *
            (Finset.univ.erase (0 : ZMod p)).card := Finset.card_product _ _
        _ = _ := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)),
            Finset.card_univ, ZMod.card]
    exact hfilter.trans_eq hprod
  have hcountR : (F.nonzeroResidueCount p : Real) <= ((p : Real) - 1) ^ 2 := by
    have h : (F.nonzeroResidueCount p : Real) <=
        ((p - 1 : Nat) : Real) * ((p - 1 : Nat) : Real) := by exact_mod_cast hcount
    simpa only [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one, pow_two] using h
  dsimp only [localProbability]
  rw [dite_eq_left hp]
  refine And.intro (div_nonneg (Nat.cast_nonneg _) hd.le) ?_
  have hdiv := div_le_div_of_nonneg_right hcountR hd.le
  simpa only [div_self (ne_of_gt hd)] using hdiv

end AffineSumFamily

end PrimeFactorOscillations

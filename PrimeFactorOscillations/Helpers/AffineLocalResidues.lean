import Mathlib.Algebra.Field.ZMod
import PrimeFactorOscillations.Definitions.AffineSumFamily
import PrimeFactorOscillations.Mathlib.Algebra.Field.FiniteAffineRoots

/-! # Finite bad moduli and exact affine prime-pair local probabilities -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.AffineSumFamily

/-- All coefficient, determinant and nonzero-shift exceptions lie below a
single cutoff depending only on the fixed family. -/
theorem eventually_good_moduli (F : AffineSumFamily) :
    exists P : Nat, forall p : Nat, P <= p ->
      (forall i : Fin F.arity, Not ((F.coeff i : ZMod p) = 0)) /\
      (forall i j : Fin F.arity, Not (i = j) ->
        Not ((F.coeff i : ZMod p) * (F.shift j : ZMod p) =
          (F.coeff j : ZMod p) * (F.shift i : ZMod p))) /\
      (forall i : Fin F.arity, (F.shift i : ZMod p) = 0 <-> F.shift i = 0) := by
  classical
  have hsmall : forall (z : Int) (p : Nat), Not (z = 0) -> z.natAbs < p ->
      Not ((z : ZMod p) = 0) := by
    intro z p hz hzp hcast
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hcast
    have hdAbs : p <= z.natAbs := by
      apply Nat.le_of_dvd (Int.natAbs_pos.mpr hz)
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
    omega
  let C := Finset.univ.sup (fun i : Fin F.arity => (F.coeff i).natAbs)
  let D := Finset.univ.sup (fun i : Fin F.arity => (F.shift i).natAbs)
  let E := Finset.univ.sup (fun i : Fin F.arity =>
    Finset.univ.sup (fun j : Fin F.arity =>
      (F.coeff i * F.shift j - F.coeff j * F.shift i).natAbs))
  refine Exists.intro (1 + C + D + E) ?_
  intro p hp
  refine And.intro ?_ (And.intro ?_ ?_)
  next =>
    intro i
    have hC : (F.coeff i).natAbs <= C :=
      Finset.le_sup (f := fun i : Fin F.arity => (F.coeff i).natAbs) (Finset.mem_univ i)
    exact hsmall (F.coeff i) p (ne_of_gt (F.coeff_pos i)) (by omega)
  next =>
    intro i j hij hsame
    have hi : (Finset.univ.sup (fun j : Fin F.arity =>
        (F.coeff i * F.shift j - F.coeff j * F.shift i).natAbs)) <= E :=
      Finset.le_sup (f := fun i : Fin F.arity => Finset.univ.sup (fun j : Fin F.arity =>
        (F.coeff i * F.shift j - F.coeff j * F.shift i).natAbs)) (Finset.mem_univ i)
    have hj : (F.coeff i * F.shift j - F.coeff j * F.shift i).natAbs <=
        Finset.univ.sup (fun j : Fin F.arity =>
          (F.coeff i * F.shift j - F.coeff j * F.shift i).natAbs) :=
      Finset.le_sup (f := fun j : Fin F.arity =>
        (F.coeff i * F.shift j - F.coeff j * F.shift i).natAbs) (Finset.mem_univ j)
    have hne := hsmall (F.coeff i * F.shift j - F.coeff j * F.shift i) p
      (sub_ne_zero.mpr (F.distinct_roots i j hij)) (by omega)
    apply hne
    simp only [Int.cast_sub, Int.cast_mul]
    exact sub_eq_zero.mpr hsame
  next =>
    intro i
    have hD : (F.shift i).natAbs <= D :=
      Finset.le_sup (f := fun i : Fin F.arity => (F.shift i).natAbs) (Finset.mem_univ i)
    constructor
    next =>
      intro hz
      by_contra hne
      exact hsmall (F.shift i) p hne (by omega) hz
    next =>
      intro hz
      rw [hz, Int.cast_zero]

/-- Beyond the proved finite exception set, the actual local residue
probability has sieve dimension equal to the number of distinct forms. -/
theorem eventually_localProbability_formula (F : AffineSumFamily) :
    exists P : Nat, forall p : Nat, P <= p -> Nat.Prime p ->
      F.localProbability p =
        ((F.arity : Real) * ((p : Real) - 2) +
          (if (exists i : Fin F.arity, F.shift i = 0) then (1 : Real) else 0)) /
          ((p : Real) - 1) ^ 2 := by
  classical
  choose P hP using F.eventually_good_moduli
  refine Exists.intro P ?_
  intro p hp hprime
  let : NeZero p := NeZero.mk hprime.ne_zero
  let : Fact (Nat.Prime p) := Fact.mk hprime
  have hgood := hP p hp
  have hzero : (exists i : Fin F.arity, (F.shift i : ZMod p) = 0) <->
      exists i : Fin F.arity, F.shift i = 0 := by
    constructor
    next =>
      intro h
      choose i hi using h
      exact Exists.intro i ((hgood.2.2 i).mp hi)
    next =>
      intro h
      choose i hi using h
      exact Exists.intro i ((hgood.2.2 i).mpr hi)
  have hcount := Finset.card_nonzero_affine_product_sum
    (show 2 <= Fintype.card (ZMod p) by simpa only [ZMod.card] using hprime.two_le)
    (fun i : Fin F.arity => (F.coeff i : ZMod p))
    (fun i : Fin F.arity => (F.shift i : ZMod p)) hgood.1 hgood.2.1
  have hcountNat : F.nonzeroResidueCount p = F.arity * (p - 2) +
      (if (exists i : Fin F.arity, F.shift i = 0) then (1 : Nat) else 0) := by
    have hrepr : F.nonzeroResidueCount p =
        (((Finset.univ.erase (0 : ZMod p)).product (Finset.univ.erase (0 : ZMod p))).filter
          (fun ab : Prod (ZMod p) (ZMod p) =>
            (Finset.univ.prod (fun i : Fin F.arity =>
              (F.coeff i : ZMod p) * (ab.1 + ab.2) + (F.shift i : ZMod p))) = 0)).card := by
      rfl
    rw [hrepr]
    simpa only [Fintype.card_fin, ZMod.card, hzero] using hcount
  dsimp only [localProbability]
  rw [dite_eq_left hprime, hcountNat]
  by_cases hz : exists i : Fin F.arity, F.shift i = 0
  next =>
    simp only [ite_eq_left hz, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub hprime.two_le, Nat.cast_ofNat, Nat.cast_one]
  next =>
    simp only [ite_eq_right hz, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub hprime.two_le, Nat.cast_ofNat, Nat.cast_zero]

end PrimeFactorOscillations.AffineSumFamily

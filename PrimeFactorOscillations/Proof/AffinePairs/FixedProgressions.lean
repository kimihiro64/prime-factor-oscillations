import BombieriVinogradov.Assembly.PrimeCountingConversion.Main
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeGapsTheory.NumberTheory.PNT

/-! # Fixed arithmetic progression estimates and prime-count normalization -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter

/-- The verified Bombieri-Vinogradov theorem supplies a simultaneous reduced
residue estimate at every fixed positive modulus, with arbitrary log saving. -/
theorem fixed_progression_prime_error
    (q : Nat) (hq : 1 <= q) (A : Real) (hA : 1 <= A) :
    exists C : Real, 0 < C /\ exists X0 : Real, forall X : Real, X0 <= X ->
      forall a : Units (ZMod q),
      abs ((Real.primeCountingZMod X q a : Real) -
        BombieriVinogradov.primeCounting X / q.totient) <=
        C * X / (Real.log X) ^ A := by
  classical
  let : NeZero q := NeZero.mk (by omega)
  have hBV := BombieriVinogradov.statement_iff_average.mp
    BombieriVinogradov.PrimeCountingConversion.weighted_to_prime_counting
  choose C hC hCX using hBV ((1 : Real) / 4) (by norm_num) A hA
  have hscale : Filter.Eventually (fun X : Real => (q : Real) <= X ^ ((1 : Real) / 4))
      Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 4)).eventually
      (Filter.eventually_ge_atTop (q : Real))
  choose X1 hX1 using Filter.eventually_atTop.mp hscale
  refine Exists.intro C (And.intro hC (Exists.intro (max 3 X1) ?_))
  intro X hX a
  have hX3 : 3 <= X := (le_max_left 3 X1).trans hX
  have hqx : q <= Nat.floor (X ^ ((1 : Real) / 4)) :=
    Nat.le_floor (hX1 X ((le_max_right 3 X1).trans hX))
  have hqmem : Membership.mem (Finset.Icc 1 (Nat.floor (X ^ ((1 : Real) / 4)))) q :=
    Finset.mem_Icc.mpr (And.intro hq hqx)
  have hnonneg : forall r : Nat, Membership.mem
      (Finset.Icc 1 (Nat.floor (X ^ ((1 : Real) / 4)))) r ->
      0 <= BombieriVinogradov.maxPrimeDiscrepancy X r := by
    intro r hr
    have hr1 := (Finset.mem_Icc.mp hr).1
    let : NeZero r := NeZero.mk (by omega)
    have hbdd : BddAbove (Set.range (fun b : Units (ZMod r) =>
        BombieriVinogradov.primeDiscrepancy X r b)) :=
      (Set.finite_range _).bddAbove
    exact (abs_nonneg _).trans (le_ciSup hbdd (1 : Units (ZMod r)))
  have hpoint : abs ((Real.primeCountingZMod X q a : Real) -
      BombieriVinogradov.primeCounting X / q.totient) <=
      BombieriVinogradov.maxPrimeDiscrepancy X q := by
    exact le_ciSup (Set.finite_range (fun b : Units (ZMod q) =>
      BombieriVinogradov.primeDiscrepancy X q b)).bddAbove a
  have hsum : BombieriVinogradov.maxPrimeDiscrepancy X q <=
      BombieriVinogradov.averagePrimeDiscrepancy X ((1 : Real) / 4) :=
    Finset.single_le_sum hnonneg hqmem
  exact hpoint.trans (hsum.trans (hCX X hX3))


/-- The maintained prime number theorem supplies an eventual positive lower
bound strong enough to normalize the fixed-progression discrepancy. -/
theorem eventually_primeCounting_lower :
    exists K : Nat, forall N : Nat, K <= N ->
      (N : Real) / (2 * Real.log (N : Real)) <= (Nat.primeCounting N : Real) /\
      0 < (Nat.primeCounting N : Real) := by
  choose C N0 hN0 using PNT.primeCounting
  have hlog : Filter.Eventually
      (fun N : Nat => max 1 (2 * C) <= Real.log (N : Real)) Filter.atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (max 1 (2 * C)))
  choose KL hKL using Filter.eventually_atTop.mp hlog
  refine Exists.intro (max 3 (max N0 KL)) ?_
  intro N hN
  have hN3 : (3 : Real) <= N := by exact_mod_cast (show 3 <= N by omega)
  have hNp : (0 : Real) < N := by linarith only [hN3]
  let L : Real := Real.log (N : Real)
  have hL1 : 1 <= L := (le_max_left 1 (2 * C)).trans (hKL N (by omega))
  have hL : 0 < L := by linarith only [hL1]
  have hCL : 2 * C <= L := (le_max_right 1 (2 * C)).trans (hKL N (by omega))
  have hdiv := div_le_div_of_nonneg_right hCL hL.le
  rw [div_self (ne_of_gt hL)] at hdiv
  have htwice : (2 * C) / L = 2 * (C / L) := by ring
  rw [htwice] at hdiv
  have hhalf : C / L <= (1 : Real) / 2 := by linarith only [hdiv]
  have hbasePos : 0 < (N : Real) / L := div_pos hNp hL
  have hrem : C * (N : Real) / L ^ 2 <= (N : Real) / (2 * L) := by
    calc
      _ = ((N : Real) / L) * (C / L) := by ring
      _ <= ((N : Real) / L) * ((1 : Real) / 2) :=
        mul_le_mul_of_nonneg_left hhalf hbasePos.le
      _ = _ := by field_simp [ne_of_gt hL]
  have hbase : (N : Real) / L = 2 * ((N : Real) / (2 * L)) := by
    field_simp [ne_of_gt hL]
  have happrox := hN0 N (by omega)
  change abs ((Nat.primeCounting N : Real) - (N : Real) / L) <= C * (N : Real) / L ^ 2
    at happrox
  have hlo : (N : Real) / (2 * L) <= (Nat.primeCounting N : Real) := by
    have herror := (abs_le.mp happrox).1
    linarith only [herror, hrem, hbase]
  exact And.intro hlo ((div_pos hNp (by linarith only [hL])).trans_le hlo)


end PrimeFactorOscillations

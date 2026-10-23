/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CarmichaelMaximalOrderLifts
import PrimeFactorOscillations.Helpers.PrimeOrderGatedRigidity

/-!
# Conditional rigidity of maximal-order lift densities

A nonzero fiber has density at least the prime-product floor.
Its relative excess pays for every closed gate and every repeated
auxiliary prime coordinate. Near equality forces small-prime gates
open and their auxiliary ownership ranks equal to one.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelConditionalRigidity

open FiniteHomProbability PrimeOrderReturnLaw PrimeOrderReturnIndex
  PrimeOrderReturnRigidity PrimeOrderGatedRigidity CarmichaelProfileExtension
  CarmichaelProfileLifts CarmichaelProfileCriterion CarmichaelProfileKernel
  CarmichaelMaximalOrderLifts CarmichaelEvenThinning

local instance imageFintype {G : Type*} [CommGroup G] [Fintype G] (L l : Nat) :
    Fintype (returnImage (G := G) L l) :=
  PrimeOrderReturnLaw.imageFintype L l

def auxiliaryRank (m B : Nat) (l : Nat.Primes) : Nat :=
  returnMultiplicity B (Monoid.exponent (Units (ZMod (m * B)))) l

def conditionalExcess (m B : Nat) (a : Units (ZMod m)) : Real :=
  maximalOrderLiftProbability m B a / vacancyFloor (exponentPrimePacket (m * B)) - 1

def conditionalPenalty (m B : Nat) (a : Units (ZMod m)) (l : Nat.Primes) : Real :=
  if returnGate m B a (l : Nat) then
    if 2 <= auxiliaryRank m B l then 1 / ((l : Nat) : Real) else 0
  else 1 / (((l : Nat) : Real) - 1)

theorem auxiliary_index_prime_pow (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (m * B))))) :
    returnIndex (G := Units (ZMod B))
      (Monoid.exponent (Units (ZMod (m * B)))) (l : Nat) = (l : Nat) ^ auxiliaryRank m B l := by
  have hBE : Dvd.dvd (Monoid.exponent (Units (ZMod B)))
      (Monoid.exponent (Units (ZMod (m * B)))) :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (auxiliary_exponent_annihilates m B hCoprime)
  apply squarefree_unit_returnIndex_eq_prime_pow B hSqB _ l _ hl
  intro p
  have hp := (Nat.mem_primeFactors.mp p.property).1
  have hpB := (Nat.mem_primeFactors.mp p.property).2.1
  exact dvd_trans (prime_period_dvd_exponent B hSqB p.val hp hpB) hBE

theorem open_auxiliary_rank_pos (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B))))
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (m * B)))))
    (hOpen : returnGate m B a (l : Nat) = true) : 0 < auxiliaryRank m B l := by
  classical
  apply Nat.pos_of_ne_zero
  intro hZero
  let E := Monoid.exponent (Units (ZMod (m * B)))
  choose u hu using (maximal_order_lift_exists_iff m B hCoprime a).mpr hFeasible
  have hIndex : returnIndex (G := Units (ZMod B)) E (l : Nat) = 1 := by
    rw [auxiliary_index_prime_pow m B hSqB hCoprime l hl, hZero, pow_zero]
  have hCardLe : Fintype.card (returnImage (G := Units (ZMod B)) E (l : Nat)) <= 1 := by
    change returnIndex (G := Units (ZMod B)) E (l : Nat) <= 1
    rw [hIndex]
  have hSub : Subsingleton (returnImage (G := Units (ZMod B)) E (l : Nat)) :=
    Fintype.card_le_one_iff_subsingleton.mp hCardLe
  let b := unitReduction (dvd_mul_left B m) u
  let x : returnImage (G := Units (ZMod B)) E (l : Nat) :=
    Subtype.mk (b ^ (E / (l : Nat))) (Exists.intro b rfl)
  have hx : x = 1 := @Subsingleton.elim _ hSub x 1
  have hAuxReturn : b ^ (E / (l : Nat)) = 1 := congrArg Subtype.val hx
  have hCondition := (returnGate_eq_true m B a (l : Nat)).mp hOpen
  have hNewReturn : u ^ (E / (l : Nat)) = 1 := by
    apply (reduction_return_gate_all_labels m B hCoprime l hl u).mpr
    refine And.intro ?_ hAuxReturn
    rw [hu.1]
    exact hCondition
  have hPattern := (maximal_order_iff_full_nonreturn (m * B) u).mp hu.2
  have hMem : Membership.mem (exponentPrimePacket (m * B)) l :=
    (exponentPrimePacket_mem (m * B) l).mpr hl
  exact hPattern (Subtype.mk l hMem) hNewReturn

theorem auxiliary_power_le_index (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (m * B)))))
    (k : Nat) (hk : k <= auxiliaryRank m B l) :
    (l : Nat) ^ k <= returnIndex (G := Units (ZMod B))
      (Monoid.exponent (Units (ZMod (m * B)))) (l : Nat) := by
  let r := auxiliaryRank m B l
  have hRepr : r = (r - k) + k := by dsimp [r]; omega
  have hPowPos : 0 < (l : Nat) ^ (r - k) := pow_pos l.property.pos _
  have hPowOne : 1 <= (l : Nat) ^ (r - k) := by omega
  rw [auxiliary_index_prime_pow m B hSqB hCoprime l hl]
  change (l : Nat) ^ k <= (l : Nat) ^ r
  calc
    (l : Nat) ^ k <= (l : Nat) ^ (r - k) * (l : Nat) ^ k := by
      simpa only [one_mul] using Nat.mul_le_mul_right ((l : Nat) ^ k) hPowOne
    _ = (l : Nat) ^ r := by rw [<- pow_add, <- hRepr]

theorem open_auxiliary_index_ge_prime (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B))))
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (m * B)))))
    (hOpen : returnGate m B a (l : Nat) = true) :
    (l : Nat) <= returnIndex (G := Units (ZMod B))
      (Monoid.exponent (Units (ZMod (m * B)))) (l : Nat) := by
  have hRank := open_auxiliary_rank_pos m B hSqB hCoprime a hFeasible l hl hOpen
  have h := auxiliary_power_le_index m B hSqB hCoprime l hl 1 (by omega)
  simpa only [pow_one] using h

theorem feasible_open_indices (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B)))) :
    forall l : exponentPrimePacket (m * B), returnGate m B a (l.val : Nat) = true ->
      ((l.val : Nat) : Real) <= (returnIndex (G := Units (ZMod B))
        (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) : Real) := by
  intro l hOpen
  exact_mod_cast open_auxiliary_index_ge_prime m B hSqB hCoprime a hFeasible l.val
    ((exponentPrimePacket_mem (m * B) l.val).mp l.property) hOpen

theorem maximalProbability_eq_gatedVacancy (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) :
    maximalOrderLiftProbability m B a =
      gatedVacancy (exponentPrimePacket (m * B))
        (fun l => returnGate m B a (l.val : Nat))
        (fun l => (returnIndex (G := Units (ZMod B))
          (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) : Real)) :=
  maximalOrderLiftProbability_eq_product m B hCoprime a

theorem conditional_penalty_le_defect (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B))))
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (m * B))))) :
    conditionalPenalty m B a l <=
      gatedCoordinateDefect ((l : Nat) : Real)
        (returnIndex (G := Units (ZMod B))
          (Monoid.exponent (Units (ZMod (m * B)))) (l : Nat) : Real)
        (returnGate m B a (l : Nat)) := by
  have hlReal : (1 : Real) < ((l : Nat) : Real) := by exact_mod_cast l.property.one_lt
  unfold conditionalPenalty
  cases hGate : returnGate m B a (l : Nat)
  { exact le_rfl }
  { change (if 2 <= auxiliaryRank m B l then 1 / ((l : Nat) : Real) else 0) <=
      coordinateDefect ((l : Nat) : Real)
        (returnIndex (G := Units (ZMod B))
          (Monoid.exponent (Units (ZMod (m * B)))) (l : Nat) : Real)
    split_ifs with hRank
    { apply coordinateDefect_ge_reciprocal _ _ hlReal
      exact_mod_cast auxiliary_power_le_index m B hSqB hCoprime l hl 2 hRank }
    { apply coordinateDefect_nonneg _ _ hlReal
      exact_mod_cast open_auxiliary_index_ge_prime m B hSqB hCoprime a hFeasible l hl hGate } }

theorem conditional_excess_ge_penalty_sum (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B)))) :
    Finset.univ.sum (fun l : exponentPrimePacket (m * B) => conditionalPenalty m B a l.val) <=
      conditionalExcess m B a := by
  classical
  unfold conditionalExcess
  rw [maximalProbability_eq_gatedVacancy m B hCoprime a]
  apply le_trans _ (gated_excess_ge_defect_sum _ _ _
    (feasible_open_indices m B hSqB hCoprime a hFeasible))
  apply Finset.sum_le_sum
  intro l _
  exact conditional_penalty_le_defect m B hSqB hCoprime a hFeasible l.val
    ((exponentPrimePacket_mem (m * B) l.val).mp l.property)

theorem feasible_density_ge_floor (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B)))) :
    vacancyFloor (exponentPrimePacket (m * B)) <= maximalOrderLiftProbability m B a := by
  rw [maximalProbability_eq_gatedVacancy m B hCoprime a]
  exact gated_vacancy_ge_floor _ _ _ (feasible_open_indices m B hSqB hCoprime a hFeasible)

theorem infeasible_density_zero (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hInfeasible : Not (Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B))))) :
    maximalOrderLiftProbability m B a = 0 := by
  have hPred :
      (fun u : {u : Units (ZMod (m * B)) // unitReduction (dvd_mul_right m B) u = a} =>
        orderOf u.val = Monoid.exponent (Units (ZMod (m * B)))) =
      (fun _ => False) := by
    funext u
    apply propext
    constructor
    { intro h
      apply hInfeasible
      exact (maximal_order_lift_exists_iff m B hCoprime a).mp
        (Exists.intro u.val (And.intro u.property h)) }
    { exact False.elim }
  unfold maximalOrderLiftProbability
  rw [hPred]
  exact uniformProbability_false

theorem conditional_density_dichotomy (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) :
    Or (maximalOrderLiftProbability m B a = 0)
      (vacancyFloor (exponentPrimePacket (m * B)) <= maximalOrderLiftProbability m B a) := by
  classical
  by_cases h : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B)))
  { exact Or.inr (feasible_density_ge_floor m B hSqB hCoprime a h) }
  { exact Or.inl (infeasible_density_zero m B hCoprime a h) }

theorem near_minimal_small_labels_unique (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B))))
    (Y : Real) (hY : 0 < Y) (hSmall : conditionalExcess m B a < 1 / Y)
    (l : exponentPrimePacket (m * B)) (hlY : ((l.val : Nat) : Real) <= Y) :
    And (returnGate m B a (l.val : Nat) = true) (auxiliaryRank m B l.val = 1) := by
  unfold conditionalExcess at hSmall
  rw [maximalProbability_eq_gatedVacancy m B hCoprime a] at hSmall
  have h := near_minimal_gate_and_index_small _ _ _
    (feasible_open_indices m B hSqB hCoprime a hFeasible) Y hY hSmall l hlY
  have hlDiv := (exponentPrimePacket_mem (m * B) l.val).mp l.property
  have hRankPos := open_auxiliary_rank_pos m B hSqB hCoprime a hFeasible l.val hlDiv h.1
  have hNotRepeated : Not (2 <= auxiliaryRank m B l.val) := by
    intro hRepeated
    have hSquare := auxiliary_power_le_index m B hSqB hCoprime l.val hlDiv 2 hRepeated
    have hSquareReal : ((l.val : Nat) : Real) ^ 2 <=
        (returnIndex (G := Units (ZMod B))
          (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) : Real) := by
      exact_mod_cast hSquare
    linarith [h.2]
  exact And.intro h.1 (by omega)

theorem conditional_density_eq_floor_iff (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B)))) :
    maximalOrderLiftProbability m B a = vacancyFloor (exponentPrimePacket (m * B)) <->
      forall l : exponentPrimePacket (m * B),
        And (returnGate m B a (l.val : Nat) = true) (auxiliaryRank m B l.val = 1) := by
  constructor
  { intro h l
    have hPos : (0 : Real) < ((l.val : Nat) : Real) := by exact_mod_cast l.val.property.pos
    have hSmall : conditionalExcess m B a < 1 / ((l.val : Nat) : Real) := by
      unfold conditionalExcess
      rw [h, div_self (ne_of_gt (vacancyFloor_pos _)), sub_self]
      exact one_div_pos.mpr hPos
    exact near_minimal_small_labels_unique m B hSqB hCoprime a hFeasible _ hPos hSmall l le_rfl }
  { intro h
    rw [maximalOrderLiftProbability_eq_product m B hCoprime a]
    unfold vacancyFloor
    apply Finset.prod_congr rfl
    intro l _
    rw [(h l).1]
    have hIndex := auxiliary_index_prime_pow m B hSqB hCoprime l.val
      ((exponentPrimePacket_mem (m * B) l.val).mp l.property)
    rw [hIndex, (h l).2, pow_one]
    exact if_pos rfl }

end PrimeFactorOscillations.CarmichaelConditionalRigidity

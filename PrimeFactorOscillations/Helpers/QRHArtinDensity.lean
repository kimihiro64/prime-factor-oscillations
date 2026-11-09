/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHPrimeSquareSpectrum
import PrimeFactorOscillations.Helpers.QRHPrimeSquareTail

/-! # The positive Euler-product density for squarefree prime differences

The finite unit-coordinate densities converge to the unconditional product
over all prime factors. A uniform quarter lower bound retains a nonzero
principal density in the signed spectral consumer.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Filter
open scoped Classical
namespace PrimeFactorOscillations.QRH

def primeSquareEulerFactor (p : Nat) : Real :=
  if Nat.Prime p then 1 - 1 / ((p * (p - 1) : Nat) : Real) else 1

def primeSquareCutoffDensity (R : Nat) : Real :=
  Nat.primeSquareUnitDensity (fun p : oddPrimeVertices R => p.val)

def artinPrimeSquareConstant : Real :=
  sInf (Set.range primeSquareCutoffDensity)

private theorem odd_prime_props (R p : Nat) (hp : Membership.mem (oddPrimeVertices R) p) :
    Nat.Prime p /\ 3 <= p /\ p <= R := by
  have hh := Finset.mem_erase.mp hp
  have hPrime := Nat.mem_primesBelow.mp hh.2
  have hTwo := hPrime.2.two_le
  exact And.intro hPrime.2 (And.intro (by omega) (by omega))

private theorem prime_defect_bounds {p : Nat} (hp : Nat.Prime p) :
    0 <= 1 / ((p * (p - 1) : Nat) : Real) /\
      1 / ((p * (p - 1) : Nat) : Real) <= 1 := by
  have hSub : 1 <= p - 1 := by have h := hp.two_le; omega
  have hDenNat : 2 <= p * (p - 1) := by
    simpa using Nat.mul_le_mul hp.two_le hSub
  have hDen : (1 : Real) <= ((p * (p - 1) : Nat) : Real) := by
    have h : (2 : Real) <= ((p * (p - 1) : Nat) : Real) := by exact_mod_cast hDenNat
    linarith
  refine And.intro (by positivity) ?_
  simpa using div_le_div_of_nonneg_left
    (show (0 : Real) <= 1 by norm_num) (show (0 : Real) < 1 by norm_num) hDen

private theorem euler_factor_bounds (p : Nat) :
    0 <= primeSquareEulerFactor p /\ primeSquareEulerFactor p <= 1 := by
  by_cases hp : Nat.Prime p
  { have h := prime_defect_bounds hp
    simp only [primeSquareEulerFactor, ite_eq_left hp]
    exact And.intro (by linarith) (by linarith) }
  { simp only [primeSquareEulerFactor, ite_eq_right hp]
    norm_num }

private theorem euler_product_bounds (S : Finset Nat) :
    0 <= S.prod primeSquareEulerFactor /\ S.prod primeSquareEulerFactor <= 1 := by
  refine Finset.induction_on S ?_ ?_
  { simp }
  { intro p T hp hT
    rw [Finset.prod_insert hp]
    refine And.intro (mul_nonneg (euler_factor_bounds p).1 hT.1) ?_
    calc
      _ <= 1 * T.prod primeSquareEulerFactor :=
        mul_le_mul_of_nonneg_right (euler_factor_bounds p).2 hT.1
      _ <= 1 := by simpa using hT.2 }

private theorem euler_product_antitone {S T : Finset Nat}
    (hST : forall p, Membership.mem S p -> Membership.mem T p) :
    T.prod primeSquareEulerFactor <= S.prod primeSquareEulerFactor := by
  have hPart := Finset.prod_sdiff (f := primeSquareEulerFactor) hST
  rw [<- hPart]
  have hS := euler_product_bounds S
  have hRest := euler_product_bounds (T \ S)
  calc
    _ <= 1 * S.prod primeSquareEulerFactor :=
      mul_le_mul_of_nonneg_right hRest.2 hS.1
    _ = _ := one_mul _

private theorem cutoff_density_eq_prod (R : Nat) :
    primeSquareCutoffDensity R =
      (oddPrimeVertices R).prod primeSquareEulerFactor / 2 := by
  unfold primeSquareCutoffDensity Nat.primeSquareUnitDensity
  rw [Finset.prod_coe_sort (oddPrimeVertices R)
    (fun p : Nat => (1 : Real) - 1 / ((p * (p - 1) : Nat) : Real))]
  apply congrArg (fun x : Real => x / 2)
  apply Finset.prod_congr rfl
  intro p hp
  rw [primeSquareEulerFactor, ite_eq_left (odd_prime_props R p hp).1]

private theorem one_sub_sum_le_defect_product (S : Finset Nat) (a : Nat -> Real)
    (hB : forall p, Membership.mem S p -> 0 <= a p /\ a p <= 1) :
    1 - S.sum a <= S.prod (fun p => 1 - a p) := by
  classical
  revert hB
  refine Finset.induction_on S ?_ ?_
  { intro hB
    simp }
  { intro p T hp ih hB
    have hPB := hB p (Finset.mem_insert_self p T)
    have hTB : forall q, Membership.mem T q -> 0 <= a q /\ a q <= 1 := by
      intro q hq
      exact hB q (Finset.mem_insert_of_mem hq)
    have hI := ih hTB
    have hSum : 0 <= T.sum a := Finset.sum_nonneg (fun q hq => (hTB q hq).1)
    have hScale := mul_le_mul_of_nonneg_left hI (sub_nonneg.mpr hPB.2)
    have hPos := mul_nonneg hPB.1 hSum
    rw [Finset.sum_insert hp, Finset.prod_insert hp]
    nlinarith only [hScale, hPos] }

theorem primeSquareCutoffDensity_bounds (R : Nat) :
    (1 / 4 : Real) <= primeSquareCutoffDensity R /\
      primeSquareCutoffDensity R <= 1 / 2 := by
  classical
  let S := oddPrimeVertices R
  let a : Nat -> Real := fun p => 1 / ((p * (p - 1) : Nat) : Real)
  have hB : forall p, Membership.mem S p -> 0 <= a p /\ a p <= 1 := by
    intro p hp
    exact prime_defect_bounds (odd_prime_props R p hp).1
  have hSum : S.sum a <= (1 / 2 : Real) := by
    have hTail := reciprocal_square_tail_sum_le S 2 (max 2 R)
      (by norm_num) (le_max_left _ _) (fun p hp => by
        have hh := odd_prime_props R p hp
        exact And.intro (by omega) (le_trans hh.2.2 (le_max_right _ _)))
    calc
      _ = S.sum (fun p => 1 / ((p : Real) * ((p : Real) - 1))) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hh := (odd_prime_props R p hp).1.one_le
        dsimp only [a]
        rw [Nat.cast_mul, Nat.cast_sub hh, Nat.cast_one]
      _ <= _ := hTail
  have hLow := one_sub_sum_le_defect_product S a hB
  have hProd : S.prod (fun p => 1 - a p) = S.prod primeSquareEulerFactor := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [primeSquareEulerFactor, ite_eq_left (odd_prime_props R p hp).1]
  have hUpper := (euler_product_bounds S).2
  rw [hProd] at hLow
  rw [cutoff_density_eq_prod]
  change (1 / 4 : Real) <= S.prod primeSquareEulerFactor / 2 /\
    S.prod primeSquareEulerFactor / 2 <= 1 / 2
  exact And.intro (by linarith) (by linarith)

private theorem cutoff_density_antitone : Antitone primeSquareCutoffDensity := by
  intro R T hRT
  have hSub : forall p, Membership.mem (oddPrimeVertices R) p ->
      Membership.mem (oddPrimeVertices T) p := by
    intro p hp
    have hh := Finset.mem_erase.mp hp
    have hPrime := Nat.mem_primesBelow.mp hh.2
    exact Finset.mem_erase.mpr (And.intro hh.1
      (Nat.mem_primesBelow.mpr (And.intro (by omega) hPrime.2)))
  rw [cutoff_density_eq_prod, cutoff_density_eq_prod]
  exact div_le_div_of_nonneg_right (euler_product_antitone hSub) (by norm_num)

private theorem cutoff_density_bddBelow : BddBelow (Set.range primeSquareCutoffDensity) := by
  refine Exists.intro (1 / 4 : Real) ?_
  intro x hx
  choose R hR using hx
  rw [<- hR]
  exact (primeSquareCutoffDensity_bounds R).1

theorem artinPrimeSquareConstant_le_cutoff_density (R : Nat) :
    artinPrimeSquareConstant <= primeSquareCutoffDensity R :=
  csInf_le cutoff_density_bddBelow (Exists.intro R rfl)

theorem artinPrimeSquareConstant_bounds :
    (1 / 4 : Real) <= artinPrimeSquareConstant /\ artinPrimeSquareConstant <= 1 / 2 := by
  have hNonempty : (Set.range primeSquareCutoffDensity).Nonempty :=
    Exists.intro (primeSquareCutoffDensity 0) (Exists.intro 0 rfl)
  have hLow : (1 / 4 : Real) <= artinPrimeSquareConstant := by
    apply le_csInf hNonempty
    intro x hx
    choose R hR using hx
    rw [<- hR]
    exact (primeSquareCutoffDensity_bounds R).1
  exact And.intro hLow ((artinPrimeSquareConstant_le_cutoff_density 0).trans
    (primeSquareCutoffDensity_bounds 0).2)

theorem tendsto_primeSquareCutoffDensity :
    Tendsto primeSquareCutoffDensity atTop (nhds artinPrimeSquareConstant) := by
  exact tendsto_atTop_ciInf cutoff_density_antitone cutoff_density_bddBelow

private theorem range_product_eq_cutoff_density (R : Nat) (hR : 2 <= R) :
    (Finset.range (R + 1)).prod primeSquareEulerFactor = primeSquareCutoffDensity R := by
  classical
  let P := Nat.primesBelow (R + 1)
  have h2 : Membership.mem P 2 :=
    Nat.mem_primesBelow.mpr (And.intro (by omega) Nat.prime_two)
  have hInsert : Insert.insert 2 (oddPrimeVertices R) = P := Finset.insert_erase h2
  have hFilter : P.prod primeSquareEulerFactor =
      (Finset.range (R + 1)).prod primeSquareEulerFactor := by
    dsimp only [P, Nat.primesBelow]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    by_cases hPrime : Nat.Prime p <;> simp [primeSquareEulerFactor, hPrime]
  have hNot : Not (Membership.mem (oddPrimeVertices R) 2) := by
    simp [oddPrimeVertices]
  have hFactor : primeSquareEulerFactor 2 = (1 / 2 : Real) := by
    simp only [primeSquareEulerFactor, ite_eq_left Nat.prime_two]
    norm_num
  calc
    _ = P.prod primeSquareEulerFactor := hFilter.symm
    _ = (Insert.insert 2 (oddPrimeVertices R)).prod primeSquareEulerFactor :=
      congrArg (fun T : Finset Nat => T.prod primeSquareEulerFactor) hInsert.symm
    _ = primeSquareEulerFactor 2 * (oddPrimeVertices R).prod primeSquareEulerFactor :=
      Finset.prod_insert hNot
    _ = _ := by rw [hFactor, cutoff_density_eq_prod]; ring1

private theorem constant_le_finite_euler_product (S : Finset Nat) :
    artinPrimeSquareConstant <= S.prod primeSquareEulerFactor := by
  let R := max 2 (S.sup id)
  have hR : 2 <= R := le_max_left _ _
  have hSub : forall p, Membership.mem S p -> Membership.mem (Finset.range (R + 1)) p := by
    intro p hp
    have hMax : p <= S.sup id := Finset.le_sup (f := id) hp
    exact Finset.mem_range.mpr (by dsimp only [R]; omega)
  calc
    _ <= primeSquareCutoffDensity R := artinPrimeSquareConstant_le_cutoff_density R
    _ = (Finset.range (R + 1)).prod primeSquareEulerFactor :=
      (range_product_eq_cutoff_density R hR).symm
    _ <= _ := euler_product_antitone hSub

theorem artinPrimeSquareConstant_hasProd :
    HasProd primeSquareEulerFactor artinPrimeSquareConstant := by
  change Tendsto (fun S : Finset Nat => S.prod primeSquareEulerFactor)
    atTop (nhds artinPrimeSquareConstant)
  apply tendsto_order.mpr
  refine And.intro ?_ ?_
  { intro x hx
    exact Filter.Eventually.of_forall (fun S =>
      hx.trans_le (constant_le_finite_euler_product S)) }
  { intro x hx
    have hSmall := (tendsto_primeSquareCutoffDensity.eventually (gt_mem_nhds hx)).and
      (eventually_ge_atTop (2 : Nat))
    choose R hR using hSmall.exists
    apply Filter.eventually_atTop.mpr
    refine Exists.intro (Finset.range (R + 1)) ?_
    intro S hS
    calc
      _ <= (Finset.range (R + 1)).prod primeSquareEulerFactor :=
        euler_product_antitone hS
      _ = primeSquareCutoffDensity R := range_product_eq_cutoff_density R hR.2
      _ < x := hR.1 }

theorem artinPrimeSquareConstant_eq_tprod :
    artinPrimeSquareConstant = tprod primeSquareEulerFactor :=
  artinPrimeSquareConstant_hasProd.tprod_eq.symm

end PrimeFactorOscillations.QRH

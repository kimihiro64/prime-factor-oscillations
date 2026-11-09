/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHPrimeSquareFibres
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.FiberKernelGap
import PrimeFactorOscillations.Mathlib.Data.Nat.Prime.SquareUnitKernel

/-! # The complete finite signed estimate on actual prime vertices

The physical cutoff kernel retains the modulus-four mode and every odd
prime-square coordinate. The final comparison uses the uniform prime-fibre
bound and keeps the complete exceptional packet.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

open scoped Classical

noncomputable section
namespace PrimeFactorOscillations.QRH

def oddPrimeVertices (X : Nat) : Finset Nat :=
  (Nat.primesBelow (X + 1)).erase 2

def primeResidueSign (q : Nat) : Real :=
  if (q : ZMod 4) = 1 then 1 else -1

def primeSquareCutoffKernel (S : Finset Nat) (q r : Nat) : Real :=
  if (q : ZMod 4) = (r : ZMod 4) then 0 else
    if forall p : S, Not ((q : ZMod (p.val ^ 2)) = (r : ZMod (p.val ^ 2)))
      then 1 else 0

private def residueUnit (m q : Nat) : Units (ZMod m) :=
  if h : IsUnit (q : ZMod m) then h.unit else 1

private theorem residueUnit_val {m q : Nat} (h : IsUnit (q : ZMod m)) :
    (residueUnit m q).val = (q : ZMod m) := by
  simp only [residueUnit, dite_eq_left h]
  exact h.unit_spec

private def primeSquareUnitMap (S : Finset Nat) (q : Nat) :
    Prod Bool ((p : S) -> Units (ZMod (p.val ^ 2))) :=
  (ZMod.unitsFourEquivBool (residueUnit 4 q),
    fun p => residueUnit (p.val ^ 2) q)

private theorem prime_square_unit_of_ne {p q : Nat}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : Not (q = p)) :
    IsUnit (q : ZMod (p ^ 2)) := by
  apply (ZMod.isUnit_iff_coprime q (p ^ 2)).mpr
  exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hq hp).mpr hne)

private theorem regular_prime_units (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p)
    {q : Nat} (hq : Nat.Prime q) (hq2 : Not (q = 2))
    (hqS : Not (Membership.mem S q)) :
    IsUnit (q : ZMod 4) /\
      forall p : S, IsUnit (q : ZMod (p.val ^ 2)) := by
  refine And.intro ?_ ?_
  { simpa using prime_square_unit_of_ne Nat.prime_two hq hq2 }
  { intro p
    apply prime_square_unit_of_ne (hS p.val p.property) hq
    intro heq
    apply hqS
    rw [heq]
    exact p.property }

private theorem primeSquareUnitMap_bool_eq_iff (S : Finset Nat) {q r : Nat}
    (hq : IsUnit (q : ZMod 4)) (hr : IsUnit (r : ZMod 4)) :
    (primeSquareUnitMap S q).1 = (primeSquareUnitMap S r).1 <->
      (q : ZMod 4) = (r : ZMod 4) := by
  change ZMod.unitsFourEquivBool (residueUnit 4 q) =
      ZMod.unitsFourEquivBool (residueUnit 4 r) <-> _
  rw [ZMod.unitsFourEquivBool_eq_iff, residueUnit_val hq, residueUnit_val hr]

private theorem primeSquareUnitMap_kernel (S : Finset Nat) {q r : Nat}
    (hq4 : IsUnit (q : ZMod 4)) (hr4 : IsUnit (r : ZMod 4))
    (hq : forall p : S, IsUnit (q : ZMod (p.val ^ 2)))
    (hr : forall p : S, IsUnit (r : ZMod (p.val ^ 2))) :
    primeSquareCutoffKernel S q r =
      Nat.primeSquareUnitKernel (fun p : S => p.val)
        (primeSquareUnitMap S q) (primeSquareUnitMap S r) := by
  have h4 := primeSquareUnitMap_bool_eq_iff S hq4 hr4
  have hodd :
      (forall p : S, Not (((primeSquareUnitMap S q).2 p).val =
        ((primeSquareUnitMap S r).2 p).val)) <->
      (forall p : S, Not ((q : ZMod (p.val ^ 2)) = (r : ZMod (p.val ^ 2)))) := by
    apply forall_congr'
    intro p
    change Not ((residueUnit (p.val ^ 2) q).val =
      (residueUnit (p.val ^ 2) r).val) <-> _
    rw [residueUnit_val (hq p), residueUnit_val (hr p)]
  simp only [primeSquareCutoffKernel, Nat.primeSquareUnitKernel, h4, hodd]

private theorem primeSquareUnitMap_sign (S : Finset Nat) {q : Nat}
    (hq : IsUnit (q : ZMod 4)) :
    primeResidueSign q = Finset.binaryProductSign (primeSquareUnitMap S q) := by
  have h := ZMod.unitsFourSign_eq_binary (residueUnit 4 q)
  rw [ZMod.unitsFourSign, residueUnit_val hq] at h
  cases hb : ZMod.unitsFourEquivBool (residueUnit 4 q) <;>
    simpa [primeResidueSign, Finset.binaryProductSign, primeSquareUnitMap, hb] using h

private theorem primeResidueSign_sq (q : Nat) :
    (primeResidueSign q) ^ 2 = 1 := by
  simp only [primeResidueSign]
  split_ifs <;> norm_num

private theorem primeSquareCutoffKernel_abs_le_one (S : Finset Nat) (q r : Nat) :
    abs (primeSquareCutoffKernel S q r) <= 1 := by
  simp only [primeSquareCutoffKernel]
  split_ifs <;> norm_num

private theorem regular_units_of_mem (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p) (X : Nat)
    {q : Nat} (hq : Membership.mem ((oddPrimeVertices X).filter
      (fun q => Not (Membership.mem S q))) q) :
    IsUnit (q : ZMod 4) /\
      forall p : S, IsUnit (q : ZMod (p.val ^ 2)) := by
  have ht := Finset.mem_filter.mp hq
  have hp := Finset.mem_erase.mp ht.1
  exact regular_prime_units S hS (Nat.mem_primesBelow.mp hp.2).2 hp.1 ht.2

private theorem primeSquareUnitMap_cast_tuple_eq (S : Finset Nat) {q r : Nat}
    (hq4 : IsUnit (q : ZMod 4)) (hr4 : IsUnit (r : ZMod 4))
    (hq : forall p : S, IsUnit (q : ZMod (p.val ^ 2)))
    (hr : forall p : S, IsUnit (r : ZMod (p.val ^ 2)))
    (hmap : primeSquareUnitMap S q = primeSquareUnitMap S r) :
    (fun p : (insert 2 S : Finset Nat) => (q : ZMod (p.val ^ 2))) =
      (fun p : (insert 2 S : Finset Nat) => (r : ZMod (p.val ^ 2))) := by
  funext p
  cases Finset.mem_insert.mp p.property with
  | inl h2 =>
    have h4 := (primeSquareUnitMap_bool_eq_iff S hq4 hr4).mp
      (congrArg Prod.fst hmap)
    have hm : p.val ^ 2 = 4 := by rw [h2]; norm_num
    exact Eq.mp (congrArg (fun m : Nat =>
      (q : ZMod m) = (r : ZMod m)) hm.symm) h4
  | inr hp =>
    have hval := congrArg
      (fun x : Prod Bool ((p : S) -> Units (ZMod (p.val ^ 2))) =>
        (x.2 (Subtype.mk p.val hp)).val) hmap
    change (residueUnit (p.val ^ 2) q).val =
      (residueUnit (p.val ^ 2) r).val at hval
    rw [residueUnit_val (hq (Subtype.mk p.val hp)),
      residueUnit_val (hr (Subtype.mk p.val hp))] at hval
    exact hval

private theorem unit_map_fibre_le_raw_bound (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p) (X : Nat) (B : Real)
    (hRaw : forall u : (p : (insert 2 S : Finset Nat)) -> ZMod (p.val ^ 2),
      ((Finset.filter
        (fun q => (fun p : (insert 2 S : Finset Nat) =>
          (q : ZMod (p.val ^ 2))) = u)
        ((Nat.primesBelow (X + 1)).filter
          (fun q => Not (Membership.mem (insert 2 S : Finset Nat) q)))).card : Real) <= B)
    (u : Prod Bool ((p : S) -> Units (ZMod (p.val ^ 2)))) :
    ((Finset.filter (fun q => primeSquareUnitMap S q = u)
      ((oddPrimeVertices X).filter
        (fun q => Not (Membership.mem S q)))).card : Real) <= B := by
  let t := (oddPrimeVertices X).filter (fun q => Not (Membership.mem S q))
  let T := (Nat.primesBelow (X + 1)).filter
    (fun q => Not (Membership.mem (insert 2 S : Finset Nat) q))
  let k (q : Nat) : (p : (insert 2 S : Finset Nat)) -> ZMod (p.val ^ 2) :=
    fun p => (q : ZMod (p.val ^ 2))
  let F := t.filter (fun q => primeSquareUnitMap S q = u)
  have ht : t = T := by
    ext q
    simp [t, T, oddPrimeVertices, and_left_comm, and_comm]
  change (F.card : Real) <= B
  by_cases hF : F.Nonempty
  { choose a ha using hF
    have haT := (Finset.mem_filter.mp ha).1
    have haU := regular_units_of_mem S hS X haT
    have hsub : forall {q}, Membership.mem F q ->
        Membership.mem (T.filter (fun q => k q = k a)) q := by
      intro q hq
      have hqT := (Finset.mem_filter.mp hq).1
      have hqU := regular_units_of_mem S hS X hqT
      refine Finset.mem_filter.mpr (And.intro ?_ ?_)
      { rwa [ht] at hqT }
      { apply primeSquareUnitMap_cast_tuple_eq S hqU.1 haU.1 hqU.2 haU.2
        exact (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp ha).2.symm }
    have hcard := Finset.card_le_card @hsub
    exact le_trans (by exact_mod_cast hcard) (hRaw (k a)) }
  { have hzero : F.card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hF)
    rw [hzero]
    have hB := hRaw (fun p : (insert 2 S : Finset Nat) => (0 : ZMod (p.val ^ 2)))
    have h0 : (0 : Real) <= B := le_trans (Nat.cast_nonneg _) hB
    simpa only [Nat.cast_zero] using h0 }

private theorem oddPrimeVertices_count_upper (X : Nat) :
    (Nat.primesBelow (X + 1)).card <= (oddPrimeVertices X).card + 1 := by
  unfold oddPrimeVertices
  by_cases h2 : Membership.mem (Nat.primesBelow (X + 1)) 2
  { rw [Finset.card_erase_add_one h2] }
  { rw [Finset.erase_eq_of_notMem h2]
    exact Nat.le_succ _ }

private theorem regular_prime_exceptions_le (S : Finset Nat) (X : Nat) :
    ((oddPrimeVertices X) \
      ((oddPrimeVertices X).filter (fun q => Not (Membership.mem S q)))).card <= S.card := by
  apply Finset.card_le_card
  intro q hq
  have h := Finset.mem_sdiff.mp hq
  by_cases hqS : Membership.mem S q
  { exact hqS }
  { exact False.elim (h.2 (Finset.mem_filter.mpr (And.intro h.1 hqS))) }

/-- The complete finite two-mode comparison on actual odd primes. The
constant precedes every coordinate set, endpoint, tolerance and real weight.
The sparsity hypothesis counts all coordinate-prime exceptions; its full
three-rectangle contribution remains in the displayed allowance. -/
theorem exists_finite_prime_square_spectral_gap :
    exists C : Real, 0 < C /\
      forall (S : Finset Nat)
        (hS : forall p, Membership.mem S p -> Nat.Prime p)
        (h3 : forall p, Membership.mem S p -> 3 <= p)
        (X : Nat) (tau : Real),
        0 < (oddPrimeVertices X).card -> 0 <= tau ->
        (S.card : Real) <= tau ^ 2 * ((oddPrimeVertices X).card : Real) ->
        forall f : Nat -> Real,
          let N := (insert 2 S : Finset Nat).prod (fun p => p ^ 2)
          let M := (insert 2 S : Finset Nat).prod (fun p => p * (p - 1))
          let D := Nat.primeSquareUnitDensity (fun p : S => p.val)
          let n : Real := ((oddPrimeVertices X).card : Real)
          let delta := (1 + (M : Real) *
            (C * (X : Real) ^ (7 / 8 : Real) *
              (1 + Real.log (N : Real) + Real.log ((X : Real) + 2)) ^ 2)) / n
          let a := (oddPrimeVertices X).sum f / n
          let b := (oddPrimeVertices X).sum (fun q => primeResidueSign q * f q) / n
          let e := (oddPrimeVertices X).sum (fun q => (f q) ^ 2) / n
          abs (Finset.kernelBilinear (oddPrimeVertices X) (primeSquareCutoffKernel S) f f /
              n ^ 2 - D * (a ^ 2 - b ^ 2)) <=
            D / 5 * (e - a ^ 2 - b ^ 2) +
              (D * delta / 5 + (4 * D + 2) * tau + tau ^ 2) * e := by
  choose C hC hBound using exists_prime_square_tuple_fibre_count_upper
  refine Exists.intro C (And.intro hC ?_)
  intro S hS h3 X tau hnNat htau hsmall f
  -- Match the generic product theorem before enumerating the dependent carrier.
  letI : DecidableEq S := Classical.decEq S
  let (p : S) : NeZero (p.val ^ 2) :=
    NeZero.mk (pow_ne_zero 2 (hS p.val p.property).ne_zero)
  let s := oddPrimeVertices X
  let t := s.filter (fun q => Not (Membership.mem S q))
  let U : Finset (Prod Bool ((p : S) -> Units (ZMod (p.val ^ 2)))) := Finset.univ
  let N := (insert 2 S : Finset Nat).prod (fun p => p ^ 2)
  let M := (insert 2 S : Finset Nat).prod (fun p => p * (p - 1))
  let D := Nat.primeSquareUnitDensity (fun p : S => p.val)
  let n : Real := (s.card : Real)
  let E := C * (X : Real) ^ (7 / 8 : Real) *
    (1 + Real.log (N : Real) + Real.log ((X : Real) + 2)) ^ 2
  let delta := (1 + (M : Real) * E) / n
  have hn : 0 < n := by
    dsimp only [n, s]
    exact_mod_cast hnNat
  have h2S : Not (Membership.mem S 2) := by
    intro h2
    have h := h3 2 h2
    omega
  have hAll : forall p, Membership.mem (insert 2 S : Finset Nat) p -> Nat.Prime p := by
    intro p hp
    cases Finset.mem_insert.mp hp with
    | inl h => simpa only [h] using Nat.prime_two
    | inr h => exact hS p h
  have hCardOdd : Fintype.card ((p : S) -> Units (ZMod (p.val ^ 2))) =
      S.prod (fun p => p * (p - 1)) := by
    rw [<- Nat.card_eq_fintype_card, Nat.card_prime_sq_unit_tuples S hS,
      Nat.totient_prod_prime_sq S hS]
  have hM : U.card = M := by
    change Fintype.card (Prod Bool ((p : S) -> Units (ZMod (p.val ^ 2)))) = M
    rw [Fintype.card_prod, Fintype.card_bool, hCardOdd]
    simp [M, h2S]
  have hMNat : 0 < M := by
    rw [<- hM]
    exact Finset.card_pos.mpr Finset.univ_nonempty
  have hMpos : (0 : Real) < (M : Real) := by exact_mod_cast hMNat
  have hE : 0 <= E := by
    exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg X) _))
      (sq_nonneg _)
  have hdelta : 0 <= delta :=
    div_nonneg (add_nonneg (by norm_num) (mul_nonneg hMpos.le hE)) hn.le
  have hP : ((Nat.primesBelow (X + 1)).card : Real) <= n + 1 := by
    dsimp only [n, s]
    exact_mod_cast oddPrimeVertices_count_upper X
  have hcount : forall u, Membership.mem U u ->
      (U.card : Real) * ((t.filter (fun q => primeSquareUnitMap S q = u)).card : Real) <=
        (1 + delta) * (s.card : Real) := by
    intro u hu
    have hocc := unit_map_fibre_le_raw_bound S hS X
      (((Nat.primesBelow (X + 1)).card : Real) / (M : Real) + E)
      (by intro v; simpa only [M, E, N] using hBound (insert 2 S) hAll X v) u
    calc
      _ = (M : Real) * ((t.filter (fun q => primeSquareUnitMap S q = u)).card : Real) := by
        rw [hM]
      _ <= (M : Real) *
          (((Nat.primesBelow (X + 1)).card : Real) / (M : Real) + E) :=
        mul_le_mul_of_nonneg_left hocc hMpos.le
      _ = ((Nat.primesBelow (X + 1)).card : Real) + (M : Real) * E := by
        field_simp [ne_of_gt hMpos] <;> ring1
      _ <= n + 1 + (M : Real) * E := by linarith [hP]
      _ = (1 + delta) * (s.card : Real) := by
        change n + 1 + (M : Real) * E = (1 + (1 + (M : Real) * E) / n) * n
        field_simp [ne_of_gt hn] <;> ring1
  have hsmall' : ((s \ t).card : Real) <= tau ^ 2 * (s.card : Real) := by
    exact le_trans (by exact_mod_cast regular_prime_exceptions_le S X) hsmall
  have hD : 0 <= D :=
    (Nat.prime_square_unit_density_bounds (fun p : S => p.val)
      (fun p => hS p.val p.property) (fun p => h3 p.val p.property)).1.le
  have hident : forall q, Membership.mem t q -> forall r, Membership.mem t r ->
      primeSquareCutoffKernel S q r =
        Nat.primeSquareUnitKernel (fun p : S => p.val)
          (primeSquareUnitMap S q) (primeSquareUnitMap S r) := by
    intro q hq r hr
    have hqU := regular_units_of_mem S hS X hq
    have hrU := regular_units_of_mem S hS X hr
    exact primeSquareUnitMap_kernel S hqU.1 hrU.1 hqU.2 hrU.2
  have hsign : forall q, Membership.mem t q ->
      primeResidueSign q = Finset.binaryProductSign (primeSquareUnitMap S q) := by
    intro q hq
    exact primeSquareUnitMap_sign S (regular_units_of_mem S hS X hq).1
  have hT : forall {q}, Membership.mem t q -> Membership.mem s q := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hmap : forall q, Membership.mem t q ->
      Membership.mem U (primeSquareUnitMap S q) := by
    intro q hq
    simp only [U, Finset.mem_univ]
  have hmodel : forall w : Prod Bool ((p : S) -> Units (ZMod (p.val ^ 2))) -> Real,
      abs (Finset.kernelBilinear U
        (Nat.primeSquareUnitKernel (fun p : S => p.val)) w w -
        D * ((U.sum w) ^ 2 -
          (U.sum (fun u => Finset.binaryProductSign u * w u)) ^ 2)) <=
        D / 5 * ((U.card : Real) * U.sum (fun u => (w u) ^ 2) -
          (U.sum w) ^ 2 -
          (U.sum (fun u => Finset.binaryProductSign u * w u)) ^ 2) := by
    intro w
    simpa only [U, D] using Nat.prime_square_unit_binary_gap (fun p : S => p.val)
      (fun p => hS p.val p.property) (fun p => h3 p.val p.property) w
  have h := @Finset.kernel_fibre_fifth_gap_with_exceptions Nat
    (Prod Bool ((p : S) -> Units (ZMod (p.val ^ 2))))
    (inferInstance : DecidableEq (Prod Bool ((p : S) -> Units (ZMod (p.val ^ 2)))))
    (inferInstance : DecidableEq Nat)
    s t U (primeSquareUnitMap S) @hT hmap
    (primeSquareCutoffKernel S) (Nat.primeSquareUnitKernel (fun p : S => p.val))
    primeResidueSign Finset.binaryProductSign D delta tau hnNat hD hdelta htau
    hcount hsmall'
    (by intro q hq r hr; exact primeSquareCutoffKernel_abs_le_one S q r)
    hident (by intro q hq; exact primeResidueSign_sq q) hsign hmodel f
  simpa only [s, D, delta, n, M, E, N] using h

end PrimeFactorOscillations.QRH

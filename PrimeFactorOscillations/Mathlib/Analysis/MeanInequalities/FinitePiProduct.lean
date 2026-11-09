/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Fintype.BigOperators
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.RawProductSpectrum

/-! # Exact complete-product models for finite dependent tuples

The presentation retains an actual coordinate equivalence and the kernel
pointwise. Its construction uses only finite cardinalities, never an
assumed analytic estimate.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section
namespace Finset

universe u

def allDifferentPiKernel {I : Type u} (B : I -> Type u)
    (x y : (i : I) -> B i) : Real := by
  classical
  exact if forall i, Not (x i = y i) then 1 else 0

def completePiDensity {I : Type u} [Fintype I] (B : I -> Type u)
    [forall i, Fintype (B i)] : Real :=
  Finset.univ.prod (fun i => ((Fintype.card (B i) : Real) - 1) /
    (Fintype.card (B i) : Real))

private structure RawPiPresentation (A : Type u) (K : A -> A -> Real) (D : Real) where
  carrier : Type u
  enumeration : Fintype carrier
  kernel : carrier -> carrier -> Real
  equiv : Equiv A carrier
  raw : @IsRawCompleteProduct carrier (@Finset.univ carrier enumeration) kernel D
  agree : forall x y, K x y = kernel (equiv x) (equiv y)

private def RawPiPresentation.coordinate {A B : Type u} [Fintype A]
    [DecidableEq A] {K : B -> B -> Real} {D : Real}
    (r : RawPiPresentation B K D) (hA : 6 <= Fintype.card A) :
    RawPiPresentation (Prod A B) (rawCompleteCoordinateKernel K)
      (((Fintype.card A : Real) - 1) / (Fintype.card A : Real) * D) := by
  let : Fintype r.carrier := r.enumeration
  refine
    { carrier := Prod A r.carrier
      enumeration := inferInstance
      kernel := rawCompleteCoordinateKernel r.kernel
      equiv := Equiv.prodCongr (Equiv.refl A) r.equiv
      raw := ?_
      agree := ?_ }
  { have ha : 6 <= (Finset.univ : Finset A).card := by
      simpa only [card_univ] using hA
    have hs : (Finset.univ : Finset A).product (Finset.univ : Finset r.carrier) =
        (Finset.univ : Finset (Prod A r.carrier)) := Finset.univ_product_univ
    have h := IsRawCompleteProduct.coordinate Finset.univ Finset.univ r.kernel D ha r.raw
    simpa only [hs, card_univ] using h }
  { intro x y
    change (if x.1 = y.1 then 0 else K x.2 y.2) =
      (if x.1 = y.1 then 0 else r.kernel (r.equiv x.2) (r.equiv y.2))
    rw [r.agree x.2 y.2] }

private theorem completePi_raw_presentation {I : Type u} [Fintype I]
    (B : I -> Type u) [forall i, Fintype (B i)]
    (hB : forall i, 6 <= Fintype.card (B i)) :
    Nonempty (RawPiPresentation ((i : I) -> B i)
      (allDifferentPiKernel B) (completePiDensity B)) := by
  classical
  let P : (J : Type u) -> [Fintype J] -> Prop := fun J _ =>
    forall (C : J -> Type u) [forall j, Fintype (C j)],
      (forall j, 6 <= Fintype.card (C j)) ->
      Nonempty (RawPiPresentation ((j : J) -> C j)
        (allDifferentPiKernel C) (completePiDensity C))
  have hAll : P I := by
    apply Fintype.induction_empty_option (P := P) ?_ ?_ ?_ I
    { intro J J' instJ' e ih
      intro C instC hC
      let : Fintype J := Fintype.ofEquiv J' e.symm
      have hPull := ih (fun j => C (e j)) (fun j => hC (e j))
      cases hPull with
      | intro r =>
        let q := Equiv.piCongrLeft C e
        have hD : completePiDensity (fun j => C (e j)) = completePiDensity C := by
          exact Fintype.prod_equiv e _ _ (fun j => rfl)
        refine Nonempty.intro
          { carrier := r.carrier
            enumeration := r.enumeration
            kernel := r.kernel
            equiv := q.symm.trans r.equiv
            raw := ?_
            agree := ?_ }
        { simpa only [hD] using r.raw }
        { intro x y
          have hK : allDifferentPiKernel C x y =
              allDifferentPiKernel (fun j => C (e j)) (q.symm x) (q.symm y) := by
            have hIff : (forall j, Not (x j = y j)) <->
                (forall j, Not ((q.symm x) j = (q.symm y) j)) := by
              change (forall j, Not (x j = y j)) <->
                (forall j, Not (x (e j) = y (e j)))
              constructor
              { intro h j
                exact h (e j) }
              { intro h j
                exact Eq.mp (congrArg (fun k => Not (x k = y k))
                  (e.apply_symm_apply j)) (h (e.symm j)) }
            by_cases h : forall j, Not (x j = y j)
            { have hh := hIff.mp h
              simp [allDifferentPiKernel, h, hh] }
            { have hh : Not (forall j, Not ((q.symm x) j = (q.symm y) j)) :=
                fun hh => h (hIff.mpr hh)
              simp only [allDifferentPiKernel, h, hh, ite_false] }
          exact hK.trans (r.agree (q.symm x) (q.symm y)) } }
    { intro C instC hC
      let e : Equiv ((j : PEmpty.{u + 1}) -> C j) PUnit.{u + 1} :=
        { toFun := fun _ => PUnit.unit
          invFun := fun _ j => PEmpty.elim j
          left_inv := fun x => funext (fun j => PEmpty.elim j)
          right_inv := fun x => Subsingleton.elim _ _ }
      refine Nonempty.intro
        { carrier := PUnit.{u + 1}
          enumeration := inferInstance
          kernel := fun _ _ => 1
          equiv := e
          raw := ?_
          agree := ?_ }
      { simpa [completePiDensity] using
          (IsRawCompleteProduct.singleton (PUnit.unit : PUnit.{u + 1})) }
      { intro x y
        simp [allDifferentPiKernel] } }
    { intro J instJ ih C instC hC
      have hTail := ih (fun j => C (some j)) (fun j => hC (some j))
      cases hTail with
      | intro r =>
        let q := @Equiv.piOptionEquivProd _ C
        let next := r.coordinate (hC none)
        have hD : ((Fintype.card (C none) : Real) - 1) /
            (Fintype.card (C none) : Real) *
              completePiDensity (fun j => C (some j)) = completePiDensity C := by
          simp only [completePiDensity, Fintype.prod_option]
        refine Nonempty.intro
          { carrier := next.carrier
            enumeration := next.enumeration
            kernel := next.kernel
            equiv := q.trans next.equiv
            raw := ?_
            agree := ?_ }
        { simpa only [hD] using next.raw }
        { intro x y
          have hK : allDifferentPiKernel C x y =
              rawCompleteCoordinateKernel (allDifferentPiKernel (fun j => C (some j)))
                (q x) (q y) := by
            by_cases hxy : x none = y none
            { have hn : Not (forall i, Not (x i = y i)) := by
                intro h
                exact h none hxy
              simp [allDifferentPiKernel, rawCompleteCoordinateKernel, q,
                Equiv.piOptionEquivProd_apply, hxy, hn] }
            { simp [allDifferentPiKernel, rawCompleteCoordinateKernel, q,
                Equiv.piOptionEquivProd_apply, Option.forall, hxy] }
          exact hK.trans (next.agree (q x) (q y)) } }
  exact hAll B hB

/-- The raw density is positive and at most one, uniformly in the finite family. -/
theorem completePiDensity_bounds {I : Type u} [Fintype I]
    (B : I -> Type u) [forall i, Fintype (B i)]
    (hB : forall i, 6 <= Fintype.card (B i)) :
    0 < completePiDensity B /\ completePiDensity B <= 1 := by
  have hRep := completePi_raw_presentation B hB
  cases hRep with
  | intro r =>
    choose P hP hD hOne hScale using r.raw.normalized_witness
    exact And.intro hD hOne


private theorem sum_univ_reindex {A B : Type u} [Fintype A] [Fintype B]
    (e : Equiv A B) (f : A -> Real) :
    (Finset.univ : Finset A).sum f =
      (Finset.univ : Finset B).sum (fun b => f (e.symm b)) := by
  simpa only [e.symm_apply_apply] using
    e.sum_comp (fun b => f (e.symm b))

private theorem kernelBilinear_univ_reindex {A B : Type u}
    [Fintype A] [Fintype B] (e : Equiv A B)
    (K : A -> A -> Real) (L : B -> B -> Real)
    (hKL : forall x y, K x y = L (e x) (e y)) (f : A -> Real) :
    kernelBilinear Finset.univ K f f =
      kernelBilinear Finset.univ L (fun b => f (e.symm b)) (fun b => f (e.symm b)) := by
  unfold kernelBilinear
  rw [sum_univ_reindex e]
  apply Finset.sum_congr rfl
  intro x hx
  rw [sum_univ_reindex e]
  apply Finset.sum_congr rfl
  intro y hy
  rw [hKL]
  simp only [e.apply_symm_apply]

/-- The full signed binary kernel on actual dependent tuples, with the
constant and parity modes retained in counting normalization. -/
theorem kernelBilinear_complete_pi_binary_gap {I : Type u} [Fintype I]
    (B : I -> Type u) [forall i, Fintype (B i)]
    (hB : forall i, 6 <= Fintype.card (B i))
    (f : Prod Bool ((i : I) -> B i) -> Real) :
    abs (kernelBilinear Finset.univ (rawCompleteCoordinateKernel (allDifferentPiKernel B)) f f -
      completePiDensity B / 2 *
        (((Finset.univ : Finset (Prod Bool ((i : I) -> B i))).sum f) ^ 2 -
          ((Finset.univ : Finset (Prod Bool ((i : I) -> B i))).sum
            (fun x => binaryProductSign x * f x)) ^ 2)) <=
      (completePiDensity B / 2) / 5 *
        (((Finset.univ : Finset (Prod Bool ((i : I) -> B i))).card : Real) *
            (Finset.univ : Finset (Prod Bool ((i : I) -> B i))).sum (fun x => (f x) ^ 2) -
          ((Finset.univ : Finset (Prod Bool ((i : I) -> B i))).sum f) ^ 2 -
          ((Finset.univ : Finset (Prod Bool ((i : I) -> B i))).sum
            (fun x => binaryProductSign x * f x)) ^ 2) := by
  classical
  have hRep := completePi_raw_presentation B hB
  cases hRep with
  | intro r =>
    let : Fintype r.carrier := r.enumeration
    let e : Equiv (Prod Bool ((i : I) -> B i)) (Prod Bool r.carrier) :=
      Equiv.prodCongr (Equiv.refl Bool) r.equiv
    let g (z : Prod Bool r.carrier) : Real := f (e.symm z)
    have hKernel : forall x y,
        rawCompleteCoordinateKernel (allDifferentPiKernel B) x y =
          rawCompleteCoordinateKernel r.kernel (e x) (e y) := by
      intro x y
      change (if x.1 = y.1 then 0 else allDifferentPiKernel B x.2 y.2) =
        (if x.1 = y.1 then 0 else r.kernel (r.equiv x.2) (r.equiv y.2))
      rw [r.agree x.2 y.2]
    have hQ := kernelBilinear_univ_reindex e
      (rawCompleteCoordinateKernel (allDifferentPiKernel B))
      (rawCompleteCoordinateKernel r.kernel) hKernel f
    have hSum : (Finset.univ : Finset (Prod Bool ((i : I) -> B i))).sum f =
        (Finset.univ : Finset (Prod Bool r.carrier)).sum g :=
      sum_univ_reindex e f
    have hEnergy : (Finset.univ : Finset (Prod Bool ((i : I) -> B i))).sum
        (fun x => (f x) ^ 2) =
        (Finset.univ : Finset (Prod Bool r.carrier)).sum (fun z => (g z) ^ 2) :=
      sum_univ_reindex e (fun x => (f x) ^ 2)
    have hSign (z : Prod Bool r.carrier) :
        binaryProductSign (e.symm z) = binaryProductSign z := by
      rfl
    have hSigma : (Finset.univ : Finset (Prod Bool ((i : I) -> B i))).sum
        (fun x => binaryProductSign x * f x) =
        (Finset.univ : Finset (Prod Bool r.carrier)).sum
          (fun z => binaryProductSign z * g z) := by
      rw [sum_univ_reindex e]
      apply Finset.sum_congr rfl
      intro z hz
      change binaryProductSign (e.symm z) * f (e.symm z) =
        binaryProductSign z * f (e.symm z)
      rw [hSign]
    have hCard : (Finset.univ : Finset (Prod Bool ((i : I) -> B i))).card =
        (Finset.univ : Finset (Prod Bool r.carrier)).card := by
      simpa only [Finset.card_univ] using Fintype.card_congr e
    have hBool : (Insert.insert false (Singleton.singleton true) : Finset Bool) =
        Finset.univ := by decide
    have hSupport : binaryProductSupport (Finset.univ : Finset r.carrier) =
        (Finset.univ : Finset (Prod Bool r.carrier)) := by
      have h : (Finset.univ : Finset Bool).product (Finset.univ : Finset r.carrier) =
          (Finset.univ : Finset (Prod Bool r.carrier)) := Finset.univ_product_univ
      simpa only [binaryProductSupport, hBool] using h
    have hGap := r.raw.binary_model_gap g
    rw [hSupport] at hGap
    change abs (kernelBilinear Finset.univ (rawCompleteCoordinateKernel r.kernel) g g -
      completePiDensity B / 2 *
        ((Finset.univ.sum g) ^ 2 -
          (Finset.univ.sum (fun z => binaryProductSign z * g z)) ^ 2)) <=
      (completePiDensity B / 2) / 5 *
        (((Finset.univ : Finset (Prod Bool r.carrier)).card : Real) *
            Finset.univ.sum (fun z => (g z) ^ 2) -
          (Finset.univ.sum g) ^ 2 -
          (Finset.univ.sum (fun z => binaryProductSign z * g z)) ^ 2) at hGap
    rw [<- hQ, <- hSum, <- hEnergy, <- hSigma, <- hCard] at hGap
    exact hGap

end Finset

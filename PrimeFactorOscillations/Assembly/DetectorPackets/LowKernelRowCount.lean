/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.QuadraticSieve.SquareParts
import PrimeFactorOscillations.Assembly.DetectorPackets.RadicalCoupledPacket

/-!
# LowKernelRowCount

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
# Uniform count of the low squarefree-kernel rows

All finite sets of actual FreeRow elements are included. The six generators
of each principal ideal are charged explicitly. No numerical testing or
zero-density hypothesis is used.
-/

set_option maxHeartbeats 1200000

noncomputable section
namespace OAI.SevenEighths.LowKernelRowCount

open scoped Classical
open HeckeFamily HeckeInverseAmplification QuadraticSquarefreeKernel ProbeHighRowFamily
local notation "O" => HeckeFamily.O

theorem span_fiber_card (R : Finset FreeRow) (I : Ideal O) :
    (R.filter fun u => (Ideal.span {u.val}:Ideal O)=I).card<=6 := by
  letI : Fintype (Units O) := Fintype.ofEquiv
    OAI.PrimaryIdealUnitReindex.unitCoordinates
    OAI.PrimaryIdealUnitReindex.unitCoordinateEquiv.symm
  have h6 : Fintype.card (Units O)=6 := by
    simpa only [Nat.card_eq_fintype_card] using OAI.PrimaryIdealUnitReindex.card_units_eq_six
  let T := R.filter fun u => (Ideal.span {u.val}:Ideal O)=I
  change T.card<=6
  by_cases hT : T.Nonempty
  . let r := Classical.choose hT
    have hr := Classical.choose_spec hT
    have ha (u : T) : Associated u.val.val r.val := by
      apply Ideal.span_singleton_eq_span_singleton.mp
      exact (Finset.mem_filter.mp u.property).2.trans (Finset.mem_filter.mp hr).2.symm
    let f (u : T) : Units O := Classical.choose (ha u)
    have hf : Function.Injective f := by
      intro u v huv
      have hu : u.val.val*(f u:O)=r.val := Classical.choose_spec (ha u)
      have hv : v.val.val*(f v:O)=r.val := Classical.choose_spec (ha v)
      rw [huv] at hu
      have he := congrArg (fun t : O => t*((Inv.inv (f v):Units O):O)) (hu.trans hv.symm)
      apply Subtype.ext
      apply Subtype.ext
      simpa [mul_assoc] using he
    have hc := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe, h6] using hc
  . have he : T=Finset.empty := Finset.not_nonempty_iff_eq_empty.mp hT
    rw [he]
    exact Nat.zero_le 6

theorem ideal_low_count (T : Finset (Ideal O)) (U K : Real) (hU : 1<=U) (hK : 1<=K)
    (hT : forall I, Membership.mem T I -> Not (I=0) /\
      (I.absNorm:Real)<=U /\ ((squarefreePart I).absNorm:Real)<=K) :
    (T.card:Real)<=16384*K*Real.sqrt U := by
  let A := T.image squarePart
  let B := T.image squarefreePart
  have hUn : 0<=U := zero_le_one.trans hU
  have hsqrt := Real.sq_sqrt hUn
  have hroot := Real.sqrt_nonneg U
  have hroot1 : 1<=Real.sqrt U := by nlinarith
  have hparts (I : Ideal O) (hI : Membership.mem T I) :
      Not (squarePart I=0) /\ ((squarePart I).absNorm:Real)<=Real.sqrt U := by
    have hh := hT I hI
    have he := squarePart_sq_mul_squarefreePart I
    have hA : Not (squarePart I=0) := by
      intro h
      apply hh.1
      rw [<-he, h, zero_pow (by decide), zero_mul]
    have hB : Not (squarefreePart I=0) := (squarefree_squarefreePart I).ne_zero
    have hBN : (1:Real)<=((squarefreePart I).absNorm:Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hB)
    have heN : ((squarePart I).absNorm:Real)^2*((squarefreePart I).absNorm:Real)=I.absNorm := by
      exact_mod_cast (show (squarePart I).absNorm^2*(squarefreePart I).absNorm=I.absNorm by
        simpa only [map_mul, map_pow] using congrArg Ideal.absNorm he)
    refine And.intro hA ?_
    have hAn : (0:Real)<=((squarePart I).absNorm:Real) := Nat.cast_nonneg _
    have hsq : ((squarePart I).absNorm:Real)^2<=U := by
      have hm := mul_le_mul_of_nonneg_left hBN (sq_nonneg ((squarePart I).absNorm:Real))
      nlinarith [hh.2.1]
    nlinarith
  have hAc : (A.card:Real)<=128*Real.sqrt U := by
    apply OAI.DescentFiberCost.finite_ideal_count_real A (Real.sqrt U) hroot1
    . intro J hJ
      choose I hI he using Finset.mem_image.mp hJ
      simpa [<-he] using (hparts I hI).1
    . intro J hJ
      choose I hI he using Finset.mem_image.mp hJ
      simpa only [<-he] using (hparts I hI).2
  have hBc : (B.card:Real)<=128*K := by
    apply OAI.DescentFiberCost.finite_ideal_count_real B K hK
    . intro J hJ
      choose I hI he using Finset.mem_image.mp hJ
      simpa [<-he] using (squarefree_squarefreePart I).ne_zero
    . intro J hJ
      choose I hI he using Finset.mem_image.mp hJ
      simpa only [<-he] using (hT I hI).2.2
  have hcard : T.card<=(A.product B).card := by
    apply Finset.card_le_card_of_injOn (fun I => (squarePart I, squarefreePart I))
    . intro I hI
      exact Finset.mem_product.mpr (And.intro
        (Finset.mem_image_of_mem squarePart hI) (Finset.mem_image_of_mem squarefreePart hI))
    . intro I hI J hJ he
      have hh := congrArg (fun p : Prod (Ideal O) (Ideal O) => p.1^2*p.2) he
      simpa only [squarePart_sq_mul_squarefreePart] using hh
  have hcardR : (T.card:Real)<=(A.card:Real)*(B.card:Real) := by
    exact_mod_cast (hcard.trans_eq (Finset.card_product A B))
  calc
    _ <= (128*Real.sqrt U)*(128*K) :=
      hcardR.trans (mul_le_mul hAc hBc (Nat.cast_nonneg _) (by positivity))
    _ = _ := by ring

theorem row_low_count (R : Finset FreeRow) (U K : Real) (hU : 1<=U) (hK : 1<=K)
    (hR : forall u, Membership.mem R u -> rowNorm u<=U /\
      ((squarefreePart (Ideal.span {u.val}:Ideal O)).absNorm:Real)<=K) :
    (R.card:Real)<=98304*K*Real.sqrt U := by
  let T := R.image fun u => (Ideal.span {u.val}:Ideal O)
  have hTc := ideal_low_count T U K hU hK (by
    intro I hI
    choose u hu he using Finset.mem_image.mp hI
    rw [<-he]
    exact And.intro (Ideal.span_singleton_eq_bot.not.mpr u.property.1) (hR u hu))
  have hmap : forall u, Membership.mem R u ->
      Membership.mem T (Ideal.span {u.val}:Ideal O) :=
    fun u hu => Finset.mem_image_of_mem _ hu
  have hfiber (I : Ideal O) (_hI : Membership.mem T I) :
      (R.filter fun u => (Ideal.span {u.val}:Ideal O)=I).card<=6 := span_fiber_card R I
  have hc := Finset.card_le_mul_card_image_of_maps_to hmap 6 hfiber
  have hcR : (R.card:Real)<=6*(T.card:Real) := by exact_mod_cast hc
  calc
    _ <= 6*(16384*K*Real.sqrt U) := hcR.trans (mul_le_mul_of_nonneg_left hTc (by norm_num))
    _ = _ := by ring

end OAI.SevenEighths.LowKernelRowCount


/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import OAI.NumberTheory.DirichletL.PrimeRows.Ramified

/-!
# Ramified Euler bounds in the extended region

Controls every supported ramified row and the complete finite ramified product.
The subpower bound retains the source exclusions and is uniform in the contour
heights throughout the stated region.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.RamifiedEulerContinuation
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeEuler
open OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.ConcretePrimeRowBridge
open OAI.SevenEighths.ProbePrimePower
local notation "O" => OAI.ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (HasQuotient.Quotient O (Ideal.span {p} : Ideal O)) = 2))

include hc in
theorem rowMarkedTerm_extended_region (eta a rho x w z : Complex)
    (heta : norm eta <= 1) (ha : norm a <= 1) (hrho : rho ^ 6 = 1)
    (hx : (3 / 4 : Real) <= x.re) (hw : (19 / 20 : Real) <= w.re)
    (hz : (33 / 200 : Real) <= z.re)
    (j e l k m : Nat) (ht : 0 < e + 3 * l) (hk : k <= 1) :
    norm (rowMarkedTerm p hp hg eta a
      ((Ideal.absNorm (Ideal.span {p}) : Complex) ^ (-x))
      ((Ideal.absNorm (Ideal.span {p}) : Complex) ^ (-w))
      (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j e l k m) <= 2 := by
  rw [<- sourceRowTerm_pos p hp hg eta a rho x w z j e l k m (by omega)]
  apply (sourceRowTerm_norm_le p hp hg hc eta a rho x w z
    heta ha hrho j e l k m ht hk).trans
  have hP : Prime (Ideal.span {p} : Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ1 : (1 : Real) <= Ideal.absNorm (Ideal.span {p}) := by
    have hh := OAI.SmoothMobiusCorrection.prime_norm_two_le
      (Subtype.mk (Ideal.span {p}) hP)
    change 2 <= Ideal.absNorm (Ideal.span {p}) at hh
    have hn : (1 : Nat) <= Ideal.absNorm (Ideal.span {p}) := by omega
    exact_mod_cast hn
  have he :
      (1 / 2 - x.re) * (e : Real) + (2 - 3 * x.re) * (l : Real) +
        (1 / 2 - w.re) * (k : Real) - 6 * z.re * (m : Real) <= 0 := by
    have h1 := mul_nonpos_of_nonpos_of_nonneg
      (show 1 / 2 - x.re <= 0 by linarith) (Nat.cast_nonneg e : (0 : Real) <= _)
    have h2 := mul_nonpos_of_nonpos_of_nonneg
      (show 2 - 3 * x.re <= 0 by linarith) (Nat.cast_nonneg l : (0 : Real) <= _)
    have h3 := mul_nonpos_of_nonpos_of_nonneg
      (show 1 / 2 - w.re <= 0 by linarith) (Nat.cast_nonneg k : (0 : Real) <= _)
    have h4 : 0 <= 6 * z.re * (m : Real) := by positivity
    linarith
  have hh := Real.rpow_le_one_of_one_le_of_nonpos hQ1 he
  linarith

theorem evenRatio_extended_half (Q : Real) (hQ : 4 <= Q) (a x z : Complex)
    (ha : norm a <= 1) (hx : (3 / 4 : Real) <= x.re)
    (hz : (33 / 200 : Real) <= z.re) :
    norm (evenRatio Q a ((Q : Complex) ^ (-x)) (coordV Q z)) <= 1 / 2 := by
  rw [evenRatio_eq_coordR Q (by linarith)]
  have hA : norm (a ^ 2) <= 1 := by
    rw [pow_two, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg a) ha).trans ha
  apply (coordR_norm_le Q (by linarith) (a ^ 2) x z hA).trans
  exact rpow_le_half Q _ hQ (by linarith)

include hc in
theorem rowBaseFinite_extended_region (eta a rho x w z : Complex)
    (hQ : (4 : Real) <= Ideal.absNorm (Ideal.span {p}))
    (heta : norm eta <= 1) (ha : norm a <= 1) (hrho : rho ^ 6 = 1)
    (hx : (3 / 4 : Real) <= x.re) (hw : (19 / 20 : Real) <= w.re)
    (hz : (33 / 200 : Real) <= z.re)
    (j e l : Nat) (ht : 0 < e + 3 * l) :
    norm (rowBaseFinite p hp hg eta a
      ((Ideal.absNorm (Ideal.span {p}) : Complex) ^ (-x))
      ((Ideal.absNorm (Ideal.span {p}) : Complex) ^ (-w))
      (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j e l) <= 16 := by
  classical
  have hv := ProbeLocal.inv_one_sub_norm_le_two _
    (second_region_V_half _ hQ z hz)
  have ht' (k : Fin 2) (m : Nat) :=
    rowMarkedTerm_extended_region p hp hg hc eta a rho x w z
      heta ha hrho hx hw hz j e l k.val m ht (by omega)
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ <= Finset.univ.sum (fun _k : Fin 2 => (8 : Real)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_add_le _ _).trans
      have hab := (norm_add_le _ _).trans (add_le_add (ht' k 0) (ht' k 1))
      have hd : norm (rowMarkedTerm p hp hg eta a
          ((Ideal.absNorm (Ideal.span {p}) : Complex) ^ (-x))
          ((Ideal.absNorm (Ideal.span {p}) : Complex) ^ (-w))
          (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j e l k.val 2 /
            (1 - coordV (Ideal.absNorm (Ideal.span {p})) z)) <= 4 := by
        rw [div_eq_mul_inv, norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by norm_num)).trans_eq
          (by norm_num)
      linarith
    _ = _ := by norm_num

include hc in
theorem rowClosedMarked_extended_region (eta a rho x w z : Complex)
    (hQ : (4 : Real) <= Ideal.absNorm (Ideal.span {p}))
    (heta : norm eta <= 1) (ha : norm a <= 1) (hrho : rho ^ 6 = 1)
    (hx : (3 / 4 : Real) <= x.re) (hw : (19 / 20 : Real) <= w.re)
    (hz : (33 / 200 : Real) <= z.re) (j : Nat) :
    norm (rowClosedMarked p hp hg eta a
      ((Ideal.absNorm (Ideal.span {p}) : Complex) ^ (-x))
      ((Ideal.absNorm (Ideal.span {p}) : Complex) ^ (-w))
      (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j) <= 128 := by
  have h02 := rowBaseFinite_extended_region p hp hg hc eta a rho x w z
    hQ heta ha hrho hx hw hz j 0 2 (by norm_num)
  have h10 := rowBaseFinite_extended_region p hp hg hc eta a rho x w z
    hQ heta ha hrho hx hw hz j 1 0 (by norm_num)
  have h01 := rowBaseFinite_extended_region p hp hg hc eta a rho x w z
    hQ heta ha hrho hx hw hz j 0 1 (by norm_num)
  have h11 := rowBaseFinite_extended_region p hp hg hc eta a rho x w z
    hQ heta ha hrho hx hw hz j 1 1 (by norm_num)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _
    (evenRatio_extended_half _ hQ a x z ha hx hz)
  simp only [Complex.ofReal_natCast] at hr
  unfold rowClosedMarked
  rw [div_eq_mul_inv, norm_mul]
  apply (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11))
    (norm_nonneg _)).trans
  nlinarith

include hc in
theorem ramifiedClosed_extended_bound (eta a rho x w z : Complex)
    (hQ : (4 : Real) <= Ideal.absNorm (Ideal.span {p}))
    (heta : norm eta <= 1) (ha : norm a <= 1) (hrho : rho ^ 6 = 1)
    (hx : (3 / 4 : Real) <= x.re) (hw : (19 / 20 : Real) <= w.re)
    (hz : (33 / 200 : Real) <= z.re) (j : Nat) :
    norm (ramifiedClosed p hp hg eta a rho x w z j) <= 193 := by
  have hb := rowClosedMarked_extended_region p hp hg hc eta a rho x w z
    hQ heta ha hrho hx hw hz j
  have hv := second_region_V_half _ hQ z hz
  have hs := norm_sub_le (1 : Complex) (coordV (Ideal.absNorm (Ideal.span {p})) z)
  simp only [norm_one] at hs
  unfold ramifiedClosed
  apply (norm_add_le _ _).trans
  rw [norm_one, norm_mul]
  have hm := mul_le_mul
    (show norm (1 - coordV (Ideal.absNorm (Ideal.span {p})) z) <= 3 / 2 by linarith)
    hb (norm_nonneg _) (by norm_num : (0 : Real) <= 3 / 2)
  linarith


open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.ProbeRow
open OAI.SevenEighths.ProbeHighRowFamily OAI.SevenEighths.HeckeInverseAmplification
open OAI.CanonicalQuadraticSieve OAI.CanonicalRowCompletion
abbrev SourcePrime := OAI.SmoothMobiusCorrection.PrimeIdeal

theorem ramifiedCorrection_extended_bound
    (eta : OAI.SevenEighths.HeckeFamily.Character) (u : FreeRow) (P : SourcePrime)
    (hs : Supported P.val) (hQ : (4 : Real) <= P.val.absNorm) (x w z : Complex)
    (hx : (3 / 4 : Real) <= x.re) (hw : (19 / 20 : Real) <= w.re)
    (hz : (33 / 200 : Real) <= z.re) :
    norm (ramifiedCorrection eta u P hs x w z) <= 193 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p} = P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := by rw [hspan]; exact hs
  have hg := supported_prime_data p hp hsp
  have ha : norm (actualACube eta p) <= 1 := by
    have h := actualAPhase_norm_le_one eta p
    rw [<- actualACube_sq, norm_pow] at h
    nlinarith [norm_nonneg (actualACube eta p)]
  have hQp : (4 : Real) <= Ideal.absNorm (Ideal.span {p}) := by rw [hspan]; exact hQ
  exact ramifiedClosed_extended_bound p hp hg.1 hg.2 _ _ _ x w z
    hQp (targetMonoid_norm_le_one eta p) ha
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2
      (unitPart_coprime u p hp)) hx hw hz _

private theorem finite_product_norm_bound {I : Type*} (F : Finset I)
    (f : I -> Complex) (C : Real) (hC : 0 <= C) :
    (forall i, Membership.mem F i -> norm (f i) <= C) ->
      norm (F.prod f) <= C ^ F.card := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro hf
    simp
  | @insert i F hi ih =>
    intro hf
    have hfi := hf i (Finset.mem_insert_self i F)
    have hF := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hcard : (insert i F).card = F.card + 1 := by simp [hi]
    rw [Finset.prod_insert hi, norm_mul, hcard, pow_succ]
    exact (mul_le_mul hfi hF (norm_nonneg _) hC).trans_eq (mul_comm _ _)

theorem ramified_product_extended_subpower (eps : Real) (heps : 0 < eps) :
    Exists (fun C : Real => 0 < C /\
      forall (S : Finset (Ideal O)) (hS : SourceExclusions S)
        (eta : OAI.SevenEighths.HeckeFamily.Character) (u : FreeRow) (x w z : Complex),
        (3 / 4 : Real) <= x.re -> (19 / 20 : Real) <= w.re ->
          (33 / 200 : Real) <= z.re ->
            norm ((ramifiedPrimes S u).attach.prod (fun P =>
              ramifiedCorrection eta u P.val
                (outside_prime_supported S hS.bad P.val
                  (Finset.mem_filter.mp P.property).2) x w z)) <=
              C * ((Ideal.span {u.val} : Ideal O).absNorm : Real) ^ eps) := by
  classical
  have hex := OAI.SevenEighths.HeckeDeletionBounds.constant_pow_primeSupport_bound
    193 eps (by norm_num) heps
  let C : Real := Classical.choose hex
  have hC := Classical.choose_spec hex
  refine Exists.intro C (And.intro hC.1 ?_)
  intro S hS eta u x w z hx hw hz
  have hcard : (ramifiedPrimes S u).card <=
      (OAI.IdealMobiusDivisorSum.primeSupport (Ideal.span {u.val})).card := by
    rw [<- OAI.SevenEighths.HeckeDeletionBounds.primeSet_card]
    exact Finset.card_filter_le _ _
  calc
    _ <= (193 : Real) ^ (ramifiedPrimes S u).card := by
      have h := finite_product_norm_bound (ramifiedPrimes S u).attach
        (fun P => ramifiedCorrection eta u P.val
          (outside_prime_supported S hS.bad P.val
            (Finset.mem_filter.mp P.property).2) x w z) 193 (by norm_num)
        (fun P _ => ramifiedCorrection_extended_bound eta u P.val _
          (by exact_mod_cast (hS.tail.norm_four P.val
            (Finset.mem_filter.mp P.property).2)) x w z hx hw hz)
      simpa only [Finset.card_attach] using h
    _ <= (193 : Real) ^
        (OAI.IdealMobiusDivisorSum.primeSupport (Ideal.span {u.val})).card := by
      have h := Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : Real) <= 193)
        (by exact_mod_cast hcard :
          ((ramifiedPrimes S u).card : Real) <=
            ((OAI.IdealMobiusDivisorSum.primeSupport (Ideal.span {u.val})).card : Real))
      simpa only [Real.rpow_natCast] using h
    _ <= _ := hC.2 _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
end PrimeFactorOscillations.RamifiedEulerContinuation

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PrimeFactorOscillations.Assembly.FiniteFieldNativeArithmeticAgreement

/-!
# Sharp energy of finite native agreement families

The physical diagonal is one. Every prime pair and real coefficient is fixed
before the independent field scale tends to infinity. The sharp lower bound
retains both squareclass kernels and every signed coefficient product.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter FiniteFieldIntegerWindowTransfer

def nativeAgreementKernel {I : Type*} (n h : I -> Nat) (i j : I) : Real := by
  classical
  exact if i = j then 1 else nativeAgreementRate (n i) (h i) (n j) (h j)

def nativeAgreementForm {I : Type*} [Fintype I]
    (n h : I -> Nat) (c : I -> Real) : Real :=
  Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
    c i * c j * nativeAgreementKernel n h i j))

def nativeAgreementMassForm {I : Type*} [Fintype I]
    (n h : I -> Nat) (c : I -> Real) (U : Nat) : Real :=
  Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
    c i * c j *
      (nativeAgreementMass (n i) (h i) (n j) (h j)
          (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))))

theorem native_agreement_form_lower_bound {I : Type*} [Fintype I]
    (n h : I -> Nat) (hn : forall i, 0 < n i) (hh : forall i, 0 < h i)
    (c : I -> Real) :
    (3 / 8 : Real) * ((Finset.univ.sum c) ^ 2 +
      Finset.univ.sum (fun i => (c i) ^ 2)) <= nativeAgreementForm n h c := by
  classical
  have hpositive (a : I -> Nat) (ha : forall i, 0 < a i) :
      0 <= Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        if IsSquare (a i * a j) then c i * c j else 0)) := by
    have htrans (a b d : Nat) (hb : 0 < b)
        (hab : IsSquare (a * b)) (hbd : IsSquare (b * d)) : IsSquare (a * d) := by
      have hsq : IsSquare ((b * b) * (a * d)) := by
        convert hab.mul hbd using 1
        ring
      let r := Classical.choose hsq
      have hr : (b * b) * (a * d) = r * r := Classical.choose_spec hsq
      have hdiv : Dvd.dvd (b ^ 2) (r ^ 2) := by
        refine Exists.intro (a * d) ?_
        simpa only [pow_two] using hr.symm
      have hbr : Dvd.dvd b r :=
        (Nat.pow_dvd_pow_iff (by decide : Not ((2 : Nat) = 0))).mp hdiv
      let t := Classical.choose hbr
      have ht : r = b * t := Classical.choose_spec hbr
      refine Exists.intro t ?_
      have hmul : (b * b) * (a * d) = (b * b) * (t * t) := by
        rw [hr, ht]
        ring
      exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hb hb) hmul
    let s : Setoid I :=
      { r := fun i j => IsSquare (a i * a j)
        iseqv :=
          { refl := fun i => IsSquare.mul_self (a i)
            symm := fun hij => by simpa only [mul_comm] using hij
            trans := fun hij hjk => htrans _ _ _ (ha _) hij hjk } }
    let : Fintype (Quotient s) := Quotient.fintype s
    let f : I -> Quotient s := Quotient.mk s
    have hrel (i j : I) : (f j = f i) <-> IsSquare (a i * a j) := by
      change (Quotient.mk s j = Quotient.mk s i) <-> IsSquare (a i * a j)
      rw [Quotient.eq]
      change IsSquare (a j * a i) <-> IsSquare (a i * a j)
      rw [mul_comm]
    have hid :
        Finset.univ.sum (fun q : Quotient s =>
          (Finset.univ.sum (fun i => if f i = q then c i else 0)) ^ 2) =
        Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
          if IsSquare (a i * a j) then c i * c j else 0)) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [ite_mul, mul_ite, zero_mul, mul_zero]
      rw [Fintype.sum_ite_eq (f i)]
      simp only [hrel, mul_comm]
    rw [<- hid]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let L : I -> I -> Prop := fun i j => IsSquare ((h i * n i) * (h j * n j))
  let V : I -> I -> Prop := fun i j =>
    IsSquare ((h i * (n i + h i)) * (h j * (n j + h j)))
  have hK (i j : I) :
      nativeAgreementKernel n h i j =
        (3 : Real) / 8 + (if L i j then 1 else 0) / 8 +
          (if V i j then 1 else 0) / 8 + (if i = j then 3 / 8 else 0) := by
    by_cases hij : i = j
    . subst j
      have hl : L i i := IsSquare.mul_self _
      have hv : V i i := IsSquare.mul_self _
      norm_num [nativeAgreementKernel, hl, hv]
    . have hl : h i * h j * n i * n j = (h i * n i) * (h j * n j) := by ring
      have hv : h i * h j * (n i + h i) * (n j + h j) =
          (h i * (n i + h i)) * (h j * (n j + h j)) := by ring
      simp only [nativeAgreementKernel, ite_eq_right hij]
      rw [native_agreement_rate_eq_square_test _ _ _ _ (hn i) (hh i) (hn j) (hh j),
        hl, hv]
      change (3 + (if L i j then (1 : Real) else 0) +
        (if V i j then (1 : Real) else 0)) / 8 = _
      ring
  let SL : Real := Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
    if L i j then c i * c j else 0))
  let SV : Real := Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
    if V i j then c i * c j else 0))
  have hSL : 0 <= SL := hpositive (fun i => h i * n i)
    (fun i => Nat.mul_pos (hh i) (hn i))
  have hSV : 0 <= SV := hpositive (fun i => h i * (n i + h i))
    (fun i => Nat.mul_pos (hh i) (by have hi := hn i; omega))
  have hsum_mul (b : Real) (f : I -> I -> Real) :
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => b * f i j)) =
        b * Finset.univ.sum (fun i => Finset.univ.sum (fun j => f i j)) := by
    simp only [<- Finset.mul_sum]
  have hbase : Finset.univ.sum (fun i => Finset.univ.sum (fun j => c i * c j)) =
      (Finset.univ.sum c) ^ 2 := by
    simp only [<- Finset.mul_sum, <- Finset.sum_mul, pow_two]
  have hdiag :
      Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        if i = j then (c i) ^ 2 else 0)) =
        Finset.univ.sum (fun i => (c i) ^ 2) := by
    simp only [Fintype.sum_ite_eq]
  have hparts : nativeAgreementForm n h c =
      (3 / 8 : Real) * (Finset.univ.sum c) ^ 2 +
        (3 / 8 : Real) * Finset.univ.sum (fun i => (c i) ^ 2) +
        (1 / 8 : Real) * SL + (1 / 8 : Real) * SV := by
    calc
      nativeAgreementForm n h c =
          Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
            (3 / 8 : Real) * (c i * c j) +
            (3 / 8 : Real) * (if i = j then (c i) ^ 2 else 0) +
            (1 / 8 : Real) * (if L i j then c i * c j else 0) +
            (1 / 8 : Real) * (if V i j then c i * c j else 0))) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hK]
        by_cases hij : i = j
        . subst j
          simp only [ite_true]
          split_ifs <;> ring
        . simp only [ite_eq_right hij]
          split_ifs <;> ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, hsum_mul, hbase, hdiag]
        rfl
  linarith only [hparts, hSL, hSV]

theorem native_agreement_mass_form_tendsto {I : Type*} [Fintype I]
    (n h : I -> Nat)
    (hn : forall i, Nat.Prime (n i)) (hnh : forall i, Nat.Prime (n i + h i))
    (hh : forall i, 0 < h i)
    (hinj : Function.Injective (fun i => Prod.mk (n i) (h i))) (c : I -> Real) :
    Tendsto (nativeAgreementMassForm n h c) atTop (nhds (nativeAgreementForm n h c)) := by
  classical
  unfold nativeAgreementMassForm nativeAgreementForm
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  apply tendsto_const_nhds.mul
  by_cases hij : i = j
  . subst j
    have hm := precise_core_tendsto_atTop.eventually
      eventually_reciprocal_square_band_positive
    have heq : Filter.Eventually (fun U : Nat =>
        nativeAgreementMass (n i) (h i) (n i) (h i)
            (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) = 1)
        atTop := by
      filter_upwards [hm] with U hM
      have hp : 0 < reciprocalBand (preciseCore U + 1)
          (preciseCore U * preciseCore U + 1) :=
        (show (0 : Real) < Real.log 2 / 2 by positivity).trans_le hM
      simp only [nativeAgreementMass, ite_true]
      change reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) = 1
      exact div_self (ne_of_gt hp)
    simpa only [nativeAgreementKernel, ite_true] using
      (tendsto_const_nhds.congr' (heq.mono (fun _ hU => hU.symm)) :
        Tendsto (fun U : Nat =>
          nativeAgreementMass (n i) (h i) (n i) (h i)
              (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
            reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
          atTop (nhds (1 : Real)))
  . have hneq : Not (And (n i = n j) (h i = h j)) := by
      intro heq
      exact hij (hinj (Prod.ext heq.1 heq.2))
    simpa only [nativeAgreementKernel, ite_eq_right hij] using
      native_agreement_ratio_tendsto_rate (n i) (h i) (n j) (h j)
        (hn i) (hnh i) (hn j) (hnh j) (hh i) (hh j) hneq

private def sharpN : Fin 4 -> Nat := ![11, 11, 41, 41]

private def sharpH : Fin 4 -> Nat := ![32, 128, 2, 98]

private def sharpC : Fin 4 -> Real := ![1, -1, -1, 1]

private theorem sharp_n_prime : forall i, Nat.Prime (sharpN i) := by
  intro i
  fin_cases i <;> norm_num [sharpN]

private theorem sharp_q_prime : forall i, Nat.Prime (sharpN i + sharpH i) := by
  intro i
  fin_cases i <;> norm_num [sharpN, sharpH]

private theorem sharp_h_pos : forall i, 0 < sharpH i := by
  intro i
  fin_cases i <;> norm_num [sharpH]

private theorem sharp_injective :
    Function.Injective (fun i => Prod.mk (sharpN i) (sharpH i)) := by
  intro i j heq
  fin_cases i <;> fin_cases j
  all_goals first | rfl | norm_num [sharpN, sharpH] at heq

set_option maxRecDepth 4096 in
private theorem sharp_kernel (i j : Fin 4) :
    nativeAgreementKernel sharpN sharpH i j =
      if i = j then (1 : Real) else
        if i + j = 3 then (3 / 8 : Real) else 1 / 2 := by
  have hnonsq (N r : Nat) (hlo : r * r < N)
      (hhi : N < (r + 1) * (r + 1)) : Not (IsSquare N) := by
    intro hs
    choose t ht using hs
    by_cases htr : t <= r
    . have hm : t * t <= r * r := Nat.mul_le_mul htr htr
      omega
    . have hrt : r + 1 <= t := by omega
      have hm : (r + 1) * (r + 1) <= t * t := Nat.mul_le_mul hrt hrt
      omega
  have hs0 : IsSquare (495616 : Nat) :=
    Exists.intro 704 (by norm_num)
  have hs1 : Not (IsSquare (24481792 : Nat)) :=
    hnonsq 24481792 4947 (by norm_num) (by norm_num)
  have hs2 : Not (IsSquare (28864 : Nat)) :=
    hnonsq 28864 169 (by norm_num) (by norm_num)
  have hs3 : IsSquare (118336 : Nat) :=
    Exists.intro 344 (by norm_num)
  have hs4 : Not (IsSquare (1414336 : Nat)) :=
    hnonsq 1414336 1189 (by norm_num) (by norm_num)
  have hs5 : Not (IsSquare (18743872 : Nat)) :=
    hnonsq 18743872 4329 (by norm_num) (by norm_num)
  have hs6 : Not (IsSquare (115456 : Nat)) :=
    hnonsq 115456 339 (by norm_num) (by norm_num)
  have hs7 : Not (IsSquare (1530112 : Nat)) :=
    hnonsq 1530112 1236 (by norm_num) (by norm_num)
  have hs8 : Not (IsSquare (5657344 : Nat)) :=
    hnonsq 5657344 2378 (by norm_num) (by norm_num)
  have hs9 : IsSquare (242362624 : Nat) :=
    Exists.intro 15568 (by norm_num)
  have hs10 : IsSquare (329476 : Nat) :=
    Exists.intro 574 (by norm_num)
  have hs11 : Not (IsSquare (1171492 : Nat)) :=
    hnonsq 1171492 1082 (by norm_num) (by norm_num)
  classical
  by_cases hij : i = j
  . simp only [nativeAgreementKernel, ite_eq_left hij]
  . simp only [nativeAgreementKernel, ite_eq_right hij]
    rw [native_agreement_rate_eq_square_test _ _ _ _ (sharp_n_prime i).pos (sharp_h_pos i) (sharp_n_prime j).pos (sharp_h_pos j)]
    fin_cases i <;> fin_cases j
    all_goals
      first
      | exact False.elim (hij rfl)
      | norm_num [sharpN, sharpH, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11]

theorem native_agreement_three_eighths_sharp :
    exists n h : Fin 4 -> Nat, exists c : Fin 4 -> Real,
      (forall i, Nat.Prime (n i)) /\ (forall i, Nat.Prime (n i + h i)) /\
      (forall i, 0 < h i) /\ Function.Injective (fun i => Prod.mk (n i) (h i)) /\
      Finset.univ.sum c = 0 /\ Finset.univ.sum (fun i => (c i) ^ 2) = 4 /\
      nativeAgreementForm n h c = 3 / 2 := by
  refine Exists.intro sharpN (Exists.intro sharpH (Exists.intro sharpC
    (And.intro sharp_n_prime (And.intro sharp_q_prime
      (And.intro sharp_h_pos (And.intro sharp_injective ?_))))))
  constructor
  . norm_num [sharpC, Fin.sum_univ_succ]
  constructor
  . norm_num [sharpC, Fin.sum_univ_succ]
  . unfold nativeAgreementForm
    simp_rw [sharp_kernel]
    norm_num [sharpC, Fin.sum_univ_succ]

end PrimeFactorOscillations.FiniteFieldIntegerSignature

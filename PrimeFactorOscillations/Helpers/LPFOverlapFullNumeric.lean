/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFOverlapTargetNumeric
import PrimeFactorOscillations.Helpers.LPFPrimePrefixNumeric

/-!
# Complete numerical prime-target overlap

The row residue error has coefficient 524288 uniformly in every modulus and
all row parameters. The complete squarefree expansion keeps every weight.
Both cofactor branches give coefficient 1048576 at exponent fifteen sixteenths.
The full off-diagonal moment retains the factor 6^q, the Euler moment factor
72*log(q+2), and the complete modulus and truncated-product error. Nonunit
inputs are accounted for by the upper comparison with the unit principal mean.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_weighted_prime_row_residue_numeric :
    forall {I : Type*} (X y m D : Nat) (J : Finset I)
        (modulus : I -> Nat) (w : I -> Real)
        (a : (d : I) -> Units (ZMod (modulus d))),
        (forall d, Membership.mem J d -> And (1 <= modulus d) (modulus d <= D)) ->
        (forall d, Membership.mem J d -> 0 <= w d) ->
        Finset.sum (Nat.largestPrimeFactorRow X y m) (fun (r : Nat) =>
          Finset.sum J (fun d => if (r : ZMod (modulus d)) = (a d : ZMod (modulus d)) then w d else 0)) <=
        ((Nat.largestPrimeFactorRow X y m).card : Real) *
          Finset.sum J (fun d => w d / ((modulus d).totient : Real)) +
        524288 * (X : Real) ^ (15 / 16 : Real) *
          (1 + Real.log D + Real.log ((X : Real) + 2)) ^ 2 * Finset.sum J w := by
  classical
  intro I X y m D J modulus w a hJ hw
  let R := Nat.largestPrimeFactorRow X y m
  let E := 524288 * (X : Real) ^ (15 / 16 : Real) *
    (1 + Real.log D + Real.log ((X : Real) + 2)) ^ 2
  have hCount : forall d, Membership.mem J d ->
      (((R.filter (fun (r : Nat) => (r : ZMod (modulus d)) = (a d : ZMod (modulus d)))).card : Real) <=
        (R.card : Real) / ((modulus d).totient : Real) + E) := by
    intro d hd
    have hdLow := (hJ d hd).1
    have hdD := (hJ d hd).2
    letI : NeZero (modulus d) := NeZero.mk (by omega)
    let Ed := 524288 * (X : Real) ^ (15 / 16 : Real) *
      (1 + Real.log (modulus d) + Real.log ((X : Real) + 2)) ^ 2
    have hEd : 0 <= Ed := by
      dsimp [Ed]
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg X) _))
        (sq_nonneg _)
    have hResidue := DirichletCharacter.abs_residue_count_sub_unit_mean_le
      R (fun (r : Nat) => (r : ZMod (modulus d))) (a d) Ed hEd
      (fun chi hchi => QRH.lpf_prime_row_numeric chi hchi X y m)
    have hUnitCard : ((R.filter (fun (r : Nat) => IsUnit (r : ZMod (modulus d)))).card : Real) <=
        (R.card : Real) := Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
    have hUnitMean := div_le_div_of_nonneg_right hUnitCard (Nat.cast_nonneg (modulus d).totient)
    have hLogd : 0 <= Real.log (modulus d) := Real.log_nonneg (by exact_mod_cast hdLow)
    have hLogdD : Real.log (modulus d) <= Real.log D :=
      Real.log_le_log (by exact_mod_cast (show 0 < modulus d by omega)) (by exact_mod_cast hdD)
    have hLogX : 0 <= Real.log ((X : Real) + 2) := Real.log_nonneg (by
      have h : (0 : Real) <= (X : Real) := Nat.cast_nonneg X
      linarith)
    have hSq : (1 + Real.log (modulus d) + Real.log ((X : Real) + 2)) ^ 2 <=
        (1 + Real.log D + Real.log ((X : Real) + 2)) ^ 2 := by nlinarith
    have hEdE : Ed <= E := mul_le_mul_of_nonneg_left hSq
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg X) _))
    have hUpper := (le_abs_self _).trans hResidue
    linarith
  have hReorder :
      Finset.sum R (fun (r : Nat) => Finset.sum J
        (fun d => if (r : ZMod (modulus d)) = (a d : ZMod (modulus d)) then w d else 0)) =
      Finset.sum J (fun d => w d *
        ((R.filter (fun (r : Nat) => (r : ZMod (modulus d)) = (a d : ZMod (modulus d)))).card : Real)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    rw [<- Finset.sum_filter]
    simp [mul_comm]
  change Finset.sum R (fun (r : Nat) => Finset.sum J
      (fun d => if (r : ZMod (modulus d)) = (a d : ZMod (modulus d)) then w d else 0)) <=
    (R.card : Real) * Finset.sum J (fun d => w d / ((modulus d).totient : Real)) + E * Finset.sum J w
  rw [hReorder]
  calc
    _ <= Finset.sum J (fun d => w d * ((R.card : Real) / ((modulus d).totient : Real) + E)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hCount d hd) (hw d hd)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring

theorem lpf_squarefree_prime_row_moment_numeric :
    forall (X y m : Nat) (P : Finset Nat) (q : Nat)
        (a : (A : Finset Nat) -> Units (ZMod (Finset.prod A (fun p => p)))),
        (forall p, Membership.mem P p -> 3 <= p) ->
        Finset.sum (Nat.largestPrimeFactorRow X y m) (fun (r : Nat) =>
          Finset.sum P.powerset (fun A =>
            if (r : ZMod (Finset.prod A (fun p => p))) =
                (a A : ZMod (Finset.prod A (fun p => p))) then
              Finset.prod A (fun p => singularFactor p ^ q - 1) else 0)) <=
        ((Nat.largestPrimeFactorRow X y m).card : Real) *
          Finset.sum P.powerset (fun A =>
            Finset.prod A (fun p => singularFactor p ^ q - 1) /
              ((Finset.prod A (fun p => p)).totient : Real)) +
        524288 * (X : Real) ^ (15 / 16 : Real) *
          (1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
            Real.log ((X : Real) + 2)) ^ 2 *
            (Finset.prod P singularFactor) ^ q := by
  classical
  intro X y m P q a hP
  have hMod : forall A, Membership.mem P.powerset A ->
      And (1 <= Finset.prod A (fun p => p))
        (Finset.prod A (fun p => p) <= Finset.prod P (fun p => p)) := by
    intro A hA
    have hSub := Finset.mem_powerset.mp hA
    refine And.intro ?_ ?_
    next =>
      apply Finset.one_le_prod
      intro p hp
      have h := hP p (hSub hp)
      omega
    next =>
      apply Finset.prod_le_prod_of_subset_of_one_le hSub
      intro p hp hNot
      have h := hP p hp
      omega
  have hWeight : forall A, Membership.mem P.powerset A ->
      0 <= Finset.prod A (fun p => singularFactor p ^ q - 1) := by
    intro A hA
    apply Finset.prod_nonneg
    intro p hp
    exact singular_moment_weight_nonneg p q (hP p (Finset.mem_powerset.mp hA hp))
  have h := lpf_weighted_prime_row_residue_numeric X y m (Finset.prod P (fun p => p)) P.powerset
    (fun A => Finset.prod A (fun p => p))
    (fun A => Finset.prod A (fun p => singularFactor p ^ q - 1)) a hMod hWeight
  rw [singular_moment_total_weight] at h
  exact h

theorem lpf_prime_row_singular_packet_power_numeric :
    forall (X y m N : Nat) (P : Finset Nat) (q : Nat)
        (a : (A : Finset Nat) -> Units (ZMod (Finset.prod A (fun p => p)))),
        5 <= q ->
        (forall p, Membership.mem P p -> And (Nat.Prime p) (And (5 <= p) (p < N))) ->
        Finset.sum (Nat.largestPrimeFactorRow X y m) (fun (r : Nat) =>
          Finset.sum P.powerset (fun A =>
            if (r : ZMod (Finset.prod A (fun p => p))) =
                (a A : ZMod (Finset.prod A (fun p => p))) then
              Finset.prod A (fun p => singularFactor p ^ q - 1) else 0)) <=
        ((Nat.largestPrimeFactorRow X y m).card : Real) *
          (72 * Real.log ((q : Real) + 2)) ^ q +
        524288 * (X : Real) ^ (15 / 16 : Real) *
          (1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
            Real.log ((X : Real) + 2)) ^ 2 * (Finset.prod P singularFactor) ^ q := by
  classical
  intro X y m N P q a hq hP
  have hPacket := lpf_squarefree_prime_row_moment_numeric X y m P q a
    (fun p hp => by have h := (hP p hp).2.1; omega)
  have hMain : Finset.sum P.powerset (fun A =>
      Finset.prod A (fun p => singularFactor p ^ q - 1) /
        ((Finset.prod A (fun p => p)).totient : Real)) <=
      (72 * Real.log ((q : Real) + 2)) ^ q := by
    rw [singular_moment_principal_sum_eq P q (fun p hp => (hP p hp).1)]
    exact lpf_singular_euler_moment_numeric P N q hq hP
  have hScaled := mul_le_mul_of_nonneg_left hMain
    (Nat.cast_nonneg (Nat.largestPrimeFactorRow X y m).card)
  exact hPacket.trans (_root_.add_le_add hScaled (le_refl _))

theorem lpf_primeTarget_truncated_branch_power_numeric :
    forall (X y m r n q : Nat) (P S : Finset Nat),
        Nat.Prime r -> 3 <= r -> 5 <= q -> Or (n = 1) (n = 3) ->
        (forall p, Membership.mem P p -> And (Nat.Prime p) (And (3 < p) (p < r))) ->
        S <= Nat.largestPrimeFactorRow X y m ->
        (forall s, Membership.mem S s ->
          And (Nat.Prime s) (And (3 <= s) (primeTargetCofactor s = n))) ->
        Finset.sum S (fun s =>
          (Finset.prod (P.filter (fun p => Dvd.dvd p
            ((primeTargetSum r - primeTargetSum s) +
              (primeTargetSum s - primeTargetSum r)))) singularFactor) ^ q) <=
          ((Nat.largestPrimeFactorRow X y m).card : Real) *
            (72 * Real.log ((q : Real) + 2)) ^ q +
          524288 * (X : Real) ^ (15 / 16 : Real) *
            (1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
              Real.log ((X : Real) + 2)) ^ 2 * (Finset.prod P singularFactor) ^ q := by
  classical
  intro X y m r n q P S hr hr3 hq hn hP hS hPrimes
  have hResidue : forall A : Finset Nat, A <= P ->
      exists a : Units (ZMod (Finset.prod A (fun p => p))), forall s : Nat,
        Nat.Prime s -> 3 <= s -> primeTargetCofactor s = n ->
        (Dvd.dvd (Finset.prod A (fun p => p))
          ((primeTargetSum r - primeTargetSum s) + (primeTargetSum s - primeTargetSum r)) <->
          (s : ZMod (Finset.prod A (fun p => p))) = (a : ZMod (Finset.prod A (fun p => p)))) := by
    intro A hA
    exact exists_primeTarget_branch_residue r n _ hr hr3 hn
      (primeTarget_modulus_coprime r A hr (fun p hp => hP p (hA hp)))
  let a (A : Finset Nat) : Units (ZMod (Finset.prod A (fun p => p))) :=
    if hA : A <= P then Classical.choose (hResidue A hA) else 1
  have ha : forall A : Finset Nat, A <= P -> forall s : Nat,
      Nat.Prime s -> 3 <= s -> primeTargetCofactor s = n ->
      (Dvd.dvd (Finset.prod A (fun p => p))
        ((primeTargetSum r - primeTargetSum s) + (primeTargetSum s - primeTargetSum r)) <->
        (s : ZMod (Finset.prod A (fun p => p))) = (a A : ZMod (Finset.prod A (fun p => p)))) := by
    intro A hA s hs hs3 hsn
    dsimp [a]
    rw [dite_eq_left hA]
    exact Classical.choose_spec (hResidue A hA) s hs hs3 hsn
  let packet (s : Nat) : Real := Finset.sum P.powerset (fun A =>
    if (s : ZMod (Finset.prod A (fun p => p))) =
        (a A : ZMod (Finset.prod A (fun p => p))) then
      Finset.prod A (fun p => singularFactor p ^ q - 1) else 0)
  have hWeight : forall A : Finset Nat, A <= P ->
      0 <= Finset.prod A (fun p => singularFactor p ^ q - 1) := by
    intro A hA
    apply Finset.prod_nonneg
    intro p hp
    exact singular_moment_weight_nonneg p q (by have h := (hP p (hA hp)).2.1; omega)
  have hExact : forall s, Membership.mem S s ->
      (Finset.prod (P.filter (fun p => Dvd.dvd p
        ((primeTargetSum r - primeTargetSum s) +
          (primeTargetSum s - primeTargetSum r)))) singularFactor) ^ q = packet s := by
    intro s hs
    rw [truncated_singular_moment_expansion]
    apply Finset.sum_congr rfl
    intro A hA
    have hAP := Finset.mem_powerset.mp hA
    have hEquiv := (singular_prime_product_dvd_iff A
      ((primeTargetSum r - primeTargetSum s) + (primeTargetSum s - primeTargetSum r))
      (fun p hp => (hP p (hAP hp)).1)).symm.trans
      (ha A hAP s (hPrimes s hs).1 (hPrimes s hs).2.1 (hPrimes s hs).2.2)
    simp only [hEquiv]
  have hPacketNonneg : forall s : Nat, 0 <= packet s := by
    intro s
    apply Finset.sum_nonneg
    intro A hA
    split_ifs
    next => exact hWeight A (Finset.mem_powerset.mp hA)
    next => exact le_refl 0
  have hCount : Finset.sum S packet <=
      Finset.sum (Nat.largestPrimeFactorRow X y m) packet :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun s _ _ => hPacketNonneg s)
  calc
    _ = Finset.sum S packet := Finset.sum_congr rfl hExact
    _ <= Finset.sum (Nat.largestPrimeFactorRow X y m) packet := hCount
    _ <= _ := lpf_prime_row_singular_packet_power_numeric X y m r P q a hq
      (fun p hp => And.intro (hP p hp).1
        (And.intro (by
          have h := hP p hp
          have h4 : Not (p = 4) := by intro he; subst p; norm_num at h
          omega) (hP p hp).2.2))

theorem lpf_primeTarget_truncated_moment_power_numeric :
    forall (X y m r q : Nat) (P S : Finset Nat),
        Nat.Prime r -> 3 <= r -> 5 <= q ->
        (forall p, Membership.mem P p -> And (Nat.Prime p) (And (3 < p) (p < r))) ->
        S <= Nat.largestPrimeFactorRow X y m ->
        (forall s, Membership.mem S s -> And (Nat.Prime s) (3 <= s)) ->
        Finset.sum S (fun s =>
          (Finset.prod (P.filter (fun p => Dvd.dvd p
            ((primeTargetSum r - primeTargetSum s) +
              (primeTargetSum s - primeTargetSum r)))) singularFactor) ^ q) <=
          2 * ((Nat.largestPrimeFactorRow X y m).card : Real) *
            (72 * Real.log ((q : Real) + 2)) ^ q +
          1048576 * (X : Real) ^ (15 / 16 : Real) *
            (1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
              Real.log ((X : Real) + 2)) ^ 2 * (Finset.prod P singularFactor) ^ q := by
  classical
  intro X y m r q P S hr hr3 hq hP hS hPrimes
  let F (s : Nat) : Real :=
    (Finset.prod (P.filter (fun p => Dvd.dvd p
      ((primeTargetSum r - primeTargetSum s) +
        (primeTargetSum s - primeTargetSum r)))) singularFactor) ^ q
  have hOne := lpf_primeTarget_truncated_branch_power_numeric X y m r 1 q P (S.filter (fun s => primeTargetCofactor s = 1))
    hr hr3 hq (Or.inl rfl) hP
    (fun s hs => hS (Finset.mem_filter.mp hs).1)
    (fun s hs => And.intro (hPrimes s (Finset.mem_filter.mp hs).1).1
      (And.intro (hPrimes s (Finset.mem_filter.mp hs).1).2 (Finset.mem_filter.mp hs).2))
  have hThree := lpf_primeTarget_truncated_branch_power_numeric X y m r 3 q P (S.filter (fun s => primeTargetCofactor s = 3))
    hr hr3 hq (Or.inr rfl) hP
    (fun s hs => hS (Finset.mem_filter.mp hs).1)
    (fun s hs => And.intro (hPrimes s (Finset.mem_filter.mp hs).1).1
      (And.intro (hPrimes s (Finset.mem_filter.mp hs).1).2 (Finset.mem_filter.mp hs).2))
  have hSplit : Finset.sum S F =
      Finset.sum (S.filter (fun s => primeTargetCofactor s = 1)) F +
      Finset.sum (S.filter (fun s => primeTargetCofactor s = 3)) F := by
    rw [Finset.sum_filter, Finset.sum_filter, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hBranch : Or (primeTargetCofactor s = 1) (primeTargetCofactor s = 3) := by
      unfold primeTargetCofactor
      split_ifs <;> simp
    rcases hBranch with h | h <;> simp [F, h]
  change Finset.sum S F <= _
  rw [hSplit]
  have h := _root_.add_le_add hOne hThree
  dsimp [F]
  nlinarith

private theorem lpf_overlap_numeric_singularFactor_nonneg (p : Nat) (hp : 3 <= p) :
    0 <= singularFactor p := by
  have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast hp
  exact add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith only [hpR]))

private theorem lpf_overlap_numeric_pow_mono (a b : Real) (ha : 0 <= a) (hab : a <= b) (q : Nat) :
    a ^ q <= b ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (pow_nonneg (ha.trans hab) q)


theorem lpf_primeTarget_full_finite_power_numeric :
    forall M r q : Nat,
      4 <= M -> 4 <= Real.log (M : Real) ->
      3 <= Real.log (Real.log (M : Real)) ->
      Membership.mem (nextPrimeWindow M) r -> 5 <= q ->
      Finset.sum ((nextPrimeWindow M).erase r) (fun s =>
        singularDivisorProduct (primeTargetSeparation r s) ^ q) <=
      (6 : Real) ^ q *
        (2 * ((nextPrimeWindow M).card : Real) *
          (72 * Real.log ((q : Real) + 2)) ^ q +
        1048576 * ((5 * M / 4 : Nat) : Real) ^ (15 / 16 : Real) *
          (1 + Real.log ((Finset.prod (primeTargetCutoff M) (fun p => p) : Nat) : Real) +
            Real.log (((5 * M / 4 : Nat) : Real) + 2)) ^ 2 *
          (Finset.prod (primeTargetCutoff M) singularFactor) ^ q) := by
  classical
  intro M r q hM hLog hLogLog hr hq
  have hr' := nextPrimeWindow_spec M r hr
  have hMpos : (0 : Real) < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have hLogLt : Real.log (M : Real) < (M : Real) := by
    have h := Real.log_le_sub_one_of_pos hMpos
    linarith
  have hCutoff : forall p, Membership.mem (primeTargetCutoff M) p ->
      And (Nat.Prime p) (And (3 < p) (p < r)) := by
    intro p hp
    have h := (primeTargetCutoff_mem M p (by omega)).mp hp
    have hpM : p < M := by exact_mod_cast h.2.2.trans_lt hLogLt
    exact And.intro h.1 (And.intro h.2.1 (by omega))
  have hSub : (nextPrimeWindow M).erase r <=
      Nat.largestPrimeFactorRow (5 * M / 4) M 1 := by
    rw [<- nextPrimeWindow_eq_row]
    exact Finset.erase_subset _ _
  have hPrimes : forall s, Membership.mem ((nextPrimeWindow M).erase r) s ->
      And (Nat.Prime s) (3 <= s) := by
    intro s hs
    have h := nextPrimeWindow_spec M s (Finset.mem_erase.mp hs).2
    exact And.intro h.1 (by omega)
  have hMoment := lpf_primeTarget_truncated_moment_power_numeric (5 * M / 4) M 1 r q (primeTargetCutoff M)
    ((nextPrimeWindow M).erase r) hr'.1 (by omega) hq hCutoff hSub hPrimes
  rw [<- nextPrimeWindow_eq_row] at hMoment
  let F (s : Nat) : Real := (Finset.prod
    ((primeTargetCutoff M).filter (fun p => Dvd.dvd p (primeTargetSeparation r s)))
      singularFactor) ^ q
  have hPoint : forall s, Membership.mem ((nextPrimeWindow M).erase r) s ->
      singularDivisorProduct (primeTargetSeparation r s) ^ q <= (6 : Real) ^ q * F s := by
    intro s hs
    have hs' := Finset.mem_erase.mp hs
    have hv := primeTargetSeparation_pos M r s (by omega) hr hs'.2 hs'.1
    have hvM := primeTargetSeparation_le M r s hM hr hs'.2
    have hProduct := singularDivisorProduct_le_cutoff_six M _ hM hv hvM hLog hLogLog
    have hNonneg : 0 <= singularDivisorProduct (primeTargetSeparation r s) := by
      apply Finset.prod_nonneg
      intro p hp
      exact lpf_overlap_numeric_singularFactor_nonneg p (Finset.mem_filter.mp hp).2
    have h := lpf_overlap_numeric_pow_mono _ _ hNonneg hProduct q
    simpa only [mul_pow] using h
  calc
    _ <= Finset.sum ((nextPrimeWindow M).erase r) (fun s => (6 : Real) ^ q * F s) :=
      Finset.sum_le_sum hPoint
    _ = (6 : Real) ^ q * Finset.sum ((nextPrimeWindow M).erase r) F :=
      (Finset.mul_sum _ _ _).symm
    _ <= _ := mul_le_mul_of_nonneg_left hMoment (by positivity)

end PrimeFactorOscillations.LPF


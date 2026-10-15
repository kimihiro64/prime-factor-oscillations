/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFOverlapMomentNumeric
import PrimeFactorOscillations.Helpers.LPFPrimeTargetFull

/-!
# Explicit main terms for complete LPF prime-target overlap

Both cofactor branches and the complete off-diagonal divisor products are
retained. The tail factor is six, the growing-order Euler factor is 72,
and the target-window cardinality has a uniform Chebyshev bound.
The residue error constant is still existential: these finite estimates
alone do not certify a numerical entry threshold.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem exists_prime_row_singular_packet_numeric :
    exists C : Real, And (0 < C)
      (forall (X y m N : Nat) (P : Finset Nat) (q : Nat)
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
        C * (X : Real) ^ (7 / 8 : Real) *
          (1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
            Real.log ((X : Real) + 2)) ^ 2 * (Finset.prod P singularFactor) ^ q) := by
  classical
  let C : Real := Classical.choose exists_squarefree_prime_row_moment_bound
  have hC := Classical.choose_spec exists_squarefree_prime_row_moment_bound
  refine Exists.intro C (And.intro hC.1 ?_)
  intro X y m N P q a hq hP
  have hPacket := hC.2 X y m P q a
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

theorem exists_primeTarget_truncated_branch_numeric :
    exists C : Real, And (0 < C)
      (forall (X y m r n q : Nat) (P S : Finset Nat),
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
          C * (X : Real) ^ (7 / 8 : Real) *
            (1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
              Real.log ((X : Real) + 2)) ^ 2 * (Finset.prod P singularFactor) ^ q) := by
  classical
  let C : Real := Classical.choose exists_prime_row_singular_packet_numeric
  have hC := Classical.choose_spec exists_prime_row_singular_packet_numeric
  refine Exists.intro C (And.intro hC.1 ?_)
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
    _ <= _ := hC.2 X y m r P q a hq
      (fun p hp => And.intro (hP p hp).1
        (And.intro (by
          have h := hP p hp
          have h4 : Not (p = 4) := by intro he; subst p; norm_num at h
          omega) (hP p hp).2.2))

/-- Both cofactor branches, with no assumption on coprimality of input primes. -/
theorem exists_primeTarget_truncated_moment_numeric :
    exists C : Real, And (0 < C)
      (forall (X y m r q : Nat) (P S : Finset Nat),
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
          C * (X : Real) ^ (7 / 8 : Real) *
            (1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
              Real.log ((X : Real) + 2)) ^ 2 * (Finset.prod P singularFactor) ^ q) := by
  classical
  let C : Real := Classical.choose exists_primeTarget_truncated_branch_numeric
  have hC := Classical.choose_spec exists_primeTarget_truncated_branch_numeric
  refine Exists.intro (2 * C) (And.intro (mul_pos (by norm_num) hC.1) ?_)
  intro X y m r q P S hr hr3 hq hP hS hPrimes
  let F (s : Nat) : Real :=
    (Finset.prod (P.filter (fun p => Dvd.dvd p
      ((primeTargetSum r - primeTargetSum s) +
        (primeTargetSum s - primeTargetSum r)))) singularFactor) ^ q
  have hOne := hC.2 X y m r 1 q P (S.filter (fun s => primeTargetCofactor s = 1))
    hr hr3 hq (Or.inl rfl) hP
    (fun s hs => hS (Finset.mem_filter.mp hs).1)
    (fun s hs => And.intro (hPrimes s (Finset.mem_filter.mp hs).1).1
      (And.intro (hPrimes s (Finset.mem_filter.mp hs).1).2 (Finset.mem_filter.mp hs).2))
  have hThree := hC.2 X y m r 3 q P (S.filter (fun s => primeTargetCofactor s = 3))
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


private theorem lpf_singularFactor_nonneg_numeric (p : Nat) (hp : 3 <= p) :
    0 <= singularFactor p := by
  have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast hp
  exact add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith only [hpR]))

theorem singularDivisorProduct_le_cutoff_six (M v : Nat) (hM : 4 <= M)
    (hv : 0 < v) (hvM : v <= 2 * M)
    (hLog : 4 <= Real.log (M : Real))
    (hLogLog : 3 <= Real.log (Real.log (M : Real))) :
    singularDivisorProduct v <= 6 *
      Finset.prod ((primeTargetCutoff M).filter (fun p => Dvd.dvd p v)) singularFactor := by
  classical
  let Q := v.primeFactors.filter (fun p => 3 <= p)
  have hQ : forall p, Membership.mem Q p ->
      And (Nat.Prime p) (And (3 <= p) (Dvd.dvd p v)) := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    exact And.intro (Nat.prime_of_mem_primeFactors h.1)
      (And.intro h.2 (Nat.dvd_of_mem_primeFactors h.1))
  have hSmallSet : Q.filter (fun (p : Nat) => And (3 < p) ((p : Real) <= Real.log (M : Real))) =
      (primeTargetCutoff M).filter (fun p => Dvd.dvd p v) := by
    apply Finset.ext
    intro p
    constructor
    next =>
      intro hp
      have h := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr (And.intro
        ((primeTargetCutoff_mem M p (by omega)).mpr
          (And.intro (hQ p h.1).1 h.2)) (hQ p h.1).2.2)
    next =>
      intro hp
      have h := Finset.mem_filter.mp hp
      have hc := (primeTargetCutoff_mem M p (by omega)).mp h.1
      apply Finset.mem_filter.mpr
      refine And.intro ?_ hc.2
      apply Finset.mem_filter.mpr
      exact And.intro
        (Nat.mem_primeFactors.mpr (And.intro hc.1 (And.intro h.2 (by omega))))
        (by omega)
  have hTail := singular_product_le_truncated Q v (Real.log (M : Real)) hv hLog hQ
  rw [hSmallSet] at hTail
  have hMpos : (0 : Real) < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have hLogV : Real.log (v : Real) <= 1 + Real.log (M : Real) := by
    calc
      _ <= Real.log (2 * (M : Real)) :=
        Real.log_le_log (by exact_mod_cast hv) (by exact_mod_cast hvM)
      _ = Real.log 2 + Real.log (M : Real) :=
        Real.log_mul (by norm_num) hMpos.ne'
      _ <= _ := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
        linarith only [h]
  have hY : 0 < Real.log (M : Real) := by linarith only [hLog]
  have hLL : 0 < Real.log (Real.log (M : Real)) := by linarith only [hLogLog]
  have hFraction : 2 * Real.log (v : Real) /
      (Real.log (M : Real) * Real.log (Real.log (M : Real))) <= 1 := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos hY hLL)).mp
    have hCancel : (2 * Real.log (v : Real) /
        (Real.log (M : Real) * Real.log (Real.log (M : Real)))) *
        (Real.log (M : Real) * Real.log (Real.log (M : Real))) =
        2 * Real.log (v : Real) := by field_simp
    rw [hCancel, one_mul]
    nlinarith only [hLogV, hLog, hLogLog, mul_nonneg hY.le (sub_nonneg.mpr hLogLog)]
  have hLow : 0 <= Finset.prod
      ((primeTargetCutoff M).filter (fun p => Dvd.dvd p v)) singularFactor := by
    apply Finset.prod_nonneg
    intro p hp
    have h := (primeTargetCutoff_mem M p (by omega)).mp (Finset.mem_filter.mp hp).1
    exact lpf_singularFactor_nonneg_numeric p (by omega)
  have hExp : 2 * Real.exp (2 * Real.log (v : Real) /
      (Real.log (M : Real) * Real.log (Real.log (M : Real)))) <= 6 := by
    have h := Real.exp_le_exp.mpr hFraction
    have hOne := Real.exp_one_lt_three.le
    linarith only [h, hOne]
  exact hTail.trans (mul_le_mul_of_nonneg_right hExp hLow)

private theorem nonneg_pow_mono (a b : Real) (ha : 0 <= a) (hab : a <= b) (q : Nat) :
    a ^ q <= b ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (pow_nonneg (ha.trans hab) q)

/-- Full off-diagonal divisor moments on the actual target window, with every error. -/
theorem exists_primeTarget_full_finite_numeric :
    exists C : Real, And (0 < C) (forall M r q : Nat,
      4 <= M -> 4 <= Real.log (M : Real) ->
      3 <= Real.log (Real.log (M : Real)) ->
      Membership.mem (nextPrimeWindow M) r -> 5 <= q ->
      Finset.sum ((nextPrimeWindow M).erase r) (fun s =>
        singularDivisorProduct (primeTargetSeparation r s) ^ q) <=
      (6 : Real) ^ q *
        (2 * ((nextPrimeWindow M).card : Real) *
          (72 * Real.log ((q : Real) + 2)) ^ q +
        C * ((5 * M / 4 : Nat) : Real) ^ (7 / 8 : Real) *
          (1 + Real.log ((Finset.prod (primeTargetCutoff M) (fun p => p) : Nat) : Real) +
            Real.log (((5 * M / 4 : Nat) : Real) + 2)) ^ 2 *
          (Finset.prod (primeTargetCutoff M) singularFactor) ^ q)) := by
  classical
  let C : Real := Classical.choose exists_primeTarget_truncated_moment_numeric
  have hC := Classical.choose_spec exists_primeTarget_truncated_moment_numeric
  refine Exists.intro C (And.intro hC.1 ?_)
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
  have hMoment := hC.2 (5 * M / 4) M 1 r q (primeTargetCutoff M)
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
      exact lpf_singularFactor_nonneg_numeric p (Finset.mem_filter.mp hp).2
    have h := nonneg_pow_mono _ _ hNonneg hProduct q
    simpa only [mul_pow] using h
  calc
    _ <= Finset.sum ((nextPrimeWindow M).erase r) (fun s => (6 : Real) ^ q * F s) :=
      Finset.sum_le_sum hPoint
    _ = (6 : Real) ^ q * Finset.sum ((nextPrimeWindow M).erase r) F :=
      (Finset.mul_sum _ _ _).symm
    _ <= _ := mul_le_mul_of_nonneg_left hMoment (by positivity)


theorem lpf_nextPrimeWindow_card_numeric (M : Nat) (hM : 2 <= M) :
    ((nextPrimeWindow M).card : Real) <=
      (25 / 14 : Real) * (M : Real) / Real.log (M : Real) := by
  have hMReal : (2 : Real) <= (M : Real) := by exact_mod_cast hM
  have hMPos : (0 : Real) < (M : Real) := by linarith only [hMReal]
  have hLog : 0 < Real.log (M : Real) := Real.log_pos (by linarith only [hMReal])
  let R := (Finset.Ioc 0 (5 * M / 4)).filter Nat.Prime
  have hSub : nextPrimeWindow M <= R := by
    intro p hp
    have h := nextPrimeWindow_spec M p hp
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_Ioc.mpr (And.intro h.1.pos h.2.2)) h.1)
  have hLower : ((nextPrimeWindow M).card : Real) * Real.log (M : Real) <=
      Finset.sum (nextPrimeWindow M) (fun p => Real.log (p : Real)) := by
    calc
      _ = Finset.sum (nextPrimeWindow M) (fun _ => Real.log (M : Real)) := by simp
      _ <= _ := by
        apply Finset.sum_le_sum
        intro p hp
        have h := nextPrimeWindow_spec M p hp
        exact Real.log_le_log hMPos (by exact_mod_cast h.2.1.le)
  have hUpper : Finset.sum (nextPrimeWindow M) (fun p => Real.log (p : Real)) <=
      Chebyshev.theta ((5 * M / 4 : Nat) : Real) := by
    have hTheta := Chebyshev.theta.eq_1 ((5 * M / 4 : Nat) : Real)
    simp only [Nat.floor_natCast] at hTheta
    rw [hTheta]
    apply Finset.sum_le_sum_of_subset_of_nonneg hSub
    intro p hp hNot
    have h := (Finset.mem_filter.mp hp).2
    exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  have hTheta := Chebyshev.theta_le_log4_mul_x
    ((show (0 : Real) <= ((5 * M / 4 : Nat) : Real) from Nat.cast_nonneg _))
  have hLogFour : Real.log (4 : Real) <= 10 / 7 := by
    have h := log_two_le_five_sevenths
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [h]
  have hX : ((5 * M / 4 : Nat) : Real) <= (5 / 4 : Real) * (M : Real) := by
    have h : (4 : Real) * ((5 * M / 4 : Nat) : Real) <= 5 * (M : Real) := by
      exact_mod_cast (show 4 * (5 * M / 4) <= 5 * M by omega)
    linarith only [h]
  have hX0 : (0 : Real) <= ((5 * M / 4 : Nat) : Real) := Nat.cast_nonneg _
  have hTheta' : Chebyshev.theta ((5 * M / 4 : Nat) : Real) <=
      (25 / 14 : Real) * (M : Real) := by
    have h := mul_le_mul_of_nonneg_right hLogFour hX0
    have hh := mul_le_mul_of_nonneg_left hX (by norm_num : (0 : Real) <= 10 / 7)
    linarith only [hTheta, h, hh]
  have hBound := hLower.trans (hUpper.trans hTheta')
  calc
    _ = (((nextPrimeWindow M).card : Real) * Real.log (M : Real)) /
        Real.log (M : Real) := by field_simp
    _ <= _ := div_le_div_of_nonneg_right hBound hLog.le

end PrimeFactorOscillations.LPF

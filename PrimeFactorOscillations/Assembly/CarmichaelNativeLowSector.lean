/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCompanionMasks

/-!
# Low native product range in the signed Carmichael unit

This module estimates only the isolated companion-cancelled low product range.
The complementary high native core remains signed and unestimated here.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelNativeLowSector
open scoped Classical
open CarmichaelCompanionCancellation CarmichaelCompanionMasks

/-- The positive harmonic prefix is monotone in its actual inclusive cutoff. -/
theorem harmonic_prefix_mono {B N : Nat} (hBN : B <= N) :
    harmonicPrefix B <= harmonicPrefix N := by
  unfold harmonicPrefix
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun n hn => Finset.mem_Ioc.mpr
      (And.intro (Finset.mem_Ioc.mp hn).1 ((Finset.mem_Ioc.mp hn).2.trans hBN)))
    (fun n _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))

/-- The positive reciprocal-maximum kernel on the full supported low native product region. -/
def productRegionKernel (N T : Nat) : Real :=
  (Finset.Icc 1 N).sum (fun a => (Finset.Icc 1 N).sum (fun c =>
    if a * c <= T then 1 / ((max a c : Nat) : Real) else 0))

/-- The full ac<=T reciprocal-maximum kernel has a square-root product cost. -/
theorem product_region_kernel_bound (N T : Nat) :
    productRegionKernel N T <=
      2 * (T.sqrt : Real) * harmonicPrefix N := by
  classical
  let S := Finset.Icc 1 N
  have hterm : forall a, Membership.mem S a ->
      forall c, Membership.mem S c ->
      (if a * c <= T then 1 / ((max a c : Nat) : Real) else 0) <=
        (if c <= T.sqrt then 1 / (a : Real) else 0) +
        (if a <= T.sqrt then 1 / (c : Real) else 0) := by
    intro a ha c hc
    have ha0 : 0 <= (1 : Real) / (a : Real) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
    have hc0 : 0 <= (1 : Real) / (c : Real) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
    by_cases hp : a * c <= T
    . rw [ite_eq_left hp]
      by_cases hac : c <= a
      . have hcs : c <= T.sqrt := Nat.le_sqrt.mpr
          ((Nat.mul_le_mul_right c hac).trans hp)
        rw [max_eq_left hac, ite_eq_left hcs]
        split_ifs <;> linarith
      . have hca : a <= c := Nat.le_of_lt (Nat.lt_of_not_ge hac)
        have has : a <= T.sqrt := Nat.le_sqrt.mpr
          ((Nat.mul_le_mul_left a hca).trans hp)
        rw [max_eq_right hca, ite_eq_left has]
        split_ifs <;> linarith
    . rw [ite_eq_right hp]
      split_ifs <;> linarith
  have hcount : (S.filter (fun n => n <= T.sqrt)).card <= T.sqrt := by
    calc
      _ <= (Finset.Icc 1 T.sqrt).card := Finset.card_le_card (by
        intro n hn
        exact Finset.mem_Icc.mpr (And.intro (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
          (Finset.mem_filter.mp hn).2))
      _ = T.sqrt := by simp
  have hsum : S.sum (fun a => 1 / (a : Real)) = harmonicPrefix N := by
    apply Finset.sum_congr
    . ext n
      simp [S]
      intro _
      exact Nat.succ_le_iff
    . intro _ _; rfl
  have he : S.sum (fun a => S.sum (fun c =>
      if c <= T.sqrt then 1 / (a : Real) else 0)) =
      ((S.filter (fun n => n <= T.sqrt)).card : Real) * harmonicPrefix N := by
    simp_rw [<- Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [<- Finset.mul_sum, hsum]
  have hf : S.sum (fun a => S.sum (fun c =>
      if a <= T.sqrt then 1 / (c : Real) else 0)) =
      ((S.filter (fun n => n <= T.sqrt)).card : Real) * harmonicPrefix N := by
    rw [Finset.sum_comm]
    exact he
  have hH : 0 <= harmonicPrefix N := by
    exact Finset.sum_nonneg (fun _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
  calc
    _ <= S.sum (fun a => S.sum (fun c =>
        (if c <= T.sqrt then 1 / (a : Real) else 0) +
        (if a <= T.sqrt then 1 / (c : Real) else 0))) := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum (fun c hc => hterm a ha c hc)
    _ = 2 * ((S.filter (fun n => n <= T.sqrt)).card : Real) * harmonicPrefix N := by
      simp_rw [Finset.sum_add_distrib]
      rw [he, hf]
      ring
    _ <= _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcount) (by norm_num)) hH

/-- The exact two companion cutoffs cost at most 2N/max(a,c). -/
theorem companion_cutoff_cost (N a c : Nat)
    (ha : 0 < a) (_hc : 0 < c) (haN : a <= N) (hcN : c <= N) :
    (((min (N / a) (N / c) + 1 : Nat) : Real)) <=
      2 * (N : Real) / ((max a c : Nat) : Real) := by
  have hmax : 0 < max a c := lt_of_lt_of_le ha (le_max_left _ _)
  have hmaxN : max a c <= N := max_le haN hcN
  have hmin : min (N / a) (N / c) <= N / max a c := by
    by_cases hac : c <= a
    . rw [max_eq_left hac]; exact min_le_left _ _
    . rw [max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hac))]
      exact min_le_right _ _
  have hint : (min (N / a) (N / c) + 1) * max a c <= 2 * N := by
    calc
      _ <= (N / max a c + 1) * max a c :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_right hmin 1)
      _ = N / max a c * max a c + max a c := by ring
      _ <= N + N := Nat.add_le_add (Nat.div_mul_le_self _ _) hmaxN
      _ = _ := by ring
  have hr : 0 < ((max a c : Nat) : Real) := Nat.cast_pos.mpr hmax
  have hi : ((min (N / a) (N / c) + 1 : Nat) : Real) *
      ((max a c : Nat) : Real) <= 2 * (N : Real) := by exact_mod_cast hint
  have he : (2 * (N : Real) / ((max a c : Nat) : Real)) *
      ((max a c : Nat) : Real) = 2 * (N : Real) := by field_simp
  nlinarith

/-- The exact finite companion-cutoff cost on ac<=T. -/
def lowCompanionCost (N T : Nat) : Real :=
  (Finset.Icc 1 N).sum (fun a => (Finset.Icc 1 N).sum (fun c =>
    if a * c <= T then ((min (N / a) (N / c) + 1 : Nat) : Real) else 0))

/-- Aggregate every retained companion cutoff on the full low-product region. -/
theorem low_companion_cost_bound (N T : Nat) :
    lowCompanionCost N T <=
      4 * (N : Real) * (T.sqrt : Real) * harmonicPrefix N := by
  have hN : 0 <= (2 : Real) * (N : Real) := by positivity
  calc
    _ <= (2 * (N : Real)) * productRegionKernel N T := by
      unfold lowCompanionCost productRegionKernel
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro c hc
      by_cases hp : a * c <= T
      . rw [ite_eq_left hp, ite_eq_left hp]
        simpa only [div_eq_mul_inv, one_mul] using
          companion_cutoff_cost N a c (Finset.mem_Icc.mp ha).1
            (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hc).2
      . simp only [ite_eq_right hp, mul_zero]
        exact le_refl _
    _ <= (2 * (N : Real)) *
        (2 * (T.sqrt : Real) * harmonicPrefix N) :=
      mul_le_mul_of_nonneg_left (product_region_kernel_bound N T) hN
    _ = _ := by ring

/-- The actual base-change norm-fiber coefficient, with all ideal prime-power norms. -/
def nativeCoefficient {q : Nat} (chi : DirichletCharacter Complex q) (a : Nat) : Complex :=
  OAI.ShortDraftHeckeBridge.normFiberCoeff
    (OAI.ShortDraftHeckeBridge.baseChangeWeight chi) a

private theorem native_coefficient_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (a : Nat) (ha : 0 < a) :
    norm (nativeCoefficient chi a) <= (a.divisors.card : Real) := by
  unfold nativeCoefficient
  rw [OAI.ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff chi a
    (Nat.ne_of_gt ha)]
  exact pair_inverse_coeff_divisor_bound chi
    (OAI.ShortDraftHeckeBridge.baseChangeChar chi) a

/-- Both native coefficients and the complete amplified companion with both cross-coprimality masks. -/
def nativeTerm {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H N : Nat) (W : Nat -> Nat -> Complex) (a c : Nat) : Complex :=
  nativeCoefficient chi a * star (nativeCoefficient chi c) *
    weightedCompanionPacket (OAI.ShortDraftHeckeBridge.baseChangeChar chi)
      (H * c) (H * a) (N / a) (N / c)
      (amplifiedWindow G a (W a)) (amplifiedWindow G c (W c))

/-- The signed low native sector with every rational outer coprimality condition retained. -/
def lowNativePacket {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H N T : Nat) (W : Nat -> Nat -> Complex) : Complex :=
  (Finset.Icc 1 N).sum (fun a => (Finset.Icc 1 N).sum (fun c =>
    if a * c <= T /\ Nat.Coprime a c /\ Nat.Coprime a H /\ Nat.Coprime c H
    then nativeTerm chi G H N W a c else 0))

private theorem cap_bound (q H a B N : Nat) (w : Nat -> Complex)
    (M V : Real) (hM : 0 <= M) (hV : 0 <= V) (hBN : B <= N)
    (ha : (a.divisors.card : Real) <= M)
    (hH : (H.divisors.card : Real) <= M)
    (hw : windowVariation w B <= V) :
    companionCap q H a B w <=
      M * (harmonicPrefix N) ^ 2 * V * (M * (q : Real)) := by
  have hB0 : 0 <= harmonicPrefix B :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hs : (harmonicPrefix B) ^ 2 <= (harmonicPrefix N) ^ 2 := by
    simpa only [pow_two] using
      mul_self_le_mul_self hB0 (harmonic_prefix_mono hBN)
  have hw0 : 0 <= windowVariation w B := by unfold windowVariation; positivity
  unfold companionCap
  exact mul_le_mul
    (mul_le_mul (mul_le_mul ha hs (sq_nonneg _) hM) hw hw0 (by positivity))
    (mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg _))
    (by positivity) (by positivity)

/-- Apply the proved companion cancellation to the actual native coefficients and both cross masks. -/
theorem native_term_bound {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1)
    (G : Finset Nat) (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (H N a c : Nat) (hH : 0 < H) (ha : 0 < a) (hc : 0 < c)
    (haN : a <= N) (hcN : c <= N) (W : Nat -> Nat -> Complex)
    (M V : Real) (hM : 0 <= M) (hV : 0 <= V)
    (hdiv : forall n, 0 < n -> n <= H * N -> (n.divisors.card : Real) <= M)
    (hvar : forall n, Membership.mem (Finset.Icc 1 N) n ->
      windowVariation (W n) (N / n) <= V) :
    norm (nativeTerm chi G H N W a c) <=
      (((q * 3 : Nat) : Real) ^ 2 * M ^ 6 * V ^ 2 *
        (harmonicPrefix N) ^ 4) *
        ((min (N / a) (N / c) + 1 : Nat) : Real) := by
  have hNN : N <= H * N := by
    simpa only [Nat.succ_eq_add_one, Nat.zero_add, Nat.one_mul] using
      Nat.mul_le_mul_right N (Nat.succ_le_of_lt hH)
  have hta : (a.divisors.card : Real) <= M := hdiv a ha (haN.trans hNN)
  have htc : (c.divisors.card : Real) <= M := hdiv c hc (hcN.trans hNN)
  have hHa : (H * a).divisors.card <= M := by
    exact_mod_cast hdiv (H * a) (Nat.mul_pos hH ha) (Nat.mul_le_mul_left H haN)
  have hHc : ((H * c).divisors.card : Real) <= M :=
    hdiv (H * c) (Nat.mul_pos hH hc) (Nat.mul_le_mul_left H hcN)
  let Q : Real := ((q * 3 : Nat) : Real)
  let Z : Real := M * (harmonicPrefix N) ^ 2 * V * (M * Q)
  have hz : 0 <= Z := by dsimp only [Z, Q]; positivity
  have hl : companionCap (q * 3) (H * c) a (N / a) (W a) <= Z :=
    cap_bound (q * 3) (H * c) a (N / a) N (W a) M V hM hV
      (Nat.div_le_self _ _) hta hHc (hvar a (Finset.mem_Icc.mpr (And.intro ha haN)))
  have hr : companionCap (q * 3) (H * a) c (N / c) (W c) <= Z :=
    cap_bound (q * 3) (H * a) c (N / c) N (W c) M V hM hV
      (Nat.div_le_self _ _) htc hHa (hvar c (Finset.mem_Icc.mpr (And.intro hc hcN)))
  have hp := amplified_packet_bound
    (OAI.ShortDraftHeckeBridge.baseChangeChar chi) (cubic_companion_ne_one chi hchi)
    (H * c) (H * a) (N / a) (N / c) (Nat.mul_pos hH hc) (Nat.mul_pos hH ha)
    G hG a c ha hc (W a) (W c)
  have hn := mul_le_mul
    ((native_coefficient_bound chi a ha).trans hta)
    ((native_coefficient_bound chi c hc).trans htc) (norm_nonneg _) hM
  unfold nativeTerm
  rw [norm_mul, norm_mul, norm_star]
  calc
    _ <= (M * M) *
        (((min (N / a) (N / c) + 1 : Nat) : Real) * Z * Z) := by
      apply mul_le_mul hn
      . exact hp.trans (mul_le_mul
          (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)) hr
          (by unfold companionCap windowVariation; positivity) (by positivity))
      . exact norm_nonneg _
      . positivity
    _ = _ := by dsimp only [Z, Q]; ring

/-- A complete finite bound for the signed low native packet with explicit divisor and variation caps. -/
theorem low_native_packet_bound {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1)
    (G : Finset Nat) (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (H N T : Nat) (hH : 0 < H) (W : Nat -> Nat -> Complex)
    (M V : Real) (hM : 0 <= M) (hV : 0 <= V)
    (hdiv : forall n, 0 < n -> n <= H * N -> (n.divisors.card : Real) <= M)
    (hvar : forall n, Membership.mem (Finset.Icc 1 N) n ->
      windowVariation (W n) (N / n) <= V) :
    norm (lowNativePacket chi G H N T W) <=
      4 * (((q * 3 : Nat) : Real) ^ 2) * M ^ 6 * V ^ 2 *
        (harmonicPrefix N) ^ 5 * (N : Real) * (T.sqrt : Real) := by
  let K : Real := ((q * 3 : Nat) : Real) ^ 2 * M ^ 6 * V ^ 2 *
    (harmonicPrefix N) ^ 4
  have hK : 0 <= K := by dsimp only [K]; positivity
  calc
    _ <= K * lowCompanionCost N T := by
      unfold lowNativePacket lowCompanionCost
      rw [Finset.mul_sum]
      calc
        _ <= (Finset.Icc 1 N).sum (fun a =>
            norm ((Finset.Icc 1 N).sum (fun c =>
              if a * c <= T /\ Nat.Coprime a c /\ Nat.Coprime a H /\ Nat.Coprime c H
              then nativeTerm chi G H N W a c else 0))) := norm_sum_le _ _
        _ <= _ := by
          apply Finset.sum_le_sum
          intro a ha
          rw [Finset.mul_sum]
          calc
            _ <= (Finset.Icc 1 N).sum (fun c =>
                norm (if a * c <= T /\ Nat.Coprime a c /\ Nat.Coprime a H /\ Nat.Coprime c H
                  then nativeTerm chi G H N W a c else 0)) := norm_sum_le _ _
            _ <= _ := by
              apply Finset.sum_le_sum
              intro c hc
              by_cases hcond : a * c <= T /\ Nat.Coprime a c /\ Nat.Coprime a H /\ Nat.Coprime c H
              . rw [ite_eq_left hcond, ite_eq_left hcond.1]
                exact native_term_bound chi hchi G hG H N a c hH
                  (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hc).1
                  (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hc).2 W M V hM hV hdiv hvar
              . rw [ite_eq_right hcond, norm_zero]
                split_ifs <;> positivity
    _ <= K * (4 * (N : Real) * (T.sqrt : Real) * harmonicPrefix N) :=
      mul_le_mul_of_nonneg_left (low_companion_cost_bound N T) hK
    _ = _ := by dsimp only [K]; ring

private theorem harmonic_subpower (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall N : Nat, harmonicPrefix N <= C * (N : Real) ^ eps := by
  let f : Nat -> Real := fun n => (n : Real) ^ (-1 - eps)
  have hs : Summable f := Real.summable_nat_rpow.mpr (by linarith)
  have hf : forall n, 0 <= f n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have ht : 0 <= tsum f := tsum_nonneg hf
  refine Exists.intro (1 + tsum f) (And.intro (by linarith) ?_)
  intro N
  calc
    _ <= (N : Real) ^ eps * (Finset.Ioc 0 N).sum f := by
      unfold harmonicPrefix
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : 0 < (n : Real) := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
      have he : 1 / (n : Real) = (n : Real) ^ eps * f n := by
        dsimp only [f]
        calc
          _ = (n : Real) ^ (-1 : Real) := by simp [Real.rpow_neg_one]
          _ = _ := by
            rw [<- Real.rpow_add hn0]
            congr 1
            ring
      rw [he]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2)
          (le_of_lt heps)) (hf n)
    _ <= (N : Real) ^ eps * tsum f :=
      mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => hf n) hs)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ <= _ := by
      have hp : 0 <= (N : Real) ^ eps := Real.rpow_nonneg (Nat.cast_nonneg _) _
      nlinarith

/-- Discharge all divisor and harmonic growth costs uniformly in q,H,N,T and finite prime masks. -/
theorem low_native_packet_subpower (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
      chi ^ 3 = 1 ->
      forall (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H N T : Nat), 0 < H -> 0 < N ->
      forall (W : Nat -> Nat -> Complex) (V : Real), 0 <= V ->
      (forall n, Membership.mem (Finset.Icc 1 N) n ->
        windowVariation (W n) (N / n) <= V) ->
      norm (lowNativePacket chi G H N T W) <=
        C * (((q * 3 : Nat) : Real) ^ 2) * V ^ 2 *
          ((H * N : Nat) : Real) ^ eps * (N : Real) * (T.sqrt : Real) := by
  choose A hA ha using QuadraticDivisorMean.divisor_card_subpower
    (eps / 12) (by linarith)
  choose B hB hb using harmonic_subpower (eps / 10) (by linarith)
  refine Exists.intro (4 * A ^ 6 * B ^ 5) (And.intro (by positivity) ?_)
  intro q inst chi hchi G hG H N T hH hN W V hV hvar
  have hR : 0 < ((H * N : Nat) : Real) := Nat.cast_pos.mpr (Nat.mul_pos hH hN)
  have hNN : N <= H * N := by
    simpa only [Nat.succ_eq_add_one, Nat.zero_add, Nat.one_mul] using
      Nat.mul_le_mul_right N (Nat.succ_le_of_lt hH)
  let M : Real := A * ((H * N : Nat) : Real) ^ (eps / 12)
  have hM : 0 <= M := by dsimp only [M]; positivity
  have hdiv : forall n, 0 < n -> n <= H * N -> (n.divisors.card : Real) <= M := by
    intro n hn hnR
    exact (ha n hn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hnR) (by linarith))
      (le_of_lt hA))
  have hh : harmonicPrefix N <= B * ((H * N : Nat) : Real) ^ (eps / 10) :=
    (hb N).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hNN) (by linarith))
      (le_of_lt hB))
  have hh0 : 0 <= harmonicPrefix N :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hh5 : (harmonicPrefix N) ^ 5 <=
      (B * ((H * N : Nat) : Real) ^ (eps / 10)) ^ 5 := by
    gcongr
  have he6 : (((H * N : Nat) : Real) ^ (eps / 12)) ^ 6 =
      ((H * N : Nat) : Real) ^ (eps / 2) := by
    rw [<- Real.rpow_natCast _ 6, <- Real.rpow_mul (le_of_lt hR)]
    congr 1
    norm_num <;> ring
  have he5 : (((H * N : Nat) : Real) ^ (eps / 10)) ^ 5 =
      ((H * N : Nat) : Real) ^ (eps / 2) := by
    rw [<- Real.rpow_natCast _ 5, <- Real.rpow_mul (le_of_lt hR)]
    congr 1
    norm_num <;> ring
  have hmass : M ^ 6 * (harmonicPrefix N) ^ 5 <=
      A ^ 6 * B ^ 5 * ((H * N : Nat) : Real) ^ eps := by
    calc
      _ <= M ^ 6 * (B * ((H * N : Nat) : Real) ^ (eps / 10)) ^ 5 :=
        mul_le_mul_of_nonneg_left hh5 (pow_nonneg hM _)
      _ = A ^ 6 * B ^ 5 *
          (((H * N : Nat) : Real) ^ (eps / 2) *
            ((H * N : Nat) : Real) ^ (eps / 2)) := by
        dsimp only [M]
        rw [mul_pow, mul_pow, he6, he5]
        ring
      _ = _ := by
        rw [<- Real.rpow_add hR, show eps / 2 + eps / 2 = eps by ring]
  have hlow := low_native_packet_bound chi hchi G hG H N T hH W M V hM hV hdiv hvar
  calc
    _ <= 4 * (((q * 3 : Nat) : Real) ^ 2) * M ^ 6 * V ^ 2 *
        (harmonicPrefix N) ^ 5 * (N : Real) * (T.sqrt : Real) := hlow
    _ = (4 * (((q * 3 : Nat) : Real) ^ 2) * V ^ 2 * (N : Real) * (T.sqrt : Real)) *
        (M ^ 6 * (harmonicPrefix N) ^ 5) := by ring
    _ <= (4 * (((q * 3 : Nat) : Real) ^ 2) * V ^ 2 * (N : Real) * (T.sqrt : Real)) *
        (A ^ 6 * B ^ 5 * ((H * N : Nat) : Real) ^ eps) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

/-- Sample the fixed physical window at the actual product a times i+1 divided by D. -/
def scaledWindow (f : Real -> Complex) (a D : Nat) (i : Nat) : Complex :=
  f (((a * (i + 1) : Nat) : Real) / (D : Real))

/-- The actual sampled fixed window has a variation bound independent of its native index and scale. -/
theorem scaled_window_variation (f : Real -> Complex) (L : NNReal)
    (hf : LipschitzWith L f) (D a : Nat) (hD : 0 < D)
    (ha : 0 < a) (haN : a <= 4 * D) :
    windowVariation (scaledWindow f a D) ((4 * D) / a) <=
      norm (f 0) + 8 * (L : Real) := by
  let B := (4 * D) / a
  have hB : 0 < B := Nat.div_pos haN ha
  have hDR : 0 < (D : Real) := Nat.cast_pos.mpr hD
  have hL : 0 <= (L : Real) := L.coe_nonneg
  have hstep : 0 <= (a : Real) / (D : Real) :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hDR)
  have hcap : ((a * B : Nat) : Real) / (D : Real) <= 4 := by
    have hi : a * B <= 4 * D := by
      simpa only [Nat.mul_comm a B] using Nat.div_mul_le_self (4 * D) a
    have hir : ((a * B : Nat) : Real) <= 4 * (D : Real) := by exact_mod_cast hi
    have he : (((a * B : Nat) : Real) / (D : Real)) * (D : Real) =
        ((a * B : Nat) : Real) := by field_simp
    nlinarith
  have hend : norm (scaledWindow f a D (B - 1)) <= norm (f 0) + 4 * (L : Real) := by
    have hi : B - 1 + 1 = B := Nat.sub_add_cancel hB
    have hx0 : 0 <= ((a * B : Nat) : Real) / (D : Real) :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hDR)
    have hnorm := hf.norm_sub_le (((a * B : Nat) : Real) / (D : Real)) 0
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hx0] at hnorm
    have hleft := mul_le_mul_of_nonneg_left hcap hL
    have htriangle := norm_add_le
      (f (((a * B : Nat) : Real) / (D : Real)) - f 0) (f 0)
    have he : f (((a * B : Nat) : Real) / (D : Real)) - f 0 + f 0 =
        f (((a * B : Nat) : Real) / (D : Real)) := by ring
    rw [he] at htriangle
    unfold scaledWindow
    rw [hi]
    linarith
  have hinc : forall i : Nat,
      norm (scaledWindow f a D (i + 1) - scaledWindow f a D i) <=
        (L : Real) * ((a : Real) / (D : Real)) := by
    intro i
    have hnorm := hf.norm_sub_le
      (((a * ((i + 1) + 1) : Nat) : Real) / (D : Real))
      (((a * (i + 1) : Nat) : Real) / (D : Real))
    have he : (((a * ((i + 1) + 1) : Nat) : Real) / (D : Real)) -
        (((a * (i + 1) : Nat) : Real) / (D : Real)) =
        (a : Real) / (D : Real) := by push_cast; ring
    rw [he, Real.norm_eq_abs, abs_of_nonneg hstep] at hnorm
    exact hnorm
  have hlength : ((B - 1 : Nat) : Real) * ((a : Real) / (D : Real)) <= 4 := by
    calc
      _ <= (B : Real) * ((a : Real) / (D : Real)) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le B 1)) hstep
      _ = ((a * B : Nat) : Real) / (D : Real) := by push_cast; ring
      _ <= 4 := hcap
  have hsum : (Finset.range (B - 1)).sum (fun i =>
      norm (scaledWindow f a D (i + 1) - scaledWindow f a D i)) <= 4 * (L : Real) := by
    calc
      _ <= (Finset.range (B - 1)).sum (fun _ =>
          (L : Real) * ((a : Real) / (D : Real))) :=
        Finset.sum_le_sum (fun i _ => hinc i)
      _ = (L : Real) * (((B - 1 : Nat) : Real) *
          ((a : Real) / (D : Real))) := by simp; ring
      _ <= (L : Real) * 4 := mul_le_mul_of_nonneg_left hlength hL
      _ = _ := by ring
  exact (add_le_add hend hsum).trans_eq (by ring)

/-- Apply the low-product estimate at N=4D,T=D with the sampled-window variation discharged. -/
theorem scaled_low_native_packet_subpower (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
      chi ^ 3 = 1 ->
      forall (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H D : Nat), 0 < H -> 0 < D ->
      forall (f : Real -> Complex) (L : NNReal), LipschitzWith L f ->
      norm (lowNativePacket chi G H (4 * D) D (fun a => scaledWindow f a D)) <=
        C * (((q * 3 : Nat) : Real) ^ 2) * (norm (f 0) + 8 * (L : Real)) ^ 2 *
          ((H * (4 * D) : Nat) : Real) ^ eps *
            ((4 * D : Nat) : Real) * (D.sqrt : Real) := by
  choose C hC hc using low_native_packet_subpower eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro q inst chi hchi G hG H D hH hD f L hf
  exact hc chi hchi G hG H (4 * D) D hH (by omega)
    (fun a => scaledWindow f a D) (norm (f 0) + 8 * (L : Real)) (by positivity)
    (fun a ha => scaled_window_variation f L hf D a hD
      (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2)

/-- The nonnegative first-derivative seminorm of the full combined Schwartz window. -/
def schwartzLipschitzConstant (f : SchwartzMap Real Complex) : NNReal :=
  Subtype.mk ((SchwartzMap.seminorm Real 0 1) f)
    (NonnegHomClass.apply_nonneg _ _)

/-- The first Schwartz seminorm supplies the required global Lipschitz constant. -/
theorem schwartz_lipschitz (f : SchwartzMap Real Complex) :
    LipschitzWith (schwartzLipschitzConstant f) (f : Real -> Complex) := by
  apply lipschitzWith_of_nnnorm_fderiv_le f.differentiable
  intro x
  apply NNReal.coe_le_coe.mp
  change norm (fderiv Real (f : Real -> Complex) x) <= (SchwartzMap.seminorm Real 0 1) f
  have h := SchwartzMap.norm_iteratedFDeriv_le_seminorm Real f 1 x
  rw [norm_iteratedFDeriv_one] at h
  exact h

/-- An unconditional target-sized bound for the actual Schwartz-window low native sector, uniform in G. -/
theorem schwartz_low_native_packet_subpower (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
      chi ^ 3 = 1 ->
      forall (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H D : Nat), 0 < H -> 0 < D ->
      forall f : SchwartzMap Real Complex,
      norm (lowNativePacket chi G H (4 * D) D (fun a => scaledWindow f a D)) <=
        C * (((q * 3 : Nat) : Real) ^ 2) *
          (norm (f 0) + 8 * (schwartzLipschitzConstant f : Real)) ^ 2 *
          ((H * (4 * D) : Nat) : Real) ^ eps *
            ((4 * D : Nat) : Real) * (D.sqrt : Real) := by
  choose C hC hc using scaled_low_native_packet_subpower eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro q inst chi hchi G hG H D hH hD f
  exact hc chi hchi G hG H D hH hD f (schwartzLipschitzConstant f) (schwartz_lipschitz f)

end PrimeFactorOscillations.CarmichaelNativeLowSector

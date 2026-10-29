/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNativeHyperbola
import PrimeFactorOscillations.Assembly.CarmichaelSquarepartCancellation

/-!
# Squarefree rational core of the signed high native packet

The projected terms retain the original rational indices a*b and c*d,
all product amplifiers, cross masks and the complete complex window.
The nonsquarefree high contribution is jointly bounded at
D^(3/2+epsilon) through its exact cancellation against the two low sectors.
All divisor and physical rescaled-variation budgets are discharged.
No improved bound for the retained squarefree high core is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

noncomputable section
namespace PrimeFactorOscillations.CarmichaelSquarefreeHighRemainder
open scoped Classical
open CarmichaelNativeLowSector CarmichaelNativeHyperbola
open CarmichaelCompanionCancellation CarmichaelCompanionMasks
open CarmichaelSquarepartCancellation

/-- The actual rational kernel projected at both full rational inputs. -/
def squarefreeKernel (G : Finset Nat) (H : Nat) (W : Nat -> Complex)
    (n m : Nat) : Complex :=
  if Squarefree n /\ Squarefree m then rationalKernel G H W n m else 0

/-- A native term with squarefree full rational inputs, before any norm. -/
def squarefreeNativeTerm {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H N : Nat) (W : Nat -> Complex) (a c : Nat) : Complex :=
  (nativeCoefficient chi a * star (nativeCoefficient chi c)) *
    (Finset.Icc 1 (N / a)).sum (fun b =>
      (Finset.Icc 1 (N / c)).sum (fun d =>
        (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
          star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3)))) *
            squarefreeKernel G H W (a * b) (c * d)))

/-- Every original low native pair with its full squarefree rational projection. -/
def lowSquarefreePacket {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H N T : Nat) (W : Nat -> Complex) : Complex :=
  (Finset.Icc 1 N).sum (fun a => (Finset.Icc 1 N).sum (fun c =>
    if a * c <= T then squarefreeNativeTerm chi G H N W a c else 0))

/-- The original high region, without dropping any squarefree projected pair. -/
def highSquarefreePacket {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H N T : Nat) (W : Nat -> Complex) : Complex :=
  (Finset.Icc 1 N).sum (fun a => (Finset.Icc 1 N).sum (fun c =>
    if T < a * c then squarefreeNativeTerm chi G H N W a c else 0))

private theorem reciprocal_sqrt_prefix (N : Nat) :
    (Finset.Icc 1 N).sum (fun n => 1 / Real.sqrt (n : Real)) <=
      2 * Real.sqrt (N : Real) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsets : Finset.Icc 1 (N + 1) =
        insert (N + 1) (Finset.Icc 1 N) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : Not (Membership.mem (Finset.Icc 1 N) (N + 1)) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsets, Finset.sum_insert hnot]
    have hx : (Real.sqrt (N : Real)) ^ 2 = N :=
      Real.sq_sqrt (Nat.cast_nonneg N)
    have hy : (Real.sqrt ((N + 1 : Nat) : Real)) ^ 2 = (N : Real) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Real.sq_sqrt (Nat.cast_nonneg (N + 1))
    have hypos : 0 < Real.sqrt ((N + 1 : Nat) : Real) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.succ_pos N)
    have hid : (1 / Real.sqrt ((N + 1 : Nat) : Real)) *
        Real.sqrt ((N + 1 : Nat) : Real) = 1 := by
      field_simp [ne_of_gt hypos]
    have hmul : (1 / Real.sqrt ((N + 1 : Nat) : Real)) *
        Real.sqrt ((N + 1 : Nat) : Real) <=
        (2 * (Real.sqrt ((N + 1 : Nat) : Real) - Real.sqrt (N : Real))) *
          Real.sqrt ((N + 1 : Nat) : Real) := by
      nlinarith [sq_nonneg
        (Real.sqrt ((N + 1 : Nat) : Real) - Real.sqrt (N : Real))]
    have hstep : 1 / Real.sqrt ((N + 1 : Nat) : Real) <=
        2 * (Real.sqrt ((N + 1 : Nat) : Real) - Real.sqrt (N : Real)) := by
      by_contra h
      have hbad := mul_lt_mul_of_pos_right (lt_of_not_ge h) hypos
      exact (not_lt_of_ge hmul) hbad
    linarith
private theorem mobius_zero_of_nonsquarefree (n : Nat) (h : Not (Squarefree n)) :
    (ArithmeticFunction.moebius n : Complex) = 0 := by
  have hi : ArithmeticFunction.moebius n ^ 2 = 0 := by
    rw [ArithmeticFunction.moebius_sq, ite_eq_right h]
  have hz : ArithmeticFunction.moebius n = 0 := by nlinarith
  exact_mod_cast hz

/-- The full native projection equals the original rational Mobius unit exactly. -/
theorem rational_unit_squarefree_native {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H N : Nat) (W : Nat -> Complex) :
    rationalUnit chi G H N W =
      (Finset.Icc 1 N).sum (fun a => (Finset.Icc 1 N).sum
        (fun c => squarefreeNativeTerm chi G H N W a c)) := by
  have hproject : rationalUnit chi G H N W =
      (Finset.Icc 1 N).sum (fun n =>
        (chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex)) *
          (Finset.Icc 1 N).sum (fun m =>
            star (chi (m : ZMod q) * (ArithmeticFunction.moebius m : Complex)) *
              squarefreeKernel G H W n m)) := by
    unfold rationalUnit
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hn : Squarefree n
    . by_cases hm : Squarefree m
      . rw [squarefreeKernel, ite_eq_left (And.intro hn hm)]
      . simp only [mobius_zero_of_nonsquarefree m hm, mul_zero, star_zero, zero_mul]
    . simp only [mobius_zero_of_nonsquarefree n hn, mul_zero, zero_mul]
  rw [hproject, native_bilinear_hyperbola chi N]
  rfl

/-- The projected low and high sectors partition every supported native pair once. -/
theorem squarefree_low_high_split {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H N T : Nat) (W : Nat -> Complex) :
    rationalUnit chi G H N W =
      lowSquarefreePacket chi G H N T W + highSquarefreePacket chi G H N T W := by
  rw [rational_unit_squarefree_native]
  unfold lowSquarefreePacket highSquarefreePacket
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : a * c <= T
  . rw [ite_eq_left h, ite_eq_right (Nat.not_lt_of_ge h), add_zero]
  . rw [ite_eq_right h, ite_eq_left (Nat.lt_of_not_ge h), zero_add]

/-- All nonsquarefree high contributions equal the signed difference of the two low sectors. -/
theorem nonsquarefree_high_cancellation {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H N T : Nat) (W : Nat -> Complex) :
    highNativePacket chi G H N T (productWindow W) -
        highSquarefreePacket chi G H N T W =
      lowSquarefreePacket chi G H N T W -
        lowNativePacket chi G H N T (productWindow W) := by
  have hfull := full_native_low_high_split chi G H N T (productWindow W)
  have hsf := squarefree_low_high_split chi G H N T W
  rw [<- rational_unit_native_packet chi G H N W] at hfull
  calc
    _ = (lowNativePacket chi G H N T (productWindow W) +
        highNativePacket chi G H N T (productWindow W)) -
          lowNativePacket chi G H N T (productWindow W) -
            highSquarefreePacket chi G H N T W := by ring
    _ = _ := by rw [<- hfull, hsf]; ring
private theorem squarefree_window_value (w : Nat -> Complex) (n : Nat) (hn : 0 < n) :
    squarefreeWindow w (n - 1) = if Squarefree n then w (n - 1) else 0 := by
  have hi : n - 1 + 1 = n := Nat.sub_add_cancel hn
  by_cases hs : Squarefree n
  . have hInt : ArithmeticFunction.moebius n ^ 2 = 1 := by
      rw [ArithmeticFunction.moebius_sq, ite_eq_left hs]
    have hComplex : (ArithmeticFunction.moebius n : Complex) ^ 2 = 1 := by
      exact_mod_cast hInt
    simp only [squarefreeWindow, hi, hComplex, one_mul, ite_eq_left hs]
  . simp only [squarefreeWindow, hi, mobius_zero_of_nonsquarefree n hs,
      zero_pow (by decide : Not (2 = 0)), zero_mul, ite_eq_right hs]

private theorem squarefree_masked_value {q : Nat}
    (psi : DirichletCharacter Complex q) (G : Finset Nat)
    (K a b : Nat) (hb : 0 < b) (W : Nat -> Complex) :
    squarefreeWindow (amplifiedWindow G a (productWindow W a)) (b - 1) *
        maskedCharacter psi K b =
      if Squarefree b /\ Nat.Coprime b K then
        ((AllPrimeMask.amplifier G (a * b) : Complex) * W (a * b)) *
          psi (b : ZMod q) else 0 := by
  have hi : b - 1 + 1 = b := Nat.sub_add_cancel hb
  rw [squarefree_window_value _ b hb]
  unfold maskedCharacter
  by_cases hs : Squarefree b
  . by_cases hK : Nat.Coprime b K
    . rw [ite_eq_left hs, ite_eq_left hK, ite_eq_left (And.intro hs hK)]
      simp only [amplifiedWindow, productWindow, hi]
    . have hbad : Not (Squarefree b /\ Nat.Coprime b K) := fun h => hK h.2
      simp only [ite_eq_left hs, ite_eq_right hK, mul_zero, ite_eq_right hbad]
  . have hbad : Not (Squarefree b /\ Nat.Coprime b K) := fun h => hs h.1
    simp only [ite_eq_right hs, zero_mul, ite_eq_right hbad]

private theorem squarefree_pair_conditions (H a c b d : Nat) :
    (Squarefree (a * b) /\ Squarefree (c * d) /\ unitGood H (a * b) (c * d)) <->
      (Squarefree a /\ Squarefree c /\ unitGood H a c) /\
        Nat.Coprime b d /\
        (Squarefree b /\ Nat.Coprime b (H * a * c)) /\
        (Squarefree d /\ Nat.Coprime d (H * a * c)) := by
  unfold unitGood
  simp only [Nat.squarefree_mul_iff, Nat.coprime_mul_iff_right, Nat.coprime_comm,
    and_assoc, and_comm, and_left_comm]

private theorem squarefree_product_kernel {q : Nat}
    (psi : DirichletCharacter Complex q) (G : Finset Nat)
    (H a c b d : Nat) (hb : 0 < b) (hd : 0 < d) (W : Nat -> Complex) :
    (psi (b : ZMod q) * star (psi (d : ZMod q))) *
        squarefreeKernel G H W (a * b) (c * d) =
      if Squarefree a /\ Squarefree c /\ unitGood H a c then
        (if Nat.Coprime b d then
          (squarefreeWindow (amplifiedWindow G a (productWindow W a)) (b - 1) *
            maskedCharacter psi (H * a * c) b) *
          star (squarefreeWindow (amplifiedWindow G c (productWindow W c)) (d - 1) *
            maskedCharacter psi (H * a * c) d)
        else 0)
      else 0 := by
  have hiff := squarefree_pair_conditions H a c b d
  by_cases hfull : Squarefree (a * b) /\ Squarefree (c * d) /\
      unitGood H (a * b) (c * d)
  . have hr := hiff.mp hfull
    rw [squarefreeKernel, ite_eq_left (And.intro hfull.1 hfull.2.1),
      rationalKernel, ite_eq_left hfull.2.2, ite_eq_left hr.1,
      ite_eq_left hr.2.1, squarefree_masked_value psi G (H * a * c) a b hb W,
      squarefree_masked_value psi G (H * a * c) c d hd W,
      ite_eq_left hr.2.2.1, ite_eq_left hr.2.2.2]
    simp only [star_mul]
    ring
  . have hz : squarefreeKernel G H W (a * b) (c * d) = 0 := by
      by_cases hs : Squarefree (a * b) /\ Squarefree (c * d)
      . have hg : Not (unitGood H (a * b) (c * d)) :=
          fun h => hfull (And.intro hs.1 (And.intro hs.2 h))
        rw [squarefreeKernel, ite_eq_left hs, rationalKernel, ite_eq_right hg]
      . rw [squarefreeKernel, ite_eq_right hs]
    rw [hz, mul_zero]
    symm
    by_cases hO : Squarefree a /\ Squarefree c /\ unitGood H a c
    . rw [ite_eq_left hO]
      by_cases hbd : Nat.Coprime b d
      . rw [ite_eq_left hbd, squarefree_masked_value psi G (H * a * c) a b hb W,
          squarefree_masked_value psi G (H * a * c) c d hd W]
        by_cases hbK : Squarefree b /\ Nat.Coprime b (H * a * c)
        . rw [ite_eq_left hbK]
          by_cases hdK : Squarefree d /\ Nat.Coprime d (H * a * c)
          . exact False.elim (hfull
              (hiff.mpr (And.intro hO (And.intro hbd (And.intro hbK hdK)))))
          . simp only [ite_eq_right hdK, star_zero, mul_zero]
        . simp only [ite_eq_right hbK, zero_mul]
      . exact ite_eq_right hbd
    . exact ite_eq_right hO

/-- The projected native row uses squarefree companions and both full cross masks. -/
theorem squarefree_native_term_factorization {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H N a c : Nat) (W : Nat -> Complex) :
    squarefreeNativeTerm chi G H N W a c =
      if Squarefree a /\ Squarefree c /\ unitGood H a c then
        (nativeCoefficient chi a * star (nativeCoefficient chi c)) *
          squarefreeCompanionPacket (OAI.ShortDraftHeckeBridge.baseChangeChar chi)
            G (H * a * c) (H * a * c) a c (N / a) (N / c)
            (productWindow W a) (productWindow W c)
      else 0 := by
  let psi := OAI.ShortDraftHeckeBridge.baseChangeChar chi
  unfold squarefreeNativeTerm
  by_cases hO : Squarefree a /\ Squarefree c /\ unitGood H a c
  . rw [ite_eq_left hO]
    congr 1
    unfold squarefreeCompanionPacket weightedCompanionPacket
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    have h := squarefree_product_kernel psi G H a c b d
      (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hd).1 W
    rw [ite_eq_left hO] at h
    exact h
  . rw [ite_eq_right hO]
    have hz : (Finset.Icc 1 (N / a)).sum (fun b =>
        (Finset.Icc 1 (N / c)).sum (fun d =>
          (psi (b : ZMod (q * 3)) * star (psi (d : ZMod (q * 3)))) *
            squarefreeKernel G H W (a * b) (c * d))) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      apply Finset.sum_eq_zero
      intro d hd
      have h := squarefree_product_kernel psi G H a c b d
        (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hd).1 W
      rw [ite_eq_right hO] at h
      exact h
    rw [hz, mul_zero]
private theorem sqrt_companion_cutoffs (N a c : Nat) (ha : 0 < a) (hc : 0 < c) :
    Real.sqrt (((N / a : Nat) : Real) * ((N / c : Nat) : Real)) <=
      (N : Real) / Real.sqrt ((a * c : Nat) : Real) := by
  have hleft : ((N / a : Nat) : Real) * (a : Real) <= N := by
    exact_mod_cast Nat.div_mul_le_self N a
  have hright : ((N / c : Nat) : Real) * (c : Real) <= N := by
    exact_mod_cast Nat.div_mul_le_self N c
  have hprod : (((N / a : Nat) : Real) * ((N / c : Nat) : Real)) *
      ((a * c : Nat) : Real) <= (N : Real) ^ 2 := by
    calc
      _ = (((N / a : Nat) : Real) * (a : Real)) *
          (((N / c : Nat) : Real) * (c : Real)) := by push_cast; ring
      _ <= (N : Real) * (N : Real) :=
        mul_le_mul hleft hright (by positivity) (Nat.cast_nonneg N)
      _ = _ := by ring
  have hs := Real.sqrt_le_sqrt hprod
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg N)] at hs
  have hpos : 0 < Real.sqrt ((a * c : Nat) : Real) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.mul_pos ha hc))
  have he : ((N : Real) / Real.sqrt ((a * c : Nat) : Real)) *
      Real.sqrt ((a * c : Nat) : Real) = N := by
    field_simp [ne_of_gt hpos]
  by_contra h
  have hbad := mul_lt_mul_of_pos_right (lt_of_not_ge h) hpos
  rw [he] at hbad
  exact (not_lt_of_ge hs) hbad

private theorem sqrt_divisor_row (T a : Nat) (ha : 0 < a) :
    (1 / Real.sqrt (a : Real)) * (2 * Real.sqrt ((T / a : Nat) : Real)) <=
      2 * Real.sqrt (T : Real) / (a : Real) := by
  have har : 0 < (a : Real) := Nat.cast_pos.mpr ha
  have hroot : 0 < Real.sqrt (a : Real) := Real.sqrt_pos.mpr har
  have hfloor : ((T / a : Nat) : Real) * (a : Real) <= T := by
    exact_mod_cast Nat.div_mul_le_self T a
  have hs := Real.sqrt_le_sqrt hfloor
  rw [Real.sqrt_mul (Nat.cast_nonneg (T / a))] at hs
  have he : ((1 / Real.sqrt (a : Real)) *
      (2 * Real.sqrt ((T / a : Nat) : Real))) * (a : Real) =
        2 * (Real.sqrt ((T / a : Nat) : Real) * Real.sqrt (a : Real)) := by
    calc
      _ = ((1 / Real.sqrt (a : Real)) *
          (2 * Real.sqrt ((T / a : Nat) : Real))) *
            (Real.sqrt (a : Real)) ^ 2 := by rw [Real.sq_sqrt (le_of_lt har)]
      _ = _ := by field_simp [ne_of_gt hroot]
  have hf : (2 * Real.sqrt (T : Real) / (a : Real)) * (a : Real) =
      2 * Real.sqrt (T : Real) := by field_simp [ne_of_gt har]
  have hmul : ((1 / Real.sqrt (a : Real)) *
      (2 * Real.sqrt ((T / a : Nat) : Real))) * (a : Real) <=
        (2 * Real.sqrt (T : Real) / (a : Real)) * (a : Real) := by
    rw [he, hf]
    linarith
  by_contra h
  exact (not_lt_of_ge hmul) (mul_lt_mul_of_pos_right (lt_of_not_ge h) har)

private theorem reciprocal_sqrt_hyperbola (N T : Nat) :
    (Finset.Icc 1 N).sum (fun a => (Finset.Icc 1 N).sum (fun c =>
      if a * c <= T then 1 / Real.sqrt ((a * c : Nat) : Real) else 0)) <=
        2 * Real.sqrt (T : Real) * harmonicPrefix N := by
  let S := Finset.Icc 1 N
  have hrow (a : Nat) (haS : Membership.mem S a) :
      S.sum (fun c => if a * c <= T then
          1 / Real.sqrt ((a * c : Nat) : Real) else 0) <=
        2 * Real.sqrt (T : Real) / (a : Real) := by
    have ha : 0 < a := (Finset.mem_Icc.mp haS).1
    have hsub : S.filter (fun c => a * c <= T) <= Finset.Icc 1 (T / a) := by
      intro c hc
      have hm := Finset.mem_filter.mp hc
      apply Finset.mem_Icc.mpr
      refine And.intro (Finset.mem_Icc.mp hm.1).1 ?_
      apply (Nat.le_div_iff_mul_le ha).mpr
      simpa only [Nat.mul_comm] using hm.2
    have hprefix :
        (S.filter (fun c => a * c <= T)).sum (fun c => 1 / Real.sqrt (c : Real)) <=
          2 * Real.sqrt ((T / a : Nat) : Real) :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)).trans (reciprocal_sqrt_prefix (T / a))
    calc
      _ = (1 / Real.sqrt (a : Real)) *
          (S.filter (fun c => a * c <= T)).sum
            (fun c => 1 / Real.sqrt (c : Real)) := by
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hp : a * c <= T
        . rw [ite_eq_left hp, ite_eq_left hp, Nat.cast_mul,
            Real.sqrt_mul (Nat.cast_nonneg a)]
          field_simp
        . rw [ite_eq_right hp, ite_eq_right hp]
      _ <= (1 / Real.sqrt (a : Real)) *
          (2 * Real.sqrt ((T / a : Nat) : Real)) :=
        mul_le_mul_of_nonneg_left hprefix (by positivity)
      _ <= _ := sqrt_divisor_row T a ha
  have hsum : S.sum (fun a => 1 / (a : Real)) = harmonicPrefix N := by
    have hsets : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    change (Finset.Icc 1 N).sum (fun a => 1 / (a : Real)) = _
    rw [hsets]
    rfl
  calc
    _ <= S.sum (fun a => 2 * Real.sqrt (T : Real) / (a : Real)) :=
      Finset.sum_le_sum hrow
    _ = (2 * Real.sqrt (T : Real)) * S.sum (fun a => 1 / (a : Real)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [hsum]
/-- Squarefree character cancellation on one actual native projected row. -/
theorem squarefree_native_term_bound {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1)
    (G : Finset Nat) (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (H N a c : Nat) (hH : 0 < H) (ha : 0 < a) (hc : 0 < c)
    (haN : a <= N) (hcN : c <= N) (W : Nat -> Complex)
    (M V : Real) (hM : 0 <= M) (hV : 0 <= V)
    (hdiv : forall n, 0 < n -> n <= H * N ^ 2 -> (n.divisors.card : Real) <= M)
    (hvar : forall n, Membership.mem (Finset.Icc 1 N) n ->
      forall k, 0 < k -> k <= N ->
        windowVariation (dilatedWindow k (productWindow W n)) (N / n / k) <= V) :
    norm (squarefreeNativeTerm chi G H N W a c) <=
      (((q * 3 : Nat) : Real) ^ 2 * M ^ 6 * V ^ 2 *
        (harmonicPrefix N) ^ 5) *
          ((N : Real) / Real.sqrt ((a * c : Nat) : Real)) := by
  have hN : 0 < N := ha.trans_le haN
  have hNsq : N ^ 2 <= H * N ^ 2 := by
    simpa only [Nat.succ_eq_add_one, Nat.zero_add, Nat.one_mul] using
      Nat.mul_le_mul_right (N ^ 2) (Nat.succ_le_iff.mpr hH)
  have hNN : N <= H * N ^ 2 := by
    apply le_trans _ hNsq
    simpa only [Nat.succ_eq_add_one, Nat.zero_add, Nat.one_mul, pow_two] using
      Nat.mul_le_mul_right N (Nat.succ_le_iff.mpr hN)
  have hHarm : 0 <= harmonicPrefix N :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hK : 0 < H * a * c := Nat.mul_pos (Nat.mul_pos hH ha) hc
  have hcoef (n : Nat) (hn : 0 < n) (hnN : n <= N) :
      norm (nativeCoefficient chi n) <= M := by
    calc
      _ <= (n.divisors.card : Real) := by
        unfold nativeCoefficient
        rw [OAI.ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff chi n
          (Nat.ne_of_gt hn)]
        exact pair_inverse_coeff_divisor_bound chi
          (OAI.ShortDraftHeckeBridge.baseChangeChar chi) n
      _ <= M := hdiv n hn (hnN.trans hNN)
  let Q : Real := ((q * 3 : Nat) : Real)
  let Z : Real := M * (harmonicPrefix N) ^ 2 * V * (M * Q)
  have hZ : 0 <= Z := by dsimp only [Z, Q]; positivity
  have hmask (k : Nat) (hk : k <= N / a) :
      (H * a * c) * k <= H * N ^ 2 := by
    have hak : a * k <= N := by
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hk
    calc
      _ = (H * c) * (a * k) := by ring
      _ <= (H * N) * N := Nat.mul_le_mul (Nat.mul_le_mul_left H hcN) hak
      _ = _ := by ring
  have hleft : forall k, Membership.mem (Finset.Ioc 0 (N / a)) k ->
      companionCap (q * 3) ((H * a * c) * k) (a * k) ((N / a) / k)
        (dilatedWindow k (productWindow W a)) <= Z := by
    intro k hk
    have hkpos := (Finset.mem_Ioc.mp hk).1
    have hkB := (Finset.mem_Ioc.mp hk).2
    have hkN := hkB.trans (Nat.div_le_self N a)
    have hak : a * k <= N := by
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hkB
    exact cap_bound (q * 3) ((H * a * c) * k) (a * k) ((N / a) / k)
      N (dilatedWindow k (productWindow W a)) M V hM hV
      ((Nat.div_le_self _ _).trans (Nat.div_le_self _ _))
      (hdiv (a * k) (Nat.mul_pos ha hkpos) (hak.trans hNN))
      (hdiv ((H * a * c) * k) (Nat.mul_pos hK hkpos) (hmask k hkB))
      (hvar a (Finset.mem_Icc.mpr (And.intro ha haN)) k hkpos hkN)
  have hright : forall k, Membership.mem (Finset.Ioc 0 (N / a)) k ->
      companionCap (q * 3) ((H * a * c) * k) (c * k) ((N / c) / k)
        (dilatedWindow k (productWindow W c)) <= Z := by
    intro k hk
    have hkpos := (Finset.mem_Ioc.mp hk).1
    have hkB := (Finset.mem_Ioc.mp hk).2
    have hkN := hkB.trans (Nat.div_le_self N a)
    have hck : c * k <= H * N ^ 2 :=
      (show c * k <= N ^ 2 by
        simpa only [pow_two] using Nat.mul_le_mul hcN hkN).trans hNsq
    exact cap_bound (q * 3) ((H * a * c) * k) (c * k) ((N / c) / k)
      N (dilatedWindow k (productWindow W c)) M V hM hV
      ((Nat.div_le_self _ _).trans (Nat.div_le_self _ _))
      (hdiv (c * k) (Nat.mul_pos hc hkpos) hck)
      (hdiv ((H * a * c) * k) (Nat.mul_pos hK hkpos) (hmask k hkB))
      (hvar c (Finset.mem_Icc.mpr (And.intro hc hcN)) k hkpos hkN)
  have hpacket := squarefree_coprime_harmonic_bound
    (OAI.ShortDraftHeckeBridge.baseChangeChar chi) (cubic_companion_ne_one chi hchi)
    G hG (H * a * c) (H * a * c) a c (N / a) (N / c) hK hK ha hc
    (productWindow W a) (productWindow W c) Z Z hZ hZ hleft hright
  have hp :
      norm (squarefreeCompanionPacket (OAI.ShortDraftHeckeBridge.baseChangeChar chi)
        G (H * a * c) (H * a * c) a c (N / a) (N / c)
        (productWindow W a) (productWindow W c)) <=
        Z * Z * Real.sqrt (((N / a : Nat) : Real) * ((N / c : Nat) : Real)) *
          harmonicPrefix N :=
    hpacket.trans (mul_le_mul_of_nonneg_left
      (harmonic_prefix_mono (Nat.div_le_self N a)) (by positivity))
  rw [squarefree_native_term_factorization]
  by_cases hO : Squarefree a /\ Squarefree c /\ unitGood H a c
  . rw [ite_eq_left hO, norm_mul, norm_mul, norm_star]
    calc
      _ <= (M * M) *
          (Z * Z * Real.sqrt (((N / a : Nat) : Real) * ((N / c : Nat) : Real)) *
            harmonicPrefix N) :=
        mul_le_mul
          (mul_le_mul (hcoef a ha haN) (hcoef c hc hcN) (norm_nonneg _) hM)
          hp (norm_nonneg _) (by positivity)
      _ = (Q ^ 2 * M ^ 6 * V ^ 2 * (harmonicPrefix N) ^ 5) *
          Real.sqrt (((N / a : Nat) : Real) * ((N / c : Nat) : Real)) := by
        dsimp only [Z]
        ring
      _ <= _ := mul_le_mul_of_nonneg_left (sqrt_companion_cutoffs N a c ha hc)
        (by dsimp only [Q]; positivity)
  . rw [ite_eq_right hO, norm_zero]
    positivity

/-- A target-sized low projected packet, with explicit divisor and rescaled-variation budgets. -/
theorem low_squarefree_native_packet_bound {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1)
    (G : Finset Nat) (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (H N T : Nat) (hH : 0 < H) (W : Nat -> Complex)
    (M V : Real) (hM : 0 <= M) (hV : 0 <= V)
    (hdiv : forall n, 0 < n -> n <= H * N ^ 2 -> (n.divisors.card : Real) <= M)
    (hvar : forall n, Membership.mem (Finset.Icc 1 N) n ->
      forall k, 0 < k -> k <= N ->
        windowVariation (dilatedWindow k (productWindow W n)) (N / n / k) <= V) :
    norm (lowSquarefreePacket chi G H N T W) <=
      2 * (((q * 3 : Nat) : Real) ^ 2) * M ^ 6 * V ^ 2 *
        (harmonicPrefix N) ^ 6 * (N : Real) * Real.sqrt (T : Real) := by
  let K : Real := (((q * 3 : Nat) : Real) ^ 2) * M ^ 6 * V ^ 2 *
    (harmonicPrefix N) ^ 5
  have hHarm : 0 <= harmonicPrefix N :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hK : 0 <= K := by dsimp only [K]; positivity
  calc
    _ <= (K * (N : Real)) *
        (Finset.Icc 1 N).sum (fun a => (Finset.Icc 1 N).sum (fun c =>
          if a * c <= T then 1 / Real.sqrt ((a * c : Nat) : Real) else 0)) := by
      unfold lowSquarefreePacket
      rw [Finset.mul_sum]
      calc
        _ <= (Finset.Icc 1 N).sum (fun a =>
            norm ((Finset.Icc 1 N).sum (fun c =>
              if a * c <= T then squarefreeNativeTerm chi G H N W a c else 0))) :=
          norm_sum_le _ _
        _ <= _ := by
          apply Finset.sum_le_sum
          intro a ha
          rw [Finset.mul_sum]
          calc
            _ <= (Finset.Icc 1 N).sum (fun c =>
                norm (if a * c <= T then squarefreeNativeTerm chi G H N W a c else 0)) :=
              norm_sum_le _ _
            _ <= _ := by
              apply Finset.sum_le_sum
              intro c hc
              by_cases hp : a * c <= T
              . rw [ite_eq_left hp, ite_eq_left hp]
                calc
                  _ <= K * ((N : Real) / Real.sqrt ((a * c : Nat) : Real)) :=
                    squarefree_native_term_bound chi hchi G hG H N a c hH
                      (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hc).1
                      (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hc).2
                      W M V hM hV hdiv hvar
                  _ = _ := by ring
              . simp only [ite_eq_right hp, norm_zero, mul_zero]
                exact le_refl 0
    _ <= (K * (N : Real)) * (2 * Real.sqrt (T : Real) * harmonicPrefix N) :=
      mul_le_mul_of_nonneg_left (reciprocal_sqrt_hyperbola N T) (by positivity)
    _ = _ := by dsimp only [K]; ring
/-- The complete projected low sector has uniform subpower dependence on all masks. -/
theorem low_squarefree_native_packet_subpower (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
      chi ^ 3 = 1 ->
      forall (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H N T : Nat), 0 < H -> 0 < N ->
      forall (W : Nat -> Complex) (V : Real), 0 <= V ->
      (forall n, Membership.mem (Finset.Icc 1 N) n ->
        forall k, 0 < k -> k <= N ->
          windowVariation (dilatedWindow k (productWindow W n)) (N / n / k) <= V) ->
      norm (lowSquarefreePacket chi G H N T W) <=
        C * (((q * 3 : Nat) : Real) ^ 2) * V ^ 2 *
          ((H * N : Nat) : Real) ^ eps * (N : Real) * Real.sqrt (T : Real) := by
  choose A hA ha using QuadraticDivisorMean.divisor_card_subpower
    (eps / 24) (by linarith)
  choose B hB hb using harmonic_subpower (eps / 12) (by linarith)
  refine Exists.intro (2 * A ^ 6 * B ^ 6) (And.intro (by positivity) ?_)
  intro q inst chi hchi G hG H N T hH hN W V hV hvar
  have hR : 0 < ((H * N : Nat) : Real) := Nat.cast_pos.mpr (Nat.mul_pos hH hN)
  have hNN : N <= H * N := by
    simpa only [Nat.succ_eq_add_one, Nat.zero_add, Nat.one_mul] using
      Nat.mul_le_mul_right N (Nat.succ_le_iff.mpr hH)
  have hsize : H * N ^ 2 <= (H * N) ^ 2 := by
    calc
      _ <= H * (H * N ^ 2) := by
        simpa only [Nat.succ_eq_add_one, Nat.zero_add, Nat.one_mul] using
          Nat.mul_le_mul_right (H * N ^ 2) (Nat.succ_le_iff.mpr hH)
      _ = _ := by ring
  let M : Real := A * ((H * N : Nat) : Real) ^ (eps / 12)
  have hM : 0 <= M := by dsimp only [M]; positivity
  have he2 : (((H * N : Nat) : Real) ^ 2) ^ (eps / 24) =
      ((H * N : Nat) : Real) ^ (eps / 12) := by
    rw [<- Real.rpow_natCast _ 2, <- Real.rpow_mul (le_of_lt hR)]
    congr 1
    norm_num; ring
  have hdiv : forall n, 0 < n -> n <= H * N ^ 2 ->
      (n.divisors.card : Real) <= M := by
    intro n hn hnBound
    have hnR : (n : Real) <= ((H * N : Nat) : Real) ^ 2 := by
      exact_mod_cast hnBound.trans hsize
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg n) hnR
      (show 0 <= eps / 24 by linarith)
    rw [he2] at hp
    exact (ha n hn).trans (mul_le_mul_of_nonneg_left hp (le_of_lt hA))
  have hh : harmonicPrefix N <= B * ((H * N : Nat) : Real) ^ (eps / 12) :=
    (hb N).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hNN) (by linarith))
      (le_of_lt hB))
  have hh0 : 0 <= harmonicPrefix N :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hh6 : (harmonicPrefix N) ^ 6 <=
      (B * ((H * N : Nat) : Real) ^ (eps / 12)) ^ 6 := by
    gcongr
  have he6 : (((H * N : Nat) : Real) ^ (eps / 12)) ^ 6 =
      ((H * N : Nat) : Real) ^ (eps / 2) := by
    rw [<- Real.rpow_natCast _ 6, <- Real.rpow_mul (le_of_lt hR)]
    congr 1
    norm_num; ring
  have hmass : M ^ 6 * (harmonicPrefix N) ^ 6 <=
      A ^ 6 * B ^ 6 * ((H * N : Nat) : Real) ^ eps := by
    calc
      _ <= M ^ 6 * (B * ((H * N : Nat) : Real) ^ (eps / 12)) ^ 6 :=
        mul_le_mul_of_nonneg_left hh6 (pow_nonneg hM _)
      _ = A ^ 6 * B ^ 6 *
          (((H * N : Nat) : Real) ^ (eps / 2) *
            ((H * N : Nat) : Real) ^ (eps / 2)) := by
        dsimp only [M]
        simp only [mul_pow, he6]
        ring
      _ = _ := by
        rw [<- Real.rpow_add hR, show eps / 2 + eps / 2 = eps by ring]
  have hlow := low_squarefree_native_packet_bound chi hchi G hG H N T hH
    W M V hM hV hdiv hvar
  calc
    _ <= 2 * (((q * 3 : Nat) : Real) ^ 2) * M ^ 6 * V ^ 2 *
        (harmonicPrefix N) ^ 6 * (N : Real) * Real.sqrt (T : Real) := hlow
    _ = (2 * (((q * 3 : Nat) : Real) ^ 2) * V ^ 2 * (N : Real) *
        Real.sqrt (T : Real)) * (M ^ 6 * (harmonicPrefix N) ^ 6) := by ring
    _ <= (2 * (((q * 3 : Nat) : Real) ^ 2) * V ^ 2 * (N : Real) *
        Real.sqrt (T : Real)) *
          (A ^ 6 * B ^ 6 * ((H * N : Nat) : Real) ^ eps) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

private theorem linear_window_dilate (f : Real -> Complex) (a D k : Nat)
    (hk : 0 < k) :
    dilatedWindow k (scaledWindow f a D) = scaledWindow f (a * k) D := by
  funext i
  have hi : k * (i + 1) - 1 + 1 = k * (i + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos hk (Nat.succ_pos i))
  unfold dilatedWindow scaledWindow
  rw [hi, Nat.mul_assoc]

private theorem linear_window_rescaled_variation (f : SchwartzMap Real Complex)
    (D a k : Nat) (hD : 0 < D) (ha : 0 < a) (hk : 0 < k) :
    windowVariation (dilatedWindow k (scaledWindow f a D)) ((4 * D) / a / k) <=
      squareWindowBudget f := by
  rw [linear_window_dilate f a D k hk, Nat.div_div_eq_div_mul]
  have hsup (x : Real) : norm (f x) <= (SchwartzMap.seminorm Real 0 0) f := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.norm_iteratedFDeriv_le_seminorm Real f 0 x
  have hL : 0 <= (schwartzLipschitzConstant f : Real) :=
    (schwartzLipschitzConstant f).coe_nonneg
  by_cases hcap : a * k <= 4 * D
  . exact (scaled_window_variation f (schwartzLipschitzConstant f)
      (schwartz_lipschitz f) D (a * k) hD (Nat.mul_pos ha hk) hcap).trans
        (by unfold squareWindowBudget; linarith [hsup 0])
  . have hz : (4 * D) / (a * k) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_not_ge hcap)
    rw [hz]
    simp only [windowVariation, Nat.zero_sub, Finset.range_zero, Finset.sum_empty, add_zero]
    have hbound : norm (scaledWindow f (a * k) D 0) <=
        (SchwartzMap.seminorm Real 0 0) f :=
      hsup ((((a * k) * (0 + 1) : Nat) : Real) / (D : Real))
    exact hbound.trans (by unfold squareWindowBudget; linarith)

/-- The physical projected low estimate has no unproved variation or divisor hypothesis. -/
theorem schwartz_low_squarefree_native_packet_subpower (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
      chi ^ 3 = 1 ->
      forall (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H D : Nat), 0 < H -> 0 < D ->
      forall f : SchwartzMap Real Complex,
      norm (lowSquarefreePacket chi G H (4 * D) D
        (fun n => f ((n : Real) / (D : Real)))) <=
        C * (((q * 3 : Nat) : Real) ^ 2) * (squareWindowBudget f) ^ 2 *
          ((H * (4 * D) : Nat) : Real) ^ eps *
            ((4 * D : Nat) : Real) * Real.sqrt (D : Real) := by
  choose C hC hc using low_squarefree_native_packet_subpower eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro q inst chi hchi G hG H D hH hD f
  have hbudget : 0 <= squareWindowBudget f := by
    unfold squareWindowBudget
    exact add_nonneg (NonnegHomClass.apply_nonneg _ _)
      (mul_nonneg (by norm_num) (schwartzLipschitzConstant f).coe_nonneg)
  apply hc chi hchi G hG H (4 * D) D hH (by omega)
    (fun n => f ((n : Real) / (D : Real))) (squareWindowBudget f) hbudget
  intro n hn k hk _
  exact linear_window_rescaled_variation f D n k hD (Finset.mem_Icc.mp hn).1 hk
/-- Only the squarefree high core remains after a fully proved target-sized arithmetic remainder. -/
theorem rational_unit_squarefree_high_remainder (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
      chi ^ 3 = 1 ->
      forall (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H D : Nat), 0 < H -> 0 < D ->
      forall f : SchwartzMap Real Complex,
      norm (rationalUnit chi G H (4 * D) (fun n => f ((n : Real) / (D : Real))) -
        highSquarefreePacket chi G H (4 * D) D
          (fun n => f ((n : Real) / (D : Real)))) <=
        C * (((q * 3 : Nat) : Real) ^ 2) * (squareWindowBudget f) ^ 2 *
          ((H * (4 * D) : Nat) : Real) ^ eps *
            ((4 * D : Nat) : Real) * Real.sqrt (D : Real) := by
  choose C hC hc using schwartz_low_squarefree_native_packet_subpower eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro q inst chi hchi G hG H D hH hD f
  rw [squarefree_low_high_split, add_sub_cancel_right]
  exact hc chi hchi G hG H D hH hD f

/-- Every nonsquarefree rational high row is jointly bounded at the target power. -/
theorem nonsquarefree_high_subpower (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
      chi ^ 3 = 1 ->
      forall (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H D : Nat), 0 < H -> 0 < D ->
      forall f : SchwartzMap Real Complex,
      norm (highNativePacket chi G H (4 * D) D (fun a => scaledWindow f a D) -
        highSquarefreePacket chi G H (4 * D) D
          (fun n => f ((n : Real) / (D : Real)))) <=
        C * (((q * 3 : Nat) : Real) ^ 2) * (squareWindowBudget f) ^ 2 *
          ((H * (4 * D) : Nat) : Real) ^ eps *
            ((4 * D : Nat) : Real) * Real.sqrt (D : Real) := by
  choose A hA ha using schwartz_low_squarefree_native_packet_subpower eps heps
  choose B hB hb using schwartz_low_native_packet_subpower eps heps
  refine Exists.intro (A + B) (And.intro (by linarith) ?_)
  intro q inst chi hchi G hG H D hH hD f
  let W : Nat -> Complex := fun n => f ((n : Real) / (D : Real))
  let Z : Real := (((q * 3 : Nat) : Real) ^ 2) * (squareWindowBudget f) ^ 2 *
    ((H * (4 * D) : Nat) : Real) ^ eps *
      ((4 * D : Nat) : Real) * Real.sqrt (D : Real)
  have hw : productWindow W = (fun a => scaledWindow f a D) := rfl
  have hsf : norm (lowSquarefreePacket chi G H (4 * D) D W) <= A * Z := by
    have h := ha chi hchi G hG H D hH hD f
    calc
      _ <= A * (((q * 3 : Nat) : Real) ^ 2) * (squareWindowBudget f) ^ 2 *
          ((H * (4 * D) : Nat) : Real) ^ eps *
            ((4 * D : Nat) : Real) * Real.sqrt (D : Real) := h
      _ = _ := by dsimp only [Z]; ring
  have hsup : norm (f 0) <= (SchwartzMap.seminorm Real 0 0) f := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.norm_iteratedFDeriv_le_seminorm Real f 0 0
  have hL : 0 <= (schwartzLipschitzConstant f : Real) :=
    (schwartzLipschitzConstant f).coe_nonneg
  have hbudget : norm (f 0) + 8 * (schwartzLipschitzConstant f : Real) <=
      squareWindowBudget f := by unfold squareWindowBudget; linarith
  have hbudget0 : 0 <= norm (f 0) + 8 * (schwartzLipschitzConstant f : Real) := by
    positivity
  have hroot : ((D.sqrt : Nat) : Real) <= Real.sqrt (D : Real) := by
    have hn : D.sqrt ^ 2 <= D := by
      simpa only [pow_two] using Nat.le_sqrt.mp (le_refl D.sqrt)
    have hr : (((D.sqrt : Nat) : Real)) ^ 2 <= (D : Real) := by exact_mod_cast hn
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg D), Real.sqrt_nonneg (D : Real),
      (show 0 <= ((D.sqrt : Nat) : Real) from Nat.cast_nonneg D.sqrt)]
  have hplain : norm (lowNativePacket chi G H (4 * D) D (productWindow W)) <= B * Z := by
    rw [hw]
    have h := hb chi hchi G hG H D hH hD f
    calc
      _ <= B * (((q * 3 : Nat) : Real) ^ 2) *
          (norm (f 0) + 8 * (schwartzLipschitzConstant f : Real)) ^ 2 *
            ((H * (4 * D) : Nat) : Real) ^ eps *
              ((4 * D : Nat) : Real) * ((D.sqrt : Nat) : Real) := h
      _ <= B * (((q * 3 : Nat) : Real) ^ 2) * (squareWindowBudget f) ^ 2 *
          ((H * (4 * D) : Nat) : Real) ^ eps *
            ((4 * D : Nat) : Real) * Real.sqrt (D : Real) := by
        gcongr
      _ = _ := by dsimp only [Z]; ring
  have hcancel := nonsquarefree_high_cancellation chi G H (4 * D) D W
  rw [hw] at hcancel
  rw [hcancel]
  calc
    _ <= norm (lowSquarefreePacket chi G H (4 * D) D W) +
        norm (lowNativePacket chi G H (4 * D) D (productWindow W)) := norm_sub_le _ _
    _ <= A * Z + B * Z := add_le_add hsf hplain
    _ = _ := by dsimp only [Z]; ring
end PrimeFactorOscillations.CarmichaelSquarefreeHighRemainder

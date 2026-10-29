/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNativeLowSector

/-!
# Exact native hyperbola reconstruction of the rational Carmichael unit

The exact finite reconstruction retains every native norm prime power.
The low native estimate may only be consumed after this dictionary is proved.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
namespace PrimeFactorOscillations.CarmichaelNativeHyperbola
open scoped Classical
open CarmichaelNativeLowSector

/-- Exact one-column native reconstruction with every norm prime power and the true floor cutoff. -/
theorem native_weighted_hyperbola {q : Nat}
    (chi : DirichletCharacter Complex q) (N : Nat) (W : Nat -> Complex) :
    (Finset.Icc 1 N).sum (fun n =>
      (chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex)) * W n) =
    (Finset.Icc 1 N).sum (fun a => nativeCoefficient chi a *
      (Finset.Icc 1 (N / a)).sum (fun b =>
        OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) * W (a * b))) := by
  classical
  let R := Finset.Icc 1 N
  let F := fun p : Prod Nat Nat => nativeCoefficient chi p.1 *
    OAI.ShortDraftHeckeBridge.baseChangeChar chi (p.2 : ZMod (q * 3)) * W (p.1 * p.2)
  have hsets : Finset.Ioc 0 N = R := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc, R]
    constructor
    . intro h
      exact And.intro (Nat.succ_le_iff.mpr h.1) h.2
    . intro h
      exact And.intro (Nat.succ_le_iff.mp h.1) h.2
  have hrow : forall n, Membership.mem R n ->
      (chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex)) * W n =
        (Finset.product R R).sum (fun p => if p.1 * p.2 = n then F p else 0) := by
    intro n hn
    have hn0 : Not (n = 0) := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
    have hrec : n.divisorsAntidiagonal.sum (fun p =>
        nativeCoefficient chi p.1 *
          OAI.ShortDraftHeckeBridge.baseChangeChar chi (p.2 : ZMod (q * 3))) =
        chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex) := by
      simpa only [LSeries.convolution_def, nativeCoefficient] using
        CarmichaelArithmeticUnit.normFiber_companion_recovery chi n
    calc
      _ = n.divisorsAntidiagonal.sum (fun p =>
          nativeCoefficient chi p.1 *
            OAI.ShortDraftHeckeBridge.baseChangeChar chi (p.2 : ZMod (q * 3))) * W n :=
        congrArg (fun z : Complex => z * W n) hrec.symm
      _ = n.divisorsAntidiagonal.sum F := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        dsimp only [F]
        rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
      _ = _ := by
        rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn0 (Finset.mem_Icc.mp hn).2,
          hsets]
        exact Finset.sum_filter _ _
  have hcut : forall a, Membership.mem R a ->
      R.sum (fun b => if a * b <= N then F (a, b) else 0) =
        (Finset.Icc 1 (N / a)).sum (fun b => F (a, b)) := by
    intro a ha
    have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
    have hsub : Finset.Icc 1 (N / a) <= R := by
      intro b hb
      exact Finset.mem_Icc.mpr (And.intro (Finset.mem_Icc.mp hb).1
        ((Finset.mem_Icc.mp hb).2.trans (Nat.div_le_self _ _)))
    symm
    calc
      _ = (Finset.Icc 1 (N / a)).sum (fun b =>
          if a * b <= N then F (a, b) else 0) := by
        apply Finset.sum_congr rfl
        intro b hb
        have hp : a * b <= N := by
          simpa only [Nat.mul_comm] using
            (Nat.le_div_iff_mul_le ha0).mp (Finset.mem_Icc.mp hb).2
        exact (ite_eq_left hp).symm
      _ = _ := by
        apply Finset.sum_subset hsub
        intro b hb hnot
        have hp : Not (a * b <= N) := by
          intro hab
          apply hnot
          apply Finset.mem_Icc.mpr
          refine And.intro (Finset.mem_Icc.mp hb).1 ?_
          apply (Nat.le_div_iff_mul_le ha0).mpr
          simpa only [Nat.mul_comm] using hab
        exact ite_eq_right hp
  calc
    _ = R.sum (fun n => (Finset.product R R).sum
        (fun p => if p.1 * p.2 = n then F p else 0)) := Finset.sum_congr rfl hrow
    _ = (Finset.product R R).sum (fun p =>
        if Membership.mem R (p.1 * p.2) then F p else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_ite_eq R (p.1 * p.2) (fun _ => F p)
    _ = R.sum (fun a => R.sum (fun b =>
        if a * b <= N then F (a, b) else 0)) := by
      calc
        _ = R.sum (fun a => R.sum (fun b =>
            if Membership.mem R (a * b) then F (a, b) else 0)) :=
          Finset.sum_product R R (fun p : Prod Nat Nat =>
            if Membership.mem R (p.1 * p.2) then F p else 0)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          have hp0 : 0 < a * b :=
            Nat.mul_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1
          by_cases hp : a * b <= N
          . rw [ite_eq_left (Finset.mem_Icc.mpr (And.intro hp0 hp)), ite_eq_left hp]
          . have hm : Not (Membership.mem R (a * b)) := by
              intro h
              exact hp (Finset.mem_Icc.mp h).2
            rw [ite_eq_right hm, ite_eq_right hp]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hcut a ha, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [F]
      ring

/-- The conjugated column reconstructs with its full character phase. -/
theorem native_weighted_hyperbola_star {q : Nat}
    (chi : DirichletCharacter Complex q) (N : Nat) (W : Nat -> Complex) :
    (Finset.Icc 1 N).sum (fun n =>
      star (chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex)) * W n) =
    (Finset.Icc 1 N).sum (fun a => star (nativeCoefficient chi a) *
      (Finset.Icc 1 (N / a)).sum (fun b =>
        star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3))) *
          W (a * b))) := by
  have h := congrArg star (native_weighted_hyperbola chi N (fun n => star (W n)))
  simpa only [star_sum, star_mul, star_star, mul_comm, mul_left_comm, mul_assoc] using h

/-- Reconstruct both columns for an arbitrary complex kernel without a symmetry hypothesis. -/
theorem native_bilinear_hyperbola {q : Nat}
    (chi : DirichletCharacter Complex q) (N : Nat) (K : Nat -> Nat -> Complex) :
    (Finset.Icc 1 N).sum (fun n =>
      (chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex)) *
        (Finset.Icc 1 N).sum (fun m =>
          star (chi (m : ZMod q) * (ArithmeticFunction.moebius m : Complex)) * K n m)) =
    (Finset.Icc 1 N).sum (fun a => (Finset.Icc 1 N).sum (fun c =>
      (nativeCoefficient chi a * star (nativeCoefficient chi c)) *
        (Finset.Icc 1 (N / a)).sum (fun b => (Finset.Icc 1 (N / c)).sum (fun d =>
          OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
          star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3))) *
            K (a * b) (c * d))))) := by
  rw [native_weighted_hyperbola chi N]
  simp_rw [native_weighted_hyperbola_star chi N]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = (Finset.Icc 1 (N / a)).sum (fun b => (Finset.Icc 1 N).sum (fun c =>
        (Finset.Icc 1 (N / c)).sum (fun d =>
          (nativeCoefficient chi a * star (nativeCoefficient chi c)) *
            (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
              star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3))) *
                K (a * b) (c * d))))) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = (Finset.Icc 1 N).sum (fun c => (Finset.Icc 1 (N / a)).sum (fun b =>
        (Finset.Icc 1 (N / c)).sum (fun d =>
          (nativeCoefficient chi a * star (nativeCoefficient chi c)) *
            (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
              star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3))) *
                K (a * b) (c * d))))) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      simp_rw [Finset.mul_sum]

/-- The exact rational coprimality conditions for one finite unit pair. -/
def unitGood (H n m : Nat) : Prop :=
  Nat.Coprime n m /\ Nat.Coprime n H /\ Nat.Coprime m H

/-- Keep the original rational weight at the full native product. -/
def productWindow (W : Nat -> Complex) (a : Nat) (i : Nat) : Complex :=
  W (a * (i + 1))

/-- The original product-amplifier and coprimality kernel, retaining its complex window. -/
def rationalKernel (G : Finset Nat) (H : Nat) (W : Nat -> Complex)
    (n m : Nat) : Complex :=
  if unitGood H n m then
    ((AllPrimeMask.amplifier G n : Complex) * W n) *
      star ((AllPrimeMask.amplifier G m : Complex) * W m)
  else 0

/-- Rational product coprimality is exactly the outer conditions and both inner cross masks. -/
theorem coprime_product_kernel {q : Nat}
    (psi : DirichletCharacter Complex q) (G : Finset Nat) (H a c b d : Nat)
    (hbpos : 0 < b) (hdpos : 0 < d) (W : Nat -> Complex) :
    (psi (b : ZMod q) * star (psi (d : ZMod q))) *
        rationalKernel G H W (a * b) (c * d) =
      if unitGood H a c then
        (if Nat.Coprime b d then
          (CarmichaelCompanionMasks.amplifiedWindow G a (productWindow W a) (b - 1) *
            CarmichaelCompanionCancellation.maskedCharacter psi (H * c) b) *
          star (CarmichaelCompanionMasks.amplifiedWindow G c (productWindow W c) (d - 1) *
            CarmichaelCompanionCancellation.maskedCharacter psi (H * a) d)
        else 0)
      else 0 := by
  classical
  have hib : b - 1 + 1 = b := Nat.sub_add_cancel hbpos
  have hid : d - 1 + 1 = d := Nat.sub_add_cancel hdpos
  have hgood : unitGood H (a * b) (c * d) <->
      unitGood H a c /\ Nat.Coprime b d /\
        Nat.Coprime b (H * c) /\ Nat.Coprime d (H * a) := by
    unfold unitGood
    rw [Nat.coprime_mul_iff_left (m := a) (n := b) (k := c * d),
      Nat.coprime_mul_iff_right (k := a) (m := c) (n := d),
      Nat.coprime_mul_iff_right (k := b) (m := c) (n := d),
      Nat.coprime_mul_iff_left (m := a) (n := b) (k := H),
      Nat.coprime_mul_iff_left (m := c) (n := d) (k := H),
      Nat.coprime_mul_iff_right (k := b) (m := H) (n := c),
      Nat.coprime_mul_iff_right (k := d) (m := H) (n := a)]
    constructor
    . intro h
      exact And.intro (And.intro h.1.1.1 (And.intro h.2.1.1 h.2.2.1))
        (And.intro h.1.2.2
          (And.intro (And.intro h.2.1.2 h.1.2.1)
            (And.intro h.2.2.2 h.1.1.2.symm)))
    . intro h
      exact And.intro
        (And.intro (And.intro h.1.1 h.2.2.2.2.symm)
          (And.intro h.2.2.1.2 h.2.1))
        (And.intro (And.intro h.1.2.1 h.2.2.1.1)
          (And.intro h.1.2.2 h.2.2.2.1))
  by_cases hO : unitGood H a c
  . rw [ite_eq_left hO]
    by_cases hbd : Nat.Coprime b d
    . rw [ite_eq_left hbd]
      by_cases hb : Nat.Coprime b (H * c)
      . by_cases hd : Nat.Coprime d (H * a)
        . have hR : unitGood H (a * b) (c * d) :=
            hgood.mpr (And.intro hO (And.intro hbd (And.intro hb hd)))
          rw [rationalKernel, ite_eq_left hR]
          unfold CarmichaelCompanionCancellation.maskedCharacter
          rw [ite_eq_left hb, ite_eq_left hd]
          simp only [CarmichaelCompanionMasks.amplifiedWindow, productWindow, hib, hid,
            star_mul]
          ring
        . have hR : Not (unitGood H (a * b) (c * d)) := by
            intro h
            exact hd (hgood.mp h).2.2.2
          rw [rationalKernel, ite_eq_right hR]
          unfold CarmichaelCompanionCancellation.maskedCharacter
          rw [ite_eq_left hb, ite_eq_right hd]
          simp only [star_zero, mul_zero]
      . have hR : Not (unitGood H (a * b) (c * d)) := by
          intro h
          exact hb (hgood.mp h).2.2.1
        rw [rationalKernel, ite_eq_right hR]
        unfold CarmichaelCompanionCancellation.maskedCharacter
        rw [ite_eq_right hb]
        simp only [zero_mul, mul_zero]
    . have hR : Not (unitGood H (a * b) (c * d)) := by
        intro h
        exact hbd (hgood.mp h).2.1
      rw [rationalKernel, ite_eq_right hR, ite_eq_right hbd]
      simp only [mul_zero]
  . have hR : Not (unitGood H (a * b) (c * d)) := by
      intro h
      exact hO (hgood.mp h).1
    rw [ite_eq_right hO, rationalKernel, ite_eq_right hR, mul_zero]

/-- The full finite rational unit with both actual Mobius-character coefficients. -/
def rationalUnit {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H N : Nat) (W : Nat -> Complex) : Complex :=
  (Finset.Icc 1 N).sum (fun n =>
    (chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex)) *
      (Finset.Icc 1 N).sum (fun m =>
        star (chi (m : ZMod q) * (ArithmeticFunction.moebius m : Complex)) *
          rationalKernel G H W n m))

/-- Every native index pair, with both cross masks inside the original native term. -/
def fullNativePacket {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H N : Nat) (W : Nat -> Nat -> Complex) : Complex :=
  (Finset.Icc 1 N).sum (fun a => (Finset.Icc 1 N).sum (fun c =>
    if unitGood H a c then nativeTerm chi G H N W a c else 0))

/-- The full signed complement ac>T, including short and unit companion indices. -/
def highNativePacket {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H N T : Nat) (W : Nat -> Nat -> Complex) : Complex :=
  (Finset.Icc 1 N).sum (fun a => (Finset.Icc 1 N).sum (fun c =>
    if T < a * c /\ unitGood H a c then nativeTerm chi G H N W a c else 0))

/-- The factored unit is the original compensated coefficient form with the full product amplifier. -/
theorem rational_unit_actual_weights {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H N : Nat) (W : Nat -> Complex) :
    rationalUnit chi G H N W =
      (Finset.Icc 1 N).sum (fun n => (Finset.Icc 1 N).sum (fun m =>
        if unitGood H n m then
          ((chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex)) *
            (AllPrimeMask.amplifier G n : Complex) * W n) *
          star ((chi (m : ZMod q) * (ArithmeticFunction.moebius m : Complex)) *
            (AllPrimeMask.amplifier G m : Complex) * W m)
        else 0)) := by
  unfold rationalUnit
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : unitGood H n m
  . rw [rationalKernel, ite_eq_left h, ite_eq_left h]
    simp only [star_mul]
    ring
  . rw [rationalKernel, ite_eq_right h, ite_eq_right h, mul_zero, mul_zero]

/-- The entire finite rational unit equals the complete signed native packet. -/
theorem rational_unit_native_packet {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H N : Nat) (W : Nat -> Complex) :
    rationalUnit chi G H N W =
      fullNativePacket chi G H N (productWindow W) := by
  unfold rationalUnit
  rw [native_bilinear_hyperbola chi N]
  unfold fullNativePacket
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  let psi := OAI.ShortDraftHeckeBridge.baseChangeChar chi
  have hinner :
      (Finset.Icc 1 (N / a)).sum (fun b => (Finset.Icc 1 (N / c)).sum (fun d =>
        psi (b : ZMod (q * 3)) * star (psi (d : ZMod (q * 3))) *
          rationalKernel G H W (a * b) (c * d))) =
      if unitGood H a c then
        CarmichaelCompanionCancellation.weightedCompanionPacket psi
          (H * c) (H * a) (N / a) (N / c)
          (CarmichaelCompanionMasks.amplifiedWindow G a (productWindow W a))
          (CarmichaelCompanionMasks.amplifiedWindow G c (productWindow W c))
      else 0 := by
    by_cases hO : unitGood H a c
    . rw [ite_eq_left hO]
      unfold CarmichaelCompanionCancellation.weightedCompanionPacket
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      have h := coprime_product_kernel psi G H a c b d
        (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hd).1 W
      rw [ite_eq_left hO] at h
      exact h
    . rw [ite_eq_right hO]
      apply Finset.sum_eq_zero
      intro b hb
      apply Finset.sum_eq_zero
      intro d hd
      have h := coprime_product_kernel psi G H a c b d
        (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hd).1 W
      rw [ite_eq_right hO] at h
      exact h
  change (nativeCoefficient chi a * star (nativeCoefficient chi c)) *
      (Finset.Icc 1 (N / a)).sum (fun b => (Finset.Icc 1 (N / c)).sum (fun d =>
        psi (b : ZMod (q * 3)) * star (psi (d : ZMod (q * 3))) *
          rationalKernel G H W (a * b) (c * d))) = _
  rw [hinner]
  by_cases hO : unitGood H a c
  . rw [ite_eq_left hO, ite_eq_left hO]
    rfl
  . rw [ite_eq_right hO, ite_eq_right hO, mul_zero]

/-- Partition the native packet exactly at ac<=T, preserving every supported term. -/
theorem full_native_low_high_split {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H N T : Nat) (W : Nat -> Nat -> Complex) :
    fullNativePacket chi G H N W =
      lowNativePacket chi G H N T W + highNativePacket chi G H N T W := by
  unfold fullNativePacket lowNativePacket highNativePacket
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hO : unitGood H a c
  . have hO' : Nat.Coprime a c /\ Nat.Coprime a H /\ Nat.Coprime c H := hO
    by_cases h : a * c <= T
    . have hl : a * c <= T /\ Nat.Coprime a c /\ Nat.Coprime a H /\ Nat.Coprime c H :=
        And.intro h hO'
      have hh : Not (T < a * c /\ unitGood H a c) := by
        intro h'
        exact (Nat.not_lt_of_ge h) h'.1
      rw [ite_eq_left hO, ite_eq_left hl, ite_eq_right hh, add_zero]
    . have hl : Not (a * c <= T /\ Nat.Coprime a c /\ Nat.Coprime a H /\ Nat.Coprime c H) := by
        intro h'
        exact h h'.1
      have hh : T < a * c /\ unitGood H a c := And.intro (Nat.lt_of_not_ge h) hO
      rw [ite_eq_left hO, ite_eq_right hl, ite_eq_left hh, zero_add]
  . have hl : Not (a * c <= T /\ Nat.Coprime a c /\ Nat.Coprime a H /\ Nat.Coprime c H) := by
      intro h
      exact hO h.2
    have hh : Not (T < a * c /\ unitGood H a c) := by
      intro h
      exact hO h.2
    rw [ite_eq_right hO, ite_eq_right hl, ite_eq_right hh, zero_add]

/-- The actual rational unit differs from its retained high native core by the proved target-sized low remainder. -/
theorem rational_unit_high_core_remainder (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
      chi ^ 3 = 1 ->
      forall (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H D : Nat), 0 < H -> 0 < D ->
      forall f : SchwartzMap Real Complex,
      norm (rationalUnit chi G H (4 * D) (fun n => f ((n : Real) / (D : Real))) -
        highNativePacket chi G H (4 * D) D (fun a => scaledWindow f a D)) <=
        C * (((q * 3 : Nat) : Real) ^ 2) *
          (norm (f 0) + 8 * (schwartzLipschitzConstant f : Real)) ^ 2 *
          ((H * (4 * D) : Nat) : Real) ^ eps *
            ((4 * D : Nat) : Real) * (D.sqrt : Real) := by
  choose C hC hc using schwartz_low_native_packet_subpower eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro q inst chi hchi G hG H D hH hD f
  have hw : productWindow (fun n => f ((n : Real) / (D : Real))) =
      (fun a => scaledWindow f a D) := by
    funext a i
    rfl
  rw [rational_unit_native_packet, hw, full_native_low_high_split, add_sub_cancel_right]
  exact hc chi hchi G hG H D hH hD f

end PrimeFactorOscillations.CarmichaelNativeHyperbola

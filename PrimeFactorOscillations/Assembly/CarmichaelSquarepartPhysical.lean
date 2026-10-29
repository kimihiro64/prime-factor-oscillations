/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelNativeSquarepart

/-!
# Physical companion ranges after native square-part transfer

The exact finite range permutation keeps the square part, plain companion
phase and arbitrary complex coupled window together. It is the entry to
applying the uniform squarefree mean at the actual square-root cutoffs.
No estimate of the retained signed small-square core is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelSquarepartPhysical

open CarmichaelNativeSquarepart

private theorem square_hyperbola_swap (M : Nat) (F : Nat -> Nat -> Complex) :
    (Finset.Icc 1 (Nat.sqrt M)).sum (fun s =>
      (Finset.Icc 1 (M / s ^ 2)).sum (fun b => F s b)) =
      (Finset.Icc 1 M).sum (fun b =>
        (Finset.Icc 1 (Nat.sqrt (M / b))).sum (fun s => F s b)) := by
  classical
  let L : Finset (Sigma (fun _ : Nat => Nat)) :=
    (Finset.Icc 1 (Nat.sqrt M)).sigma (fun s => Finset.Icc 1 (M / s ^ 2))
  let R : Finset (Sigma (fun _ : Nat => Nat)) :=
    (Finset.Icc 1 M).sigma (fun b => Finset.Icc 1 (Nat.sqrt (M / b)))
  have he : L.sum (fun sb => F sb.1 sb.2) =
      R.sum (fun bs => F bs.2 bs.1) := by
    apply Finset.sum_bij
      (fun sb _ => (Sigma.mk sb.2 sb.1 : Sigma (fun _ : Nat => Nat)))
    . intro sb hsb
      have h := Finset.mem_sigma.mp hsb
      have hspos : 0 < sb.1 := (Finset.mem_Icc.mp h.1).1
      have hb := Finset.mem_Icc.mp h.2
      have hprod := (Nat.le_div_iff_mul_le (pow_pos hspos 2)).mp hb.2
      have hsnew : sb.1 <= Nat.sqrt (M / sb.2) := by
        apply Nat.le_sqrt.mpr
        apply (Nat.le_div_iff_mul_le hb.1).mpr
        nlinarith only [hprod]
      apply Finset.mem_sigma.mpr
      exact And.intro
        (Finset.mem_Icc.mpr (And.intro hb.1 (hb.2.trans (Nat.div_le_self _ _))))
        (Finset.mem_Icc.mpr (And.intro hspos hsnew))
    . intro sb _ uv _ heq
      apply Sigma.ext
      . exact congrArg (fun z : Sigma (fun _ : Nat => Nat) => z.2) heq
      . exact heq_of_eq (congrArg (fun z : Sigma (fun _ : Nat => Nat) => z.1) heq)
    . intro bs hbs
      have h := Finset.mem_sigma.mp hbs
      have hb := Finset.mem_Icc.mp h.1
      have hs := Finset.mem_Icc.mp h.2
      have hsprod := Nat.le_sqrt.mp hs.2
      have hsM : bs.2 <= Nat.sqrt M :=
        Nat.le_sqrt.mpr (hsprod.trans (Nat.div_le_self _ _))
      have hbnew : bs.1 <= M / bs.2 ^ 2 := by
        apply (Nat.le_div_iff_mul_le (pow_pos hs.1 2)).mpr
        have hprod := (Nat.le_div_iff_mul_le hb.1).mp hsprod
        nlinarith only [hprod]
      have hmem : Membership.mem L (Sigma.mk bs.2 bs.1) :=
        Finset.mem_sigma.mpr
          (And.intro (Finset.mem_Icc.mpr (And.intro hs.1 hsM))
            (Finset.mem_Icc.mpr (And.intro hb.1 hbnew)))
      exact Exists.intro (Sigma.mk bs.2 bs.1) (Exists.intro hmem rfl)
    . intro sb _
      rfl
  calc
    _ = L.sum (fun sb => F sb.1 sb.2) :=
      Finset.sum_sigma' (Finset.Icc 1 (Nat.sqrt M))
        (fun s => Finset.Icc 1 (M / s ^ 2)) F
    _ = R.sum (fun bs => F bs.2 bs.1) := he
    _ = _ := Finset.sum_sigma (Finset.Icc 1 M)
      (fun b => Finset.Icc 1 (Nat.sqrt (M / b))) (fun bs => F bs.2 bs.1)

/-- Move the original companion outside the square-part sum at its true physical cutoff. -/
theorem native_companion_range_swap {q : Nat}
    (chi : DirichletCharacter Complex q) (N r : Nat)
    (W : Nat -> Nat -> Complex) :
    (Finset.Icc 1 (Nat.sqrt (N / r))).sum (fun s =>
      squarepartCoefficient chi r s *
        (Finset.Icc 1 (N / (r * s ^ 2))).sum (fun b =>
          OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) * W s b)) =
      (Finset.Icc 1 (N / r)).sum (fun b =>
        OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
          (Finset.Icc 1 (Nat.sqrt (N / (r * b)))).sum (fun s =>
            squarepartCoefficient chi r s * W s b)) := by
  have hcut (k : Nat) : N / (r * k) = N / r / k :=
    (Nat.div_div_eq_div_mul N r k).symm
  simp_rw [hcut]
  calc
    _ = (Finset.Icc 1 (Nat.sqrt (N / r))).sum (fun s =>
        (Finset.Icc 1 (N / r / s ^ 2)).sum (fun b =>
          squarepartCoefficient chi r s *
            OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) * W s b)) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = (Finset.Icc 1 (N / r)).sum (fun b =>
        (Finset.Icc 1 (Nat.sqrt (N / r / b))).sum (fun s =>
          squarepartCoefficient chi r s *
            OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) * W s b)) :=
      square_hyperbola_swap (N / r) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring

open CarmichaelSquarepartCancellation
open CarmichaelCompanionCancellation
open CarmichaelCompanionMasks
open scoped Classical

/-- The actual supported rectangle, with all squarefree, character and amplifier terms. -/
def squarefreeRectanglePacket {q : Nat} (psi : DirichletCharacter Complex q)
    (G : Finset Nat) (H K a c B C R T : Nat) (w v : Nat -> Complex) : Complex :=
  (Finset.Icc R B).sum (fun s => (Finset.Icc T C).sum (fun t =>
    if Nat.Coprime s t then
      (squarefreeWindow (amplifiedWindow G a w) (s - 1) * maskedCharacter psi H s) *
        star (squarefreeWindow (amplifiedWindow G c v) (t - 1) * maskedCharacter psi K t)
    else 0))

private theorem interval_prefix (R B : Nat) (hR : 0 < R) (F : Nat -> Complex) :
    (Finset.Icc R B).sum F =
      (Finset.Icc 1 B).sum F - (Finset.Icc 1 (min B (R - 1))).sum F := by
  classical
  have hsub : Finset.Icc 1 (min B (R - 1)) <= Finset.Icc 1 B := by
    intro n hn
    have h := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr (And.intro h.1 (h.2.trans (min_le_left _ _)))
  have he : Finset.Icc R B =
      (Finset.Icc 1 B) \ (Finset.Icc 1 (min B (R - 1))) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_sdiff]
    omega
  rw [he]
  exact (eq_sub_iff_add_eq).mpr (Finset.sum_sdiff hsub)

/-- Exact four-prefix subtraction keeps all overlaps before any remainder bound. -/
theorem squarefree_rectangle_identity {q : Nat}
    (psi : DirichletCharacter Complex q) (G : Finset Nat)
    (H K a c B C R T : Nat) (hR : 0 < R) (hT : 0 < T)
    (w v : Nat -> Complex) :
    squarefreeRectanglePacket psi G H K a c B C R T w v =
      squarefreeCompanionPacket psi G H K a c B C w v -
      squarefreeCompanionPacket psi G H K a c (min B (R - 1)) C w v -
      squarefreeCompanionPacket psi G H K a c B (min C (T - 1)) w v +
      squarefreeCompanionPacket psi G H K a c
        (min B (R - 1)) (min C (T - 1)) w v := by
  unfold squarefreeRectanglePacket squarefreeCompanionPacket weightedCompanionPacket
  rw [interval_prefix R B hR]
  simp_rw [interval_prefix T C hT]
  simp only [Finset.sum_sub_distrib]
  ring

private theorem square_budget_nonneg (f : SchwartzMap Real Complex) :
    0 <= squareWindowBudget f := by
  unfold squareWindowBudget
  exact add_nonneg (NonnegHomClass.apply_nonneg _ _)
    (mul_nonneg (by norm_num)
      (CarmichaelNativeLowSector.schwartzLipschitzConstant f).coe_nonneg)

private theorem norm_four_prefix_le (a b c d : Complex) (M : Real)
    (ha : norm a <= M) (hb : norm b <= M)
    (hc : norm c <= M) (hd : norm d <= M) :
    norm (a - b - c + d) <= 4 * M := by
  calc
    _ <= norm (a - b - c) + norm d := norm_add_le _ _
    _ <= (norm (a - b) + norm c) + norm d :=
      add_le_add (norm_sub_le (a - b) c) (le_refl (norm d))
    _ <= ((norm a + norm b) + norm c) + norm d :=
      add_le_add (add_le_add (norm_sub_le a b) (le_refl (norm c))) (le_refl (norm d))
    _ <= ((M + M) + M) + M := add_le_add (add_le_add (add_le_add ha hb) hc) hd
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- The exact four-prefix rectangle uses only the two actual dilation-variation budgets. -/
theorem rectangle_subpower_of_variation (eps : Real) (heps : 0 < eps) :
    exists Ceps : Real, 0 < Ceps /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
      (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H K a c B C R T : Nat), 0 < H -> 0 < K -> 0 < a -> 0 < c ->
      0 < R -> 0 < T -> forall (w v : Nat -> Complex) (Vf Vg : Real),
      0 <= Vf -> 0 <= Vg ->
      (forall B1, B1 <= B -> forall k, 0 < k ->
        windowVariation (dilatedWindow k w) (B1 / k) <= Vf) ->
      (forall C1, C1 <= C -> forall k, 0 < k ->
        windowVariation (dilatedWindow k v) (C1 / k) <= Vg) ->
      norm (squarefreeRectanglePacket
        (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2))
        G H K a c B C R T w v) <=
        Ceps * (((q * 3 : Nat) : Real) ^ 2) * Vf * Vg *
          (((H + K + a + c + 1) * (B + C + 1) : Nat) : Real) ^ eps *
            Real.sqrt ((B : Real) * (C : Real)) := by
  choose C0 hC0 hmain using squarefree_packet_subpower_of_variation eps heps
  refine Exists.intro (4 * C0) (And.intro (by positivity) ?_)
  intro q inst chi G hG H K a c B C R T hH hK ha hc hR hT w v Vf Vg hf0 hg0 hvarf hvarg
  let X : Nat := (H + K + a + c + 1) * (B + C + 1)
  let Z : Real := C0 * (((q * 3 : Nat) : Real) ^ 2) *
    Vf * Vg
  let M : Real := Z * (X : Real) ^ eps * Real.sqrt ((B : Real) * (C : Real))
  have hZ : 0 <= Z := by dsimp only [Z]; positivity
  have hprefix (B1 C1 : Nat) (hB : B1 <= B) (hC : C1 <= C) :
      norm (squarefreeCompanionPacket
        (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2))
        G H K a c B1 C1 w v) <= M := by
    have hraw := hmain chi G hG H K a c B1 C1 hH hK ha hc w v Vf Vg hf0 hg0
      (fun k hk _ => hvarf B1 hB k hk)
      (fun k hk _ => hvarg C1 hC k hk)
    have hX :
        (((H + K + a + c + 1) * (B1 + C1 + 1) : Nat) : Real) <= (X : Real) :=
      Nat.cast_le.mpr (Nat.mul_le_mul_left _ (by omega))
    have hpow := Real.rpow_le_rpow
      (Nat.cast_nonneg ((H + K + a + c + 1) * (B1 + C1 + 1))) hX (le_of_lt heps)
    have hprod : (B1 : Real) * (C1 : Real) <= (B : Real) * (C : Real) :=
      mul_le_mul (Nat.cast_le.mpr hB) (Nat.cast_le.mpr hC)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact hraw.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hpow hZ) (Real.sqrt_le_sqrt hprod)
      (Real.sqrt_nonneg _) (mul_nonneg hZ (Real.rpow_nonneg (Nat.cast_nonneg X) eps)))
  rw [squarefree_rectangle_identity _ G H K a c B C R T hR hT]
  calc
    _ <= 4 * M := norm_four_prefix_le _ _ _ _ M
      (hprefix B C (le_refl _) (le_refl _))
      (hprefix (min B (R - 1)) C (min_le_left _ _) (le_refl _))
      (hprefix B (min C (T - 1)) (le_refl _) (min_le_left _ _))
      (hprefix (min B (R - 1)) (min C (T - 1)) (min_le_left _ _) (min_le_left _ _))
    _ = _ := by dsimp only [M, Z, X]; ring

set_option maxHeartbeats 800000 in
/-- Every positive lower rectangle has the same physical square-root mean, with no cutoff power loss. -/
theorem squared_rectangle_subpower (eps : Real) (heps : 0 < eps) :
    exists Ceps : Real, 0 < Ceps /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
      (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H K a c B C A E D R T : Nat), 0 < H -> 0 < K -> 0 < a -> 0 < c ->
      0 < D -> A * B ^ 2 <= 4 * D -> E * C ^ 2 <= 4 * D ->
      0 < R -> 0 < T -> forall (f g : SchwartzMap Real Complex),
      norm (squarefreeRectanglePacket
        (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2))
        G H K a c B C R T (squaredWindow f A D) (squaredWindow g E D)) <=
        Ceps * (((q * 3 : Nat) : Real) ^ 2) * squareWindowBudget f * squareWindowBudget g *
          (((H + K + a + c + 1) * (B + C + 1) : Nat) : Real) ^ eps *
            Real.sqrt ((B : Real) * (C : Real)) := by
  choose Ceps hCeps hmain using rectangle_subpower_of_variation eps heps
  refine Exists.intro Ceps (And.intro hCeps ?_)
  intro q inst chi G hG H K a c B C A E D R T hH hK ha hc hD hAB hEC hR hT f g
  exact hmain chi G hG H K a c B C R T hH hK ha hc hR hT
    (squaredWindow f A D) (squaredWindow g E D) (squareWindowBudget f) (squareWindowBudget g)
    (square_budget_nonneg f) (square_budget_nonneg g)
    (by
      intro B1 hB k hk
      exact squared_window_rescaled_variation f A D B1 k hD hk
        ((Nat.mul_le_mul_left A (show B1 ^ 2 <= B ^ 2 by nlinarith)).trans hAB))
    (by
      intro C1 hC k hk
      exact squared_window_rescaled_variation g E D C1 k hD hk
        ((Nat.mul_le_mul_left E (show C1 ^ 2 <= C ^ 2 by nlinarith)).trans hEC))

private theorem square_product_cutoff (N r s : Nat) (hr : 0 < r) :
    r * s ^ 2 <= N <-> s <= Nat.sqrt (N / r) := by
  constructor
  . intro h
    apply Nat.le_sqrt.mpr
    apply (Nat.le_div_iff_mul_le hr).mpr
    nlinarith only [h]
  . intro h
    have hh := (Nat.le_div_iff_mul_le hr).mp (Nat.le_sqrt.mp h)
    nlinarith only [hh]

private theorem squarepart_pairs_cutoff (N : Nat) (F : Prod Nat Nat -> Complex) :
    (squarepartPairs N).sum F =
      (Finset.Icc 1 N).sum (fun r => if Squarefree r then
        (Finset.Icc 1 (Nat.sqrt (N / r))).sum (fun s => F (r, s)) else 0) := by
  classical
  unfold squarepartPairs
  rw [Finset.sum_filter]
  have hprod := Finset.sum_product
    ((Finset.Icc 1 N).filter (fun r => Squarefree r)) (Finset.Icc 1 (Nat.sqrt N))
    (fun rs : Prod Nat Nat => if rs.1 * rs.2 ^ 2 <= N then F rs else 0)
  refine Eq.trans hprod ?_
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hsf : Squarefree r
  . simp only [ite_eq_left hsf]
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    have hsub : Finset.Icc 1 (Nat.sqrt (N / r)) <= Finset.Icc 1 (Nat.sqrt N) := by
      intro s hs
      have h := Finset.mem_Icc.mp hs
      exact Finset.mem_Icc.mpr (And.intro h.1
        (Nat.le_sqrt.mpr ((Nat.le_sqrt.mp h.2).trans (Nat.div_le_self _ _))))
    symm
    calc
      _ = (Finset.Icc 1 (Nat.sqrt (N / r))).sum (fun s =>
          if r * s ^ 2 <= N then F (r, s) else 0) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact (ite_eq_left ((square_product_cutoff N r s hrpos).mpr
          (Finset.mem_Icc.mp hs).2)).symm
      _ = _ := by
        apply Finset.sum_subset hsub
        intro s hs hnot
        apply ite_eq_right
        intro hprod
        apply hnot
        exact Finset.mem_Icc.mpr (And.intro (Finset.mem_Icc.mp hs).1
          ((square_product_cutoff N r s hrpos).mp hprod))
  . simp only [ite_eq_right hsf]

/-- The native pair bijection has exactly the physical floor-square endpoint. -/
theorem native_squarepart_hyperbola {q : Nat}
    (chi : DirichletCharacter Complex q) (N : Nat) (W : Nat -> Complex) :
    (Finset.Icc 1 N).sum (fun n =>
      OAI.ShortDraftHeckeBridge.normFiberCoeff
        (OAI.ShortDraftHeckeBridge.baseChangeWeight chi) n * W n) =
      (Finset.Icc 1 N).sum (fun r => if Squarefree r then
        (Finset.Icc 1 (Nat.sqrt (N / r))).sum (fun s =>
          squarepartCoefficient chi r s * W (r * s ^ 2)) else 0) := by
  rw [native_squarepart_sum]
  exact squarepart_pairs_cutoff N _

/-- The original rational column is regrouped by the actual product r*b, with all phases. -/
theorem rational_column_squarepart_rows {q : Nat}
    (chi : DirichletCharacter Complex q) (N : Nat) (W : Nat -> Complex) :
    (Finset.Icc 1 N).sum (fun n =>
      (chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex)) * W n) =
      (Finset.Icc 1 N).sum (fun r => if Squarefree r then
        (Finset.Icc 1 (N / r)).sum (fun b =>
          OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
            (Finset.Icc 1 (Nat.sqrt (N / (r * b)))).sum (fun s =>
              squarepartCoefficient chi r s * W ((r * s ^ 2) * b))) else 0) := by
  have hnative := CarmichaelNativeHyperbola.native_weighted_hyperbola chi N W
  have hsp := native_squarepart_hyperbola chi N (fun a =>
    (Finset.Icc 1 (N / a)).sum (fun b =>
      OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) * W (a * b)))
  calc
    _ = (Finset.Icc 1 N).sum (fun a =>
        OAI.ShortDraftHeckeBridge.normFiberCoeff
          (OAI.ShortDraftHeckeBridge.baseChangeWeight chi) a *
          (Finset.Icc 1 (N / a)).sum (fun b =>
            OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
              W (a * b))) := by
      simpa only [CarmichaelNativeLowSector.nativeCoefficient] using hnative
    _ = (Finset.Icc 1 N).sum (fun r => if Squarefree r then
        (Finset.Icc 1 (Nat.sqrt (N / r))).sum (fun s =>
          squarepartCoefficient chi r s *
            (Finset.Icc 1 (N / (r * s ^ 2))).sum (fun b =>
              OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
                W ((r * s ^ 2) * b))) else 0) := hsp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hsf : Squarefree r
      . simp only [ite_eq_left hsf]
        exact native_companion_range_swap chi N r (fun s b => W ((r * s ^ 2) * b))
      . simp only [ite_eq_right hsf]

/-- Every prime amplifier depends on the support of the square part, with no coprimality loss. -/
theorem amplifier_square_argument (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p) (m s : Nat) :
    AllPrimeMask.amplifier G (m * s ^ 2) = AllPrimeMask.amplifier G (m * s) := by
  classical
  unfold AllPrimeMask.amplifier
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := hG p hp
  have hiff : Dvd.dvd p (m * s ^ 2) <-> Dvd.dvd p (m * s) := by
    rw [hprime.dvd_mul, hprime.dvd_mul]
    constructor
    . intro h
      cases h with
      | inl hm => exact Or.inl hm
      | inr hs => exact Or.inr (hprime.dvd_of_dvd_pow hs)
    . intro h
      cases h with
      | inl hm => exact Or.inl hm
      | inr hs =>
          apply Or.inr
          simpa only [pow_two] using dvd_mul_of_dvd_left hs s
  by_cases hleft : Dvd.dvd p (m * s ^ 2)
  . have hright : Dvd.dvd p (m * s) := hiff.mp hleft
    rw [ite_eq_left hleft, ite_eq_left hright]
  . have hright : Not (Dvd.dvd p (m * s)) := by
      intro h
      exact hleft (hiff.mpr h)
    rw [ite_eq_right hleft, ite_eq_right hright]

private theorem unit_good_square_products (H m n s t : Nat) :
    CarmichaelNativeHyperbola.unitGood H (m * s ^ 2) (n * t ^ 2) <->
      CarmichaelNativeHyperbola.unitGood H m n /\
        Nat.Coprime s t /\ Nat.Coprime s (H * n) /\ Nat.Coprime t (H * m) := by
  unfold CarmichaelNativeHyperbola.unitGood
  simp only [Nat.coprime_mul_iff_right,
    Nat.coprime_pow_right_iff (by decide : 0 < 2),
    Nat.coprime_comm, and_assoc, and_comm, and_left_comm]

/-- The complete row has exactly the cross masks H*r*n and H*u*m. -/
theorem unit_good_squarepart_masks (H r u m n s t : Nat) :
    (Nat.Coprime r s /\ Nat.Coprime u t /\
      CarmichaelNativeHyperbola.unitGood H (m * s ^ 2) (n * t ^ 2)) <->
      (CarmichaelNativeHyperbola.unitGood H m n /\ Nat.Coprime s t /\
        Nat.Coprime s (H * r * n) /\ Nat.Coprime t (H * u * m)) := by
  rw [unit_good_square_products]
  simp only [Nat.coprime_mul_iff_right, Nat.coprime_comm,
    and_assoc, and_comm, and_left_comm]

open CarmichaelNativeLowSector

private theorem physical_squarepart_atom {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (H r u b d D s t : Nat) (hs : 0 < s) (ht : 0 < t) (f : Real -> Complex) :
    squarepartCoefficient chi r s * star (squarepartCoefficient chi u t) *
      CarmichaelNativeHyperbola.rationalKernel G H
        (fun n => f ((n : Real) / (D : Real))) ((r * s ^ 2) * b) ((u * t ^ 2) * d) =
      if CarmichaelNativeHyperbola.unitGood H (r * b) (u * d) then
        (nativeCoefficient chi r * star (nativeCoefficient chi u)) *
          (if Nat.Coprime s t then
            (squarefreeWindow (amplifiedWindow G (r * b) (squaredWindow f (r * b) D))
              (s - 1) *
              maskedCharacter (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2))
                (H * r * (u * d)) s) *
            star (squarefreeWindow
                (amplifiedWindow G (u * d) (squaredWindow f (u * d) D)) (t - 1) *
              maskedCharacter (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2))
                (H * u * (r * b)) t)
          else 0)
      else 0 := by
  have hs1 : s - 1 + 1 = s := Nat.sub_add_cancel hs
  have ht1 : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have hmb : (r * s ^ 2) * b = (r * b) * s ^ 2 := by ring
  have hnd : (u * t ^ 2) * d = (u * d) * t ^ 2 := by ring
  rw [hmb, hnd]
  simp only [squarefreeWindow, amplifiedWindow, squaredWindow, hs1, ht1]
  have hsupport := unit_good_squarepart_masks H r u (r * b) (u * d) s t
  by_cases hleft : Nat.Coprime r s /\ Nat.Coprime u t /\
      CarmichaelNativeHyperbola.unitGood H ((r * b) * s ^ 2) ((u * d) * t ^ 2)
  . have hright := hsupport.mp hleft
    simp only [squarepartCoefficient, nativeCoefficient,
      CarmichaelNativeHyperbola.rationalKernel,
      ite_eq_left hleft.1, ite_eq_left hleft.2.1, ite_eq_left hleft.2.2,
      ite_eq_left hright.1, ite_eq_left hright.2.1,
      maskedCharacter, ite_eq_left hright.2.2.1, ite_eq_left hright.2.2.2,
      amplifier_square_argument G hG (r * b) s,
      amplifier_square_argument G hG (u * d) t, star_mul]
    ring
  . have hzero :
        squarepartCoefficient chi r s * star (squarepartCoefficient chi u t) *
          CarmichaelNativeHyperbola.rationalKernel G H
            (fun n => f ((n : Real) / (D : Real)))
            ((r * b) * s ^ 2) ((u * d) * t ^ 2) = 0 := by
      by_cases hrs : Nat.Coprime r s
      . by_cases hut : Nat.Coprime u t
        . have hbad : Not (CarmichaelNativeHyperbola.unitGood H
              ((r * b) * s ^ 2) ((u * d) * t ^ 2)) := by
            intro h
            exact hleft (And.intro hrs (And.intro hut h))
          simp only [CarmichaelNativeHyperbola.rationalKernel, ite_eq_right hbad, mul_zero]
        . simp only [squarepartCoefficient, ite_eq_right hut, star_zero, mul_zero, zero_mul]
      . simp only [squarepartCoefficient, ite_eq_right hrs, zero_mul]
    rw [hzero]
    symm
    by_cases houter : CarmichaelNativeHyperbola.unitGood H (r * b) (u * d)
    . rw [ite_eq_left houter]
      have hbad : Not (Nat.Coprime s t /\ Nat.Coprime s (H * r * (u * d)) /\
          Nat.Coprime t (H * u * (r * b))) := by
        intro h
        exact hleft (hsupport.mpr (And.intro houter h))
      by_cases hst : Nat.Coprime s t
      . rw [ite_eq_left hst]
        by_cases hmask : Nat.Coprime s (H * r * (u * d))
        . have hother : Not (Nat.Coprime t (H * u * (r * b))) := by
            intro h
            exact hbad (And.intro hst (And.intro hmask h))
          simp only [maskedCharacter, ite_eq_right hother, mul_zero, star_zero]
        . simp only [maskedCharacter, ite_eq_right hmask, mul_zero, zero_mul]
      . rw [ite_eq_right hst, mul_zero]
    . exact ite_eq_right houter

/-- The actual physical row, with every native coefficient and original product amplifier. -/
def physicalSquarepartRectangle {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H r u b d B C D R T : Nat) (f : Real -> Complex) : Complex :=
  (Finset.Icc R B).sum (fun s => (Finset.Icc T C).sum (fun t =>
    squarepartCoefficient chi r s * star (squarepartCoefficient chi u t) *
      CarmichaelNativeHyperbola.rationalKernel G H
        (fun n => f ((n : Real) / (D : Real)))
        ((r * s ^ 2) * b) ((u * t ^ 2) * d)))

/-- Identify the full physical row with its exact coupled squarefree rectangle. -/
theorem physical_squarepart_rectangle {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (H r u b d B C D R T : Nat) (hR : 0 < R) (hT : 0 < T)
    (f : Real -> Complex) :
    physicalSquarepartRectangle chi G H r u b d B C D R T f =
      if CarmichaelNativeHyperbola.unitGood H (r * b) (u * d) then
        (nativeCoefficient chi r * star (nativeCoefficient chi u)) *
          squarefreeRectanglePacket
            (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2))
            G (H * r * (u * d)) (H * u * (r * b)) (r * b) (u * d) B C R T
            (squaredWindow f (r * b) D) (squaredWindow f (u * d) D)
      else 0 := by
  unfold physicalSquarepartRectangle
  by_cases houter : CarmichaelNativeHyperbola.unitGood H (r * b) (u * d)
  . rw [ite_eq_left houter]
    unfold squarefreeRectanglePacket
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    have h := physical_squarepart_atom chi G hG H r u b d D s t
      (hR.trans_le (Finset.mem_Icc.mp hs).1) (hT.trans_le (Finset.mem_Icc.mp ht).1) f
    rw [ite_eq_left houter] at h
    exact h
  . rw [ite_eq_right houter]
    apply Finset.sum_eq_zero
    intro s hs
    apply Finset.sum_eq_zero
    intro t ht
    have h := physical_squarepart_atom chi G hG H r u b d D s t
      (hR.trans_le (Finset.mem_Icc.mp hs).1) (hT.trans_le (Finset.mem_Icc.mp ht).1) f
    rw [ite_eq_right houter] at h
    exact h

/-- An independent square-root bound for the actual physical row with every mask and native factor. -/
theorem physical_squarepart_rectangle_bound (eps : Real) (heps : 0 < eps) :
    exists Ceps : Real, 0 < Ceps /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
      (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H r u b d B C D R T : Nat), 0 < H -> 0 < r -> 0 < u -> 0 < b -> 0 < d ->
      0 < D -> (r * b) * B ^ 2 <= 4 * D -> (u * d) * C ^ 2 <= 4 * D ->
      0 < R -> 0 < T -> forall (f : SchwartzMap Real Complex),
      norm (physicalSquarepartRectangle chi G H r u b d B C D R T f) <=
        norm (nativeCoefficient chi r) * norm (nativeCoefficient chi u) *
          (Ceps * (((q * 3 : Nat) : Real) ^ 2) * (squareWindowBudget f) ^ 2 *
            (((H * r * (u * d) + H * u * (r * b) + r * b + u * d + 1) *
                (B + C + 1) : Nat) : Real) ^ eps *
              Real.sqrt ((B : Real) * (C : Real))) := by
  choose Ceps hCeps hrect using squared_rectangle_subpower eps heps
  refine Exists.intro Ceps (And.intro hCeps ?_)
  intro q inst chi G hG H r u b d B C D R T hH hr hu hb hd hD hAB hEC hR hT f
  rw [physical_squarepart_rectangle chi G hG H r u b d B C D R T hR hT]
  by_cases houter : CarmichaelNativeHyperbola.unitGood H (r * b) (u * d)
  . rw [ite_eq_left houter, norm_mul, norm_mul, norm_star]
    have hm : 0 < r * b := Nat.mul_pos hr hb
    have hn : 0 < u * d := Nat.mul_pos hu hd
    have hleft : 0 < H * r * (u * d) := Nat.mul_pos (Nat.mul_pos hH hr) hn
    have hright : 0 < H * u * (r * b) := Nat.mul_pos (Nat.mul_pos hH hu) hm
    have hmean := hrect chi G hG
      (H * r * (u * d)) (H * u * (r * b)) (r * b) (u * d)
      B C (r * b) (u * d) D R T hleft hright hm hn hD hAB hEC hR hT f f
    calc
      _ <= norm (nativeCoefficient chi r) * norm (nativeCoefficient chi u) *
          (Ceps * (((q * 3 : Nat) : Real) ^ 2) * squareWindowBudget f * squareWindowBudget f *
            (((H * r * (u * d) + H * u * (r * b) + r * b + u * d + 1) *
                (B + C + 1) : Nat) : Real) ^ eps *
              Real.sqrt ((B : Real) * (C : Real))) :=
        mul_le_mul_of_nonneg_left hmean (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  . rw [ite_eq_right houter, norm_zero]
    positivity

private theorem column_rows_filtered {q : Nat}
    (chi : DirichletCharacter Complex q) (N : Nat) (W : Nat -> Complex) :
    (Finset.Icc 1 N).sum (fun n =>
      (chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex)) * W n) =
      ((Finset.Icc 1 N).filter (fun r => Squarefree r)).sum (fun r =>
        (Finset.Icc 1 (N / r)).sum (fun b =>
          OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
            (Finset.Icc 1 (Nat.sqrt (N / (r * b)))).sum (fun s =>
              squarepartCoefficient chi r s * W ((r * s ^ 2) * b)))) := by
  simpa only [Finset.sum_filter] using rational_column_squarepart_rows chi N W

private theorem column_rows_filtered_star {q : Nat}
    (chi : DirichletCharacter Complex q) (N : Nat) (W : Nat -> Complex) :
    (Finset.Icc 1 N).sum (fun n =>
      star (chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex)) * W n) =
      ((Finset.Icc 1 N).filter (fun r => Squarefree r)).sum (fun r =>
        (Finset.Icc 1 (N / r)).sum (fun b =>
          star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3))) *
            (Finset.Icc 1 (Nat.sqrt (N / (r * b)))).sum (fun s =>
              star (squarepartCoefficient chi r s) * W ((r * s ^ 2) * b)))) := by
  have h := congrArg star (column_rows_filtered chi N (fun n => star (W n)))
  simpa only [star_sum, star_mul, star_star, mul_comm, mul_left_comm, mul_assoc] using h

private theorem squarepart_six_sum
    (R U : Finset Nat) (B D : Nat -> Finset Nat)
    (S T : Nat -> Nat -> Finset Nat) (F : Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Complex) :
    R.sum (fun r => (B r).sum (fun b => (S r b).sum (fun s =>
      U.sum (fun u => (D u).sum (fun d => (T u d).sum (fun t => F r b s u d t)))))) =
      R.sum (fun r => U.sum (fun u => (B r).sum (fun b =>
        (D u).sum (fun d => (S r b).sum (fun s => (T u d).sum
          (fun t => F r b s u d t)))))) := by
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = (B r).sum (fun b => U.sum (fun u => (S r b).sum (fun s =>
        (D u).sum (fun d => (T u d).sum (fun t => F r b s u d t))))) := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = U.sum (fun u => (B r).sum (fun b => (S r b).sum (fun s =>
        (D u).sum (fun d => (T u d).sum (fun t => F r b s u d t))))) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm

/-- The full signed two-column form is regrouped at both actual product cutoffs. -/
theorem rational_bilinear_squarepart_rows {q : Nat}
    (chi : DirichletCharacter Complex q) (N : Nat) (K : Nat -> Nat -> Complex) :
    (Finset.Icc 1 N).sum (fun n =>
      (chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex)) *
        (Finset.Icc 1 N).sum (fun m =>
          star (chi (m : ZMod q) * (ArithmeticFunction.moebius m : Complex)) * K n m)) =
      ((Finset.Icc 1 N).filter (fun r => Squarefree r)).sum (fun r =>
        ((Finset.Icc 1 N).filter (fun u => Squarefree u)).sum (fun u =>
          (Finset.Icc 1 (N / r)).sum (fun b => (Finset.Icc 1 (N / u)).sum (fun d =>
            (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
              star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3)))) *
              (Finset.Icc 1 (Nat.sqrt (N / (r * b)))).sum (fun s =>
                (Finset.Icc 1 (Nat.sqrt (N / (u * d)))).sum (fun t =>
                  (squarepartCoefficient chi r s * star (squarepartCoefficient chi u t)) *
                    K ((r * s ^ 2) * b) ((u * t ^ 2) * d))))))) := by
  rw [column_rows_filtered chi N]
  simp_rw [column_rows_filtered_star chi N]
  simp_rw [Finset.mul_sum]
  refine Eq.trans (squarepart_six_sum
    ((Finset.Icc 1 N).filter (fun r => Squarefree r))
    ((Finset.Icc 1 N).filter (fun u => Squarefree u))
    (fun r => Finset.Icc 1 (N / r)) (fun u => Finset.Icc 1 (N / u))
    (fun r b => Finset.Icc 1 (Nat.sqrt (N / (r * b))))
    (fun u d => Finset.Icc 1 (Nat.sqrt (N / (u * d))))
    (fun r b s u d t =>
      OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
        (squarepartCoefficient chi r s *
          (star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3))) *
            (star (squarepartCoefficient chi u t) *
              K ((r * s ^ 2) * b) ((u * t ^ 2) * d)))))) ?_
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The actual original unit is the complete signed sum of the physical coupled rows. -/
theorem rational_unit_physical_squarepart_rows {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H N D : Nat) (f : Real -> Complex) :
    CarmichaelNativeHyperbola.rationalUnit chi G H N
        (fun n => f ((n : Real) / (D : Real))) =
      ((Finset.Icc 1 N).filter (fun r => Squarefree r)).sum (fun r =>
        ((Finset.Icc 1 N).filter (fun u => Squarefree u)).sum (fun u =>
          (Finset.Icc 1 (N / r)).sum (fun b => (Finset.Icc 1 (N / u)).sum (fun d =>
            (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
              star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3)))) *
              physicalSquarepartRectangle chi G H r u b d
                (Nat.sqrt (N / (r * b))) (Nat.sqrt (N / (u * d))) D 1 1 f)))) := by
  simpa only [CarmichaelNativeHyperbola.rationalUnit, physicalSquarepartRectangle] using
    rational_bilinear_squarepart_rows chi N
      (CarmichaelNativeHyperbola.rationalKernel G H
        (fun n => f ((n : Real) / (D : Real))))

/-- The actual physical cutoffs discharge both quadratic window support hypotheses. -/
theorem physical_rows_actual_cutoff_bound (eps : Real) (heps : 0 < eps) :
    exists Ceps : Real, 0 < Ceps /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
      (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H r u b d D R T : Nat), 0 < H -> 0 < r -> 0 < u -> 0 < b -> 0 < d ->
      0 < D -> 0 < R -> 0 < T -> forall (f : SchwartzMap Real Complex),
      let B := Nat.sqrt (4 * D / (r * b))
      let C := Nat.sqrt (4 * D / (u * d))
      norm (physicalSquarepartRectangle chi G H r u b d B C D R T f) <=
        norm (nativeCoefficient chi r) * norm (nativeCoefficient chi u) *
          (Ceps * (((q * 3 : Nat) : Real) ^ 2) * (squareWindowBudget f) ^ 2 *
            (((H * r * (u * d) + H * u * (r * b) + r * b + u * d + 1) *
                (B + C + 1) : Nat) : Real) ^ eps *
              Real.sqrt ((B : Real) * (C : Real))) := by
  choose Ceps hCeps hbound using physical_squarepart_rectangle_bound eps heps
  refine Exists.intro Ceps (And.intro hCeps ?_)
  intro q inst chi G hG H r u b d D R T hH hr hu hb hd hD hR hT f
  exact hbound chi G hG H r u b d
    (Nat.sqrt (4 * D / (r * b))) (Nat.sqrt (4 * D / (u * d))) D R T
    hH hr hu hb hd hD
    ((square_product_cutoff (4 * D) (r * b) _ (Nat.mul_pos hr hb)).mpr le_rfl)
    ((square_product_cutoff (4 * D) (u * d) _ (Nat.mul_pos hu hd)).mpr le_rfl)
    hR hT f

end PrimeFactorOscillations.CarmichaelSquarepartPhysical

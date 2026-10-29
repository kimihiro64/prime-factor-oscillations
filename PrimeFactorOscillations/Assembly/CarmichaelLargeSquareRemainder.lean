/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelSquarepartPhysical

/-!
# Aggregate costs for an extracted large-square remainder

The complete physical row is cancelled before its norm is bounded.
This module sums only an explicitly isolated large-square remainder.
The signed small-square core, all compensation terms and the full reciprocal
L-function consumer are retained; no improved global boundary is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelLargeSquareRemainder
open scoped Classical
open CarmichaelNativeLowSector CarmichaelCompanionCancellation CarmichaelCompanionMasks

/-- Positive outer cost after the coupled physical rectangle has been cancelled. -/
def hyperbolaMass {q : Nat} (chi : DirichletCharacter Complex q) (M : Nat) : Real :=
  (Finset.Icc 1 M).sum (fun r => (Finset.Icc 1 (M / r)).sum (fun b =>
    norm (nativeCoefficient chi r) *
      (((r * b : Nat) : Real) ^ (3 / 4 : Real) / ((r * b : Nat) : Real))))

private theorem harmonic_icc (M : Nat) :
    (Finset.Icc 1 M).sum (fun n => 1 / (n : Real)) = harmonicPrefix M := by
  have he : Finset.Icc 1 M = Finset.Ioc 0 M := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [he]
  rfl

/-- Rankin weighting retains the three-quarter cutoff power without a Gram step. -/
theorem hyperbola_mass_cap {q : Nat} (chi : DirichletCharacter Complex q)
    (M : Nat) (A : Real) (hA : 0 <= A)
    (hcap : forall r, Membership.mem (Finset.Icc 1 M) r ->
      norm (nativeCoefficient chi r) <= A) :
    hyperbolaMass chi M <= A * (M : Real) ^ (3 / 4 : Real) *
      (harmonicPrefix M) ^ 2 := by
  have hh : 0 <= harmonicPrefix M :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hterm : forall r, Membership.mem (Finset.Icc 1 M) r ->
      forall b, Membership.mem (Finset.Icc 1 (M / r)) b ->
      norm (nativeCoefficient chi r) *
        (((r * b : Nat) : Real) ^ (3 / 4 : Real) / ((r * b : Nat) : Real)) <=
      (A * (M : Real) ^ (3 / 4 : Real) * (1 / (r : Real))) * (1 / (b : Real)) := by
    intro r hr b hb
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    have hmb : r * b <= M := by
      have h := (Nat.le_div_iff_mul_le hrpos).mp (Finset.mem_Icc.mp hb).2
      simpa only [Nat.mul_comm] using h
    have hp : ((r * b : Nat) : Real) ^ (3 / 4 : Real) <=
        (M : Real) ^ (3 / 4 : Real) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hmb) (by norm_num)
    calc
      _ <= A * (((r * b : Nat) : Real) ^ (3 / 4 : Real) / ((r * b : Nat) : Real)) :=
        mul_le_mul_of_nonneg_right (hcap r hr) (by positivity)
      _ <= A * ((M : Real) ^ (3 / 4 : Real) / ((r * b : Nat) : Real)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hp (Nat.cast_nonneg _)) hA
      _ = _ := by
        push_cast
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  unfold hyperbolaMass
  calc
    _ <= (Finset.Icc 1 M).sum (fun r =>
        (A * (M : Real) ^ (3 / 4 : Real) * harmonicPrefix M) * (1 / (r : Real))) := by
      apply Finset.sum_le_sum
      intro r hr
      calc
        _ <= (Finset.Icc 1 (M / r)).sum (fun b =>
            (A * (M : Real) ^ (3 / 4 : Real) * (1 / (r : Real))) *
              (1 / (b : Real))) :=
          Finset.sum_le_sum (fun b hb => hterm r hr b hb)
        _ = (A * (M : Real) ^ (3 / 4 : Real) * (1 / (r : Real))) *
            harmonicPrefix (M / r) := by
          rw [<- Finset.mul_sum, harmonic_icc]
        _ <= (A * (M : Real) ^ (3 / 4 : Real) * (1 / (r : Real))) *
            harmonicPrefix M :=
          mul_le_mul_of_nonneg_left (harmonic_prefix_mono (Nat.div_le_self M r))
            (by positivity)
        _ = _ := by ring
    _ = _ := by
      rw [<- Finset.mul_sum, harmonic_icc]
      ring

private theorem coefficient_divisor_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (r : Nat) (hr : 0 < r) :
    norm (nativeCoefficient chi r) <= (r.divisors.card : Real) := by
  unfold nativeCoefficient
  rw [OAI.ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff chi r
    (Nat.ne_of_gt hr)]
  exact pair_inverse_coeff_divisor_bound chi
    (OAI.ShortDraftHeckeBridge.baseChangeChar chi) r

/-- The native outer hyperbola costs only M^(3/4+eps), uniformly in the character. -/
theorem hyperbola_mass_subpower (eps : Real) (heps : 0 < eps) :
    exists Ceps : Real, 0 < Ceps /\
      forall {q : Nat} (chi : DirichletCharacter Complex q) (M : Nat),
      hyperbolaMass chi M <= Ceps * (M : Real) ^ (3 / 4 + eps : Real) := by
  choose A hA hdiv using QuadraticDivisorMean.divisor_card_subpower
    (eps / 2) (by linarith)
  choose B hB hH using harmonic_subpower (eps / 4) (by linarith)
  refine Exists.intro (A * B ^ 2) (And.intro (by positivity) ?_)
  intro q chi M
  by_cases hM : M = 0
  . subst M
    simp only [hyperbolaMass, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),
      Finset.sum_empty]
    positivity
  have hMp : 0 < (M : Real) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
  have hcap : forall r, Membership.mem (Finset.Icc 1 M) r ->
      norm (nativeCoefficient chi r) <= A * (M : Real) ^ (eps / 2) := by
    intro r hr
    have hrp : 0 < r := (Finset.mem_Icc.mp hr).1
    exact (coefficient_divisor_bound chi r hrp).trans
      ((hdiv r hrp).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _)
          (Nat.cast_le.mpr (Finset.mem_Icc.mp hr).2) (by linarith)) (le_of_lt hA)))
  have hbound := hyperbola_mass_cap chi M (A * (M : Real) ^ (eps / 2))
    (by positivity) hcap
  have hh : 0 <= harmonicPrefix M :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hp : (harmonicPrefix M) ^ 2 <= (B * (M : Real) ^ (eps / 4)) ^ 2 := by
    gcongr
    exact hH M
  have he2 : ((M : Real) ^ (eps / 4)) ^ 2 = (M : Real) ^ (eps / 2) := by
    rw [<- Real.rpow_natCast _ 2, <- Real.rpow_mul (le_of_lt hMp)]
    congr 1
    norm_num; ring
  calc
    _ <= (A * (M : Real) ^ (eps / 2)) * (M : Real) ^ (3 / 4 : Real) *
        (B * (M : Real) ^ (eps / 4)) ^ 2 :=
      hbound.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    _ = _ := by
      rw [mul_pow, he2]
      calc
        _ = (A * B ^ 2) *
            ((M : Real) ^ (eps / 2) * (M : Real) ^ (3 / 4 : Real) *
              (M : Real) ^ (eps / 2)) := by ring
        _ = _ := by
          rw [<- Real.rpow_add hMp, <- Real.rpow_add hMp]
          congr 2
          ring

private theorem quarter_cutoff (N m B : Nat) (hm : 0 < m)
    (hcap : m * B ^ 2 <= N) :
    Real.sqrt (B : Real) <= (N : Real) ^ (1 / 4 : Real) *
      ((m : Real) ^ (3 / 4 : Real) / (m : Real)) := by
  have hmR : 0 < (m : Real) := Nat.cast_pos.mpr hm
  have hcapR : (m : Real) * (B : Real) ^ 2 <= (N : Real) := by exact_mod_cast hcap
  have hp := Real.rpow_le_rpow (by positivity : 0 <= (m : Real) * (B : Real) ^ 2)
    hcapR (by norm_num : (0 : Real) <= 1 / 4)
  rw [Real.mul_rpow (Nat.cast_nonneg m) (sq_nonneg (B : Real))] at hp
  have hs : ((B : Real) ^ 2) ^ (1 / 4 : Real) = Real.sqrt (B : Real) := by
    rw [<- Real.rpow_natCast _ 2, <- Real.rpow_mul (Nat.cast_nonneg B)]
    norm_num
    exact (Real.sqrt_eq_rpow _).symm
  rw [hs] at hp
  have hc : (m : Real) ^ (1 / 4 : Real) *
      ((m : Real) ^ (3 / 4 : Real) / (m : Real)) = 1 := by
    calc
      _ = ((m : Real) ^ (1 / 4 : Real) * (m : Real) ^ (3 / 4 : Real)) /
          (m : Real) := by ring
      _ = 1 := by
        rw [<- Real.rpow_add hmR, show (1 / 4 : Real) + 3 / 4 = 1 by norm_num,
          Real.rpow_one, div_self (ne_of_gt hmR)]
  calc
    _ = ((m : Real) ^ (1 / 4 : Real) *
        ((m : Real) ^ (3 / 4 : Real) / (m : Real))) * Real.sqrt (B : Real) := by
      rw [hc, one_mul]
    _ = ((m : Real) ^ (1 / 4 : Real) * Real.sqrt (B : Real)) *
        ((m : Real) ^ (3 / 4 : Real) / (m : Real)) := by ring
    _ <= _ := mul_le_mul_of_nonneg_right hp (by positivity)

private theorem square_root_cutoff_cost (N m n B C : Nat)
    (hN : 0 < N) (hm : 0 < m) (hn : 0 < n)
    (hB : m * B ^ 2 <= N) (hC : n * C ^ 2 <= N) :
    Real.sqrt ((B : Real) * (C : Real)) <=
      (N : Real) ^ (1 / 2 : Real) *
        ((m : Real) ^ (3 / 4 : Real) / (m : Real)) *
        ((n : Real) ^ (3 / 4 : Real) / (n : Real)) := by
  have hleft := quarter_cutoff N m B hm hB
  have hright := quarter_cutoff N n C hn hC
  calc
    _ = Real.sqrt (B : Real) * Real.sqrt (C : Real) :=
      Real.sqrt_mul (Nat.cast_nonneg B) _
    _ <= ((N : Real) ^ (1 / 4 : Real) *
          ((m : Real) ^ (3 / 4 : Real) / (m : Real))) *
        ((N : Real) ^ (1 / 4 : Real) *
          ((n : Real) ^ (3 / 4 : Real) / (n : Real))) :=
      mul_le_mul hleft hright (Real.sqrt_nonneg _) (by positivity)
    _ = ((N : Real) ^ (1 / 4 : Real) * (N : Real) ^ (1 / 4 : Real)) *
        ((m : Real) ^ (3 / 4 : Real) / (m : Real)) *
        ((n : Real) ^ (3 / 4 : Real) / (n : Real)) := by ring
    _ = _ := by
      rw [<- Real.rpow_add (Nat.cast_pos.mpr hN)]
      norm_num

private theorem physical_size_le (N H r u b d B C : Nat)
    (hb : 0 < b) (hd : 0 < d) (hm : r * b <= N) (hn : u * d <= N)
    (hB : B <= N) (hC : C <= N) :
    (H * r * (u * d) + H * u * (r * b) + r * b + u * d + 1) *
      (B + C + 1) <= (2 * H * N ^ 2 + 2 * N + 1) * (2 * N + 1) := by
  have hr : r <= N := (by nlinarith : r <= r * b).trans hm
  have hu : u <= N := (by nlinarith : u <= u * d).trans hn
  have hleft := Nat.mul_le_mul (Nat.mul_le_mul_left H hr) hn
  have hright := Nat.mul_le_mul (Nat.mul_le_mul_left H hu) hm
  apply Nat.mul_le_mul
  . nlinarith only [hleft, hright, hm, hn]
  . omega

/-- The complete cancelled row is bounded by two three-quarter hyperbola weights. -/
theorem physical_row_outer_cost (eps : Real) (heps : 0 < eps) :
    exists Ceps : Real, 0 < Ceps /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
      (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H r u b d B C D R T : Nat),
      0 < H -> 0 < r -> 0 < u -> 0 < b -> 0 < d -> 0 < D ->
      r * b <= 4 * D -> u * d <= 4 * D ->
      (r * b) * B ^ 2 <= 4 * D -> (u * d) * C ^ 2 <= 4 * D ->
      B <= 4 * D -> C <= 4 * D -> 0 < R -> 0 < T ->
      forall (f : SchwartzMap Real Complex),
      norm (CarmichaelSquarepartPhysical.physicalSquarepartRectangle
        chi G H r u b d B C D R T f) <=
        (Ceps * (((q * 3 : Nat) : Real) ^ 2) *
          (CarmichaelSquarepartCancellation.squareWindowBudget f) ^ 2 *
          (((2 * H * (4 * D) ^ 2 + 2 * (4 * D) + 1) *
            (2 * (4 * D) + 1) : Nat) : Real) ^ eps *
          ((4 * D : Nat) : Real) ^ (1 / 2 : Real)) *
        (norm (nativeCoefficient chi r) *
          (((r * b : Nat) : Real) ^ (3 / 4 : Real) / ((r * b : Nat) : Real))) *
        (norm (nativeCoefficient chi u) *
          (((u * d : Nat) : Real) ^ (3 / 4 : Real) / ((u * d : Nat) : Real))) := by
  choose Ceps hCeps hrow using
    CarmichaelSquarepartPhysical.physical_squarepart_rectangle_bound eps heps
  refine Exists.intro Ceps (And.intro hCeps ?_)
  intro q inst chi G hG H r u b d B C D R T hH hr hu hb hd hD hm hn hBc hCc hB hC hR hT f
  have hnorm := hrow chi G hG H r u b d B C D R T hH hr hu hb hd hD hBc hCc hR hT f
  have hs := Real.rpow_le_rpow
    (Nat.cast_nonneg ((H * r * (u * d) + H * u * (r * b) + r * b + u * d + 1) *
      (B + C + 1)))
    (Nat.cast_le.mpr (physical_size_le (4 * D) H r u b d B C hb hd hm hn hB hC))
    (le_of_lt heps)
  have hc := square_root_cutoff_cost (4 * D) (r * b) (u * d) B C
    (Nat.mul_pos (by decide) hD) (Nat.mul_pos hr hb) (Nat.mul_pos hu hd) hBc hCc
  calc
    _ <= norm (nativeCoefficient chi r) * norm (nativeCoefficient chi u) *
        (Ceps * (((q * 3 : Nat) : Real) ^ 2) *
          (CarmichaelSquarepartCancellation.squareWindowBudget f) ^ 2 *
          (((2 * H * (4 * D) ^ 2 + 2 * (4 * D) + 1) *
            (2 * (4 * D) + 1) : Nat) : Real) ^ eps *
          (((4 * D : Nat) : Real) ^ (1 / 2 : Real) *
            (((r * b : Nat) : Real) ^ (3 / 4 : Real) / ((r * b : Nat) : Real)) *
            (((u * d : Nat) : Real) ^ (3 / 4 : Real) / ((u * d : Nat) : Real)))) :=
      hnorm.trans (by gcongr)
    _ = _ := by ring

private theorem hyperbola_packet_norm {q : Nat}
    (chi : DirichletCharacter Complex q) (M L : Nat)
    (Z : Nat -> Nat -> Nat -> Nat -> Complex) (K : Real)
    (hterm : forall r, Membership.mem (Finset.Icc 1 M) r ->
      forall b, Membership.mem (Finset.Icc 1 (M / r)) b ->
      forall u, Membership.mem (Finset.Icc 1 L) u ->
      forall d, Membership.mem (Finset.Icc 1 (L / u)) d ->
      norm (Z r b u d) <=
        K * (norm (nativeCoefficient chi r) *
          (((r * b : Nat) : Real) ^ (3 / 4 : Real) / ((r * b : Nat) : Real))) *
        (norm (nativeCoefficient chi u) *
          (((u * d : Nat) : Real) ^ (3 / 4 : Real) / ((u * d : Nat) : Real)))) :
    norm ((Finset.Icc 1 M).sum (fun r => (Finset.Icc 1 (M / r)).sum (fun b =>
      (Finset.Icc 1 L).sum (fun u => (Finset.Icc 1 (L / u)).sum
        (fun d => Z r b u d))))) <= K * hyperbolaMass chi M * hyperbolaMass chi L := by
  let w := fun r b => norm (nativeCoefficient chi r) *
    (((r * b : Nat) : Real) ^ (3 / 4 : Real) / ((r * b : Nat) : Real))
  have hfactor (r b : Nat) :
      (Finset.Icc 1 L).sum (fun u => (Finset.Icc 1 (L / u)).sum
        (fun d => (K * w r b) * w u d)) = (K * w r b) * hyperbolaMass chi L := by
    simp_rw [<- Finset.mul_sum]
    rfl
  calc
    _ <= (Finset.Icc 1 M).sum (fun r => (Finset.Icc 1 (M / r)).sum (fun b =>
        (Finset.Icc 1 L).sum (fun u => (Finset.Icc 1 (L / u)).sum
          (fun d => (K * w r b) * w u d)))) := by
      apply norm_sum_le_of_le
      intro r hr
      apply norm_sum_le_of_le
      intro b hb
      apply norm_sum_le_of_le
      intro u hu
      apply norm_sum_le_of_le
      intro d hd
      exact hterm r hr b hb u hu d hd
    _ = (Finset.Icc 1 M).sum (fun r => (Finset.Icc 1 (M / r)).sum
        (fun b => (K * w r b) * hyperbolaMass chi L)) := by
      simp_rw [hfactor]
    _ = _ := by
      simp_rw [<- Finset.sum_mul, <- Finset.mul_sum]
      rfl

/-- Both square parts are large; its exact outer product cutoffs retain every phase. -/
def largeSquarePacket {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H D R T : Nat) (f : Real -> Complex) : Complex :=
  let M := 4 * D / R ^ 2
  let L := 4 * D / T ^ 2
  (Finset.Icc 1 M).sum (fun (r : Nat) => (Finset.Icc 1 (M / r)).sum (fun (b : Nat) =>
    (Finset.Icc 1 L).sum (fun (u : Nat) => (Finset.Icc 1 (L / u)).sum (fun (d : Nat) =>
      if Squarefree r /\ Squarefree u then
        (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
          star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3)))) *
          CarmichaelSquarepartPhysical.physicalSquarepartRectangle chi G H r u b d
            (Nat.sqrt (4 * D / (r * b))) (Nat.sqrt (4 * D / (u * d))) D R T f
      else 0))))

private theorem actual_square_cap (N m : Nat) (hm : 0 < m) :
    m * (Nat.sqrt (N / m)) ^ 2 <= N := by
  have h := Nat.le_sqrt.mp (le_rfl : Nat.sqrt (N / m) <= Nat.sqrt (N / m))
  have hh := (Nat.le_div_iff_mul_le hm).mp h
  nlinarith only [hh]

/-- Sum an isolated large-square sector after its full coupled rows are cancelled. -/
theorem large_square_packet_subpower (eps : Real) (heps : 0 < eps) :
    exists Ceps : Real, 0 < Ceps /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
      (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H D R T : Nat), 0 < H -> 0 < D -> 0 < R -> 0 < T ->
      forall (f : SchwartzMap Real Complex),
      norm (largeSquarePacket chi G H D R T f) <=
        Ceps * (((q * 3 : Nat) : Real) ^ 2) *
          (CarmichaelSquarepartCancellation.squareWindowBudget f) ^ 2 *
          (((2 * H * (4 * D) ^ 2 + 2 * (4 * D) + 1) *
            (2 * (4 * D) + 1) : Nat) : Real) ^ eps *
          ((4 * D : Nat) : Real) ^ (1 / 2 : Real) *
          ((4 * D / R ^ 2 : Nat) : Real) ^ (3 / 4 + eps : Real) *
          ((4 * D / T ^ 2 : Nat) : Real) ^ (3 / 4 + eps : Real) := by
  choose A hA hrow using physical_row_outer_cost eps heps
  choose B hB hmass using hyperbola_mass_subpower eps heps
  refine Exists.intro (A * B ^ 2) (And.intro (by positivity) ?_)
  intro q inst chi G hG H D R T hH hD hR hT f
  let M := 4 * D / R ^ 2
  let L := 4 * D / T ^ 2
  let K : Real := A * (((q * 3 : Nat) : Real) ^ 2) *
    (CarmichaelSquarepartCancellation.squareWindowBudget f) ^ 2 *
    (((2 * H * (4 * D) ^ 2 + 2 * (4 * D) + 1) *
      (2 * (4 * D) + 1) : Nat) : Real) ^ eps *
    ((4 * D : Nat) : Real) ^ (1 / 2 : Real)
  let Z : Nat -> Nat -> Nat -> Nat -> Complex := fun r b u d =>
    if Squarefree r /\ Squarefree u then
      (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
        star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3)))) *
        CarmichaelSquarepartPhysical.physicalSquarepartRectangle chi G H r u b d
          (Nat.sqrt (4 * D / (r * b))) (Nat.sqrt (4 * D / (u * d))) D R T f
    else 0
  have hK : 0 <= K := by dsimp only [K]; positivity
  have hM : M <= 4 * D := Nat.div_le_self _ _
  have hL : L <= 4 * D := Nat.div_le_self _ _
  have hpoint : forall r, Membership.mem (Finset.Icc 1 M) r ->
      forall b, Membership.mem (Finset.Icc 1 (M / r)) b ->
      forall u, Membership.mem (Finset.Icc 1 L) u ->
      forall d, Membership.mem (Finset.Icc 1 (L / u)) d ->
      norm (Z r b u d) <=
        K * (norm (nativeCoefficient chi r) *
          (((r * b : Nat) : Real) ^ (3 / 4 : Real) / ((r * b : Nat) : Real))) *
        (norm (nativeCoefficient chi u) *
          (((u * d : Nat) : Real) ^ (3 / 4 : Real) / ((u * d : Nat) : Real))) := by
    intro r hr b hb u hu d hd
    have hrp : 0 < r := (Finset.mem_Icc.mp hr).1
    have hup : 0 < u := (Finset.mem_Icc.mp hu).1
    have hbp : 0 < b := (Finset.mem_Icc.mp hb).1
    have hdp : 0 < d := (Finset.mem_Icc.mp hd).1
    have hm : r * b <= 4 * D := by
      have h := (Nat.le_div_iff_mul_le hrp).mp (Finset.mem_Icc.mp hb).2
      exact (by simpa only [Nat.mul_comm] using h : r * b <= M).trans hM
    have hn : u * d <= 4 * D := by
      have h := (Nat.le_div_iff_mul_le hup).mp (Finset.mem_Icc.mp hd).2
      exact (by simpa only [Nat.mul_comm] using h : u * d <= L).trans hL
    have hbound := hrow chi G hG H r u b d
      (Nat.sqrt (4 * D / (r * b))) (Nat.sqrt (4 * D / (u * d))) D R T
      hH hrp hup hbp hdp hD hm hn
      (actual_square_cap (4 * D) (r * b) (Nat.mul_pos hrp hbp))
      (actual_square_cap (4 * D) (u * d) (Nat.mul_pos hup hdp))
      ((Nat.sqrt_le_self _).trans (Nat.div_le_self _ _))
      ((Nat.sqrt_le_self _).trans (Nat.div_le_self _ _)) hR hT f
    dsimp only [Z]
    by_cases hs : Squarefree r /\ Squarefree u
    . rw [ite_eq_left hs, norm_mul, norm_mul, norm_star]
      have hphase :
          norm (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3))) *
            norm (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3))) <= 1 := by
        calc
          _ <= 1 * 1 := mul_le_mul
            ((OAI.ShortDraftHeckeBridge.baseChangeChar chi).norm_le_one _)
            ((OAI.ShortDraftHeckeBridge.baseChangeChar chi).norm_le_one _)
            (norm_nonneg _) (by norm_num)
          _ = _ := one_mul _
      calc
        _ <= 1 * norm (CarmichaelSquarepartPhysical.physicalSquarepartRectangle
            chi G H r u b d (Nat.sqrt (4 * D / (r * b)))
              (Nat.sqrt (4 * D / (u * d))) D R T f) :=
          mul_le_mul_of_nonneg_right hphase (norm_nonneg _)
        _ <= _ := by simpa only [one_mul, K] using hbound
    . rw [ite_eq_right hs, norm_zero]
      positivity
  have htotal : norm (largeSquarePacket chi G H D R T f) <=
      K * hyperbolaMass chi M * hyperbolaMass chi L := by
    exact hyperbola_packet_norm chi M L Z K hpoint
  have hmass0 (J : Nat) : 0 <= hyperbolaMass chi J := by
    unfold hyperbolaMass
    apply Finset.sum_nonneg
    intro r _
    apply Finset.sum_nonneg
    intro b _
    positivity
  calc
    _ <= K * (B * (M : Real) ^ (3 / 4 + eps : Real)) *
        (B * (L : Real) ^ (3 / 4 + eps : Real)) := by
      apply htotal.trans
      apply mul_le_mul
      . exact mul_le_mul_of_nonneg_left (hmass chi M) hK
      . exact hmass chi L
      . exact hmass0 L
      . positivity
    _ = _ := by dsimp only [K, M, L]; ring

private theorem sqrt_cutoff_lt (N m R : Nat) (hm : 0 < m) (hR : 0 < R)
    (hbad : N / R ^ 2 < m) : Nat.sqrt (N / m) < R := by
  by_contra h
  have hh := Nat.le_sqrt.mp (Nat.le_of_not_gt h)
  have hprod := (Nat.le_div_iff_mul_le hm).mp hh
  have hle : m <= N / R ^ 2 := by
    apply (Nat.le_div_iff_mul_le (pow_pos hR 2)).mpr
    nlinarith only [hprod]
  omega

/-- Every row omitted by either large-square product cutoff is identically zero. -/
theorem physical_row_zero_outside_square_cutoffs {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H r u b d D R T : Nat) (hr : 0 < r) (hu : 0 < u)
    (hb : 0 < b) (hd : 0 < d) (hR : 0 < R) (hT : 0 < T)
    (f : Real -> Complex)
    (hbad : 4 * D / R ^ 2 < r * b \/ 4 * D / T ^ 2 < u * d) :
    CarmichaelSquarepartPhysical.physicalSquarepartRectangle chi G H r u b d
      (Nat.sqrt (4 * D / (r * b))) (Nat.sqrt (4 * D / (u * d))) D R T f = 0 := by
  rcases hbad with hbad | hbad
  . have hempty := sqrt_cutoff_lt (4 * D) (r * b) R (Nat.mul_pos hr hb) hR hbad
    simp only [CarmichaelSquarepartPhysical.physicalSquarepartRectangle,
      Finset.Icc_eq_empty_of_lt hempty, Finset.sum_empty]
  . have hempty := sqrt_cutoff_lt (4 * D) (u * d) T (Nat.mul_pos hu hd) hT hbad
    simp only [CarmichaelSquarepartPhysical.physicalSquarepartRectangle,
      Finset.Icc_eq_empty_of_lt hempty, Finset.sum_empty, Finset.sum_const_zero]

private theorem truncate_hyperbola (N M : Nat) (F : Nat -> Nat -> Complex)
    (hMN : M <= N)
    (hzero : forall r b, 0 < r -> 0 < b -> M < r * b -> F r b = 0) :
    (Finset.Icc 1 N).sum (fun r => (Finset.Icc 1 (N / r)).sum (F r)) =
      (Finset.Icc 1 M).sum (fun r => (Finset.Icc 1 (M / r)).sum (F r)) := by
  calc
    _ = (Finset.Icc 1 M).sum (fun r => (Finset.Icc 1 (N / r)).sum (F r)) := by
      symm
      apply Finset.sum_subset
        (fun r hr => Finset.mem_Icc.mpr
          (And.intro (Finset.mem_Icc.mp hr).1 ((Finset.mem_Icc.mp hr).2.trans hMN)))
      intro r hr hn
      apply Finset.sum_eq_zero
      intro b hb
      have hrp : 0 < r := (Finset.mem_Icc.mp hr).1
      have hbp : 0 < b := (Finset.mem_Icc.mp hb).1
      have hMr : M < r := by
        have hh := Finset.mem_Icc.mp hr
        simp only [Finset.mem_Icc, not_and] at hn
        exact Nat.lt_of_not_ge (hn hh.1)
      exact hzero r b hrp hbp (by nlinarith)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      symm
      apply Finset.sum_subset
        (fun b hb => Finset.mem_Icc.mpr
          (And.intro (Finset.mem_Icc.mp hb).1
            ((Finset.mem_Icc.mp hb).2.trans (Nat.div_le_div_right hMN))))
      intro b hb hn
      have hrp : 0 < r := (Finset.mem_Icc.mp hr).1
      have hbp : 0 < b := (Finset.mem_Icc.mp hb).1
      apply hzero r b hrp hbp
      by_contra hprod
      have hle : b <= M / r :=
        (Nat.le_div_iff_mul_le hrp).mpr (by nlinarith only [Nat.le_of_not_gt hprod])
      exact hn (Finset.mem_Icc.mpr (And.intro hbp hle))

/-- The sector in the original full outer domain, before any cutoff restriction. -/
def fullLargeSquarePacket {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H D R T : Nat) (f : Real -> Complex) : Complex :=
  (Finset.Icc 1 (4 * D)).sum (fun (r : Nat) =>
    (Finset.Icc 1 (4 * D / r)).sum (fun (b : Nat) =>
      (Finset.Icc 1 (4 * D)).sum (fun (u : Nat) =>
        (Finset.Icc 1 (4 * D / u)).sum (fun (d : Nat) =>
          if Squarefree r /\ Squarefree u then
            (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
              star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3)))) *
              CarmichaelSquarepartPhysical.physicalSquarepartRectangle chi G H r u b d
                (Nat.sqrt (4 * D / (r * b))) (Nat.sqrt (4 * D / (u * d))) D R T f
          else 0))))

/-- The aggregate estimate is on the complete sector, with every nonzero row present. -/
theorem large_square_packet_full_support {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H D R T : Nat) (hR : 0 < R) (hT : 0 < T) (f : Real -> Complex) :
    fullLargeSquarePacket chi G H D R T f = largeSquarePacket chi G H D R T f := by
  let M := 4 * D / R ^ 2
  let L := 4 * D / T ^ 2
  let F : Nat -> Nat -> Nat -> Nat -> Complex := fun r b u d =>
    if Squarefree r /\ Squarefree u then
      (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
        star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3)))) *
        CarmichaelSquarepartPhysical.physicalSquarepartRectangle chi G H r u b d
          (Nat.sqrt (4 * D / (r * b))) (Nat.sqrt (4 * D / (u * d))) D R T f
    else 0
  have hF (r b u d : Nat) (hr : 0 < r) (hb : 0 < b)
      (hu : 0 < u) (hd : 0 < d) (hbad : M < r * b \/ L < u * d) :
      F r b u d = 0 := by
    have he := physical_row_zero_outside_square_cutoffs chi G H r u b d D R T
      hr hu hb hd hR hT f hbad
    dsimp only [F]
    by_cases hs : Squarefree r /\ Squarefree u
    . rw [ite_eq_left hs, he, mul_zero]
    . exact ite_eq_right hs
  change (Finset.Icc 1 (4 * D)).sum (fun r =>
      (Finset.Icc 1 (4 * D / r)).sum (fun b =>
        (Finset.Icc 1 (4 * D)).sum (fun u =>
          (Finset.Icc 1 (4 * D / u)).sum (fun d => F r b u d)))) =
    (Finset.Icc 1 M).sum (fun r => (Finset.Icc 1 (M / r)).sum (fun b =>
      (Finset.Icc 1 L).sum (fun u => (Finset.Icc 1 (L / u)).sum (fun d => F r b u d))))
  calc
    _ = (Finset.Icc 1 M).sum (fun r => (Finset.Icc 1 (M / r)).sum (fun b =>
        (Finset.Icc 1 (4 * D)).sum (fun u =>
          (Finset.Icc 1 (4 * D / u)).sum (fun d => F r b u d)))) := by
      apply truncate_hyperbola (4 * D) M _ (Nat.div_le_self _ _)
      intro r b hr hb hbad
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro d hd
      exact hF r b u d hr hb (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hd).1
        (Or.inl hbad)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro b hb
      apply truncate_hyperbola (4 * D) L _ (Nat.div_le_self _ _)
      intro u d hu hd hbad
      exact hF r b u d (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hb).1 hu hd
        (Or.inr hbad)

/-- The full large-square sector has the same unconditional power estimate. -/
theorem full_large_square_packet_subpower (eps : Real) (heps : 0 < eps) :
    exists Ceps : Real, 0 < Ceps /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
      (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H D R T : Nat), 0 < H -> 0 < D -> 0 < R -> 0 < T ->
      forall (f : SchwartzMap Real Complex),
      norm (fullLargeSquarePacket chi G H D R T f) <=
        Ceps * (((q * 3 : Nat) : Real) ^ 2) *
          (CarmichaelSquarepartCancellation.squareWindowBudget f) ^ 2 *
          (((2 * H * (4 * D) ^ 2 + 2 * (4 * D) + 1) *
            (2 * (4 * D) + 1) : Nat) : Real) ^ eps *
          ((4 * D : Nat) : Real) ^ (1 / 2 : Real) *
          ((4 * D / R ^ 2 : Nat) : Real) ^ (3 / 4 + eps : Real) *
          ((4 * D / T ^ 2 : Nat) : Real) ^ (3 / 4 + eps : Real) := by
  choose Ceps hCeps hbound using large_square_packet_subpower eps heps
  refine Exists.intro Ceps (And.intro hCeps ?_)
  intro q inst chi G hG H D R T hH hD hR hT f
  rw [large_square_packet_full_support chi G H D R T hR hT f]
  exact hbound chi G hG H D R T hH hD hR hT f

/-- At unit lower endpoints the sector is exactly the original full signed rational unit. -/
theorem rational_unit_full_sector {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H D : Nat) (f : Real -> Complex) :
    CarmichaelNativeHyperbola.rationalUnit chi G H (4 * D)
        (fun n => f ((n : Real) / (D : Real))) =
      fullLargeSquarePacket chi G H D 1 1 f := by
  rw [CarmichaelSquarepartPhysical.rational_unit_physical_squarepart_rows]
  unfold fullLargeSquarePacket
  simp_rw [Finset.sum_filter]
  let F : Nat -> Nat -> Nat -> Nat -> Complex := fun r b u d =>
    (OAI.ShortDraftHeckeBridge.baseChangeChar chi (b : ZMod (q * 3)) *
      star (OAI.ShortDraftHeckeBridge.baseChangeChar chi (d : ZMod (q * 3)))) *
      CarmichaelSquarepartPhysical.physicalSquarepartRectangle chi G H r u b d
        (Nat.sqrt (4 * D / (r * b))) (Nat.sqrt (4 * D / (u * d))) D 1 1 f
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : Squarefree r
  . simp only [hr, ite_true, true_and]
    change (Finset.Icc 1 (4 * D)).sum (fun u =>
        if Squarefree u then
          (Finset.Icc 1 (4 * D / r)).sum (fun b =>
            (Finset.Icc 1 (4 * D / u)).sum (fun d => F r b u d))
        else 0) =
      (Finset.Icc 1 (4 * D / r)).sum (fun b =>
        (Finset.Icc 1 (4 * D)).sum (fun u =>
          (Finset.Icc 1 (4 * D / u)).sum
            (fun d => if Squarefree u then F r b u d else 0)))
    calc
      _ = (Finset.Icc 1 (4 * D)).sum (fun u =>
          (Finset.Icc 1 (4 * D / r)).sum (fun b =>
            (Finset.Icc 1 (4 * D / u)).sum
              (fun d => if Squarefree u then F r b u d else 0))) := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : Squarefree u
        . simp only [hu, ite_true]
        . simp only [hu, ite_false, Finset.sum_const_zero]
      _ = _ := Finset.sum_comm
  . simp only [hr, ite_false, false_and, Finset.sum_const_zero]

end PrimeFactorOscillations.CarmichaelLargeSquareRemainder

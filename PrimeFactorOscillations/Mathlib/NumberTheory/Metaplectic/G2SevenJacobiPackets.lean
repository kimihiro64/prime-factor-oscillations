/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenJacobiReadout

/-!
# Coupled native Jacobi packets and compensated boundary reciprocity

The roots are extracted from the actual compensated source probes.
All torus weights remain. The six-factor packet becomes homogeneously
reciprocal at the first period boundary, using the continuous extension
of the compensated mean rather than a divergent period sum.
The lifting theorem has an explicit modified-Gauss lifting hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Jacobi

open Cubic Spectrum

/-- Every individual readout has the same physical absolute-box defect. -/
theorem powers_defect : forall i : Fin 8,
    7 * powers i 0 = 15 + 2 * (powers i 1 + powers i 2) := by decide

private theorem period_box_general (d A B s : Real)
    (hA : 0 < A) (hB : 0 < B) (hid : 7 * d = 15 + 2 * (A + B)) :
    (Exists fun u : Real => Exists fun v : Real =>
      u < 1 / 7 /\ v < 1 / 7 /\ A * u + B * v = d / 2 - s) <->
      15 / 14 < s := by
  constructor
  . intro hs
    cases hs with
    | intro u hu =>
      cases hu with
      | intro v hv =>
        have ha := mul_lt_mul_of_pos_left hv.1 hA
        have hb := mul_lt_mul_of_pos_left hv.2.1 hB
        linarith [hv.2.2]
  . intro hs
    have hpos : 0 < A + B := add_pos hA hB
    let w := (d / 2 - s) / (A + B)
    have hwid : (A + B) * w = d / 2 - s := by
      dsimp [w]
      field_simp [ne_of_gt hpos]
    have hw : w < 1 / 7 := by
      by_contra h
      have hn := mul_nonneg (le_of_lt hpos) (sub_nonneg.mpr (le_of_not_gt h))
      nlinarith [hwid]
    apply Exists.intro w
    apply Exists.intro w
    exact And.intro hw (And.intro hw (by calc
      A * w + B * w = (A + B) * w := by ring
      _ = d / 2 - s := hwid))

/-- Exact common range, retaining each individual native torus weight. -/
theorem individual_period_box (i : Fin 8) (s : Real) :
    (Exists fun u : Real => Exists fun v : Real =>
      u < 1 / 7 /\ v < 1 / 7 /\
      (powers i 1 : Real) * u + (powers i 2 : Real) * v =
        (powers i 0 : Real) / 2 - s) <-> 15 / 14 < s := by
  apply period_box_general
  . fin_cases i <;> norm_num [powers]
  . fin_cases i <;> norm_num [powers]
  . fin_cases i <;> norm_num [powers]

/-- The finite compensated mean extends continuously across the period boundary. -/
theorem finite_mean_continuous_X (i : Fin 8) (t g h j Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    Continuous (fun X : Complex => mean (finiteProbe i t g h j X Y)) := by
  have heq : (fun X : Complex => mean (finiteProbe i t g h j X Y)) =
      (fun X : Complex => 1 - phase i g h j * weight i t X Y) := by
    funext X
    exact finite_probe_mean i t g h j X Y hg hh hj
  rw [heq]
  have hw : Continuous (fun X : Complex => weight i t X Y) :=
    (continuous_const.mul (continuous_id.pow (powers i 1))).mul continuous_const
  exact continuous_const.sub (continuous_const.mul hw)

/-- Filtered extension on the nonzero-denominator domain. -/
theorem coherent_mean_tendsto_X (i : Fin 8) (t g h j Y X0 : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    Filter.Tendsto (fun X : Complex => mean (coherentProbe i t g h j X Y))
      (nhdsWithin X0 (fun X : Complex => Not (periodDenominator t X Y = 0)))
      (nhds (1 - phase i g h j * weight i t X0 Y)) := by
  let S : Set Complex := fun X => Not (periodDenominator t X Y = 0)
  have hf := (finite_mean_continuous_X i t g h j Y hg hh hj).tendsto X0
  have hw : Filter.Tendsto (fun X : Complex => mean (finiteProbe i t g h j X Y))
      (nhdsWithin X0 S) (nhds (mean (finiteProbe i t g h j X0 Y))) :=
    hf.mono_left nhdsWithin_le_nhds
  have heq : Filter.EventuallyEq (nhdsWithin X0 S)
      (fun X : Complex => mean (finiteProbe i t g h j X Y))
      (fun X : Complex => mean (coherentProbe i t g h j X Y)) := by
    apply Filter.Eventually.mono self_mem_nhdsWithin
    intro X hX
    unfold mean
    simp_rw [coherent_probe_eq i t g h j X Y hX]
  have ht := Filter.Tendsto.congr' heq hw
  simpa only [finite_probe_mean i t g h j X0 Y hg hh hj] using ht

noncomputable def extracted (i : Fin 8) (v : Fin 7 -> Complex) : Complex :=
  mean (probe i v) - 1

theorem extracted_eq (i : Fin 8) (v : Fin 7 -> Complex) :
    extracted i v = -tripleProduct i v := by
  rw [extracted, probe_mean]
  ring

private theorem grade_positive : forall (i : Fin 8) (j : Fin 3),
    0 < (grade i j).val := by decide

/-- Conditional algebraic transfer of the modified-Gauss Hasse--Davenport law. -/
theorem extracted_lift (i : Fin 8) (v w : Fin 7 -> Complex) (n : Nat)
    (hlift : forall r : Fin 7, 0 < r.val -> -w r = (-v r) ^ n) :
    extracted i w = (extracted i v) ^ n := by
  rw [extracted_eq, extracted_eq]
  unfold tripleProduct
  calc
    -(w (grade i 0) * w (grade i 1) * w (grade i 2)) =
        (-w (grade i 0)) * (-w (grade i 1)) * (-w (grade i 2)) := by ring
    _ = (-v (grade i 0)) ^ n * (-v (grade i 1)) ^ n * (-v (grade i 2)) ^ n := by
      rw [hlift (grade i 0) (grade_positive i 0),
        hlift (grade i 1) (grade_positive i 1), hlift (grade i 2) (grade_positive i 2)]
    _ = ((-v (grade i 0)) * (-v (grade i 1)) * (-v (grade i 2))) ^ n := by
      rw [mul_pow, mul_pow]
    _ = (-(v (grade i 0) * v (grade i 1) * v (grade i 2))) ^ n := by
      congr 1
      ring

noncomputable def eigenvalue (i : Fin 8) (t g h j X Y : Complex) : Complex :=
  mean (finiteProbe i t g h j X Y) - 1

theorem eigenvalue_eq (i : Fin 8) (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    eigenvalue i t g h j X Y = -(phase i g h j * weight i t X Y) := by
  rw [eigenvalue, finite_probe_mean i t g h j X Y hg hh hj]
  ring

noncomputable def eulerProbe (i : Fin 8) (t g h j X Y : Complex) (a : ZMod 7) : Complex :=
  2 - finiteProbe i t g h j X Y a

/-- The sign-corrected Euler probe has mean one minus the native extracted root. -/
theorem euler_probe_mean (i : Fin 8) (t g h j X Y : Complex) :
    mean (eulerProbe i t g h j X Y) = 1 - eigenvalue i t g h j X Y := by
  unfold eulerProbe eigenvalue
  unfold mean
  rw [Finset.sum_sub_distrib]
  norm_num
  ring

/-- Both three-root determinants retain their quadratic companion and exact native weight. -/
theorem native_norm_relations (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    eigenvalue 0 t g h j X Y * eigenvalue 3 t g h j X Y * eigenvalue 6 t g h j X Y =
        eigenvalue 1 t g h j X Y * (readoutMonomial t X Y) ^ 2 /\
    eigenvalue 2 t g h j X Y * eigenvalue 4 t g h j X Y * eigenvalue 7 t g h j X Y =
        eigenvalue 5 t g h j X Y * (readoutMonomial t X Y) ^ 2 := by
  have he (i : Fin 8) := eigenvalue_eq i t g h j X Y hg hh hj
  simp_rw [he]
  constructor <;> norm_num [phase, weight, powers, readoutMonomial] <;>
    field_simp [hg, hh, hj] <;> ring

/-- Exact paired products throughout the full torus; all native distortions remain. -/
theorem native_pair_products (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    eigenvalue 0 t g h j X Y * eigenvalue 4 t g h j X Y = (readoutMonomial t X Y) ^ 2 /\
    (t ^ 2 * X ^ 7) * (eigenvalue 2 t g h j X Y * eigenvalue 6 t g h j X Y) =
      (readoutMonomial t X Y) ^ 2 /\
    eigenvalue 3 t g h j X Y * eigenvalue 7 t g h j X Y =
      (t ^ 2 * X ^ 7) * (readoutMonomial t X Y) ^ 2 := by
  have he (i : Fin 8) := eigenvalue_eq i t g h j X Y hg hh hj
  simp_rw [he]
  constructor
  . norm_num [phase, weight, powers, readoutMonomial]
    field_simp [hg, hh, hj] <;> ring
  constructor <;> norm_num [phase, weight, powers, readoutMonomial] <;>
    field_simp [hg, hh, hj] <;> ring

/-- Reciprocal pairs are exact at the first period boundary; no individual weight is replaced. -/
theorem native_inverse_pairs (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0))
    (hX : t ^ 2 * X ^ 7 = 1) :
    eigenvalue 0 t g h j X Y * eigenvalue 4 t g h j X Y = (readoutMonomial t X Y) ^ 2 /\
    eigenvalue 2 t g h j X Y * eigenvalue 6 t g h j X Y = (readoutMonomial t X Y) ^ 2 /\
    eigenvalue 3 t g h j X Y * eigenvalue 7 t g h j X Y = (readoutMonomial t X Y) ^ 2 := by
  have hp := native_pair_products t g h j X Y hg hh hj
  simpa only [hX, one_mul] using hp

def packet6 (a b c d e f U V : Complex) : Complex :=
  ((U - a * V) * (U - b * V)) * ((U - c * V) * (U - d * V)) *
    ((U - e * V) * (U - f * V))

private theorem pair_swap (a b W U V : Complex) (hab : a * b = W ^ 2) :
    (W ^ 2 * V - a * U) * (W ^ 2 * V - b * U) =
      W ^ 2 * ((U - a * V) * (U - b * V)) := by
  rw [<- hab]
  ring

theorem packet6_swap (a b c d e f W U V : Complex)
    (hab : a * b = W ^ 2) (hcd : c * d = W ^ 2) (hef : e * f = W ^ 2) :
    packet6 a b c d e f (W ^ 2 * V) U = W ^ 6 * packet6 a b c d e f U V := by
  unfold packet6
  rw [pair_swap a b W U V hab, pair_swap c d W U V hcd, pair_swap e f W U V hef]
  ring

noncomputable def nativePacket (t g h j X Y U V : Complex) : Complex :=
  packet6 (eigenvalue 0 t g h j X Y) (eigenvalue 4 t g h j X Y)
    (eigenvalue 2 t g h j X Y) (eigenvalue 6 t g h j X Y)
    (eigenvalue 3 t g h j X Y) (eigenvalue 7 t g h j X Y) U V

/-- Full homogeneous reciprocity of the six actual compensated-readout roots. -/
theorem native_packet_reciprocity (t g h j X Y U V : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0))
    (hX : t ^ 2 * X ^ 7 = 1) :
    nativePacket t g h j X Y ((readoutMonomial t X Y) ^ 2 * V) U =
      (readoutMonomial t X Y) ^ 6 * nativePacket t g h j X Y U V := by
  have hp := native_inverse_pairs t g h j X Y hg hh hj hX
  unfold nativePacket
  exact packet6_swap _ _ _ _ _ _ (readoutMonomial t X Y) U V hp.1 hp.2.1 hp.2.2

private theorem seventh_power_lt_one (r : Real) (hr0 : 0 <= r) (hr1 : r < 1) :
    r ^ 7 < 1 := by
  have hs : 0 < r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by
    linarith [pow_nonneg hr0 6, pow_nonneg hr0 5, pow_nonneg hr0 4,
      pow_nonneg hr0 3, pow_nonneg hr0 2]
  have hp := mul_pos (sub_pos.mpr hr1) hs
  nlinarith [hp]

/-- Every interior radial point has both complete periods absolutely convergent. -/
theorem radial_domain (t X0 Y0 : Complex)
    (hX : t ^ 2 * X0 ^ 7 = 1) (hY : t ^ 2 * Y0 ^ 7 = 1)
    (r : Real) (hr0 : 0 <= r) (hr1 : r < 1) :
    norm (t ^ 2 * ((r : Complex) * X0) ^ 7) < 1 /\
    norm (t ^ 2 * ((r : Complex) * Y0) ^ 7) < 1 /\
    Not (periodDenominator t ((r : Complex) * X0) ((r : Complex) * Y0) = 0) := by
  have hx : t ^ 2 * ((r : Complex) * X0) ^ 7 = (r : Complex) ^ 7 := by
    rw [mul_pow]
    calc
      t ^ 2 * ((r : Complex) ^ 7 * X0 ^ 7) =
          (r : Complex) ^ 7 * (t ^ 2 * X0 ^ 7) := by ring
      _ = _ := by rw [hX]; ring
  have hy : t ^ 2 * ((r : Complex) * Y0) ^ 7 = (r : Complex) ^ 7 := by
    rw [mul_pow]
    calc
      t ^ 2 * ((r : Complex) ^ 7 * Y0 ^ 7) =
          (r : Complex) ^ 7 * (t ^ 2 * Y0 ^ 7) := by ring
      _ = _ := by rw [hY]; ring
  have hrn : norm (r : Complex) = r := by
    simp [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hr7 := seventh_power_lt_one r hr0 hr1
  have hn : norm ((r : Complex) ^ 7) < 1 := by
    rw [norm_pow, hrn]
    exact hr7
  have hz : Not (1 - (r : Complex) ^ 7 = 0) := by
    intro heq
    have hp : (r : Complex) ^ 7 = 1 := (sub_eq_zero.mp heq).symm
    rw [hp] at hn
    norm_num at hn
  exact And.intro (by simpa only [hx] using hn)
    (And.intro (by simpa only [hy] using hn) (by
      unfold periodDenominator
      rw [hx, hy]
      exact mul_ne_zero hz hz))

/-- Nonvacuous joint Abel limit at the double period boundary, with both factors retained. -/
theorem radial_abel_limit (i : Fin 8) (t g h j X0 Y0 : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0))
    (hX : t ^ 2 * X0 ^ 7 = 1) (hY : t ^ 2 * Y0 ^ 7 = 1) :
    Filter.NeBot (nhdsWithin (1 : Real) (Set.Iio 1)) /\
    Filter.Tendsto (fun r : Real =>
      mean (coherentProbe i t g h j ((r : Complex) * X0) ((r : Complex) * Y0)))
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds (1 - phase i g h j * weight i t X0 Y0)) := by
  constructor
  . infer_instance
  let F : Real -> Complex := fun r =>
    mean (finiteProbe i t g h j ((r : Complex) * X0) ((r : Complex) * Y0))
  have heqF : F = (fun r : Real =>
      1 - phase i g h j * weight i t ((r : Complex) * X0) ((r : Complex) * Y0)) := by
    funext r
    exact finite_probe_mean i t g h j _ _ hg hh hj
  have hcont : Continuous F := by
    rw [heqF]
    have hx : Continuous (fun r : Real => (r : Complex) * X0) :=
      Complex.continuous_ofReal.mul continuous_const
    have hy : Continuous (fun r : Real => (r : Complex) * Y0) :=
      Complex.continuous_ofReal.mul continuous_const
    have hw : Continuous (fun r : Real =>
        weight i t ((r : Complex) * X0) ((r : Complex) * Y0)) :=
      (continuous_const.mul (hx.pow (powers i 1))).mul (hy.pow (powers i 2))
    exact continuous_const.sub (continuous_const.mul hw)
  have hf : Filter.Tendsto F (nhdsWithin (1 : Real) (Set.Iio 1)) (nhds (F 1)) :=
    (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hr0 : Filter.Eventually (fun r : Real => 0 < r)
      (nhdsWithin (1 : Real) (Set.Iio 1)) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (by norm_num : (0 : Real) < 1))
  have hr1 : Filter.Eventually (fun r : Real => r < 1)
      (nhdsWithin (1 : Real) (Set.Iio 1)) := self_mem_nhdsWithin
  have heq : Filter.EventuallyEq (nhdsWithin (1 : Real) (Set.Iio 1)) F
      (fun r : Real =>
        mean (coherentProbe i t g h j ((r : Complex) * X0) ((r : Complex) * Y0))) := by
    apply Filter.Eventually.mono (hr0.and hr1)
    intro r hr
    have hd := (radial_domain t X0 Y0 hX hY r (le_of_lt hr.1) hr.2).2.2
    dsimp [F]
    unfold mean
    simp_rw [coherent_probe_eq i t g h j _ _ hd]
  have ht := Filter.Tendsto.congr' heq hf
  simpa only [F, Complex.ofReal_one, one_mul,
    finite_probe_mean i t g h j X0 Y0 hg hh hj] using ht

noncomputable def coherentPacket (t g h j X Y U V : Complex) : Complex :=
  packet6 (mean (coherentProbe 0 t g h j X Y) - 1)
    (mean (coherentProbe 4 t g h j X Y) - 1)
    (mean (coherentProbe 2 t g h j X Y) - 1)
    (mean (coherentProbe 6 t g h j X Y) - 1)
    (mean (coherentProbe 3 t g h j X Y) - 1)
    (mean (coherentProbe 7 t g h j X Y) - 1) U V

/-- The complete coherent packet has a nontrivial joint Abel limit and exact boundary reciprocity. -/
theorem abel_packet_reciprocity (t g h j X0 Y0 U V : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0))
    (hX : t ^ 2 * X0 ^ 7 = 1) (hY : t ^ 2 * Y0 ^ 7 = 1) :
    Filter.NeBot (nhdsWithin (1 : Real) (Set.Iio 1)) /\
    Filter.Tendsto (fun r : Real =>
      coherentPacket t g h j ((r : Complex) * X0) ((r : Complex) * Y0) U V)
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds (nativePacket t g h j X0 Y0 U V)) /\
    nativePacket t g h j X0 Y0 ((readoutMonomial t X0 Y0) ^ 2 * V) U =
      (readoutMonomial t X0 Y0) ^ 6 * nativePacket t g h j X0 Y0 U V := by
  constructor
  . infer_instance
  constructor
  . have he (i : Fin 8) :
        (1 - phase i g h j * weight i t X0 Y0) - 1 =
          eigenvalue i t g h j X0 Y0 := by
      rw [eigenvalue_eq i t g h j X0 Y0 hg hh hj]
      ring
    have hl (i : Fin 8) : Filter.Tendsto (fun r : Real =>
        mean (coherentProbe i t g h j ((r : Complex) * X0) ((r : Complex) * Y0)) - 1)
        (nhdsWithin (1 : Real) (Set.Iio 1)) (nhds (eigenvalue i t g h j X0 Y0)) := by
      have hs : Filter.Tendsto (fun r : Real =>
          mean (coherentProbe i t g h j ((r : Complex) * X0) ((r : Complex) * Y0)) - 1)
          (nhdsWithin (1 : Real) (Set.Iio 1))
          (nhds ((1 - phase i g h j * weight i t X0 Y0) - 1)) :=
        (radial_abel_limit i t g h j X0 Y0 hg hh hj hX hY).2.sub tendsto_const_nhds
      simpa only [he i] using hs
    have hf (i : Fin 8) : Filter.Tendsto (fun r : Real =>
        U - (mean (coherentProbe i t g h j ((r : Complex) * X0) ((r : Complex) * Y0)) - 1) * V)
        (nhdsWithin (1 : Real) (Set.Iio 1))
        (nhds (U - eigenvalue i t g h j X0 Y0 * V)) :=
      tendsto_const_nhds.sub ((hl i).mul tendsto_const_nhds)
    unfold coherentPacket nativePacket packet6
    exact (((hf 0).mul (hf 4)).mul ((hf 2).mul (hf 6))).mul ((hf 3).mul (hf 7))
  . exact native_packet_reciprocity t g h j X0 Y0 U V hg hh hj hX

/-- A canonical double-boundary point makes all eight native scales exactly equal. -/
theorem balanced_corner (u : Complex) (hu : Not (u = 0)) :
    (u ^ 7) ^ 2 * (1 / u ^ 2) ^ 7 = 1 /\
    forall i : Fin 8, weight i (u ^ 7) (1 / u ^ 2) (1 / u ^ 2) = u ^ 15 := by
  constructor
  . field_simp [hu] <;> ring
  intro i
  fin_cases i <;> norm_num [weight, powers] <;> field_simp [hu] <;> ring

/-- All eight signed Jacobi phases are recovered by a nontrivial normalized Abel limit. -/
theorem normalized_abel_readout (i : Fin 8) (u g h j : Complex)
    (hu : Not (u = 0)) (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    Filter.NeBot (nhdsWithin (1 : Real) (Set.Iio 1)) /\
    Filter.Tendsto (fun r : Real =>
      (mean (coherentProbe i (u ^ 7) g h j
        ((r : Complex) * (1 / u ^ 2)) ((r : Complex) * (1 / u ^ 2))) - 1) / u ^ 15)
      (nhdsWithin (1 : Real) (Set.Iio 1)) (nhds (-phase i g h j)) := by
  have hc := balanced_corner u hu
  have hl := radial_abel_limit i (u ^ 7) g h j (1 / u ^ 2) (1 / u ^ 2)
    hg hh hj hc.1 hc.1
  constructor
  . exact hl.1
  have he : ((1 - phase i g h j * weight i (u ^ 7) (1 / u ^ 2) (1 / u ^ 2)) - 1) /
      u ^ 15 = -phase i g h j := by
    rw [hc.2 i]
    field_simp [hu] <;> ring
  have ht : Filter.Tendsto (fun r : Real =>
      (mean (coherentProbe i (u ^ 7) g h j
        ((r : Complex) * (1 / u ^ 2)) ((r : Complex) * (1 / u ^ 2))) - 1) / u ^ 15)
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds (((1 - phase i g h j * weight i (u ^ 7) (1 / u ^ 2) (1 / u ^ 2)) - 1) /
        u ^ 15)) := by
    simpa only [div_eq_mul_inv] using
      ((hl.2.sub tendsto_const_nhds).mul (tendsto_const_nhds (x := Inv.inv (u ^ 15))))
  simpa only [he] using ht

end Metaplectic.G2Seven.Jacobi

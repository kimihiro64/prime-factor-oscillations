/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.KernelRestriction

/-! # Uniform signed kernel comparison after finite-fibre sampling

Exact fibre pushforward retains the full signed kernel. An independent upper
occupancy estimate controls its energy. The complete two-mode comparison also
retains every sparse exceptional rectangle and both squared-mean corrections.
All resulting errors are uniform over arbitrary real test functions.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace Finset

variable {I J : Type*} [DecidableEq J]

def fiberTotal (s : Finset I) (g : I -> J) (f : I -> Real) (u : J) : Real :=
  (s.filter (fun i => g i = u)).sum f

theorem sum_mul_fiberTotal (s : Finset I) (U : Finset J) (g : I -> J)
    (hmap : forall i, Membership.mem s i -> Membership.mem U (g i))
    (f : I -> Real) (H : J -> Real) :
    U.sum (fun u => H u * fiberTotal s g f u) =
      s.sum (fun i => H (g i) * f i) := by
  have h := sum_fiberwise_of_maps_to hmap (fun i => H (g i) * f i)
  rw [<- h]
  apply sum_congr rfl
  intro u hu
  unfold fiberTotal
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [(mem_filter.mp hi).2]

/-- Exact signed pushforward, for arbitrary real kernels and two test functions. -/
theorem kernelBilinear_fiberTotal (s : Finset I) (U : Finset J) (g : I -> J)
    (hmap : forall i, Membership.mem s i -> Membership.mem U (g i))
    (K : J -> J -> Real) (f b : I -> Real) :
    kernelBilinear s (fun i j => K (g i) (g j)) f b =
      kernelBilinear U K (fiberTotal s g f) (fiberTotal s g b) := by
  calc
    _ = s.sum (fun i => s.sum (fun j => K (g i) (g j) * b j) * f i) := by
      unfold kernelBilinear
      apply sum_congr rfl
      intro i hi
      rw [sum_mul]
      apply sum_congr rfl
      intro j hj
      ring1
    _ = s.sum (fun i => U.sum (fun u => K (g i) u * fiberTotal s g b u) * f i) := by
      apply sum_congr rfl
      intro i hi
      rw [sum_mul_fiberTotal s U g hmap b (K (g i))]
    _ = U.sum (fun u => U.sum (fun v => K u v * fiberTotal s g b v) *
        fiberTotal s g f u) :=
      (sum_mul_fiberTotal s U g hmap f
        (fun u => U.sum (fun v => K u v * fiberTotal s g b v))).symm
    _ = _ := by
      unfold kernelBilinear
      apply sum_congr rfl
      intro u hu
      rw [sum_mul]
      apply sum_congr rfl
      intro v hv
      ring1

/-- Uniform fibre occupancy bounds energy; no fibre mean is divided by its size. -/
theorem mul_sum_sq_fiberTotal_le (s : Finset I) (U : Finset J) (g : I -> J)
    (hmap : forall i, Membership.mem s i -> Membership.mem U (g i))
    (f : I -> Real) (W C : Real) (hW : 0 <= W)
    (hcount : forall u, Membership.mem U u ->
      W * ((s.filter (fun i => g i = u)).card : Real) <= C) :
    W * U.sum (fun u => (fiberTotal s g f u) ^ 2) <=
      C * s.sum (fun i => (f i) ^ 2) := by
  have hlocal (u : J) (hu : Membership.mem U u) :
      W * (fiberTotal s g f u) ^ 2 <=
        C * (s.filter (fun i => g i = u)).sum (fun i => (f i) ^ 2) := by
    let t := s.filter (fun i => g i = u)
    have hcs := sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : Real)) f
    simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
    have he : 0 <= t.sum (fun i => (f i) ^ 2) := sum_nonneg (fun i _ => sq_nonneg _)
    change W * (t.sum f) ^ 2 <= C * t.sum (fun i => (f i) ^ 2)
    calc
      _ <= W * ((t.card : Real) * t.sum (fun i => (f i) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hW
      _ = (W * (t.card : Real)) * t.sum (fun i => (f i) ^ 2) := by ring1
      _ <= _ := mul_le_mul_of_nonneg_right (hcount u hu) he
  calc
    _ = U.sum (fun u => W * (fiberTotal s g f u) ^ 2) := mul_sum _ _ _
    _ <= U.sum (fun u => C *
        (s.filter (fun i => g i = u)).sum (fun i => (f i) ^ 2)) := sum_le_sum hlocal
    _ = C * s.sum (fun i => (f i) ^ 2) := by
      rw [<- mul_sum, sum_fiberwise_of_maps_to hmap (fun i => (f i) ^ 2)]

/-- A finite signed two-mode comparison transfers with only an upper occupancy
bound. The complete kernel and both principal energies are retained. -/
theorem kernel_fibre_fifth_gap_unscaled (s : Finset I) (U : Finset J) (g : I -> J)
    (hmap : forall i, Membership.mem s i -> Membership.mem U (g i))
    (K : J -> J -> Real) (sigma : J -> Real) (D C : Real) (hD : 0 <= D)
    (hcount : forall u, Membership.mem U u ->
      (U.card : Real) * ((s.filter (fun i => g i = u)).card : Real) <= C)
    (hmodel : forall h : J -> Real,
      abs (kernelBilinear U K h h -
        D * ((U.sum h) ^ 2 - (U.sum (fun u => sigma u * h u)) ^ 2)) <=
      D / 5 * ((U.card : Real) * U.sum (fun u => (h u) ^ 2) -
        (U.sum h) ^ 2 - (U.sum (fun u => sigma u * h u)) ^ 2))
    (f : I -> Real) :
    abs (kernelBilinear s (fun i j => K (g i) (g j)) f f -
      D * ((s.sum f) ^ 2 - (s.sum (fun i => sigma (g i) * f i)) ^ 2)) <=
      D / 5 * (C * s.sum (fun i => (f i) ^ 2) -
        (s.sum f) ^ 2 - (s.sum (fun i => sigma (g i) * f i)) ^ 2) := by
  let F := fiberTotal s g f
  have hmean : U.sum F = s.sum f := by
    simpa only [one_mul] using sum_mul_fiberTotal s U g hmap f (fun _ => 1)
  have hsign : U.sum (fun u => sigma u * F u) =
      s.sum (fun i => sigma (g i) * f i) := sum_mul_fiberTotal s U g hmap f sigma
  have hm := hmodel F
  rw [hmean, hsign] at hm
  have he := mul_sum_sq_fiberTotal_le s U g hmap f (U.card : Real) C
    (Nat.cast_nonneg _) hcount
  rw [kernelBilinear_fiberTotal s U g hmap K f f]
  calc
    _ <= D / 5 * ((U.card : Real) * U.sum (fun u => (F u) ^ 2) -
        (s.sum f) ^ 2 - (s.sum (fun i => sigma (g i) * f i)) ^ 2) := hm
    _ <= _ := mul_le_mul_of_nonneg_left
      (sub_le_sub_right (sub_le_sub_right he _) _) (by linarith only [hD])

/-- Probability normalization of the exact fibre transfer. The error is
uniform over all real test functions, including arbitrary signed masks. -/
theorem kernel_fibre_fifth_gap (s : Finset I) (U : Finset J) (g : I -> J)
    (hmap : forall i, Membership.mem s i -> Membership.mem U (g i))
    (K : J -> J -> Real) (sigma : J -> Real) (D delta : Real)
    (hs : 0 < s.card) (hD : 0 <= D)
    (hcount : forall u, Membership.mem U u ->
      (U.card : Real) * ((s.filter (fun i => g i = u)).card : Real) <=
        (1 + delta) * (s.card : Real))
    (hmodel : forall h : J -> Real,
      abs (kernelBilinear U K h h -
        D * ((U.sum h) ^ 2 - (U.sum (fun u => sigma u * h u)) ^ 2)) <=
      D / 5 * ((U.card : Real) * U.sum (fun u => (h u) ^ 2) -
        (U.sum h) ^ 2 - (U.sum (fun u => sigma u * h u)) ^ 2))
    (f : I -> Real) :
    let n : Real := (s.card : Real)
    let a := s.sum f / n
    let b := s.sum (fun i => sigma (g i) * f i) / n
    let e := s.sum (fun i => (f i) ^ 2) / n
    abs (kernelBilinear s (fun i j => K (g i) (g j)) f f / n ^ 2 -
      D * (a ^ 2 - b ^ 2)) <= D / 5 * (e - a ^ 2 - b ^ 2) + D * delta / 5 * e := by
  dsimp only
  let n : Real := (s.card : Real)
  let A : Real := s.sum f
  let B : Real := s.sum (fun i => sigma (g i) * f i)
  let E : Real := s.sum (fun i => (f i) ^ 2)
  let Q : Real := kernelBilinear s (fun i j => K (g i) (g j)) f f
  have hn : Not (n = 0) := by
    dsimp only [n]
    exact_mod_cast Nat.ne_of_gt hs
  have h := kernel_fibre_fifth_gap_unscaled s U g hmap K sigma D
    ((1 + delta) * n) hD hcount hmodel f
  have hdiv := div_le_div_of_nonneg_right h (sq_nonneg n)
  have hleft : abs (Q / n ^ 2 - D * ((A / n) ^ 2 - (B / n) ^ 2)) =
      abs (Q - D * (A ^ 2 - B ^ 2)) / n ^ 2 := by
    calc
      _ = abs ((Q - D * (A ^ 2 - B ^ 2)) / n ^ 2) := by
        congr 1
        field_simp [hn]
      _ = _ := by rw [abs_div, abs_of_nonneg (sq_nonneg n)]
  have hright :
      (D / 5 * (((1 + delta) * n) * E - A ^ 2 - B ^ 2)) / n ^ 2 =
        D / 5 * (E / n - (A / n) ^ 2 - (B / n) ^ 2) +
          D * delta / 5 * (E / n) := by
    field_simp [hn]
    ring1
  change abs (Q / n ^ 2 - D * ((A / n) ^ 2 - (B / n) ^ 2)) <=
    D / 5 * (E / n - (A / n) ^ 2 - (B / n) ^ 2) + D * delta / 5 * (E / n)
  rw [hleft, <- hright]
  exact hdiv


variable [DecidableEq I]

/-- Complete signed fibre transfer with sparse exceptional vertices. Both
principal mean corrections and all three exceptional rectangles are retained. -/
theorem kernel_fibre_fifth_gap_with_exceptions_unscaled
    (s t : Finset I) (U : Finset J) (g : I -> J)
    (ht : forall {i}, Membership.mem t i -> Membership.mem s i)
    (hmap : forall i, Membership.mem t i -> Membership.mem U (g i))
    (K : I -> I -> Real) (L : J -> J -> Real)
    (sigma : I -> Real) (eta : J -> Real) (D delta tau : Real)
    (hD : 0 <= D) (hdelta : 0 <= delta) (htau : 0 <= tau)
    (hcount : forall u, Membership.mem U u ->
      (U.card : Real) * ((t.filter (fun i => g i = u)).card : Real) <=
        (1 + delta) * (s.card : Real))
    (hsmall : ((s \ t).card : Real) <= tau ^ 2 * (s.card : Real))
    (hK : forall i, Membership.mem s i -> forall j, Membership.mem s j ->
      abs (K i j) <= 1)
    (hident : forall i, Membership.mem t i -> forall j, Membership.mem t j ->
      K i j = L (g i) (g j))
    (hsigma : forall i, Membership.mem s i -> (sigma i) ^ 2 = 1)
    (hsign : forall i, Membership.mem t i -> sigma i = eta (g i))
    (hmodel : forall h : J -> Real,
      abs (kernelBilinear U L h h -
        D * ((U.sum h) ^ 2 - (U.sum (fun u => eta u * h u)) ^ 2)) <=
      D / 5 * ((U.card : Real) * U.sum (fun u => (h u) ^ 2) -
        (U.sum h) ^ 2 - (U.sum (fun u => eta u * h u)) ^ 2))
    (f : I -> Real) :
    abs (kernelBilinear s K f f -
      D * ((s.sum f) ^ 2 - (s.sum (fun i => sigma i * f i)) ^ 2)) <=
      D / 5 * ((1 + delta) * (s.card : Real) * s.sum (fun i => (f i) ^ 2) -
        (s.sum f) ^ 2 - (s.sum (fun i => sigma i * f i)) ^ 2) +
      ((4 * D + 2) * tau + tau ^ 2) *
        ((s.card : Real) * s.sum (fun i => (f i) ^ 2)) := by
  let n : Real := (s.card : Real)
  let E : Real := s.sum (fun i => (f i) ^ 2)
  let A : Real := s.sum f
  let B : Real := s.sum (fun i => sigma i * f i)
  let AT : Real := t.sum f
  let BT : Real := t.sum (fun i => sigma i * f i)
  let Q : Real := kernelBilinear s K f f
  let QT : Real := kernelBilinear t K f f
  have hk : kernelBilinear t K f f =
      kernelBilinear t (fun i j => L (g i) (g j)) f f := by
    unfold kernelBilinear
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [hident i hi j hj]
  have hb : t.sum (fun i => sigma i * f i) =
      t.sum (fun i => eta (g i) * f i) := by
    apply sum_congr rfl
    intro i hi
    rw [hsign i hi]
  have hreg := kernel_fibre_fifth_gap_unscaled t U g hmap L eta D
    ((1 + delta) * n) hD hcount hmodel f
  rw [<- hk, <- hb] at hreg
  have he : t.sum (fun i => (f i) ^ 2) <= E :=
    sum_le_sum_of_subset_of_nonneg @ht (fun i _ _ => sq_nonneg _)
  have hC : 0 <= (1 + delta) * n := mul_nonneg (by linarith only [hdelta])
    (Nat.cast_nonneg _)
  have hD5 : 0 <= D / 5 := by linarith only [hD]
  have hregular : abs (QT - D * (AT ^ 2 - BT ^ 2)) <=
      D / 5 * (((1 + delta) * n) * E - AT ^ 2 - BT ^ 2) := by
    calc
      _ <= D / 5 * (((1 + delta) * n) * t.sum (fun i => (f i) ^ 2) -
        AT ^ 2 - BT ^ 2) := hreg
      _ <= _ := mul_le_mul_of_nonneg_left
        (sub_le_sub_right (sub_le_sub_right
          (mul_le_mul_of_nonneg_left he hC) _) _) hD5
  have hq := abs_kernelBilinear_sub_restrict_le s t @ht K f tau htau hsmall hK
  have ha := abs_sum_sq_sub_restrict_le s t @ht f tau htau hsmall
  have hEnergySign : s.sum (fun i => (sigma i * f i) ^ 2) = E := by
    apply sum_congr rfl
    intro i hi
    rw [mul_pow, hsigma i hi, one_mul]
  have hbError := abs_sum_sq_sub_restrict_le s t @ht
    (fun i => sigma i * f i) tau htau hsmall
  rw [hEnergySign] at hbError
  have h4 : 0 <= 4 * D / 5 := by linarith only [hD]
  have h6 : 0 <= 6 * D / 5 := by linarith only [hD]
  have ha4 := mul_le_mul_of_nonneg_left (abs_le.mp ha).1 h4
  have ha6 := mul_le_mul_of_nonneg_left (abs_le.mp ha).2 h6
  have hb4 := mul_le_mul_of_nonneg_left (abs_le.mp hbError).1 h4
  have hb6 := mul_le_mul_of_nonneg_left (abs_le.mp hbError).2 h6
  change abs (Q - D * (A ^ 2 - B ^ 2)) <=
    D / 5 * (((1 + delta) * n) * E - A ^ 2 - B ^ 2) +
      ((4 * D + 2) * tau + tau ^ 2) * (n * E)
  apply abs_le.mpr
  constructor
  case left =>
    nlinarith only [(abs_le.mp hregular).1, (abs_le.mp hq).1, ha6, hb4]
  case right =>
    nlinarith only [(abs_le.mp hregular).2, (abs_le.mp hq).2, ha4, hb6]

/-- Uniform probability version of the complete signed transfer. The number
of exceptional vertices enters only through a squared mass budget. -/
theorem kernel_fibre_fifth_gap_with_exceptions
    (s t : Finset I) (U : Finset J) (g : I -> J)
    (ht : forall {i}, Membership.mem t i -> Membership.mem s i)
    (hmap : forall i, Membership.mem t i -> Membership.mem U (g i))
    (K : I -> I -> Real) (L : J -> J -> Real)
    (sigma : I -> Real) (eta : J -> Real) (D delta tau : Real)
    (hs : 0 < s.card) (hD : 0 <= D) (hdelta : 0 <= delta) (htau : 0 <= tau)
    (hcount : forall u, Membership.mem U u ->
      (U.card : Real) * ((t.filter (fun i => g i = u)).card : Real) <=
        (1 + delta) * (s.card : Real))
    (hsmall : ((s \ t).card : Real) <= tau ^ 2 * (s.card : Real))
    (hK : forall i, Membership.mem s i -> forall j, Membership.mem s j ->
      abs (K i j) <= 1)
    (hident : forall i, Membership.mem t i -> forall j, Membership.mem t j ->
      K i j = L (g i) (g j))
    (hsigma : forall i, Membership.mem s i -> (sigma i) ^ 2 = 1)
    (hsign : forall i, Membership.mem t i -> sigma i = eta (g i))
    (hmodel : forall h : J -> Real,
      abs (kernelBilinear U L h h -
        D * ((U.sum h) ^ 2 - (U.sum (fun u => eta u * h u)) ^ 2)) <=
      D / 5 * ((U.card : Real) * U.sum (fun u => (h u) ^ 2) -
        (U.sum h) ^ 2 - (U.sum (fun u => eta u * h u)) ^ 2))
    (f : I -> Real) :
    let n : Real := (s.card : Real)
    let a := s.sum f / n
    let b := s.sum (fun i => sigma i * f i) / n
    let e := s.sum (fun i => (f i) ^ 2) / n
    abs (kernelBilinear s K f f / n ^ 2 - D * (a ^ 2 - b ^ 2)) <=
      D / 5 * (e - a ^ 2 - b ^ 2) +
        (D * delta / 5 + (4 * D + 2) * tau + tau ^ 2) * e := by
  dsimp only
  let n : Real := (s.card : Real)
  let A : Real := s.sum f
  let B : Real := s.sum (fun i => sigma i * f i)
  let E : Real := s.sum (fun i => (f i) ^ 2)
  let Q : Real := kernelBilinear s K f f
  have hn : Not (n = 0) := by
    dsimp only [n]
    exact_mod_cast Nat.ne_of_gt hs
  have h := kernel_fibre_fifth_gap_with_exceptions_unscaled s t U g @ht hmap
    K L sigma eta D delta tau hD hdelta htau hcount hsmall hK hident hsigma hsign hmodel f
  have hdiv := div_le_div_of_nonneg_right h (sq_nonneg n)
  have hleft : abs (Q / n ^ 2 - D * ((A / n) ^ 2 - (B / n) ^ 2)) =
      abs (Q - D * (A ^ 2 - B ^ 2)) / n ^ 2 := by
    calc
      _ = abs ((Q - D * (A ^ 2 - B ^ 2)) / n ^ 2) := by
        congr 1
        field_simp [hn]
      _ = _ := by rw [abs_div, abs_of_nonneg (sq_nonneg n)]
  have hright :
      (D / 5 * (((1 + delta) * n) * E - A ^ 2 - B ^ 2) +
        ((4 * D + 2) * tau + tau ^ 2) * (n * E)) / n ^ 2 =
      D / 5 * (E / n - (A / n) ^ 2 - (B / n) ^ 2) +
        (D * delta / 5 + (4 * D + 2) * tau + tau ^ 2) * (E / n) := by
    field_simp [hn]
    ring1
  change abs (Q / n ^ 2 - D * ((A / n) ^ 2 - (B / n) ^ 2)) <=
    D / 5 * (E / n - (A / n) ^ 2 - (B / n) ^ 2) +
      (D * delta / 5 + (4 * D + 2) * tau + tau ^ 2) * (E / n)
  rw [hleft, <- hright]
  exact hdiv

end Finset

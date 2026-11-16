/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFullRationalReference

/-! # Separation and complete signed reference comparison

The resonant main term is retained exactly. Only the complementary rational
centers are estimated by their geometrically cancelled interval kernels.
The final comparison covers every grid frequency, including both signs
and even midpoints, without truncating the rational reference.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_packet_point_eq {R Q : Nat}
    (u : lpfRationalCenters Q) (k : Int) :
    lpfRationalPacketPoint R (u, k) =
      hamiltonianRationalCenter R Q u + (k : ZMod R) := by
  simp only [lpfRationalPacketPoint, hamiltonianRationalCenter, lpfRationalGridPoint,
    Int.cast_zero, add_zero]

theorem hamiltonian_rational_other_center_far {R : Nat} [NeZero R]
    (Q W D : Nat) (hWD : W <= D)
    (hDiv : forall q, 0 < q -> q <= Q -> Dvd.dvd q R)
    (hWidth : 2 * D * Q ^ 2 < R)
    (u v : lpfRationalCenters Q) (huv : Not (u = v)) (k : Int)
    (hk : Membership.mem (Finset.Icc (-(W : Int)) (W : Int)) k) :
    Not (Membership.mem (lpfIntervalOffsetGrid R D)
      (lpfRationalPacketPoint R (u, k) - hamiltonianRationalCenter R Q v)) := by
  intro hNear
  choose ell hEll hEq using Finset.mem_image.mp hNear
  have hkB := Finset.mem_Icc.mp hk
  have hWDi : (W : Int) <= (D : Int) := by exact_mod_cast hWD
  have hkD : Membership.mem (Finset.Icc (-(D : Int)) (D : Int)) k :=
    Finset.mem_Icc.mpr (And.intro (by omega) (by omega))
  have hU : Membership.mem
      (SProd.sprod (Finset.univ : Finset (lpfRationalCenters Q))
        (Finset.Icc (-(D : Int)) (D : Int))) (u, k) :=
    Finset.mem_product.mpr (And.intro (Finset.mem_univ _) hkD)
  have hV : Membership.mem
      (SProd.sprod (Finset.univ : Finset (lpfRationalCenters Q))
        (Finset.Icc (-(D : Int)) (D : Int))) (v, ell) :=
    Finset.mem_product.mpr (And.intro (Finset.mem_univ _) hEll)
  have hPoint : lpfRationalPacketPoint R (u, k) =
      lpfRationalPacketPoint R (v, ell) := by
    rw [hamiltonian_packet_point_eq (R := R) v ell]
    exact (sub_eq_iff_eq_add.mp hEq.symm).trans (add_comm _ _)
  have hPair := lpfRationalPacketPoint_injective Q D hDiv hWidth hU hV hPoint
  exact huv (congrArg Prod.fst hPair)

theorem hamiltonian_full_reference_near_bound {R : Nat} [NeZero R]
    (Q s L W D : Nat) (hD : 1 <= D) (hWD : W <= D)
    (hDiv : forall q, 0 < q -> q <= Q -> Dvd.dvd q R)
    (hWidth : 2 * D * Q ^ 2 < R)
    (u : lpfRationalCenters Q) (k : Int)
    (hk : Membership.mem (Finset.Icc (-(W : Int)) (W : Int)) k) :
    norm (hamiltonianFullRationalReference R Q s L (lpfRationalPacketPoint R (u, k)) -
      lpfRationalCoefficient (u.1.val + 1) * lpfGridIntervalKernel R s L k) <=
        (Q : Real) * ((R : Real) / (2 * (D : Real))) := by
  classical
  let x := lpfRationalPacketPoint R (u, k)
  let f := fun v : lpfRationalCenters Q =>
    lpfRationalCoefficient (v.1.val + 1) *
      lpfIntervalFrequencyKernel R s L (x - hamiltonianRationalCenter R Q v)
  have hMain : f u =
      lpfRationalCoefficient (u.1.val + 1) * lpfGridIntervalKernel R s L k := by
    have hDiff : x - hamiltonianRationalCenter R Q u = (k : ZMod R) := by
      dsimp [x]
      rw [hamiltonian_packet_point_eq]
      ring
    dsimp [f]
    rw [hDiff]
    rfl
  have hDiff : hamiltonianFullRationalReference R Q s L x - f u =
      Finset.univ.sum (fun v : lpfRationalCenters Q => if v = u then 0 else f v) := by
    calc
      _ = Finset.univ.sum (fun v : lpfRationalCenters Q =>
          f v - (if v = u then f u else 0)) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rfl
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases h : v = u <;> simp [h]
  have hC : 0 <= (R : Real) / (2 * (D : Real)) := by positivity
  rw [<- hMain]
  change norm (hamiltonianFullRationalReference R Q s L x - f u) <= _
  rw [hDiff]
  calc
    _ <= Finset.univ.sum (fun v : lpfRationalCenters Q =>
        norm (if v = u then 0 else f v)) := norm_sum_le _ _
    _ <= Finset.univ.sum (fun v : lpfRationalCenters Q =>
        norm (lpfRationalCoefficient (v.1.val + 1)) *
          ((R : Real) / (2 * (D : Real)))) := by
      apply Finset.sum_le_sum
      intro v hv
      by_cases h : v = u
      . simp only [h, ite_true, norm_zero]
        exact mul_nonneg (norm_nonneg _) hC
      . simp only [h, ite_false]
        dsimp [f]
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact hamiltonian_interval_kernel_outside s L D hD
          (x - hamiltonianRationalCenter R Q v)
          (hamiltonian_rational_other_center_far Q W D hWD hDiv hWidth u v
            (fun hEq => h hEq.symm) k hk)
    _ = (Finset.univ.sum (fun v : lpfRationalCenters Q =>
        norm (lpfRationalCoefficient (v.1.val + 1)))) *
          ((R : Real) / (2 * (D : Real))) := (Finset.sum_mul _ _ _).symm
    _ <= _ := mul_le_mul_of_nonneg_right (hamiltonian_rational_coefficient_mass Q) hC

theorem hamiltonian_outside_rational_grid_far {R : Nat} [NeZero R]
    (Q W : Nat) (x : ZMod R)
    (hx : Not (Membership.mem (lpfRationalGrid R Q W) x))
    (u : lpfRationalCenters Q) :
    Not (Membership.mem (lpfIntervalOffsetGrid R W)
      (x - hamiltonianRationalCenter R Q u)) := by
  intro hNear
  choose k hk hEq using Finset.mem_image.mp hNear
  apply hx
  apply Finset.mem_image.mpr
  refine Exists.intro (u, k) (And.intro ?_ ?_)
  . exact Finset.mem_product.mpr (And.intro (Finset.mem_univ _) hk)
  . rw [hamiltonian_packet_point_eq]
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hEq.symm).symm

theorem hamiltonian_full_symbol_comparison {R : Nat} [NeZero R]
    (Q s L W D : Nat) (hW : 1 <= W) (hWD : W <= D)
    (hDiv : forall q, 0 < q -> q <= Q -> Dvd.dvd q R)
    (hWidth : 2 * D * Q ^ 2 < R)
    (S : ZMod R -> Complex) (Emajor Eminor : Real)
    (hMajor : forall u : lpfRationalCenters Q, forall k : Int,
      Membership.mem (Finset.Icc (-(W : Int)) (W : Int)) k ->
      norm (S (lpfRationalPacketPoint R (u, k)) -
        lpfRationalCoefficient (u.1.val + 1) * lpfGridIntervalKernel R s L k) <= Emajor)
    (hMinor : forall x, Not (Membership.mem (lpfRationalGrid R Q W) x) ->
      norm (S x) <= Eminor) (x : ZMod R) :
    norm (S x - hamiltonianFullRationalReference R Q s L x) <=
      max (Emajor + (Q : Real) * ((R : Real) / (2 * (D : Real))))
        (Eminor + (Q : Real) * ((R : Real) / (2 * (W : Real)))) := by
  classical
  by_cases hx : Membership.mem (lpfRationalGrid R Q W) x
  . choose uk huk hEq using Finset.mem_image.mp hx
    have hk := (Finset.mem_product.mp huk).2
    subst x
    have hNear := hamiltonian_full_reference_near_bound Q s L W D
      (hW.trans hWD) hWD hDiv hWidth uk.1 uk.2 hk
    calc
      _ <= norm (S (lpfRationalPacketPoint R uk) -
          lpfRationalCoefficient (uk.1.1.val + 1) * lpfGridIntervalKernel R s L uk.2) +
        norm (hamiltonianFullRationalReference R Q s L (lpfRationalPacketPoint R uk) -
          lpfRationalCoefficient (uk.1.1.val + 1) * lpfGridIntervalKernel R s L uk.2) :=
        by
          have h := norm_sub_le_norm_sub_add_norm_sub
            (S (lpfRationalPacketPoint R uk))
            (lpfRationalCoefficient (uk.1.1.val + 1) * lpfGridIntervalKernel R s L uk.2)
            (hamiltonianFullRationalReference R Q s L (lpfRationalPacketPoint R uk))
          rw [norm_sub_rev
            (lpfRationalCoefficient (uk.1.1.val + 1) * lpfGridIntervalKernel R s L uk.2)
            (hamiltonianFullRationalReference R Q s L (lpfRationalPacketPoint R uk))] at h
          exact h
      _ <= Emajor + (Q : Real) * ((R : Real) / (2 * (D : Real))) :=
        add_le_add (hMajor uk.1 uk.2 hk) hNear
      _ <= _ := le_max_left _ _
  . calc
      _ <= norm (S x) + norm (hamiltonianFullRationalReference R Q s L x) :=
        norm_sub_le _ _
      _ <= Eminor + (Q : Real) * ((R : Real) / (2 * (W : Real))) :=
        add_le_add (hMinor x hx)
          (hamiltonian_full_reference_far_bound Q s L W hW x
            (hamiltonian_outside_rational_grid_far Q W x hx))
      _ <= _ := le_max_right _ _

end PrimeFactorOscillations.LPF

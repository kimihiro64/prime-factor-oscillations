/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenCurveTrace

/-!
# Actual finite-field Gauss inputs for the sevenfold curve readout

The Gauss and Jacobi sums are actual finite-field sums.
The source compensation and every torus scale remain explicit.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Curve

variable {F : Type*} [Field F] [Fintype F]

private theorem character_pow_mod (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (n : Nat) : chi ^ n = chi ^ (n % 7) := by
  have hseven : chi ^ 7 = 1 := by simpa only [horder] using pow_orderOf_eq_one chi
  calc
    chi ^ n = chi ^ (n % 7 + 7 * (n / 7)) := by rw [Nat.mod_add_div]
    _ = chi ^ (n % 7) := by rw [pow_add, pow_mul, hseven, one_pow, mul_one]

private theorem character_power_ne_one (chi : MulChar F Complex)
    (horder : orderOf chi = 7) (n : Nat) (hn : Not (Dvd.dvd 7 n)) :
    Not (chi ^ n = 1) := by
  intro he
  have hd := orderOf_dvd_of_pow_eq_one he
  rw [horder] at hd
  exact hn hd

private theorem character_power_order (chi : MulChar F Complex)
    (horder : orderOf chi = 7) (r : Fin 6) :
    orderOf (chi ^ (r.val + 1)) = 7 := by
  apply IsPrimitiveRoot.iff_orderOf.mp
  apply (IsPrimitiveRoot.iff_orderOf.mpr horder).pow_of_coprime (r.val + 1)
  fin_cases r <;> decide

noncomputable def normalizedGauss (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho : Complex) (n : Nat) : Complex := gaussSum (chi ^ n) psi / rho

theorem normalized_gauss_ne_zero (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho : Complex) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (r : Fin 6) :
    Not (normalizedGauss chi psi rho (r.val + 1) = 0) := by
  have hn : Not (Dvd.dvd 7 (r.val + 1)) := by fin_cases r <;> norm_num
  have hc : Not ((Fintype.card F : Complex) = 0) := by exact_mod_cast Fintype.card_ne_zero
  exact div_ne_zero (gaussSum_ne_zero_of_nontrivial hc
    (character_power_ne_one chi horder _ hn) hpsi) hrho

/-- Actual normalized Gauss sums have the reciprocal entries used by the source model. -/
theorem normalized_gauss_complement (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho : Complex) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (hrho2 : rho ^ 2 = (Fintype.card F : Complex)) (r : Fin 6) :
    normalizedGauss chi psi rho (7 - (r.val + 1)) =
      1 / normalizedGauss chi psi rho (r.val + 1) := by
  have hn : Not (Dvd.dvd 7 (r.val + 1)) := by fin_cases r <;> norm_num
  have hne := character_power_ne_one chi horder (r.val + 1) hn
  have ho := character_power_order chi horder r
  have hseven : (chi ^ (r.val + 1)) ^ 7 = 1 := by
    simpa only [ho] using pow_orderOf_eq_one (chi ^ (r.val + 1))
  have hminus : (chi ^ (r.val + 1)) (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 7) hseven
  have hpower : (chi ^ (r.val + 1)) ^ 6 = chi ^ (7 - (r.val + 1)) := by
    rw [<- pow_mul, character_pow_mod chi horder ((r.val + 1) * 6)]
    fin_cases r <;> norm_num
  have hm := gaussSum_mul_gaussSum_pow_orderOf_sub_one hne hpsi
  norm_num only [ho] at hm
  rw [hpower, hminus, one_mul] at hm
  apply (eq_div_iff (normalized_gauss_ne_zero chi psi rho horder hpsi hrho r)).mpr
  unfold normalizedGauss
  calc
    _ = (gaussSum (chi ^ (r.val + 1)) psi *
        gaussSum (chi ^ (7 - (r.val + 1))) psi) / rho ^ 2 := by
      field_simp [hrho] <;> ring
    _ = 1 := by
      rw [hm, <- hrho2]
      exact div_self (pow_ne_zero 2 hrho)

/-- Gauss--Jacobi conversion with the actual common square-root scale retained. -/
theorem normalized_diagonal_jacobi (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho : Complex) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (r : Fin 6) :
    jacobi (chi ^ (r.val + 1)) (chi ^ (r.val + 1)) / rho =
      normalizedGauss chi psi rho (r.val + 1) ^ 2 /
        normalizedGauss chi psi rho (2 * (r.val + 1)) := by
  have hn : Not (Dvd.dvd 7 (2 * (r.val + 1))) := by fin_cases r <;> norm_num
  have hne := character_power_ne_one chi horder (2 * (r.val + 1)) hn
  have he : chi ^ (r.val + 1) * chi ^ (r.val + 1) = chi ^ (2 * (r.val + 1)) := by
    rw [<- pow_add]
    congr 1
    omega
  have hprod : Not (chi ^ (r.val + 1) * chi ^ (r.val + 1) = 1) := by rw [he]; exact hne
  have hm := gauss_jacobi (chi ^ (r.val + 1)) (chi ^ (r.val + 1)) psi hprod
  rw [he] at hm
  have hc : Not ((Fintype.card F : Complex) = 0) := by exact_mod_cast Fintype.card_ne_zero
  have hG := gaussSum_ne_zero_of_nontrivial hc hne hpsi
  apply (eq_div_iff (div_ne_zero hG hrho)).mpr
  unfold normalizedGauss
  field_simp [hrho]
  simpa only [pow_two] using hm.symm

/-- The six repeated-entry source masks in character-exponent order. -/
def diagonalIndex (r : Fin 6) : Fin 8 :=
  match r.val with
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | 3 => 6
  | 4 => 7
  | _ => 4

/-- Every diagonal Jacobi sum is exactly its corresponding actual source phase. -/
theorem diagonal_phase (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho : Complex) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (hrho2 : rho ^ 2 = (Fintype.card F : Complex)) (r : Fin 6) :
    jacobi (chi ^ (r.val + 1)) (chi ^ (r.val + 1)) / rho =
      Jacobi.phase (diagonalIndex r) (normalizedGauss chi psi rho 1)
        (normalizedGauss chi psi rho 2) (normalizedGauss chi psi rho 3) := by
  rw [normalized_diagonal_jacobi chi psi rho horder hpsi hrho r]
  let G : Nat -> Complex := normalizedGauss chi psi rho
  change G (r.val + 1) ^ 2 / G (2 * (r.val + 1)) =
    Jacobi.phase (diagonalIndex r) (G 1) (G 2) (G 3)
  have h1 : Not (G 1 = 0) :=
    normalized_gauss_ne_zero chi psi rho horder hpsi hrho 0
  have h2 : Not (G 2 = 0) :=
    normalized_gauss_ne_zero chi psi rho horder hpsi hrho 1
  have h3 : Not (G 3 = 0) :=
    normalized_gauss_ne_zero chi psi rho horder hpsi hrho 2
  have h4 : G 4 = 1 / G 3 :=
    normalized_gauss_complement chi psi rho horder hpsi hrho hrho2 2
  have h5 : G 5 = 1 / G 2 :=
    normalized_gauss_complement chi psi rho horder hpsi hrho hrho2 1
  have h6 : G 6 = 1 / G 1 :=
    normalized_gauss_complement chi psi rho horder hpsi hrho hrho2 0
  have hper (n : Nat) : G n = G (n % 7) := by
    dsimp [G, normalizedGauss]
    rw [character_pow_mod chi horder n]
  have h8 : G 8 = G 1 := hper 8
  have h10 : G 10 = G 3 := hper 10
  have h12 : G 12 = G 5 := hper 12
  fin_cases r <;> norm_num [diagonalIndex, Jacobi.phase] <;>
    simp only [h4, h5, h6, h8, h10, h12] <;>
    field_simp [h1, h2, h3] <;> ring

noncomputable def boundaryTrace (u g h j : Complex) (r : Real) : Complex :=
  Finset.univ.sum (fun d : Fin 6 =>
    (Cubic.mean (Jacobi.coherentProbe (diagonalIndex d) (u ^ 7) g h j
      ((r : Complex) * (1 / u ^ 2)) ((r : Complex) * (1 / u ^ 2))) - 1) / u ^ 15)

/-- The complete compensated six-channel Abel trace is an actual curve point-count discrepancy. -/
theorem curve_trace_abel (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho u : Complex) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (hrho2 : rho ^ 2 = (Fintype.card F : Complex))
    (hu : Not (u = 0)) :
    Filter.NeBot (nhdsWithin (1 : Real) (Set.Iio 1)) /\
    Filter.Tendsto (boundaryTrace u (normalizedGauss chi psi rho 1)
      (normalizedGauss chi psi rho 2) (normalizedGauss chi psi rho 3))
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds (((Fintype.card F : Complex) - (affineCount F : Complex)) / rho)) := by
  let G : Nat -> Complex := normalizedGauss chi psi rho
  have h1 : Not (G 1 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 0
  have h2 : Not (G 2 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 1
  have h3 : Not (G 3 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 2
  have hsum : Finset.univ.sum (fun d : Fin 6 =>
      -Jacobi.phase (diagonalIndex d) (G 1) (G 2) (G 3)) =
      ((Fintype.card F : Complex) - (affineCount F : Complex)) / rho := by
    calc
      _ = Finset.univ.sum (fun d : Fin 6 =>
          -(jacobi (chi ^ (d.val + 1)) (chi ^ (d.val + 1)) / rho)) := by
        apply Finset.sum_congr rfl
        intro d _
        exact congrArg Neg.neg (diagonal_phase chi psi rho horder hpsi hrho hrho2 d).symm
      _ = _ := by
        rw [Finset.sum_neg_distrib, <- Finset.sum_div, <- neg_div]
        congr 1
        rw [affine_count_jacobi chi horder]
        ring
  constructor
  . infer_instance
  have ht := tendsto_finsetSum Finset.univ (fun d (_ : Membership.mem Finset.univ d) =>
    (Jacobi.normalized_abel_readout (diagonalIndex d) u (G 1) (G 2) (G 3) hu h1 h2 h3).2)
  unfold boundaryTrace
  simpa only [hsum] using ht

noncomputable def jacobiPacket (chi : MulChar F Complex) (U V : Complex) : Complex :=
  Finset.univ.prod (fun d : Fin 6 =>
    U + jacobi (chi ^ (d.val + 1)) (chi ^ (d.val + 1)) * V)

/-- The actual source boundary packet is precisely the diagonal Jacobi polynomial. -/
theorem jacobi_packet_identification (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho u U V : Complex) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (hrho2 : rho ^ 2 = (Fintype.card F : Complex))
    (hu : Not (u = 0)) :
    Jacobi.nativePacket (u ^ 7) (normalizedGauss chi psi rho 1)
      (normalizedGauss chi psi rho 2) (normalizedGauss chi psi rho 3)
      (1 / u ^ 2) (1 / u ^ 2) U ((rho * V) / u ^ 15) = jacobiPacket chi U V := by
  let G : Nat -> Complex := normalizedGauss chi psi rho
  have h1 : Not (G 1 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 0
  have h2 : Not (G 2 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 1
  have h3 : Not (G 3 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 2
  have hf (i : Fin 8) :
      U - Jacobi.eigenvalue i (u ^ 7) (G 1) (G 2) (G 3)
        (1 / u ^ 2) (1 / u ^ 2) * ((rho * V) / u ^ 15) =
      U + Jacobi.phase i (G 1) (G 2) (G 3) * (rho * V) := by
    rw [Jacobi.eigenvalue_eq i _ _ _ _ _ _ h1 h2 h3, (Jacobi.balanced_corner u hu).2 i]
    field_simp [hu] <;> ring
  change Jacobi.nativePacket (u ^ 7) (G 1) (G 2) (G 3)
    (1 / u ^ 2) (1 / u ^ 2) U ((rho * V) / u ^ 15) = jacobiPacket chi U V
  unfold Jacobi.nativePacket Jacobi.packet6
  simp_rw [hf]
  have he (d : Fin 6) :
      jacobi (chi ^ (d.val + 1)) (chi ^ (d.val + 1)) * V =
        Jacobi.phase (diagonalIndex d) (G 1) (G 2) (G 3) * (rho * V) := by
    calc
      _ = (jacobi (chi ^ (d.val + 1)) (chi ^ (d.val + 1)) / rho) * (rho * V) := by
        field_simp [hrho] <;> ring
      _ = _ := by rw [diagonal_phase chi psi rho horder hpsi hrho hrho2 d]
  unfold jacobiPacket
  simp_rw [he]
  norm_num [Fin.prod_univ_succ, diagonalIndex] <;> ring

end Metaplectic.G2Seven.Curve

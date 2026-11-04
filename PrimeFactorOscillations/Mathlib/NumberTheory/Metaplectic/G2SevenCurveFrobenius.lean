/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenCurveReadout

/-!
# Frobenius invariance and the vanishing branch of the curve readout

Frobenius acts on the source field; the character values remain complex.
Non-admissible field sizes are handled by the actual power permutation.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Curve

variable {F : Type*} [Field F] [Fintype F]

/-- Reindexing the source field proves complex-valued Jacobi Frobenius invariance. -/
theorem jacobi_frobenius (p : Nat) [Fact (Nat.Prime p)] [CharP F p]
    (chi phi : MulChar F Complex) :
    jacobi (chi ^ p) (phi ^ p) = jacobi chi phi := by
  have hp0 : Not (p = 0) := Nat.Prime.ne_zero (Fact.out : Nat.Prime p)
  unfold jacobi
  apply Fintype.sum_equiv (frobeniusEquiv F p).toEquiv
  intro x
  rw [MulChar.pow_apply' chi hp0, MulChar.pow_apply' phi hp0]
  change chi x ^ p * phi (1 - x) ^ p = chi (x ^ p) * phi (1 - x ^ p)
  have he : (1 - x) ^ p = 1 - x ^ p := by
    have hh := map_sub (frobenius F p) (1 : F) x
    simpa only [frobenius_def, map_one] using hh
  rw [<- map_pow, <- map_pow, he]

/-- Coprimality makes the seventh-power map an actual permutation of the whole field. -/
theorem seventh_power_bijective (hcop : Nat.Coprime (Fintype.card F - 1) 7) :
    Function.Bijective (fun x : F => x ^ 7) := by
  classical
  have hu : Nat.Coprime (Nat.card (Units F)) 7 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using hcop
  let e : Equiv (Units F) (Units F) := powCoprime hu
  constructor
  . intro x y hxy
    by_cases hx : x = 0
    . subst x
      have hy : y = 0 := by simpa using hxy.symm
      exact hy.symm
    . by_cases hy : y = 0
      . subst y
        simpa using hxy
      . have he : e (Units.mk0 x hx) = e (Units.mk0 y hy) := by
          dsimp [e]
          rw [powCoprime_apply, powCoprime_apply]
          apply Units.ext
          exact hxy
        exact congrArg (fun u : Units F => (u : F)) (e.injective he)
  . intro z
    by_cases hz : z = 0
    . apply Exists.intro 0
      simp [hz]
    . let uz : Units F := Units.mk0 z hz
      apply Exists.intro (e.symm uz : F)
      have he := congrArg (fun u : Units F => (u : F)) (e.apply_symm_apply uz)
      simpa only [e, powCoprime_apply, Units.val_pow_eq_pow_val, uz, Units.val_mk0] using he

theorem root_count_coprime (hcop : Nat.Coprime (Fintype.card F - 1) 7) (z : F) :
    rootCount z = 1 := by
  classical
  have hb := seventh_power_bijective (F := F) hcop
  cases hb.2 z with
  | intro y hy =>
    unfold rootCount
    have he : (Finset.univ.filter (fun x : F => x ^ 7 = z)) = ({y} : Finset F) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      . intro hx
        exact hb.1 (hx.trans hy.symm)
      . intro hx
        rw [hx]
        exact hy
    rw [he]
    simp

/-- The exact zero-discrepancy branch; no order-seven character is assumed. -/
theorem affine_count_coprime (hcop : Nat.Coprime (Fintype.card F - 1) 7) :
    affineCount F = Fintype.card F := by
  rw [affine_count_fibers]
  simp_rw [root_count_coprime hcop]
  simp


/-- Field sizes outside the split class have exactly zero affine discrepancy. -/
theorem affine_count_of_card_mod_ne_one (hq : Not (Fintype.card F % 7 = 1)) :
    affineCount F = Fintype.card F := by
  apply affine_count_coprime
  rw [Nat.coprime_comm, (by decide : Nat.Prime 7).coprime_iff_not_dvd]
  intro hd
  have hm := Nat.mod_eq_zero_of_dvd hd
  have hp : 0 < Fintype.card F := Fintype.card_pos
  omega

/-- Multiplication of the six nonzero exponents by the residue represented by m. -/
def scalingIndex (m r : Fin 6) : Fin 6 :=
  match m.val with
  | 0 => r
  | 1 => ![1, 3, 5, 0, 2, 4] r
  | 2 => ![2, 5, 1, 4, 0, 3] r
  | 3 => ![3, 0, 4, 1, 5, 2] r
  | 4 => ![4, 2, 0, 5, 3, 1] r
  | _ => ![5, 4, 3, 2, 1, 0] r

theorem scaling_index_spec : forall m r : Fin 6,
    (scalingIndex m r).val + 1 = ((m.val + 1) * (r.val + 1)) % 7 := by
  decide

/-- All Frobenius orbits have this common size. -/
def residueDegree (m : Fin 6) : Nat :=
  match m.val with
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | 3 => 3
  | 4 => 6
  | _ => 2

def orbitRep (m r : Fin 6) : Fin 6 :=
  match m.val with
  | 0 => r
  | 1 => ![0, 0, 2, 0, 2, 2] r
  | 2 => 0
  | 3 => ![0, 0, 2, 0, 2, 2] r
  | 4 => 0
  | _ => ![0, 1, 2, 2, 1, 0] r

def representatives (m : Fin 6) : Finset (Fin 6) :=
  match m.val with
  | 0 => Finset.univ
  | 1 => {0, 2}
  | 2 => {0}
  | 3 => {0, 2}
  | 4 => {0}
  | _ => {0, 1, 2}

noncomputable def diagonalValue (chi : MulChar F Complex) (r : Fin 6) : Complex :=
  jacobi (chi ^ (r.val + 1)) (chi ^ (r.val + 1))

/-- This is source-field Frobenius, with no operation on the complex target. -/
theorem diagonal_frobenius (p : Nat) [Fact (Nat.Prime p)] [CharP F p]
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (m : Fin 6) (hpmod : p % 7 = m.val + 1) (r : Fin 6) :
    diagonalValue chi (scalingIndex m r) = diagonalValue chi r := by
  have he : chi ^ ((scalingIndex m r).val + 1) = (chi ^ (r.val + 1)) ^ p := by
    calc
      _ = chi ^ (((r.val + 1) * p) % orderOf chi) := by
        congr 1
        rw [horder, Nat.mul_mod, hpmod, Nat.mod_eq_of_lt (by omega : r.val + 1 < 7)]
        rw [Nat.mul_comm]
        exact scaling_index_spec m r
      _ = chi ^ ((r.val + 1) * p) := pow_mod_orderOf chi _
      _ = _ := pow_mul chi _ _
  unfold diagonalValue
  rw [he]
  exact jacobi_frobenius p _ _

theorem invariant_eq_representative (m : Fin 6) (b : Fin 6 -> Complex)
    (hinv : forall r, b (scalingIndex m r) = b r) (r : Fin 6) :
    b r = b (orbitRep m r) := by
  have h0 := hinv 0
  have h1 := hinv 1
  have h2 := hinv 2
  have h3 := hinv 3
  have h4 := hinv 4
  have h5 := hinv 5
  clear hinv
  fin_cases m <;> fin_cases r <;>
    norm_num [scalingIndex, orbitRep] at * <;> simp_all

/-- One factor for each Frobenius orbit, with the original signed Jacobi value. -/
def orbitPacket (m : Fin 6) (b : Fin 6 -> Complex) (U V : Complex) : Complex :=
  (representatives m).prod (fun r => U + b r * V)

/-- Polynomial equality retains every cross term, for arbitrary U and V. -/
theorem invariant_packet (m : Fin 6) (b : Fin 6 -> Complex)
    (hinv : forall r, b (scalingIndex m r) = b r) (U V : Complex) :
    (Finset.univ.prod (fun r : Fin 6 => U + b r * V)) =
      orbitPacket m b U V ^ residueDegree m := by
  have he : forall r, b r = b (orbitRep m r) := invariant_eq_representative m b hinv
  conv_lhs => arg 2; ext r; rw [he r]
  fin_cases m <;>
    norm_num [Fin.prod_univ_succ, orbitRep, orbitPacket, representatives, residueDegree] <;>
    ring

/-- The full signed trace identity holds at every power, not just the first trace. -/
theorem invariant_power_trace (m : Fin 6) (b : Fin 6 -> Complex)
    (hinv : forall r, b (scalingIndex m r) = b r) (n : Nat) :
    (Finset.univ.sum (fun r : Fin 6 => (-b r) ^ n)) =
      (residueDegree m : Complex) *
        (representatives m).sum (fun r => (-b r) ^ n) := by
  have he : forall r, b r = b (orbitRep m r) := invariant_eq_representative m b hinv
  conv_lhs => arg 2; ext r; rw [he r]
  fin_cases m <;>
    norm_num [Fin.sum_univ_succ, orbitRep, representatives, residueDegree] <;> ring

theorem jacobi_packet_frobenius (p : Nat) [Fact (Nat.Prime p)] [CharP F p]
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (m : Fin 6) (hpmod : p % 7 = m.val + 1) (U V : Complex) :
    jacobiPacket chi U V =
      orbitPacket m (diagonalValue chi) U V ^ residueDegree m := by
  exact invariant_packet m (diagonalValue chi)
    (diagonal_frobenius p chi horder m hpmod) U V

/-- Every signed power trace compresses with the same actual Frobenius multiplicity. -/
theorem jacobi_power_trace (p : Nat) [Fact (Nat.Prime p)] [CharP F p]
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (m : Fin 6) (hpmod : p % 7 = m.val + 1) (n : Nat) :
    (Finset.univ.sum (fun r : Fin 6 => (-diagonalValue chi r) ^ n)) =
      (residueDegree m : Complex) *
        (representatives m).sum (fun r => (-diagonalValue chi r) ^ n) := by
  exact invariant_power_trace m (diagonalValue chi)
    (diagonal_frobenius p chi horder m hpmod) n


/-- The actual G2 source packet compresses after its complete native scaling. -/
theorem native_packet_frobenius (p : Nat) [Fact (Nat.Prime p)] [CharP F p]
    (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho u U V : Complex) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (hrho2 : rho ^ 2 = (Fintype.card F : Complex))
    (hu : Not (u = 0)) (m : Fin 6) (hpmod : p % 7 = m.val + 1) :
    Jacobi.nativePacket (u ^ 7) (normalizedGauss chi psi rho 1)
      (normalizedGauss chi psi rho 2) (normalizedGauss chi psi rho 3)
      (1 / u ^ 2) (1 / u ^ 2) U ((rho * V) / u ^ 15) =
      orbitPacket m (diagonalValue chi) U V ^ residueDegree m := by
  rw [jacobi_packet_identification chi psi rho u U V horder hpsi hrho hrho2 hu]
  exact jacobi_packet_frobenius p chi horder m hpmod U V

end Metaplectic.G2Seven.Curve

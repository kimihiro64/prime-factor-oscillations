/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRationalModelBlocks
import PrimeFactorOscillations.Helpers.HamiltonianRealFiniteFactors

/-! # Balanced bounded real factors retaining the full signed rational model -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianFourierBalance (n : Nat) : Real := 1 / Real.sqrt (n : Real)

def hamiltonianBalancedRationalLeft (n R Q : Nat) [NeZero R] :
    Matrix (Fin n) (lpfRationalCenters Q) Complex :=
  fun i u => (hamiltonianFourierBalance n : Complex) *
    ZMod.stdAddChar ((-hamiltonianRationalCenter R Q u) *
      ((i.val + 1 : Nat) : ZMod R))

def hamiltonianBalancedRationalRight (n R Q : Nat) [NeZero R]
    (w : lpfRationalCenters Q -> Complex) :
    Matrix (lpfRationalCenters Q) (Fin n) Complex :=
  fun u j => (hamiltonianFourierBalance n : Complex) * w u *
    ZMod.stdAddChar ((-hamiltonianRationalCenter R Q u) *
      ((j.val + 1 : Nat) : ZMod R))

theorem hamiltonian_fourier_balance_scale (n : Nat) (hn : 0 < n) :
    0 <= hamiltonianFourierBalance n /\
      (n : Real) * hamiltonianFourierBalance n ^ 2 = 1 := by
  have hnR : 0 < (n : Real) := Nat.cast_pos.mpr hn
  have hs : 0 < Real.sqrt (n : Real) := Real.sqrt_pos.mpr hnR
  have hs2 := Real.sq_sqrt (le_of_lt hnR)
  refine And.intro (by dsimp [hamiltonianFourierBalance]; positivity) ?_
  dsimp [hamiltonianFourierBalance]
  field_simp
  nlinarith only [hs2]

theorem hamiltonian_fourier_balance_complex_square (n : Nat) (hn : 0 < n) :
    (hamiltonianFourierBalance n : Complex) * (hamiltonianFourierBalance n : Complex) =
      Inv.inv (n : Complex) := by
  have hnR : 0 < (n : Real) := Nat.cast_pos.mpr hn
  have hScale := (hamiltonian_fourier_balance_scale n hn).2
  have hReal : hamiltonianFourierBalance n * hamiltonianFourierBalance n =
      1 / (n : Real) := by
    have he : (hamiltonianFourierBalance n * hamiltonianFourierBalance n) * (n : Real) = 1 := by
      nlinarith only [hScale]
    calc
      _ = ((hamiltonianFourierBalance n * hamiltonianFourierBalance n) * (n : Real)) /
          (n : Real) := by field_simp [ne_of_gt hnR]
      _ = _ := by rw [he]
  rw [<- Complex.ofReal_mul, hReal]
  push_cast
  simp only [one_div]

theorem hamiltonian_balanced_rational_factorization (n R Q : Nat) [NeZero R]
    (hn : 0 < n) (w : lpfRationalCenters Q -> Complex) :
    hamiltonianRationalOperator n R Q w =
      hamiltonianBalancedRationalLeft n R Q * hamiltonianBalancedRationalRight n R Q w := by
  have hScalar := hamiltonian_fourier_balance_complex_square n hn
  ext i j
  rw [hamiltonian_rational_operator_apply]
  change (Finset.univ.sum (fun u => w u * ZMod.stdAddChar
    ((-hamiltonianRationalCenter R Q u) *
      (((i.val + 1) + (j.val + 1) : Nat) : ZMod R)))) / (n : Complex) =
    Finset.univ.sum (fun u =>
      hamiltonianBalancedRationalLeft n R Q i u * hamiltonianBalancedRationalRight n R Q w u j)
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u hu
  have hPhase : ZMod.stdAddChar ((-hamiltonianRationalCenter R Q u) *
      (((i.val + 1) + (j.val + 1) : Nat) : ZMod R)) =
      ZMod.stdAddChar ((-hamiltonianRationalCenter R Q u) * ((i.val + 1 : Nat) : ZMod R)) *
      ZMod.stdAddChar ((-hamiltonianRationalCenter R Q u) * ((j.val + 1 : Nat) : ZMod R)) := by
    rw [Nat.cast_add, mul_add, AddChar.map_add_eq_mul]
  rw [hPhase, div_eq_mul_inv, <- hScalar]
  unfold hamiltonianBalancedRationalLeft hamiltonianBalancedRationalRight
  ring

theorem hamiltonian_balanced_rational_entries (n R Q : Nat) [NeZero R]
    (w : lpfRationalCenters Q -> Complex) (hw : forall u, norm (w u) <= 1) :
    (forall i u, norm (hamiltonianBalancedRationalLeft n R Q i u) <=
      hamiltonianFourierBalance n) /\
    (forall u i, norm (hamiltonianBalancedRationalRight n R Q w u i) <=
      hamiltonianFourierBalance n) := by
  have hs : 0 <= hamiltonianFourierBalance n := by
    dsimp [hamiltonianFourierBalance]
    positivity
  have hChar (x : ZMod R) : norm (ZMod.stdAddChar x) = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  refine And.intro ?_ ?_
  next =>
    intro i u
    simp only [hamiltonianBalancedRationalLeft, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs, hChar, mul_one, le_refl]
  next =>
    intro u i
    simp only [hamiltonianBalancedRationalRight, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs, hChar, mul_one]
    exact (mul_le_mul_of_nonneg_left (hw u) hs).trans_eq (mul_one _)

theorem hamiltonian_rational_coefficient_norm_one (q : Nat) (hq : 0 < q) :
    norm (lpfRationalCoefficient q) <= 1 := by
  have hPhiN : 0 < q.totient := Nat.totient_pos.mpr hq
  have hPhi : (1 : Real) <= (q.totient : Real) := by exact_mod_cast hPhiN
  have hPhiPos : (0 : Real) < (q.totient : Real) := by linarith only [hPhi]
  calc
    _ <= 1 / (q.totient : Real) := norm_lpfRationalCoefficient_le q hq
    _ <= (q.totient : Real) / (q.totient : Real) :=
      div_le_div_of_nonneg_right hPhi (le_of_lt hPhiPos)
    _ = 1 := by field_simp

theorem hamiltonian_rational_real_bounded_factorization (n R Q : Nat) [NeZero R]
    (hn : 0 < n) (w : lpfRationalCenters Q -> Complex) (hw : forall u, norm (w u) <= 1) :
    exists U : Matrix (Fin n) (Sum (lpfRationalCenters Q) (lpfRationalCenters Q)) Real,
      exists V : Matrix (Sum (lpfRationalCenters Q) (lpfRationalCenters Q)) (Fin n) Real,
        hamiltonianRealPartMatrix (hamiltonianRationalOperator n R Q w) = U * V /\
          norm U <= (Fintype.card (Sum (lpfRationalCenters Q) (lpfRationalCenters Q)) : Real) + 1 /\
          norm V <= (Fintype.card (Sum (lpfRationalCenters Q) (lpfRationalCenters Q)) : Real) + 1 := by
  let A := hamiltonianBalancedRationalLeft n R Q
  let B := hamiltonianBalancedRationalRight n R Q w
  have hEntries := hamiltonian_balanced_rational_entries n R Q w hw
  have hScale := hamiltonian_fourier_balance_scale n hn
  have hNorms := hamiltonian_real_factor_norm_bounds A B (hamiltonianFourierBalance n)
    hScale.1 hEntries.1 hEntries.2 (by simpa only [Fintype.card_fin] using hScale.2.le)
  refine Exists.intro (hamiltonianRealFactorLeft A)
    (Exists.intro (hamiltonianRealFactorRight B) (And.intro ?_ hNorms))
  rw [hamiltonian_balanced_rational_factorization n R Q hn w]
  exact hamiltonian_real_factor_product A B

end PrimeFactorOscillations.LPF

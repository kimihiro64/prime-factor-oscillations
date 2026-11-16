/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianHankelFourierBound
import PrimeFactorOscillations.Helpers.LPFRamanujanGeneral

/-! # The actual coprime-difference graph and its signed Fourier modes

The graph is on ZMod n. Its adjacency tests the difference of the
two vertices. Every character frequency is retained. The Ramanujan
eigenvalue is evaluated with its full signed Mobius divisor mask.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {n : Nat} [NeZero n]

def hamiltonianCoprimeRelation (x y : ZMod n) : Prop :=
  IsUnit (x - y)

def hamiltonianCoprimeAdjacency : Matrix (ZMod n) (ZMod n) Real :=
  fun x y => if IsUnit (x - y) then 1 else 0

def hamiltonianCoprimeKernel : Matrix (ZMod n) (ZMod n) Real :=
  fun x y => hamiltonianCoprimeAdjacency x y / (n.totient : Real)

def hamiltonianCoprimeCharacter (k x : ZMod n) : Complex :=
  ZMod.stdAddChar (k * x)

theorem hamiltonian_coprime_relation_symmetric (x y : ZMod n) :
    hamiltonianCoprimeRelation x y -> hamiltonianCoprimeRelation y x := by
  intro h
  change IsUnit (y - x)
  have hNeg := h.neg
  simpa only [neg_sub] using hNeg

theorem hamiltonian_coprime_relation_irreflexive [Nontrivial (ZMod n)] (x : ZMod n) :
    Not (hamiltonianCoprimeRelation x x) := by
  intro h
  change IsUnit (x - x) at h
  exact h.ne_zero (sub_self x)

theorem hamiltonian_coprime_adjacency_symmetric :
    (hamiltonianCoprimeAdjacency (n := n)).transpose = hamiltonianCoprimeAdjacency := by
  ext x y
  have h : IsUnit (y - x) <-> IsUnit (x - y) :=
    Iff.intro (hamiltonian_coprime_relation_symmetric y x)
      (hamiltonian_coprime_relation_symmetric x y)
  simp only [hamiltonianCoprimeAdjacency, Matrix.transpose_apply, h]

theorem hamiltonian_coprime_unit_sum {R : Type*} [AddCommMonoid R]
    (f : ZMod n -> R) :
    Finset.univ.sum (fun z : ZMod n => if IsUnit z then f z else 0) =
      Finset.univ.sum (fun a : Units (ZMod n) => f (a : ZMod n)) := by
  classical
  rw [<- Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun (a : Units (ZMod n)) _ => (a : ZMod n))
  case hi =>
    intro a ha
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) a.isUnit)
  case i_inj =>
    intro a ha b hb h
    exact Units.ext h
  case i_surj =>
    intro z hz
    have hUnit := (Finset.mem_filter.mp hz).2
    exact Exists.intro hUnit.unit
      (Exists.intro (Finset.mem_univ _) hUnit.unit_spec)
  case h =>
    intro a ha
    rfl

theorem hamiltonian_coprime_row_degree (x : ZMod n) :
    Finset.univ.sum (fun y => hamiltonianCoprimeAdjacency x y) = (n.totient : Real) := by
  have hChange :
      Finset.univ.sum (fun y : ZMod n => if IsUnit (x - y) then (1 : Real) else 0) =
        Finset.univ.sum (fun z : ZMod n => if IsUnit z then (1 : Real) else 0) := by
    apply Fintype.sum_equiv (Equiv.subLeft x)
    intro y
    rfl
  change Finset.univ.sum (fun y : ZMod n => if IsUnit (x - y) then (1 : Real) else 0) = _
  rw [hChange, hamiltonian_coprime_unit_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ZMod.card_units_eq_totient]

theorem hamiltonian_coprime_kernel_nonnegative (x y : ZMod n) :
    0 <= hamiltonianCoprimeKernel x y := by
  unfold hamiltonianCoprimeKernel hamiltonianCoprimeAdjacency
  positivity

theorem hamiltonian_coprime_kernel_entry_cap (x y : ZMod n) :
    hamiltonianCoprimeKernel x y <= 1 / (n.totient : Real) := by
  unfold hamiltonianCoprimeKernel hamiltonianCoprimeAdjacency
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  split_ifs <;> norm_num

theorem hamiltonian_coprime_kernel_row_sum (x : ZMod n) :
    Finset.univ.sum (fun y => hamiltonianCoprimeKernel x y) = 1 := by
  change Finset.univ.sum (fun y : ZMod n =>
    hamiltonianCoprimeAdjacency x y / (n.totient : Real)) = 1
  rw [<- Finset.sum_div, hamiltonian_coprime_row_degree]
  exact div_self (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos n)).ne')

theorem hamiltonian_coprime_kernel_symmetric :
    (hamiltonianCoprimeKernel (n := n)).transpose = hamiltonianCoprimeKernel := by
  ext x y
  change hamiltonianCoprimeAdjacency y x / (n.totient : Real) =
    hamiltonianCoprimeAdjacency x y / (n.totient : Real)
  rw [show hamiltonianCoprimeAdjacency y x = hamiltonianCoprimeAdjacency x y from
    congrArg (fun M : Matrix (ZMod n) (ZMod n) Real => M x y)
      hamiltonian_coprime_adjacency_symmetric]

theorem hamiltonian_coprime_kernel_col_sum (y : ZMod n) :
    Finset.univ.sum (fun x => hamiltonianCoprimeKernel x y) = 1 := by
  have hSym := hamiltonian_coprime_kernel_symmetric (n := n)
  have hPoint (x : ZMod n) :
      hamiltonianCoprimeKernel x y = hamiltonianCoprimeKernel y x :=
    (congrArg (fun M : Matrix (ZMod n) (ZMod n) Real => M x y) hSym).symm
  simp_rw [hPoint]
  exact hamiltonian_coprime_kernel_row_sum y

theorem hamiltonian_coprime_character_eigenmode (k x : ZMod n) :
    Finset.univ.sum (fun y : ZMod n =>
      (hamiltonianCoprimeAdjacency x y : Complex) * hamiltonianCoprimeCharacter k y) =
        LPF.lpfRamanujanSum (q := n) k.val * hamiltonianCoprimeCharacter k x := by
  have hChange :
      Finset.univ.sum (fun y : ZMod n =>
        (hamiltonianCoprimeAdjacency x y : Complex) * hamiltonianCoprimeCharacter k y) =
      Finset.univ.sum (fun z : ZMod n =>
        if IsUnit z then hamiltonianCoprimeCharacter k (x - z) else 0) := by
    apply Fintype.sum_equiv (Equiv.subLeft x)
    intro y
    by_cases h : IsUnit (x - y)
    case pos => simp [hamiltonianCoprimeAdjacency, Equiv.subLeft, h]
    case neg => simp [hamiltonianCoprimeAdjacency, Equiv.subLeft, h]
  rw [hChange, hamiltonian_coprime_unit_sum]
  have hPhase (a : Units (ZMod n)) :
      hamiltonianCoprimeCharacter k (x - (a : ZMod n)) =
        ZMod.stdAddChar (-((a : ZMod n) * k)) * hamiltonianCoprimeCharacter k x := by
    unfold hamiltonianCoprimeCharacter
    rw [show k * (x - (a : ZMod n)) = -((a : ZMod n) * k) + k * x by ring,
      AddChar.map_add_eq_mul]
  simp_rw [hPhase]
  rw [<- Finset.sum_mul]
  congr 1
  simpa only [ZMod.natCast_zmod_val] using LPF.lpfRamanujanSum_neg_frequency (q := n) k.val

theorem hamiltonian_coprime_signed_frequency_formula (k : ZMod n) :
    LPF.lpfRamanujanSum (q := n) k.val =
      (Nat.gcd n k.val).divisors.sum (fun d =>
        (d : Complex) * (ArithmeticFunction.moebius (n / d) : Complex)) :=
  LPF.lpfRamanujanSum_divisors k.val

theorem hamiltonian_coprime_primitive_frequency (a : Units (ZMod n)) :
    LPF.lpfRamanujanSum (q := n) (a : ZMod n).val =
      (ArithmeticFunction.moebius n : Complex) := by
  unfold LPF.lpfRamanujanSum
  simp only [ZMod.natCast_zmod_val]
  calc
    _ = Finset.univ.sum (fun b : Units (ZMod n) => ZMod.stdAddChar (b : ZMod n)) := by
      apply Fintype.sum_equiv (Equiv.mulRight a)
      intro b
      rfl
    _ = _ := LPF.lpf_stdAddChar_sum_units

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelLabelAverage

/-!
# Native correlation kernels as normalized permutation characters

Each local factor is a positive sum of a trivial permutation action and
the regular action on the actual return image. Their product retains the
original group and period and gives an integral fixed-point model.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelPermutationKernel

open CarmichaelCorrelation CarmichaelCorrelationLocal CarmichaelCorrelationFloor
open CarmichaelSupportRigidity PrimeOrderReturnLaw

variable {G : Type*} [CommGroup G] [Fintype G]

local instance groupDecidableEq : DecidableEq G := Classical.typeDecidableEq G

local instance imageFintype (L l : Nat) : Fintype (returnImage (G := G) L l) :=
  Fintype.ofFinite _

def localCopies (d : Nat) : Nat := d * (d - 2)

theorem localFactor_scaled_integer (d : Nat) (hd : 2 <= d) (b : Bool) :
    (((d - 1) ^ 2 : Nat) : Real) * localFactor d b =
      (localCopies d : Real) + if b then (d : Real) else 0 := by
  have hOne : (((d - 1) : Nat) : Real) = (d : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 <= d), Nat.cast_one]
  have hCopies : (localCopies d : Real) = (d : Real) * ((d : Real) - 2) := by
    unfold localCopies
    rw [Nat.cast_mul, Nat.cast_sub hd, Nat.cast_ofNat]
  have hNon : Not ((d : Real) - 1 = 0) := by
    have hD : (2 : Real) <= d := by exact_mod_cast hd
    linarith
  rw [Nat.cast_pow, hOne, hCopies, localFactor_closed d hd]
  cases b <;> norm_num <;> field_simp [hNon] <;> ring

abbrev LocalState (L l : Nat) :=
  Sum (Fin (localCopies (returnIndex (G := G) L l))) (returnImage (G := G) L l)

def returnPoint (L l : Nat) (g : G) : returnImage (G := G) L l :=
  Subtype.mk (g ^ (L / l)) (Exists.intro g rfl)

theorem returnPoint_one (L l : Nat) :
    returnPoint (G := G) L l 1 = 1 := by
  apply Subtype.ext
  exact one_pow _

theorem returnPoint_mul (L l : Nat) (g h : G) :
    returnPoint L l (g * h) = returnPoint L l g * returnPoint L l h := by
  apply Subtype.ext
  exact mul_pow g h _

def localShift (L l : Nat) (g : G) : LocalState (G := G) L l -> LocalState (G := G) L l
  | Sum.inl i => Sum.inl i
  | Sum.inr r => Sum.inr (returnPoint L l g * r)

theorem localShift_one (L l : Nat) (x : LocalState (G := G) L l) :
    localShift L l 1 x = x := by
  cases x with
  | inl i => rfl
  | inr r => simp only [localShift, returnPoint_one, one_mul]

theorem localShift_mul (L l : Nat) (g h : G) (x : LocalState (G := G) L l) :
    localShift L l (g * h) x = localShift L l g (localShift L l h x) := by
  cases x with
  | inl i => rfl
  | inr r => simp only [localShift, returnPoint_mul, mul_assoc]

abbrev LocalFixed (L l : Nat) (g : G) :=
  { x : LocalState (G := G) L l // localShift L l g x = x }

local instance localFixedFintype (L l : Nat) (g : G) : Fintype (LocalFixed L l g) :=
  Fintype.ofFinite _

theorem localFixed_card (L l : Nat) (g : G) :
    Fintype.card (LocalFixed L l g) =
      localCopies (returnIndex (G := G) L l) +
        if g ^ (L / l) = 1 then returnIndex (G := G) L l else 0 := by
  classical
  by_cases hReturn : g ^ (L / l) = 1
  . have hPoint : returnPoint L l g = 1 := Subtype.ext hReturn
    have hAll (x : LocalState (G := G) L l) : localShift L l g x = x := by
      cases x with
      | inl i => rfl
      | inr r => simp only [localShift, hPoint, one_mul]
    let E : Equiv (LocalFixed L l g) (LocalState (G := G) L l) :=
      { toFun := Subtype.val
        invFun := fun x => Subtype.mk x (hAll x)
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    rw [Fintype.card_congr E]
    simp only [hReturn, if_true, Fintype.card_sum, Fintype.card_fin]
    rfl
  . have hPoint : Not (returnPoint L l g = 1) := by
      intro h
      exact hReturn (congrArg Subtype.val h)
    have hImpossible (r : returnImage (G := G) L l)
        (h : localShift L l g (Sum.inr r) = Sum.inr r) : False := by
      have hMul : returnPoint L l g * r = r := Sum.inr.inj h
      have hOne : returnPoint L l g = 1 := by
        calc
          _ = (returnPoint L l g * r) * Inv.inv r := by
            rw [mul_assoc, mul_inv_cancel, mul_one]
          _ = r * Inv.inv r := congrArg (fun z => z * Inv.inv r) hMul
          _ = 1 := mul_inv_cancel r
      exact hPoint hOne
    let E : Equiv (LocalFixed L l g) (Fin (localCopies (returnIndex (G := G) L l))) :=
      { toFun := fun x => match x with
          | Subtype.mk (Sum.inl i) _ => i
          | Subtype.mk (Sum.inr r) h => False.elim (hImpossible r h)
        invFun := fun i => Subtype.mk (Sum.inl i) rfl
        left_inv := by
          intro x
          cases x with
          | mk x hx =>
            cases x with
            | inl i => rfl
            | inr r => exact False.elim (hImpossible r hx)
        right_inv := by intro i; rfl }
    rw [Fintype.card_congr E]
    simp only [hReturn, if_false, add_zero, Fintype.card_fin]

abbrev PacketState (S : Finset Nat.Primes) :=
  (p : S) -> LocalState (G := G) (Monoid.exponent G) (p.val : Nat)

def packetShift (S : Finset Nat.Primes) (g : G) (x : PacketState (G := G) S) :
    PacketState (G := G) S :=
  fun p => localShift (Monoid.exponent G) (p.val : Nat) g (x p)

theorem packetShift_one (S : Finset Nat.Primes) (x : PacketState (G := G) S) :
    packetShift S 1 x = x := by
  funext p
  exact localShift_one _ _ _

theorem packetShift_mul (S : Finset Nat.Primes) (g h : G)
    (x : PacketState (G := G) S) :
    packetShift S (g * h) x = packetShift S g (packetShift S h x) := by
  funext p
  exact localShift_mul _ _ _ _ _

def packetPermutation (S : Finset Nat.Primes) (g : G) :
    Equiv.Perm (PacketState (G := G) S) :=
  { toFun := packetShift S g
    invFun := packetShift S (Inv.inv g)
    left_inv := by
      intro x
      rw [<- packetShift_mul, inv_mul_cancel, packetShift_one]
    right_inv := by
      intro x
      rw [<- packetShift_mul, mul_inv_cancel, packetShift_one] }

def packetAction (S : Finset Nat.Primes) :
    MonoidHom G (Equiv.Perm (PacketState (G := G) S)) :=
  { toFun := packetPermutation S
    map_one' := by
      apply Equiv.ext
      intro x
      exact packetShift_one S x
    map_mul' := by
      intro g h
      apply Equiv.ext
      intro x
      exact packetShift_mul S g h x }

abbrev PacketFixed (S : Finset Nat.Primes) (g : G) :=
  { x : PacketState (G := G) S // packetShift S g x = x }

local instance packetFixedFintype (S : Finset Nat.Primes) (g : G) :
    Fintype (PacketFixed S g) := Fintype.ofFinite _

def packetFixedEquiv (S : Finset Nat.Primes) (g : G) :
    Equiv (PacketFixed S g)
      ((p : S) -> LocalFixed (Monoid.exponent G) (p.val : Nat) g) :=
  { toFun := fun x p => Subtype.mk (x.val p) (congrFun x.property p)
    invFun := fun x => Subtype.mk (fun p => (x p).val) (funext (fun p => (x p).property))
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; funext p; apply Subtype.ext; rfl }

theorem packetFixed_card (S : Finset Nat.Primes) (g : G) :
    Fintype.card (PacketFixed S g) =
      S.prod (fun p : Nat.Primes =>
        Fintype.card (LocalFixed (Monoid.exponent G) (p : Nat) g)) := by
  rw [Fintype.card_congr (packetFixedEquiv S g), Fintype.card_pi]
  exact Finset.prod_attach S (fun p : Nat.Primes =>
    Fintype.card (LocalFixed (Monoid.exponent G) (p : Nat) g))

def normalization (S : Finset Nat.Primes) : Nat :=
  S.prod (fun p : Nat.Primes => (returnIndex (G := G) (Monoid.exponent G) (p : Nat) - 1) ^ 2)

theorem normalization_pos (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) :
    0 < normalization (G := G) S := by
  classical
  unfold normalization
  apply Finset.prod_pos
  intro p hp
  have hD : 2 <= returnIndex (G := G) (Monoid.exponent G) (p : Nat) :=
    p.property.two_le.trans (divisor_le_returnIndex (G := G) _ (hDiv (Subtype.mk p hp)))
  exact pow_pos (by omega : 0 < returnIndex (G := G) (Monoid.exponent G) (p : Nat) - 1) 2

theorem scaled_kernel_eq_fixed_card (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) (g : G) :
    (normalization (G := G) S : Real) *
      kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g =
        (Fintype.card (PacketFixed S g) : Real) := by
  classical
  rw [canonical_product_over_labels S hDiv, packetFixed_card]
  unfold normalization
  rw [Nat.cast_prod, Nat.cast_prod, <- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [localFixed_card]
  have hD : 2 <= returnIndex (G := G) (Monoid.exponent G) (p : Nat) :=
    p.property.two_le.trans (divisor_le_returnIndex (G := G) _ (hDiv (Subtype.mk p hp)))
  simpa [returnBit] using
    localFactor_scaled_integer (returnIndex (G := G) (Monoid.exponent G) (p : Nat)) hD
      (returnBit (Monoid.exponent G) (p : Nat) g)

theorem kernel_eq_fixed_card_div (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) (g : G) :
    kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g =
      (Fintype.card (PacketFixed S g) : Real) / (normalization (G := G) S : Real) := by
  have hPos : (0 : Real) < normalization (G := G) S := by
    exact_mod_cast normalization_pos S hDiv
  apply (eq_div_iff (ne_of_gt hPos)).mpr
  simpa only [mul_comm] using scaled_kernel_eq_fixed_card S hDiv g

theorem fixed_card_mean (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) :
    Finset.univ.sum (fun g : G => (Fintype.card (PacketFixed S g) : Real)) /
      (Fintype.card G : Real) = (normalization (G := G) S : Real) := by
  have hSum :
      Finset.univ.sum (fun g : G => (Fintype.card (PacketFixed S g) : Real)) =
        (normalization (G := G) S : Real) * Finset.univ.sum
          (kernel (vacancyWeight (G := G) (Monoid.exponent G) S)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    exact (scaled_kernel_eq_fixed_card S hDiv g).symm
  rw [hSum, mul_div_assoc,
    kernel_mean_one _ (canonical_vacancy_weightSum_pos S hDiv), mul_one]

end PrimeFactorOscillations.CarmichaelPermutationKernel

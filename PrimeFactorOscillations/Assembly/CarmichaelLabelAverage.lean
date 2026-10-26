/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelSupportRigidity
import PrimeFactorOscillations.Helpers.ReturnPacketPowerSupport

/-!
# Exact native label erasure by actual group phases

A simultaneous return-image section varies one coordinate while fixing
every other active coordinate. Averaging the full original correlation
kernel over these phases erases exactly that label, with mean one retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelLabelAverage

open CarmichaelCorrelation CarmichaelCorrelationLocal CarmichaelCorrelationFloor
open CarmichaelSupportRigidity PrimeOrderReturnLaw

variable {G : Type*} [CommGroup G] [Fintype G]

local instance imageFintype (L l : Nat) : Fintype (returnImage (G := G) L l) :=
  Fintype.ofFinite _

theorem exists_label_phase_section (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (l : Nat.Primes) (hl : Membership.mem S l) :
    exists v : returnImage (G := G) (Monoid.exponent G) (l : Nat) -> G,
      (forall r, (v r) ^ (Monoid.exponent G / (l : Nat)) = r.val) /\
      (forall r, forall p : Nat.Primes, Membership.mem (S.erase l) p ->
        (v r) ^ (Monoid.exponent G / (p : Nat)) = 1) := by
  classical
  let L := Monoid.exponent G
  let R := returnImage (G := G) L (l : Nat)
  let target (r : R) (p : S) : returnImage (G := G) L (p.val : Nat) := by
    by_cases hp : p.val = l
    . rw [hp]
      exact r
    . exact 1
  have hSur := packetProjection_surjective (G := G) L S hDiv
    (fun g => Monoid.pow_exponent_eq_one g)
  choose v hv using fun r : R => hSur (target r)
  refine Exists.intro v (And.intro ?_ ?_)
  . intro r
    have h := congrArg (fun y => (y (Subtype.mk l hl)).val) (hv r)
    simpa [packetProjection, target] using h
  . intro r p hp
    have hMem := (Finset.mem_erase.mp hp).2
    have hNe := (Finset.mem_erase.mp hp).1
    have h := congrArg (fun y => (y (Subtype.mk p hMem)).val) (hv r)
    simpa [packetProjection, target, hNe] using h

theorem kernel_split_label (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (l : Nat.Primes) (hl : Membership.mem S l) (g : G) :
    kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g =
      localFactor (returnIndex (G := G) (Monoid.exponent G) (l : Nat))
        (returnBit (Monoid.exponent G) (l : Nat) g) *
      kernel (vacancyWeight (G := G) (Monoid.exponent G) (S.erase l)) g := by
  classical
  have hErase : forall p : S.erase l,
      Dvd.dvd (p.val : Nat) (Monoid.exponent G) := by
    intro p
    exact hDiv (Subtype.mk p.val (Finset.mem_erase.mp p.property).2)
  rw [canonical_product_over_labels S hDiv,
    canonical_product_over_labels (S.erase l) hErase]
  let f : Nat.Primes -> Real := fun p =>
    localFactor (returnIndex (G := G) (Monoid.exponent G) (p : Nat))
      (returnBit (Monoid.exponent G) (p : Nat) g)
  change S.prod f = f l * (S.erase l).prod f
  have hNot : Not (Membership.mem (S.erase l) l) := by simp
  have hProduct : (insert l (S.erase l)).prod f =
      f l * (S.erase l).prod f := Finset.prod_insert hNot
  rw [Finset.insert_erase hl] at hProduct
  exact hProduct

theorem erased_kernel_phase_invariant (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (l : Nat.Primes) (v : G)
    (hv : forall p : Nat.Primes, Membership.mem (S.erase l) p ->
      v ^ (Monoid.exponent G / (p : Nat)) = 1) (g : G) :
    kernel (vacancyWeight (G := G) (Monoid.exponent G) (S.erase l)) (v * g) =
      kernel (vacancyWeight (G := G) (Monoid.exponent G) (S.erase l)) g := by
  classical
  have hErase : forall p : S.erase l,
      Dvd.dvd (p.val : Nat) (Monoid.exponent G) := by
    intro p
    exact hDiv (Subtype.mk p.val (Finset.mem_erase.mp p.property).2)
  rw [canonical_product_over_labels (S.erase l) hErase,
    canonical_product_over_labels (S.erase l) hErase]
  apply Finset.prod_congr rfl
  intro p hp
  unfold returnBit
  rw [mul_pow, hv p hp, one_mul]

theorem localFactor_image_sum {R : Type*} [Group R] [Fintype R] [DecidableEq R]
    (hCard : 2 <= Fintype.card R) :
    Finset.univ.sum (fun r : R =>
      localFactor (Fintype.card R) (decide (r = 1))) = (Fintype.card R : Real) := by
  classical
  have hPoint (r : R) :
      localFactor (Fintype.card R) (decide (r = 1)) =
        1 + ((if r = 1 then (Fintype.card R : Real) else 0) - 1) /
          ((Fintype.card R : Real) - 1) ^ 2 := by
    rw [localFactor_closed _ hCard]
    by_cases h : r = 1 <;> simp [h]
  simp_rw [hPoint]
  rw [Finset.sum_add_distrib, <- Finset.sum_div, Finset.sum_sub_distrib]
  simp

theorem kernel_label_phase_sum (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (l : Nat.Primes) (hl : Membership.mem S l)
    (v : returnImage (G := G) (Monoid.exponent G) (l : Nat) -> G)
    (hCoord : forall r, (v r) ^ (Monoid.exponent G / (l : Nat)) = r.val)
    (hFixed : forall r, forall p : Nat.Primes, Membership.mem (S.erase l) p ->
      (v r) ^ (Monoid.exponent G / (p : Nat)) = 1) (g : G) :
    Finset.univ.sum (fun r => kernel
        (vacancyWeight (G := G) (Monoid.exponent G) S) (v r * g)) =
      (returnIndex (G := G) (Monoid.exponent G) (l : Nat) : Real) *
        kernel (vacancyWeight (G := G) (Monoid.exponent G) (S.erase l)) g := by
  classical
  let L := Monoid.exponent G
  let R := { x : G // Membership.mem (returnImage (G := G) L (l : Nat)) x }
  let t : R := Subtype.mk (g ^ (L / (l : Nat))) (Exists.intro g rfl)
  have hEach (r : R) :
      kernel (vacancyWeight (G := G) L S) (v r * g) =
        localFactor (Fintype.card R) (decide (r * t = 1)) *
          kernel (vacancyWeight (G := G) L (S.erase l)) g := by
    rw [kernel_split_label S hDiv l hl,
      erased_kernel_phase_invariant S hDiv l (v r) (hFixed r)]
    have hBit : returnBit L (l : Nat) (v r * g) = decide (r * t = 1) := by
      unfold returnBit
      rw [mul_pow, hCoord r]
      by_cases h : r * t = 1
      . have hVal : r.val * g ^ (L / (l : Nat)) = 1 := congrArg Subtype.val h
        simp only [hVal, h, decide_true]
      . have hVal : Not (r.val * g ^ (L / (l : Nat)) = 1) := by
          intro hValue
          exact h (Subtype.ext hValue)
        simp only [hVal, h, decide_false]
    rw [hBit]
    rfl
  let f : R -> Real := fun r => localFactor (Fintype.card R) (decide (r = 1))
  have hShift : Finset.univ.sum (fun r : R => f (r * t)) = Finset.univ.sum f :=
    Equiv.sum_comp (Equiv.mulRight t : Equiv R R) f
  have hD : 2 <= Fintype.card R :=
    l.property.two_le.trans
      (divisor_le_returnIndex (G := G) (l : Nat) (hDiv (Subtype.mk l hl)))
  calc
    _ = Finset.univ.sum (fun r : R => f (r * t) *
        kernel (vacancyWeight (G := G) L (S.erase l)) g) := by
      apply Finset.sum_congr rfl
      intro r _
      exact hEach r
    _ = Finset.univ.sum (fun r : R => f (r * t)) *
        kernel (vacancyWeight (G := G) L (S.erase l)) g :=
      (Finset.sum_mul _ _ _).symm
    _ = Finset.univ.sum f * kernel (vacancyWeight (G := G) L (S.erase l)) g := by
      rw [hShift]
    _ = _ := by
      have hTotal : Finset.univ.sum f = (Fintype.card R : Real) :=
        localFactor_image_sum hD
      rw [hTotal]
      rfl

theorem exists_exact_label_average (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (l : Nat.Primes) (hl : Membership.mem S l) :
    exists v : returnImage (G := G) (Monoid.exponent G) (l : Nat) -> G,
      (forall r, (v r) ^ (Monoid.exponent G / (l : Nat)) = r.val) /\
      (forall r, forall p : Nat.Primes, Membership.mem (S.erase l) p ->
        (v r) ^ (Monoid.exponent G / (p : Nat)) = 1) /\
      (forall g : G,
        Finset.univ.sum (fun r => kernel
            (vacancyWeight (G := G) (Monoid.exponent G) S) (v r * g)) /
          (returnIndex (G := G) (Monoid.exponent G) (l : Nat) : Real) =
        kernel (vacancyWeight (G := G) (Monoid.exponent G) (S.erase l)) g) := by
  choose v hCoord hFixed using exists_label_phase_section S hDiv l hl
  refine Exists.intro v (And.intro hCoord (And.intro hFixed ?_))
  intro g
  rw [kernel_label_phase_sum S hDiv l hl v hCoord hFixed]
  have hD : 2 <= returnIndex (G := G) (Monoid.exponent G) (l : Nat) :=
    l.property.two_le.trans (divisor_le_returnIndex (G := G) _ (hDiv (Subtype.mk l hl)))
  have hNon : Not ((returnIndex (G := G) (Monoid.exponent G) (l : Nat) : Real) = 0) := by
    exact_mod_cast (show Not (returnIndex (G := G) (Monoid.exponent G) (l : Nat) = 0) by omega)
  rw [mul_comm, mul_div_assoc, div_self hNon, mul_one]

def phaseAverage (S : Finset Nat.Primes) (l : Nat.Primes)
    (v : returnImage (G := G) (Monoid.exponent G) (l : Nat) -> G) (g : G) : Real :=
  Finset.univ.sum (fun r => kernel
      (vacancyWeight (G := G) (Monoid.exponent G) S) (v r * g)) /
    (returnIndex (G := G) (Monoid.exponent G) (l : Nat) : Real)

theorem phaseAverage_eq_erased (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (l : Nat.Primes) (hl : Membership.mem S l)
    (v : returnImage (G := G) (Monoid.exponent G) (l : Nat) -> G)
    (hCoord : forall r, (v r) ^ (Monoid.exponent G / (l : Nat)) = r.val)
    (hFixed : forall r, forall p : Nat.Primes, Membership.mem (S.erase l) p ->
      (v r) ^ (Monoid.exponent G / (p : Nat)) = 1) (g : G) :
    phaseAverage S l v g =
      kernel (vacancyWeight (G := G) (Monoid.exponent G) (S.erase l)) g := by
  unfold phaseAverage
  rw [kernel_label_phase_sum S hDiv l hl v hCoord hFixed]
  have hD : 2 <= returnIndex (G := G) (Monoid.exponent G) (l : Nat) :=
    l.property.two_le.trans (divisor_le_returnIndex (G := G) _ (hDiv (Subtype.mk l hl)))
  have hNon : Not ((returnIndex (G := G) (Monoid.exponent G) (l : Nat) : Real) = 0) := by
    exact_mod_cast (show Not (returnIndex (G := G) (Monoid.exponent G) (l : Nat) = 0) by omega)
  rw [mul_comm, mul_div_assoc, div_self hNon, mul_one]

theorem phaseAverage_mean_one (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (l : Nat.Primes) (hl : Membership.mem S l)
    (v : returnImage (G := G) (Monoid.exponent G) (l : Nat) -> G)
    (hCoord : forall r, (v r) ^ (Monoid.exponent G / (l : Nat)) = r.val)
    (hFixed : forall r, forall p : Nat.Primes, Membership.mem (S.erase l) p ->
      (v r) ^ (Monoid.exponent G / (p : Nat)) = 1) :
    Finset.univ.sum (phaseAverage S l v) / (Fintype.card G : Real) = 1 := by
  have hErase : forall p : S.erase l,
      Dvd.dvd (p.val : Nat) (Monoid.exponent G) := by
    intro p
    exact hDiv (Subtype.mk p.val (Finset.mem_erase.mp p.property).2)
  calc
    _ = Finset.univ.sum
        (kernel (vacancyWeight (G := G) (Monoid.exponent G) (S.erase l))) /
          (Fintype.card G : Real) := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      exact phaseAverage_eq_erased S hDiv l hl v hCoord hFixed g
    _ = 1 := kernel_mean_one _ (canonical_vacancy_weightSum_pos (S.erase l) hErase)

theorem phaseAverage_signed_sum {I : Type*} (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (l : Nat.Primes) (hl : Membership.mem S l)
    (v : returnImage (G := G) (Monoid.exponent G) (l : Nat) -> G)
    (hCoord : forall r, (v r) ^ (Monoid.exponent G / (l : Nat)) = r.val)
    (hFixed : forall r, forall p : Nat.Primes, Membership.mem (S.erase l) p ->
      (v r) ^ (Monoid.exponent G / (p : Nat)) = 1)
    (T : Finset I) (u : I -> G) (z : I -> Real) :
    T.sum (fun i => phaseAverage S l v (u i) * z i) =
      T.sum (fun i => kernel
        (vacancyWeight (G := G) (Monoid.exponent G) (S.erase l)) (u i) * z i) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [phaseAverage_eq_erased S hDiv l hl v hCoord hFixed]

theorem odd_kernel_quadratic_sum_zero (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (hOdd : forall p : S, Not ((p.val : Nat) = 2))
    (chi : MonoidHom G Complex) (hChi : Not (chi = 1))
    (hSquare : forall g : G, (chi g) ^ 2 = 1) :
    Finset.univ.sum (fun g : G =>
      (kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g : Complex) * chi g) = 0 := by
  simpa only [CarmichaelCorrelation.characterSum] using
    CarmichaelCorrelation.odd_vacancy_kernel_quadratic_sum_eq_zero
      (Monoid.exponent G) S hDiv hOdd
      (fun g => Monoid.pow_exponent_eq_one g) chi hChi hSquare

theorem binary_phaseAverage_floor (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (hTwo : Membership.mem S twoLabel)
    (v : returnImage (G := G) (Monoid.exponent G) 2 -> G)
    (hCoord : forall r, (v r) ^ (Monoid.exponent G / 2) = r.val)
    (hFixed : forall r, forall p : Nat.Primes, Membership.mem (S.erase twoLabel) p ->
      (v r) ^ (Monoid.exponent G / (p : Nat)) = 1) (g : G) :
    (1 / 2 : Real) <= phaseAverage S twoLabel v g := by
  rw [phaseAverage_eq_erased S hDiv twoLabel hTwo v hCoord hFixed]
  exact erase_two_kernel_floor S hDiv g

theorem binary_phaseAverage_quadratic_sum_zero (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (hTwo : Membership.mem S twoLabel)
    (v : returnImage (G := G) (Monoid.exponent G) 2 -> G)
    (hCoord : forall r, (v r) ^ (Monoid.exponent G / 2) = r.val)
    (hFixed : forall r, forall p : Nat.Primes, Membership.mem (S.erase twoLabel) p ->
      (v r) ^ (Monoid.exponent G / (p : Nat)) = 1)
    (chi : MonoidHom G Complex) (hChi : Not (chi = 1))
    (hSquare : forall g : G, (chi g) ^ 2 = 1) :
    Finset.univ.sum (fun g : G => (phaseAverage S twoLabel v g : Complex) * chi g) = 0 := by
  have hErase : forall p : S.erase twoLabel,
      Dvd.dvd (p.val : Nat) (Monoid.exponent G) := by
    intro p
    exact hDiv (Subtype.mk p.val (Finset.mem_erase.mp p.property).2)
  have hOdd : forall p : S.erase twoLabel, Not ((p.val : Nat) = 2) := by
    intro p hEq
    have hp : p.val = twoLabel := Subtype.ext hEq
    exact (Finset.mem_erase.mp p.property).1 hp
  calc
    _ = Finset.univ.sum (fun g : G =>
        (kernel (vacancyWeight (G := G) (Monoid.exponent G) (S.erase twoLabel)) g :
          Complex) * chi g) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [phaseAverage_eq_erased S hDiv twoLabel hTwo v hCoord hFixed]
    _ = 0 := odd_kernel_quadratic_sum_zero (S.erase twoLabel) hErase hOdd chi hChi hSquare

theorem binary_phaseAverage_signed_lower {I : Type*} (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (hTwo : Membership.mem S twoLabel)
    (v : returnImage (G := G) (Monoid.exponent G) 2 -> G)
    (hCoord : forall r, (v r) ^ (Monoid.exponent G / 2) = r.val)
    (hFixed : forall r, forall p : Nat.Primes, Membership.mem (S.erase twoLabel) p ->
      (v r) ^ (Monoid.exponent G / (p : Nat)) = 1)
    (T : Finset I) (u : I -> G) (z : I -> Real) (B : Real) (hB : 0 <= B)
    (hz : forall i, Membership.mem T i -> B <= z i) :
    B * (T.card : Real) / 2 <= T.sum (fun i => phaseAverage S twoLabel v (u i) * z i) := by
  have hErase : forall p : S.erase twoLabel,
      Dvd.dvd (p.val : Nat) (Monoid.exponent G) := by
    intro p
    exact hDiv (Subtype.mk p.val (Finset.mem_erase.mp p.property).2)
  have hOdd : forall p : S.erase twoLabel, Not ((p.val : Nat) = 2) := by
    intro p hEq
    have hp : p.val = twoLabel := Subtype.ext hEq
    exact (Finset.mem_erase.mp p.property).1 hp
  rw [phaseAverage_signed_sum S hDiv twoLabel hTwo v hCoord hFixed]
  exact weighted_signal_lower (S.erase twoLabel) hErase hOdd T u z B hB hz

def averagedPrimeWeight (q : Nat) [NeZero q] (S : Finset Nat.Primes) (l : Nat.Primes)
    (v : returnImage (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) (l : Nat) ->
      Units (ZMod q)) (n : Nat) : Real :=
  if hn : Nat.Coprime n q then phaseAverage S l v (ZMod.unitOfCoprime n hn) else 0

theorem averagedPrimeWeight_eq_erased (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (l : Nat.Primes) (hl : Membership.mem S l)
    (v : returnImage (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) (l : Nat) ->
      Units (ZMod q))
    (hCoord : forall r, (v r) ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = r.val)
    (hFixed : forall r, forall p : Nat.Primes, Membership.mem (S.erase l) p ->
      (v r) ^ (Monoid.exponent (Units (ZMod q)) / (p : Nat)) = 1) (n : Nat) :
    averagedPrimeWeight q S l v n = carmichaelPrimeWeight q (S.erase l) n := by
  classical
  by_cases hn : Nat.Coprime n q
  . simp only [averagedPrimeWeight, carmichaelPrimeWeight, dite_eq_left hn]
    exact phaseAverage_eq_erased S hDiv l hl v hCoord hFixed (ZMod.unitOfCoprime n hn)
  . simp only [averagedPrimeWeight, carmichaelPrimeWeight, dite_eq_right hn]

end PrimeFactorOscillations.CarmichaelLabelAverage

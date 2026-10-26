/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPrimePacketAscent
import PrimeFactorOscillations.Assembly.CarmichaelSupportRigidity

/-!
# One binary phase completes every active native packet

Flat positive coefficient mass gives the actual two-mode kernel at any
binary return index two. Its complementary unit phase is independent of
the packet and covers every active mixed packet at that same modulus.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelBinaryCompletion

open CarmichaelPrimePacket CarmichaelPrimePacketSpectrum CarmichaelPrimePacketAscent
open CarmichaelCorrelation CarmichaelCorrelationSpectrum CarmichaelSupportRigidity
open CarmichaelCorrelationLocal PrimeOrderReturnLaw
open Filter PrimeFactorUnimodality

theorem index_two_other_coefficient_zero (q : Nat) [NeZero q]
    (hDiv : Dvd.dvd 2 (Monoid.exponent (Units (ZMod q))))
    (hIndex : index q twoLabel = 2)
    (chi psi : DirichletCharacter Complex q)
    (hChi : Not (chi = 1)) (hOne : coefficient (weight q twoLabel) chi = 1)
    (hPsi : Not (psi = 1)) (hNe : Not (psi = chi)) :
    coefficient (weight q twoLabel) psi = 0 := by
  classical
  let T := Finset.univ.erase (1 : DirichletCharacter Complex q)
  let c := coefficient (weight q twoLabel)
  have hMass : T.sum c = 1 := by
    have h := nonprincipal_coefficient_mass q twoLabel hDiv
    rw [hIndex] at h
    change T.sum c = 1 / ((2 : Real) - 1) at h
    norm_num at h
    exact h
  have hOneC : c chi = 1 := hOne
  have hMem : Membership.mem T chi := by simp [T, hChi]
  have hErase : (T.erase chi).sum c = 0 := by
    have h := Finset.sum_erase_add T c hMem
    rw [hMass, hOneC] at h
    linarith
  have hMemPsi : Membership.mem (T.erase chi) psi := by simp [T, hPsi, hNe]
  have hLe := Finset.single_le_sum
    (fun gamma _ => coefficient_nonneg (weight q twoLabel) gamma) hMemPsi
  change c psi <= (T.erase chi).sum c at hLe
  rw [hErase] at hLe
  exact le_antisymm hLe (coefficient_nonneg _ psi)

theorem index_two_kernel_two_modes (q : Nat) [NeZero q]
    (hDiv : Dvd.dvd 2 (Monoid.exponent (Units (ZMod q))))
    (hIndex : index q twoLabel = 2) (chi : DirichletCharacter Complex q)
    (hChi : Not (chi = 1)) (hOne : coefficient (weight q twoLabel) chi = 1)
    (u : Units (ZMod q)) :
    (kernel (weight q twoLabel) u : Complex) =
      1 + unitCharacter chi (Inv.inv u) := by
  classical
  let f := fun psi : DirichletCharacter Complex q =>
    (coefficient (weight q twoLabel) psi : Complex) * unitCharacter psi (Inv.inv u)
  have hSum : Finset.univ.sum f = ({1, chi} : Finset _).sum f := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro psi _ hNot
    have hPsi : Not (psi = 1) := by
      intro h
      apply hNot
      simp [h]
    have hNe : Not (psi = chi) := by
      intro h
      apply hNot
      simp [h]
    rw [index_two_other_coefficient_zero q hDiv hIndex chi psi hChi hOne hPsi hNe]
    simp
  rw [kernel_expansion]
  change Finset.univ.sum f = _
  rw [hSum]
  have hPrincipal := coefficient_principal (weight q twoLabel) (weightSum_pos q twoLabel hDiv)
  simp [f, Ne.symm hChi, hPrincipal, hOne, unitCharacter_one]

theorem exists_index_two_complement (q : Nat) [NeZero q]
    (hDiv : Dvd.dvd 2 (Monoid.exponent (Units (ZMod q))))
    (hIndex : index q twoLabel = 2) :
    exists v : Units (ZMod q), forall g : Units (ZMod q),
      kernel (weight q twoLabel) g + kernel (weight q twoLabel) (v * g) = 2 := by
  choose chi hChi hPower hCoefficient using
    exists_nonprincipal_prime_character q twoLabel hDiv
  have hOne : coefficient (weight q twoLabel) chi = 1 := by
    rw [hIndex] at hCoefficient
    norm_num at hCoefficient
    exact hCoefficient
  choose v hv using exists_kernel_zero_of_index_two q twoLabel hDiv hIndex
  have hAtV := index_two_kernel_two_modes q hDiv hIndex chi hChi hOne v
  rw [hv, Complex.ofReal_zero] at hAtV
  have hPhase : unitCharacter chi (Inv.inv v) = -1 := by
    calc
      _ = (1 + unitCharacter chi (Inv.inv v)) - 1 := by ring
      _ = 0 - 1 := congrArg (fun z : Complex => z - 1) hAtV.symm
      _ = -1 := by ring
  refine Exists.intro v ?_
  intro g
  have hComplex :
      (kernel (weight q twoLabel) g : Complex) +
        (kernel (weight q twoLabel) (v * g) : Complex) = 2 := by
    rw [index_two_kernel_two_modes q hDiv hIndex chi hChi hOne g,
      index_two_kernel_two_modes q hDiv hIndex chi hChi hOne (v * g),
      mul_inv_rev, map_mul, hPhase]
    ring
  exact_mod_cast hComplex

theorem full_kernel_nonneg {G : Type*} [CommGroup G] [Fintype G]
    (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) (g : G) :
    0 <= kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g := by
  by_cases h : kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g = 0
  . rw [h]
  . exact (by norm_num : (0 : Real) <= 3 / 8).trans
      (canonical_kernel_nonzero_gap S hDiv g h)

/-- The phase depends only on q, before any packet or unit is selected. -/
theorem exists_uniform_full_packet_complement (q : Nat) [NeZero q] :
    exists v : Units (ZMod q), forall S : Finset Nat.Primes,
      (forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q)))) ->
      forall g : Units (ZMod q),
        (3 / 8 : Real) <=
          kernel (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) g +
          kernel (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S)
            (v * g) := by
  classical
  by_cases hBad : Dvd.dvd 2 (Monoid.exponent (Units (ZMod q))) /\ index q twoLabel = 2
  . choose v hCover using exists_index_two_complement q hBad.1 hBad.2
    refine Exists.intro v ?_
    intro S hDiv g
    have hLeftNonneg := full_kernel_nonneg S hDiv g
    have hRightNonneg := full_kernel_nonneg S hDiv (v * g)
    by_cases hTwo : Membership.mem S twoLabel
    . by_cases hLeftZero :
          kernel (vacancyWeight (G := Units (ZMod q))
            (Monoid.exponent (Units (ZMod q))) S) g = 0
      . have hSingleLeft : kernel (weight q twoLabel) g = 0 :=
          (canonical_kernel_same_zero_set S hDiv hTwo g).mp hLeftZero
        have hRightNot : Not
            (kernel (vacancyWeight (G := Units (ZMod q))
              (Monoid.exponent (Units (ZMod q))) S) (v * g) = 0) := by
          intro hRightZero
          have hSingleRight : kernel (weight q twoLabel) (v * g) = 0 :=
            (canonical_kernel_same_zero_set S hDiv hTwo (v * g)).mp hRightZero
          have h := hCover g
          rw [hSingleLeft, hSingleRight] at h
          norm_num at h
        have hGap := canonical_kernel_nonzero_gap S hDiv (v * g) hRightNot
        linarith
      . have hGap := canonical_kernel_nonzero_gap S hDiv g hLeftZero
        linarith
    . have hGap := kernel_ge_half_of_two_not_mem S hDiv hTwo g
      linarith
  . refine Exists.intro 1 ?_
    intro S hDiv g
    have hNot : Not
        (kernel (vacancyWeight (G := Units (ZMod q))
          (Monoid.exponent (Units (ZMod q))) S) g = 0) := by
      intro hZero
      have h := (canonical_kernel_zero_iff S hDiv g).mp hZero
      apply hBad
      exact And.intro (hDiv (Subtype.mk twoLabel h.1)) h.2.1
    have hGap := canonical_kernel_nonzero_gap S hDiv g hNot
    simpa only [one_mul] using (show (3 / 8 : Real) <=
      kernel (vacancyWeight (G := Units (ZMod q))
        (Monoid.exponent (Units (ZMod q))) S) g +
      kernel (vacancyWeight (G := Units (ZMod q))
        (Monoid.exponent (Units (ZMod q))) S) g by linarith)

def completionPhase (q : Nat) [NeZero q] : Units (ZMod q) :=
  Classical.choose (exists_uniform_full_packet_complement q)

theorem completionPhase_cover (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : Units (ZMod q)) :
    (3 / 8 : Real) <=
      kernel (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) g +
      kernel (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S)
        (completionPhase q * g) :=
  Classical.choose_spec (exists_uniform_full_packet_complement q) S hDiv g

theorem completionPhase_signed_cover (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : Units (ZMod q)) (B : Real) (hB : 0 <= B) :
    (3 / 8 : Real) * B <=
      kernel (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) g * B +
      kernel (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S)
        (completionPhase q * g) * B := by
  simpa only [add_mul] using
    mul_le_mul_of_nonneg_right (completionPhase_cover q S hDiv g) hB

def phasePrimeWeight (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (v : Units (ZMod q)) (n : Nat) : Real := by
  classical
  exact if hn : Nat.Coprime n q then
    kernel (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S)
      (v * ZMod.unitOfCoprime n hn)
    else 0

theorem phasePrimeWeight_nonneg (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (v : Units (ZMod q)) (n : Nat) : 0 <= phasePrimeWeight q S v n := by
  classical
  unfold phasePrimeWeight
  split_ifs with hn
  . exact full_kernel_nonneg S hDiv (v * ZMod.unitOfCoprime n hn)
  . exact le_rfl

def completedPrimeWeight (q : Nat) [NeZero q] (S : Finset Nat.Primes) (n : Nat) : Real :=
  (4 / 3 : Real) * (carmichaelPrimeWeight q S n + phasePrimeWeight q S (completionPhase q) n)

theorem completedPrimeWeight_bounds (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (n : Nat) :
    And (0 <= completedPrimeWeight q S n)
      (Nat.Coprime n q -> (1 / 2 : Real) <= completedPrimeWeight q S n) := by
  have h0 := primeWeight_nonneg_all_packets q S hDiv n
  have h1 := phasePrimeWeight_nonneg q S hDiv (completionPhase q) n
  constructor
  . exact mul_nonneg (by norm_num) (add_nonneg h0 h1)
  . intro hn
    have hCover := completionPhase_cover q S hDiv (ZMod.unitOfCoprime n hn)
    simp only [completedPrimeWeight, carmichaelPrimeWeight, phasePrimeWeight, dite_eq_left hn]
    linarith

def completedLocalAscentWeight (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes) (X : Nat) (i : Fin (m X)) : Real :=
  completedPrimeWeight (q X) (S X) (primeAt (a X i))

def completedLocalAscentExcess (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes) (X : Nat) : Real :=
  weightedLocalAscentExcess H m a (completedLocalAscentWeight m a q S) X

theorem completedLocalAscent_unit_weights (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X))))) :
    LocalAscentUnitWeights m a q (completedLocalAscentWeight m a q S) := by
  intro X i
  exact completedPrimeWeight_bounds (q X) (S X) (hDiv X) (primeAt (a X i))

theorem completedLocalAscentExcess_common_lower
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (X : Nat)
    (hCount : (m X : Real) / 2 <= (localAscentUnitIndices m a X (q X)).card)
    (B : Real) (hB : 0 <= B)
    (hPoint : forall i, B <= localAscentPairExcess H X (a X i)) :
    (m X : Real) * B / 4 <= completedLocalAscentExcess H m a q S X :=
  weightedLocalAscentExcess_common_lower H m a q _
    (completedLocalAscent_unit_weights m a q S hDiv) X hCount B hB hPoint

theorem completedLocalAscentExcess_unbounded_of_not_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) (hC : 0 < C) :
    exists n : Nat, X0 < (n : Real) /\
      C * (n : Real) ^ (7 / 10 : Real) < completedLocalAscentExcess H m a q S n := by
  have hQ : Filter.Eventually (fun X : Nat =>
      And (0 < q X) (q X <= X ^ (m X / 2))) atTop := by
    filter_upwards [hBudget] with X hX
    exact And.intro (Nat.pos_of_ne_zero (NeZero.ne (q X))) hX
  exact weightedLocalAscentExcess_unbounded_of_not_RH H m a hs q _
    (completedLocalAscent_unit_weights m a q S hDiv) hQ hNotRH C X0 hC

theorem riemannHypothesis_iff_completedLocalAscentExcess_nonpos
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop) :
    RiemannHypothesis <-> Filter.Eventually
      (fun X : Nat => completedLocalAscentExcess H m a q S X <= 0) atTop := by
  have hQ : Filter.Eventually (fun X : Nat =>
      And (0 < q X) (q X <= X ^ (m X / 2))) atTop := by
    filter_upwards [hBudget] with X hX
    exact And.intro (Nat.pos_of_ne_zero (NeZero.ne (q X))) hX
  exact riemannHypothesis_iff_eventually_weightedLocalAscentExcess_nonpos H m a hs q _
    (completedLocalAscent_unit_weights m a q S hDiv) hQ

theorem riemannHypothesis_iff_completedLocalAscentExcess_power_upper
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop) :
    RiemannHypothesis <-> exists C : Real, 0 < C /\
      Filter.Eventually (fun X : Nat => completedLocalAscentExcess H m a q S X <=
        C * (X : Real) ^ (7 / 10 : Real)) atTop := by
  have hQ : Filter.Eventually (fun X : Nat =>
      And (0 < q X) (q X <= X ^ (m X / 2))) atTop := by
    filter_upwards [hBudget] with X hX
    exact And.intro (Nat.pos_of_ne_zero (NeZero.ne (q X))) hX
  exact riemannHypothesis_iff_eventually_weightedLocalAscentExcess_power_upper H m a hs q _
    (completedLocalAscent_unit_weights m a q S hDiv) hQ

end PrimeFactorOscillations.CarmichaelBinaryCompletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistOptimum
/-!
# Exact energy of fully coupled quadratic-pair packets

All fields and shifts are retained in the complete finite product space.
Arbitrary signed weights may couple every choice of common scaling across
fields. The actual positive local optimizers tensorize, and the full joint
energy has an exact square-defect identity. No independent-weight assumption
or integer incomplete-interval estimate is used.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticPairTwistOptimum
attribute [local instance] Classical.propDecidable

def spanPairing (q e f alpha beta a b : Real) : Real :=
  alpha * a * sumMoment q (e * f) +
    (alpha * b + beta * a) * crossMoment q (e + f) +
      beta * b * diffMoment q (e * f) (e + f)

theorem optimalAlpha_eq_piecewise (q e f : Real) (hq : 5 < q)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1) :
    optimalAlpha q e f =
      if e * f = 1 then 2 * (q + 3) / (q ^ 2 - 5) else 2 / (q - 3) := by
  have he2 : e ^ 2 = 1 := by rcases he with he | he <;> rw [he] <;> norm_num
  have hf2 : f ^ 2 = 1 := by rcases hf with hf | hf <;> rw [hf] <;> norm_num
  by_cases hp : e * f = 1
  . simp only [ite_eq_left hp]
    have hs : (e + f) ^ 2 = 4 := by nlinarith only [he2, hf2, hp]
    unfold optimalAlpha
    congr 1
    nlinarith only [hs]
  . simp only [ite_eq_right hp]
    have hs : e + f = 0 := by
      rcases he with he | he <;> rcases hf with hf | hf <;>
        subst e <;> subst f <;> norm_num at *
    have h3 : Not (q - 3 = 0) := ne_of_gt (by linarith only [hq])
    have hp3 : Not (q + 3 = 0) := ne_of_gt (by linarith only [hq])
    have hden : q ^ 2 - 9 = (q - 3) * (q + 3) := by ring
    simp only [optimalAlpha, hs, zero_pow (by decide : Not (2 = 0)), add_zero]
    rw [hden]
    field_simp [h3, hp3]
    <;> ring

theorem optimal_spanPairing_mean (q e f a b : Real) (hq : 5 < q)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1) :
    spanPairing q e f (optimalAlpha q e f) (optimalBeta q e f) a b =
      minimumEnergy q (e * f) * (a * (q - 3) + b * (e + f)) / 2 := by
  have h0 : Not (q = 0) := ne_of_gt (by linarith only [hq])
  have h3 : Not (q - 3 = 0) := ne_of_gt (by linarith only [hq])
  have h5 : Not (q ^ 2 - 5 = 0) :=
    ne_of_gt (by nlinarith only [sq_nonneg (q - 5), hq])
  unfold spanPairing
  rw [optimalAlpha_eq_piecewise q e f hq he hf, optimalBeta_eq_piecewise q e f he hf]
  rcases he with he | he <;> rcases hf with hf | hf <;> subst e <;> subst f <;>
    norm_num [sumMoment, crossMoment, diffMoment, minimumEnergy] <;>
    field_simp [h0,h3,h5] <;> ring

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem linearProfile_pairing (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1)
    (alpha beta a b : Real) :
    (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F =>
        linearProfile c h t alpha beta * linearProfile c h t a b) =
      spanPairing (Fintype.card F : Real) (signE h) (signF h) alpha beta a b := by
  have hp (c : F) :
      (linearProfile c h t (alpha + a) (beta + b)) ^ 2 =
        (linearProfile c h t alpha beta) ^ 2 +
          2 * (linearProfile c h t alpha beta * linearProfile c h t a b) +
            (linearProfile c h t a b) ^ 2 := by
    unfold linearProfile
    ring
  have hs :
      (1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F =>
          (linearProfile c h t (alpha + a) (beta + b)) ^ 2) =
      (1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => (linearProfile c h t alpha beta) ^ 2) +
      2 * ((1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F =>
          linearProfile c h t alpha beta * linearProfile c h t a b)) +
      (1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => (linearProfile c h t a b) ^ 2) := by
    simp_rw [hp]
    simp only [Finset.sum_add_distrib, <- Finset.mul_sum]
    ring
  rw [linearProfile_energy hF h t hh ht hchi,
    linearProfile_energy hF h t hh ht hchi,
    linearProfile_energy hF h t hh ht hchi] at hs
  unfold spanPairing spanEnergy at *
  nlinarith only [hs]

theorem optimalProfile_pairing (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1)
    (hq : 5 < (Fintype.card F : Real)) (a b : Real) :
    (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F =>
        optimalProfile c h t * linearProfile c h t a b) =
      minimumEnergy (Fintype.card F : Real) (signE h * signF h) *
        ((1 / (Fintype.card F : Real)) *
          (Finset.univ.sum fun c : F => linearProfile c h t a b)) := by
  unfold optimalProfile
  rw [linearProfile_pairing hF h t hh ht hchi,
    linearProfile_mean hF h t hh ht hchi]
  rw [optimal_spanPairing_mean (Fintype.card F : Real) (signE h) (signF h) a b hq
    (QuadraticPairEuler.quadraticChar_real_signs h hh)
    (QuadraticPairEuler.quadraticChar_real_signs (-h) (neg_ne_zero.mpr hh))]
  ring

theorem optimalProfile_scaled_pairing (hF : Not (ringChar F = 2)) (h t u : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1)
    (hu : Not (u = 0)) (hq : 5 < (Fintype.card F : Real)) :
    (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F =>
        optimalProfile c h t * (monicQuadraticPairCount (u * c) (u * h) : Real)) =
      minimumEnergy (Fintype.card F : Real) (signE h * signF h) *
        ((1 / (Fintype.card F : Real)) *
          (Finset.univ.sum fun c : F =>
            (monicQuadraticPairCount (u * c) (u * h) : Real))) := by
  have hp (c : F) := scaled_count_linearProfile hF h t u c ht hchi hu
  simp_rw [hp]
  exact optimalProfile_pairing hF h t hh ht hchi hq _ _

end FiniteField.QuadraticPairTwistOptimum

namespace FiniteField.QuadraticPairTwistJoint
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (K : I -> Type*) [forall i, Fintype (K i)] [forall i, DecidableEq (K i)]

def packetMean (g : ((i : I) -> K i) -> Real) : Real :=
  (Finset.univ.prod fun i : I => 1 / (Fintype.card (K i) : Real)) *
    (Finset.univ.sum g)

def purePacket (u : (i : I) -> K i -> Real) (x : (i : I) -> K i) : Real :=
  Finset.univ.prod fun i : I => u i (x i)

theorem packetMean_pure (u : (i : I) -> K i -> Real) :
    packetMean K (purePacket K u) =
      Finset.univ.prod fun i : I =>
        (1 / (Fintype.card (K i) : Real)) * (Finset.univ.sum (u i)) := by
  unfold packetMean purePacket
  rw [<- Fintype.prod_sum u, <- Finset.prod_mul_distrib]

theorem packetMean_pure_pairing (u v : (i : I) -> K i -> Real) :
    packetMean K (fun x => purePacket K u x * purePacket K v x) =
      Finset.univ.prod fun i : I =>
        (1 / (Fintype.card (K i) : Real)) *
          (Finset.univ.sum fun c : K i => u i c * v i c) := by
  have hp (x : (i : I) -> K i) :
      purePacket K u x * purePacket K v x =
        purePacket K (fun i c => u i c * v i c) x := by
    unfold purePacket
    rw [Finset.prod_mul_distrib]
  simp_rw [hp]
  exact packetMean_pure K _

theorem packetMean_sum {J : Type*} [Fintype J]
    (g : J -> ((i : I) -> K i) -> Real) :
    packetMean K (fun x => Finset.univ.sum fun j : J => g j x) =
      Finset.univ.sum fun j : J => packetMean K (g j) := by
  unfold packetMean
  rw [Finset.sum_comm, Finset.mul_sum]

theorem packetMean_mul (a : Real) (g : ((i : I) -> K i) -> Real) :
    packetMean K (fun x => a * g x) = a * packetMean K g := by
  unfold packetMean
  rw [<- Finset.mul_sum]
  ring

def jointPacket {J : Type*} [Fintype J]
    (u : J -> (i : I) -> K i -> Real) (weight : J -> Real)
    (x : (i : I) -> K i) : Real :=
  Finset.univ.sum fun j : J => weight j * purePacket K (u j) x

theorem packetMean_joint {J : Type*} [Fintype J]
    (u : J -> (i : I) -> K i -> Real) (weight : J -> Real) :
    packetMean K (jointPacket K u weight) =
      Finset.univ.sum fun j : J => weight j * packetMean K (purePacket K (u j)) := by
  unfold jointPacket
  rw [packetMean_sum]
  simp_rw [packetMean_mul]

theorem packetMean_joint_pairing {J : Type*} [Fintype J]
    (v : (i : I) -> K i -> Real) (u : J -> (i : I) -> K i -> Real)
    (weight : J -> Real) (m : I -> Real)
    (hrow : forall (j : J) (i : I),
      (1 / (Fintype.card (K i) : Real)) *
        (Finset.univ.sum fun c : K i => v i c * u j i c) =
      m i * ((1 / (Fintype.card (K i) : Real)) * (Finset.univ.sum (u j i)))) :
    packetMean K (fun x => purePacket K v x * jointPacket K u weight x) =
      (Finset.univ.prod m) * packetMean K (jointPacket K u weight) := by
  have hb (j : J) :
      packetMean K (fun x => purePacket K v x * purePacket K (u j) x) =
        (Finset.univ.prod m) * packetMean K (purePacket K (u j)) := by
    rw [packetMean_pure_pairing]
    simp_rw [hrow j]
    rw [packetMean_pure, Finset.prod_mul_distrib]
  have hp (x : (i : I) -> K i) :
      purePacket K v x * jointPacket K u weight x =
        Finset.univ.sum fun j : J =>
          weight j * (purePacket K v x * purePacket K (u j) x) := by
    unfold jointPacket
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hp]
  rw [packetMean_sum]
  simp_rw [packetMean_mul, hb]
  rw [packetMean_joint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem packetMean_square_nonneg (w : ((i : I) -> K i) -> Real) :
    0 <= packetMean K (fun x => (w x) ^ 2) := by
  unfold packetMean
  apply mul_nonneg
  . apply Finset.prod_nonneg
    intro i _
    exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
  . apply Finset.sum_nonneg
    intro x _
    exact sq_nonneg _

theorem packetMean_square_defect (w v : ((i : I) -> K i) -> Real) (M : Real)
    (hmean : packetMean K w = 1)
    (henergy : packetMean K (fun x => (v x) ^ 2) = M)
    (hpair : packetMean K (fun x => v x * w x) = M * packetMean K w) :
    packetMean K (fun x => (w x) ^ 2) =
      M + packetMean K (fun x => (w x - v x) ^ 2) := by
  have hp (x : (i : I) -> K i) :
      (w x - v x) ^ 2 = (w x) ^ 2 - 2 * (v x * w x) + (v x) ^ 2 := by ring
  simp_rw [hp]
  unfold packetMean at *
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum]
  rw [hmean] at hpair
  linarith only [henergy, hpair]


variable [forall i, Field (K i)]

def optimalFactors (h t : (i : I) -> K i) (i : I) (c : K i) : Real :=
  QuadraticPairTwistOptimum.optimalProfile c (h i) (t i)

def minimumFactors (h : (i : I) -> K i) (i : I) : Real :=
  QuadraticPairTwistOptimum.minimumEnergy (Fintype.card (K i) : Real)
    (QuadraticPairTwistOptimum.signE (h i) * QuadraticPairTwistOptimum.signF (h i))

def countFactors {J : Type*} (h : (i : I) -> K i)
    (scale : J -> (i : I) -> K i) (j : J) (i : I) (c : K i) : Real :=
  (monicQuadraticPairCount (scale j i * c) (scale j i * h i) : Real)

def coupledCountPacket {J : Type*} [Fintype J] (h : (i : I) -> K i)
    (scale : J -> (i : I) -> K i) (weight : J -> Real) :
    ((i : I) -> K i) -> Real :=
  jointPacket K (countFactors K h scale) weight

theorem optimalPacket_law (h t : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hh : forall i, Not (h i = 0)) (ht : forall i, Not (t i = 0))
    (hchi : forall i, (quadraticChar (K i)) (t i) = -1)
    (hq : forall i, 5 < (Fintype.card (K i) : Real)) :
    packetMean K (purePacket K (optimalFactors K h t)) = 1 /\
      packetMean K (fun x => (purePacket K (optimalFactors K h t) x) ^ 2) =
        Finset.univ.prod (minimumFactors K h) /\
      (forall x, 0 <= purePacket K (optimalFactors K h t) x) := by
  have hlaw (i : I) :=
    QuadraticPairTwistOptimum.optimalProfile_law
      (hodd i) (h i) (t i) (hh i) (ht i) (hchi i) (hq i)
  constructor
  . rw [packetMean_pure]
    have hp (i : I) :
        (1 / (Fintype.card (K i) : Real)) *
          (Finset.univ.sum (optimalFactors K h t i)) = 1 := (hlaw i).1
    simp_rw [hp]
    simp
  . constructor
    . unfold packetMean purePacket
      rw [QuadraticPairEnergy.product_space_energy K (optimalFactors K h t)]
      apply Finset.prod_congr rfl
      intro i _
      exact (hlaw i).2.1
    . intro x
      apply Finset.prod_nonneg
      intro i _
      exact (hlaw i).2.2 (x i)

theorem coupled_count_packet_pairing {J : Type*} [Fintype J]
    (h t : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hh : forall i, Not (h i = 0)) (ht : forall i, Not (t i = 0))
    (hchi : forall i, (quadraticChar (K i)) (t i) = -1)
    (hq : forall i, 5 < (Fintype.card (K i) : Real))
    (scale : J -> (i : I) -> K i) (hu : forall j i, Not (scale j i = 0))
    (weight : J -> Real) :
    packetMean K (fun x =>
        purePacket K (optimalFactors K h t) x * coupledCountPacket K h scale weight x) =
      (Finset.univ.prod (minimumFactors K h)) *
        packetMean K (coupledCountPacket K h scale weight) := by
  unfold coupledCountPacket
  apply packetMean_joint_pairing
  intro j i
  exact QuadraticPairTwistOptimum.optimalProfile_scaled_pairing
    (hodd i) (h i) (t i) (scale j i) (hh i) (ht i) (hchi i) (hu j i) (hq i)

theorem coupled_count_packet_square_defect {J : Type*} [Fintype J]
    (h t : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hh : forall i, Not (h i = 0)) (ht : forall i, Not (t i = 0))
    (hchi : forall i, (quadraticChar (K i)) (t i) = -1)
    (hq : forall i, 5 < (Fintype.card (K i) : Real))
    (scale : J -> (i : I) -> K i) (hu : forall j i, Not (scale j i = 0))
    (weight : J -> Real)
    (hmean : packetMean K (coupledCountPacket K h scale weight) = 1) :
    packetMean K (fun x => (coupledCountPacket K h scale weight x) ^ 2) =
      (Finset.univ.prod (minimumFactors K h)) +
        packetMean K (fun x =>
          (coupledCountPacket K h scale weight x -
            purePacket K (optimalFactors K h t) x) ^ 2) := by
  exact packetMean_square_defect K _ _ _ hmean
    (optimalPacket_law K h t hodd hh ht hchi hq).2.1
    (coupled_count_packet_pairing K h t hodd hh ht hchi hq scale hu weight)

theorem coupled_count_packet_energy_minimum {J : Type*} [Fintype J]
    (h t : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hh : forall i, Not (h i = 0)) (ht : forall i, Not (t i = 0))
    (hchi : forall i, (quadraticChar (K i)) (t i) = -1)
    (hq : forall i, 5 < (Fintype.card (K i) : Real))
    (scale : J -> (i : I) -> K i) (hu : forall j i, Not (scale j i = 0))
    (weight : J -> Real)
    (hmean : packetMean K (coupledCountPacket K h scale weight) = 1) :
    (Finset.univ.prod (minimumFactors K h)) <=
      packetMean K (fun x => (coupledCountPacket K h scale weight x) ^ 2) := by
  rw [coupled_count_packet_square_defect K h t hodd hh ht hchi hq scale hu weight hmean]
  exact le_add_of_nonneg_right (packetMean_square_nonneg K _)


def choiceCoefficient (h : (i : I) -> K i) (i : I) (b : Bool) : Real :=
  if b then
    QuadraticPairTwistOptimum.optimalAlpha (Fintype.card (K i) : Real)
      (QuadraticPairTwistOptimum.signE (h i)) (QuadraticPairTwistOptimum.signF (h i)) -
    QuadraticPairTwistOptimum.optimalBeta (Fintype.card (K i) : Real)
      (QuadraticPairTwistOptimum.signE (h i)) (QuadraticPairTwistOptimum.signF (h i))
  else
    QuadraticPairTwistOptimum.optimalAlpha (Fintype.card (K i) : Real)
      (QuadraticPairTwistOptimum.signE (h i)) (QuadraticPairTwistOptimum.signF (h i)) +
    QuadraticPairTwistOptimum.optimalBeta (Fintype.card (K i) : Real)
      (QuadraticPairTwistOptimum.signE (h i)) (QuadraticPairTwistOptimum.signF (h i))

def canonicalScales (t : (i : I) -> K i) (choice : I -> Bool) (i : I) : K i :=
  if choice i then t i else 1

def canonicalWeights (h : (i : I) -> K i) (choice : I -> Bool) : Real :=
  Finset.univ.prod fun i : I => choiceCoefficient K h i (choice i)

theorem optimalFactors_eq_choice_sum (h t : (i : I) -> K i) (i : I) (c : K i) :
    optimalFactors K h t i c =
      Finset.univ.sum fun b : Bool => choiceCoefficient K h i b *
        (monicQuadraticPairCount ((if b then t i else 1) * c)
          ((if b then t i else 1) * h i) : Real) := by
  simp [choiceCoefficient, optimalFactors, QuadraticPairTwistOptimum.optimalProfile,
    QuadraticPairTwistOptimum.linearProfile,
    QuadraticPairTwistOptimum.countPlus, QuadraticPairTwistOptimum.countDiff]
  <;> ring

theorem canonical_packet_eq_optimum (h t : (i : I) -> K i) (x : (i : I) -> K i) :
    coupledCountPacket K h (canonicalScales K t) (canonicalWeights K h) x =
      purePacket K (optimalFactors K h t) x := by
  calc
    _ = Finset.univ.sum fun choice : I -> Bool =>
        Finset.univ.prod fun i : I => choiceCoefficient K h i (choice i) *
          (monicQuadraticPairCount ((if choice i then t i else 1) * x i)
            ((if choice i then t i else 1) * h i) : Real) := by
      unfold coupledCountPacket jointPacket canonicalWeights
        purePacket countFactors canonicalScales
      apply Finset.sum_congr rfl
      intro choice _
      rw [Finset.prod_mul_distrib]
    _ = Finset.univ.prod fun i : I =>
        Finset.univ.sum fun b : Bool => choiceCoefficient K h i b *
          (monicQuadraticPairCount ((if b then t i else 1) * x i)
            ((if b then t i else 1) * h i) : Real) :=
      (Fintype.prod_sum (fun (i : I) (b : Bool) => choiceCoefficient K h i b *
        (monicQuadraticPairCount ((if b then t i else 1) * x i)
          ((if b then t i else 1) * h i) : Real))).symm
    _ = _ := by
      unfold purePacket
      apply Finset.prod_congr rfl
      intro i _
      exact (optimalFactors_eq_choice_sum K h t i (x i)).symm

theorem canonical_weights_pos (h : (i : I) -> K i)
    (hh : forall i, Not (h i = 0))
    (hq : forall i, 5 < (Fintype.card (K i) : Real)) (choice : I -> Bool) :
    0 < canonicalWeights K h choice := by
  unfold canonicalWeights
  apply Finset.prod_pos
  intro i _
  have hp := QuadraticPairTwistOptimum.optimal_raw_coefficients_pos
    (Fintype.card (K i) : Real)
    (QuadraticPairTwistOptimum.signE (h i)) (QuadraticPairTwistOptimum.signF (h i))
    (hq i) (QuadraticPairEuler.quadraticChar_real_signs (h i) (hh i))
    (QuadraticPairEuler.quadraticChar_real_signs (-(h i)) (neg_ne_zero.mpr (hh i)))
  unfold choiceCoefficient
  split_ifs
  . exact hp.2
  . exact hp.1

theorem packetMean_square_eq_zero_iff (w : ((i : I) -> K i) -> Real) :
    packetMean K (fun x => (w x) ^ 2) = 0 <-> forall x, w x = 0 := by
  constructor
  . intro hz
    have hweight : 0 < Finset.univ.prod (fun i : I =>
        1 / (Fintype.card (K i) : Real)) := by
      apply Finset.prod_pos
      intro i _
      have hq : 0 < (Fintype.card (K i) : Real) := by
        exact_mod_cast (show 0 < Fintype.card (K i) from Fintype.card_pos)
      exact div_pos (by norm_num) hq
    unfold packetMean at hz
    have hs : (Finset.univ.sum fun x : (i : I) -> K i => (w x) ^ 2) = 0 :=
      (mul_eq_zero.mp hz).resolve_left (ne_of_gt hweight)
    intro x
    have hp := Finset.single_le_sum
      (fun y (_ : Membership.mem (Finset.univ : Finset ((i : I) -> K i)) y) =>
        sq_nonneg (w y)) (Finset.mem_univ x)
    rw [hs] at hp
    exact sq_eq_zero_iff.mp (le_antisymm hp (sq_nonneg _))
  . intro hz
    unfold packetMean
    simp_rw [hz]
    simp

theorem coupled_count_packet_equality_iff {J : Type*} [Fintype J]
    (h t : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hh : forall i, Not (h i = 0)) (ht : forall i, Not (t i = 0))
    (hchi : forall i, (quadraticChar (K i)) (t i) = -1)
    (hq : forall i, 5 < (Fintype.card (K i) : Real))
    (scale : J -> (i : I) -> K i) (hu : forall j i, Not (scale j i = 0))
    (weight : J -> Real)
    (hmean : packetMean K (coupledCountPacket K h scale weight) = 1) :
    packetMean K (fun x => (coupledCountPacket K h scale weight x) ^ 2) =
        Finset.univ.prod (minimumFactors K h) <->
      forall x, coupledCountPacket K h scale weight x =
        purePacket K (optimalFactors K h t) x := by
  have hi := coupled_count_packet_square_defect K h t hodd hh ht hchi hq scale hu weight hmean
  constructor
  . intro heq
    have hz : packetMean K (fun x =>
        (coupledCountPacket K h scale weight x -
          purePacket K (optimalFactors K h t) x) ^ 2) = 0 := by linarith only [hi, heq]
    have hp := (packetMean_square_eq_zero_iff K _).mp hz
    intro x
    exact sub_eq_zero.mp (hp x)
  . intro hp
    simp_rw [hp]
    exact (optimalPacket_law K h t hodd hh ht hchi hq).2.1


theorem canonical_scales_nonzero (t : (i : I) -> K i)
    (ht : forall i, Not (t i = 0)) :
    forall (choice : I -> Bool) (i : I), Not (canonicalScales K t choice i = 0) := by
  intro choice i
  unfold canonicalScales
  split_ifs
  . exact ht i
  . exact one_ne_zero

theorem canonical_packet_law (h t : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hh : forall i, Not (h i = 0)) (ht : forall i, Not (t i = 0))
    (hchi : forall i, (quadraticChar (K i)) (t i) = -1)
    (hq : forall i, 5 < (Fintype.card (K i) : Real)) :
    packetMean K (coupledCountPacket K h (canonicalScales K t) (canonicalWeights K h)) = 1 /\
      packetMean K (fun x =>
        (coupledCountPacket K h (canonicalScales K t) (canonicalWeights K h) x) ^ 2) =
          Finset.univ.prod (minimumFactors K h) := by
  have hp : coupledCountPacket K h (canonicalScales K t) (canonicalWeights K h) =
      purePacket K (optimalFactors K h t) := funext (canonical_packet_eq_optimum K h t)
  rw [hp]
  have hlaw := optimalPacket_law K h t hodd hh ht hchi hq
  exact And.intro hlaw.1 hlaw.2.1

end FiniteField.QuadraticPairTwistJoint

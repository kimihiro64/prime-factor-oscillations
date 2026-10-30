/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistJoint
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticTripleSymmetry
/-!
# Exact minimum cost of centering quadratic-triple counts

The canonical positive symmetric mass minimizes collision energy over all
normalized centered real masses on the full admissible shape space.
Its exact square-defect identity reuses the maintained packet theorem.
The optimum has effective support (q-1)*(q-5), exactly q+1 below the
uniform support size. No integer-prime transfer or RH estimate is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticTripleTwist
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def centeringMinimum (F : Type*) [Fintype F] : Real :=
  1/(((Fintype.card F : Real)-1)*((Fintype.card F : Real)-5))

theorem shapeState_card_pos (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F) :
    0 < Fintype.card (shapeState h) := by
  have hc : (Fintype.card (shapeState h) : Int) =
      ((Fintype.card F : Int)-2)*((Fintype.card F : Int)-3) := by
    simpa using full_shape_mass hF h t hh ht hchi
  have hqi : (5 : Int) < Fintype.card F := by exact_mod_cast hq
  have hp : (0 : Int) < Fintype.card (shapeState h) := by
    rw [hc]
    exact mul_pos (by omega) (by omega)
  exact_mod_cast hp

theorem centered_mass_canonical_pairing (h t : F) (hq : 5 < Fintype.card F)
    (M : shapeState h -> Real)
    (hnorm : Finset.univ.sum M = 1)
    (hmean : (Finset.univ.sum fun p : shapeState h =>
      M p*(compensatedWave h p.val.1 t p.val.2 : Real)) = 0) :
    (Finset.univ.sum fun p : shapeState h => M p*symmetryMass h t p) =
      centeringMinimum F := by
  have hs : (Finset.univ.sum fun p : shapeState h => M p*symmetryMass h t p) =
      (((Fintype.card F : Real)-3)*Finset.univ.sum M +
        (Finset.univ.sum fun p : shapeState h =>
          M p*(compensatedWave h p.val.1 t p.val.2 : Real))) /
          (symmetryNormalizer F : Real) := by
    calc
      _ = Finset.univ.sum (fun p : shapeState h =>
          (((Fintype.card F : Real)-3)*M p +
            M p*(compensatedWave h p.val.1 t p.val.2 : Real))/
            (symmetryNormalizer F : Real)) := by
        apply Finset.sum_congr rfl
        intro p _
        simp only [symmetryMass,symmetryWeight,Int.cast_add,Int.cast_sub,
          Int.cast_natCast,Int.cast_ofNat]
        ring
      _ = _ := by rw [<- Finset.sum_div,Finset.sum_add_distrib,<- Finset.mul_sum]
  rw [hs,hnorm,hmean]
  have hqr : (5 : Real) < Fintype.card F := by exact_mod_cast hq
  have ha : Not (((Fintype.card F : Real)-3)=0) := ne_of_gt (by linarith only [hqr])
  have hb : Not (((Fintype.card F : Real)-1)=0) := ne_of_gt (by linarith only [hqr])
  have hc : Not (((Fintype.card F : Real)-5)=0) := ne_of_gt (by linarith only [hqr])
  unfold centeringMinimum symmetryNormalizer
  push_cast
  field_simp [ha,hb,hc]
  <;> ring

theorem canonical_square_mass (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F) :
    (Finset.univ.sum fun p : shapeState h => (symmetryMass h t p)^2) =
      centeringMinimum F := by
  simpa only [pow_two] using centered_mass_canonical_pairing h t hq
    (symmetryMass h t) (sum_symmetryMass hF h t hh ht hchi hq)
    (symmetryMass_first_moment_zero hF h t hh ht hchi)

theorem singleton_shape_packetMean (h : F) (g : shapeState h -> Real) :
    QuadraticPairTwistJoint.packetMean (fun _ : Unit => shapeState h)
      (fun f => g (f ())) =
        (1/(Fintype.card (shapeState h) : Real))*Finset.univ.sum g := by
  let e : Equiv (Unit -> shapeState h) (shapeState h) :=
    { toFun := fun f => f ()
      invFun := fun p => fun _ => p
      left_inv := by intro f; funext u; cases u; rfl
      right_inv := by intro p; rfl }
  have he : (Finset.univ.sum fun f : Unit -> shapeState h => g (f ())) =
      Finset.univ.sum g := Equiv.sum_comp e g
  unfold QuadraticPairTwistJoint.packetMean
  simp only [Finset.univ_unique,Finset.prod_singleton]
  rw [he]


theorem centered_mass_square_defect (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F)
    (M : shapeState h -> Real)
    (hnorm : Finset.univ.sum M = 1)
    (hmean : (Finset.univ.sum fun p : shapeState h =>
      M p*(compensatedWave h p.val.1 t p.val.2 : Real)) = 0) :
    (Finset.univ.sum fun p : shapeState h => (M p)^2) =
      centeringMinimum F +
        (Finset.univ.sum fun p : shapeState h => (M p-symmetryMass h t p)^2) := by
  let n : Real := Fintype.card (shapeState h)
  let K : Unit -> Type _ := fun _ => shapeState h
  let w : (Unit -> shapeState h) -> Real := fun f => n*M (f ())
  let v : (Unit -> shapeState h) -> Real := fun f => n*symmetryMass h t (f ())
  have hnpos : 0 < n := by
    change (0 : Real) < Fintype.card (shapeState h)
    exact_mod_cast shapeState_card_pos hF h t hh ht hchi hq
  have hn : Not (n=0) := ne_of_gt hnpos
  have hlin (g : shapeState h -> Real) :
      QuadraticPairTwistJoint.packetMean K (fun f => n*g (f ())) =
        Finset.univ.sum g := by
    change QuadraticPairTwistJoint.packetMean (fun _ : Unit => shapeState h)
      (fun f => n*g (f ())) = _
    rw [singleton_shape_packetMean h (fun p => n*g p)]
    change (1/n)*(Finset.univ.sum fun p : shapeState h => n*g p) = _
    rw [<- Finset.mul_sum]
    field_simp [hn]
  have hsq (g : shapeState h -> Real) :
      QuadraticPairTwistJoint.packetMean K (fun f => (n*g (f ()))^2) =
        n*(Finset.univ.sum fun p : shapeState h => (g p)^2) := by
    change QuadraticPairTwistJoint.packetMean (fun _ : Unit => shapeState h)
      (fun f => (n*g (f ()))^2) = _
    rw [singleton_shape_packetMean h (fun p => (n*g p)^2)]
    change (1/n)*(Finset.univ.sum fun p : shapeState h => (n*g p)^2) = _
    calc
      _ = (1/n)*(n^2*(Finset.univ.sum fun p : shapeState h => (g p)^2)) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = _ := by field_simp [hn]
  have hwm : QuadraticPairTwistJoint.packetMean K w = 1 := by
    change QuadraticPairTwistJoint.packetMean K (fun f => n*M (f ())) = _
    rw [hlin,hnorm]
  have hve : QuadraticPairTwistJoint.packetMean K (fun f => (v f)^2) =
      n*centeringMinimum F := by
    change QuadraticPairTwistJoint.packetMean K
      (fun f => (n*symmetryMass h t (f ()))^2) = _
    rw [hsq,canonical_square_mass hF h t hh ht hchi hq]
  have hpair : QuadraticPairTwistJoint.packetMean K (fun f => v f*w f) =
      (n*centeringMinimum F)*QuadraticPairTwistJoint.packetMean K w := by
    rw [hwm,mul_one]
    have he : (fun f : Unit -> shapeState h => v f*w f) =
        (fun f => n*(n*(M (f ())*symmetryMass h t (f ())))) := by
      funext f
      unfold v w
      ring
    rw [he,hlin (fun p => n*(M p*symmetryMass h t p)),<- Finset.mul_sum,
      centered_mass_canonical_pairing h t hq M hnorm hmean]
  have hd := QuadraticPairTwistJoint.packetMean_square_defect K w v
    (n*centeringMinimum F) hwm hve hpair
  have hdiff : QuadraticPairTwistJoint.packetMean K (fun f => (w f-v f)^2) =
      n*(Finset.univ.sum fun p : shapeState h => (M p-symmetryMass h t p)^2) := by
    change QuadraticPairTwistJoint.packetMean K
      (fun f => (n*M (f ())-n*symmetryMass h t (f ()))^2) = _
    simp_rw [<- mul_sub]
    exact hsq (fun p => M p-symmetryMass h t p)
  have hws : QuadraticPairTwistJoint.packetMean K (fun f => (w f)^2) =
      n*(Finset.univ.sum fun p : shapeState h => (M p)^2) := hsq M
  rw [hws,hdiff] at hd
  have hz : n*((Finset.univ.sum fun p : shapeState h => (M p)^2) -
      (centeringMinimum F +
        (Finset.univ.sum fun p : shapeState h => (M p-symmetryMass h t p)^2))) = 0 := by
    nlinarith only [hd]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hn)

theorem centered_mass_square_minimum (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F)
    (M : shapeState h -> Real)
    (hnorm : Finset.univ.sum M = 1)
    (hmean : (Finset.univ.sum fun p : shapeState h =>
      M p*(compensatedWave h p.val.1 t p.val.2 : Real)) = 0) :
    centeringMinimum F <= (Finset.univ.sum fun p : shapeState h => (M p)^2) := by
  rw [centered_mass_square_defect hF h t hh ht hchi hq M hnorm hmean]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun p _ => sq_nonneg _))

theorem centered_mass_square_equality_iff (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F)
    (M : shapeState h -> Real)
    (hnorm : Finset.univ.sum M = 1)
    (hmean : (Finset.univ.sum fun p : shapeState h =>
      M p*(compensatedWave h p.val.1 t p.val.2 : Real)) = 0) :
    (Finset.univ.sum fun p : shapeState h => (M p)^2) = centeringMinimum F <->
      forall p : shapeState h, M p = symmetryMass h t p := by
  constructor
  . intro he
    have hd := centered_mass_square_defect hF h t hh ht hchi hq M hnorm hmean
    have hs : (Finset.univ.sum fun p : shapeState h =>
        (M p-symmetryMass h t p)^2) = 0 := by linarith only [he,hd]
    intro p
    have hp := Finset.single_le_sum (fun s (_ : Membership.mem
      (Finset.univ : Finset (shapeState h)) s) => sq_nonneg (M s-symmetryMass h t s))
      (Finset.mem_univ p)
    rw [hs] at hp
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hp (sq_nonneg _)))
  . intro he
    simp_rw [he]
    exact canonical_square_mass hF h t hh ht hchi hq


omit [Field F] [DecidableEq F] in
theorem centeringMinimum_pos (hq : 5 < Fintype.card F) :
    0 < centeringMinimum F := by
  have hqr : (5 : Real) < Fintype.card F := by exact_mod_cast hq
  unfold centeringMinimum
  exact div_pos (by norm_num)
    (mul_pos (by linarith only [hqr]) (by linarith only [hqr]))

theorem canonical_reciprocal_square_mass (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F) :
    1/(Finset.univ.sum fun p : shapeState h => (symmetryMass h t p)^2) =
      ((Fintype.card F : Real)-1)*((Fintype.card F : Real)-5) := by
  rw [canonical_square_mass hF h t hh ht hchi hq]
  simp only [centeringMinimum,one_div_one_div]

theorem centered_mass_effective_support_bound (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F)
    (M : shapeState h -> Real)
    (hnorm : Finset.univ.sum M = 1)
    (hmean : (Finset.univ.sum fun p : shapeState h =>
      M p*(compensatedWave h p.val.1 t p.val.2 : Real)) = 0) :
    1/(Finset.univ.sum fun p : shapeState h => (M p)^2) <=
      ((Fintype.card F : Real)-1)*((Fintype.card F : Real)-5) := by
  have hl := centered_mass_square_minimum hF h t hh ht hchi hq M hnorm hmean
  have hp := centeringMinimum_pos (F := F) hq
  have hi := one_div_le_one_div_of_le hp hl
  simpa only [centeringMinimum,one_div_one_div] using hi

theorem canonical_effective_support_loss (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F) :
    (Fintype.card (shapeState h) : Real) -
      1/(Finset.univ.sum fun p : shapeState h => (symmetryMass h t p)^2) =
        (Fintype.card F : Real)+1 := by
  have hci : (Fintype.card (shapeState h) : Int) =
      ((Fintype.card F : Int)-2)*((Fintype.card F : Int)-3) := by
    simpa using full_shape_mass hF h t hh ht hchi
  have hcr : (Fintype.card (shapeState h) : Real) =
      ((Fintype.card F : Real)-2)*((Fintype.card F : Real)-3) := by
    exact_mod_cast hci
  rw [hcr,canonical_reciprocal_square_mass hF h t hh ht hchi hq]
  ring

end FiniteField.QuadraticTripleTwist

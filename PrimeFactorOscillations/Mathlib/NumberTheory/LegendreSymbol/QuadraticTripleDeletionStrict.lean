/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticTripleDeletionStability
/-!
# Strict quadratic-triple deletion height

For every odd finite field of cardinal greater than seven, the integer
slack in the signed deletion-height inequality is at least one.
The proof retains the complete certificate, forces a saturated fibre
under hypothetical equality, and excludes its extreme trace by two
Legendre involutions. Characteristic three is handled separately using
the field cardinal and square residues modulo nine. The resulting bound
keeps the actual retained sum and strengthens the square-root threshold.
No integer prime-gap or RH transfer is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticTripleTwist
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem trace_root_translate (hF : Not (ringChar F = 2)) (a b : F) :
    splitCubicPointTrace a b = splitCubicPointTrace (-b) (a-b) := by
  rw [splitCubicPointTrace_eq hF,splitCubicPointTrace_eq hF]
  congr 1
  let e : Equiv F F :=
    { toFun := fun x => x+b
      invFun := fun x => x-b
      left_inv := by intro x; ring
      right_inv := by intro x; ring }
  calc
    _ = Finset.univ.sum (fun x : F =>
        quadraticChar F ((e x)*(e x-a)*(e x-b))) := (Equiv.sum_comp e _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      change quadraticChar F ((x+b)*(x+b-a)*(x+b-b)) =
        quadraticChar F (x*(x-(-b))*(x-(a-b)))
      congr 1
      ring

def regularReflect (z : regularState (F := F)) : regularState (F := F) :=
  Subtype.mk (-z.val-1) (by
    constructor
    . intro hz
      apply z.property.2
      have hn : -(z.val+1)=0 := by
        calc
          _ = -z.val-1 := by ring
          _ = 0 := hz
      exact neg_eq_zero.mp hn
    . intro hz
      apply z.property.1
      have hn : -z.val=0 := by
        calc
          _ = (-z.val-1)+1 := by ring
          _ = 0 := hz
      exact neg_eq_zero.mp hn)

def regularInverse (z : regularState (F := F)) : regularState (F := F) :=
  Subtype.mk ((Inv.inv z.val)) (by
    constructor
    . exact inv_ne_zero z.property.1
    . intro hz
      apply z.property.2
      have he : z.val*((Inv.inv z.val)+1)=z.val+1 := by
        field_simp [z.property.1]
        <;> ring
      have hm := congrArg (fun x : F => z.val*x) hz
      rw [he,mul_zero] at hm
      exact hm)

theorem trace_reflect_square (hF : Not (ringChar F = 2))
    (z : regularState (F := F)) :
    (splitCubicPointTrace (regularReflect z).val ((regularReflect z).val+1))^2 =
      (splitCubicPointTrace z.val (z.val+1))^2 := by
  have hs : splitCubicPointTrace (-z.val-1) ((-z.val-1)+1) =
      quadraticChar F (-1)*splitCubicPointTrace z.val (z.val+1) := by
    calc
      _ = splitCubicPointTrace ((-1)*z.val) ((-1)*(z.val+1)) := by
        rw [splitCubicPointTrace_comm hF]
        congr 1 <;> ring
      _ = _ := splitCubicPointTrace_scale hF (-1) (neg_ne_zero.mpr one_ne_zero)
        z.val (z.val+1)
  change (splitCubicPointTrace (-z.val-1) ((-z.val-1)+1))^2 = _
  rw [hs,mul_pow,quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero),one_mul]

theorem trace_inverse_square (hF : Not (ringChar F = 2))
    (z : regularState (F := F)) :
    (splitCubicPointTrace (regularInverse z).val ((regularInverse z).val+1))^2 =
      (splitCubicPointTrace z.val (z.val+1))^2 := by
  have hs : splitCubicPointTrace z.val (z.val+1) =
      quadraticChar F (-z.val)*splitCubicPointTrace ((Inv.inv z.val)) ((Inv.inv z.val)+1) := by
    calc
      _ = splitCubicPointTrace (-(z.val+1)) (z.val-(z.val+1)) :=
        trace_root_translate hF z.val (z.val+1)
      _ = splitCubicPointTrace ((-z.val)*((Inv.inv z.val)+1)) ((-z.val)*(Inv.inv z.val)) := by
        congr 1 <;> field_simp [z.property.1] <;> ring
      _ = quadraticChar F (-z.val)*
          splitCubicPointTrace ((Inv.inv z.val)+1) ((Inv.inv z.val)) :=
        splitCubicPointTrace_scale hF (-z.val) (neg_ne_zero.mpr z.property.1)
          ((Inv.inv z.val)+1) ((Inv.inv z.val))
      _ = _ := by rw [splitCubicPointTrace_comm hF ((Inv.inv z.val)+1) ((Inv.inv z.val))]
  have hp := congrArg (fun x : Int => x^2) hs
  rw [mul_pow,quadraticChar_sq_one (neg_ne_zero.mpr z.property.1),one_mul] at hp
  exact hp.symm

theorem distinct_regular_trace_energy (hF : Not (ringChar F = 2))
    (z w : regularState (F := F)) (hne : Not (z=w)) :
    (splitCubicPointTrace z.val (z.val+1))^2+
      (splitCubicPointTrace w.val (w.val+1))^2 <=
        ((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) := by
  calc
    _ = ({z,w} : Finset (regularState (F := F))).sum
        (fun v => (splitCubicPointTrace v.val (v.val+1))^2) := by simp [hne]
    _ <= Finset.univ.sum (fun v : regularState (F := F) =>
        (splitCubicPointTrace v.val (v.val+1))^2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
    _ = _ := sum_regular_trace_square hF

theorem trace_square_lt_cap_square (hF : Not (ringChar F = 2))
    (h3 : Not ((3 : F)=0)) (hq : 7 < Fintype.card F)
    (z : regularState (F := F)) :
    (splitCubicPointTrace z.val (z.val+1))^2 < ((Fintype.card F : Int)-3)^2 := by
  have he : 2*(splitCubicPointTrace z.val (z.val+1))^2 <=
      ((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) := by
    by_cases hr : regularReflect z=z
    . have hi : Not (regularInverse z=z) := by
        intro hi
        have hiV := congrArg Subtype.val hi
        change (Inv.inv z.val)=z.val at hiV
        have hs : z.val*z.val=1 := by
          calc
            _ = z.val*(Inv.inv z.val) := by rw [hiV]
            _ = 1 := by field_simp [z.property.1]
        have hp : (z.val-1)*(z.val+1)=0 := by
          calc
            _ = z.val*z.val-1 := by ring
            _ = 0 := by rw [hs]; ring
        have hz1 : z.val=1 :=
          sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right z.property.2)
        have hrV := congrArg Subtype.val hr
        change -z.val-1=z.val at hrV
        rw [hz1] at hrV
        apply h3
        calc
          (3 : F) = 1-((-1)-1) := by ring
          _ = 0 := by rw [hrV]; ring
      have hp := distinct_regular_trace_energy hF z (regularInverse z)
        (fun hz => hi hz.symm)
      rw [trace_inverse_square hF z] at hp
      linarith only [hp]
    . have hp := distinct_regular_trace_energy hF z (regularReflect z)
        (fun hz => hr hz.symm)
      rw [trace_reflect_square hF z] at hp
      linarith only [hp]
  have hq8 : 8 <= Fintype.card F := by omega
  have hqI : (8 : Int) <= (Fintype.card F : Int) := by exact_mod_cast hq8
  have hp : 0 < ((Fintype.card F : Int)-3)*((Fintype.card F : Int)-7) :=
    mul_pos (by omega) (by omega)
  nlinarith only [he,hp]

theorem square_mod_nine_ne_six (d : Int) : Not (d^2%9=6) := by
  intro hs
  rw [pow_two,Int.mul_emod] at hs
  have h0 : 0 <= d%9 := Int.emod_nonneg d (by norm_num)
  have h9 : d%9 < 9 := Int.emod_lt_of_pos d (by norm_num)
  have hc : d%9=0 \/ d%9=1 \/ d%9=2 \/ d%9=3 \/ d%9=4 \/
      d%9=5 \/ d%9=6 \/ d%9=7 \/ d%9=8 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h
  all_goals norm_num [h] at hs

theorem cast_three_ne_zero_of_char_ne (hc : Not (ringChar F=3)) :
    Not ((3 : F)=0) := by
  intro hz
  have hd : ringChar F = 1 \/ ringChar F=3 :=
    (Nat.dvd_prime (by decide : Nat.Prime 3)).mp ((ringChar.spec F 3).mp hz)
  have hp : Nat.Prime (ringChar F) :=
    (FiniteField.card F (ringChar F)).choose_spec.1
  rcases hd with hd | hd
  . exact hp.ne_one hd
  . exact hc hd

theorem card_mod_nine_of_char_three (hc : ringChar F=3)
    (hq : 7 < Fintype.card F) : (Fintype.card F : Int)%9=0 := by
  letI : CharP F 3 := by rw [<- hc]; infer_instance
  have hd := FiniteField.card F 3
  let n := hd.choose
  have hn0 : 0 < (n : Nat) := n.pos
  have heq : Fintype.card F=3^(n : Nat) := hd.choose_spec.2
  have hn2 : 2 <= (n : Nat) := by
    by_contra hn
    have hn1 : (n : Nat)=1 := by omega
    rw [hn1] at heq
    norm_num at heq
    omega
  have hn : (n : Nat)=(n : Nat)-2+2 := by omega
  have heq2 : Fintype.card F=9*3^((n : Nat)-2) := by
    calc
      _ = 3^(n : Nat) := heq
      _ = 3^((n : Nat)-2+2) := congrArg (fun k : Nat => 3^k) hn
      _ = _ := by rw [Nat.pow_add]; ring
  have heqI : (Fintype.card F : Int)=9*((3^((n : Nat)-2) : Nat) : Int) := by
    exact_mod_cast heq2
  omega

theorem scalar_zero_slack_window (a m : Int) (ha : 5 <= a)
    (hm : a < m) (hs : (m-a)^2=4*a) : m < 2*a-1 := by
  have ha6 : 6 <= a := by
    by_contra hh
    have ha5 : a=5 := by omega
    subst a
    by_cases hd : m-5 <= 4
    . have hl : 0 <= m-5 := by omega
      have hr : 0 <= 4-(m-5) := by omega
      nlinarith only [hs,hd,hl,mul_nonneg hl hr]
    . have hl : 5 <= m-5 := by omega
      nlinarith only [hs,hl,sq_nonneg (m-10)]
  by_contra hn
  have hp : 0 <= a*(a-6) := mul_nonneg (by omega) (by omega)
  have h0 : 0 <= m-a-(a-1) := by omega
  have h1 : 0 <= m-a+(a-1) := by omega
  nlinarith only [hs,hp,mul_nonneg h0 h1]

theorem cap_equality_forces_saturated_count {J : Type*} [DecidableEq J]
    (s : Finset J) (c : J -> Int) (a : Int)
    (hc0 : forall j, Membership.mem s j -> 0 <= c j)
    (hca : forall j, Membership.mem s j -> c j <= a)
    (ha : 5 <= a) (hm : a < s.sum c) (hs : (s.sum c-a)^2=4*a)
    (he : (s.sum fun j => (c j)^2)=a^2+(s.sum c-a)^2) :
    Exists (fun j => Membership.mem s j /\ c j=a) := by
  by_contra hn
  have hsmall : forall j, Membership.mem s j -> c j <= a-1 := by
    intro j hj
    have hne : Not (c j=a) := by
      intro heq
      exact hn (Exists.intro j (And.intro hj heq))
    have hb := hca j hj
    omega
  have hp := capped_count_squares s c (a-1) hc0 hsmall
  have hw := scalar_zero_slack_window a (s.sum c) ha hm hs
  nlinarith only [hp,he,hw]

theorem zero_slack_saturated_fibre (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 7 < Fintype.card F)
    (D : Finset (shapeState h)) (hB : deletionSlack h t D=0) :
    Exists (fun z : regularState (F := F) =>
      fibreDeletionCount h hh D z=(Fintype.card F : Int)-3) := by
  let a : Int := (Fintype.card F : Int)-3
  let m : Int := (D.card : Int)
  have hR := zero_slack_retainedWave hF h t hh ht hchi D hB
  have ha : 5 <= a := by
    have hq8 : 8 <= Fintype.card F := by omega
    have hqI : (8 : Int) <= (Fintype.card F : Int) := by exact_mod_cast hq8
    dsimp [a]
    omega
  have hm0 : 0 <= m := by dsimp [m]; exact_mod_cast (Nat.zero_le D.card)
  have hs : (m-a)^2=4*a := by
    have hb := hB
    unfold deletionSlack at hb
    change (m-a)^2-4*a-2*retainedWave h t D=0 at hb
    rw [hR] at hb
    linarith only [hb]
  have hlarge : a < m := by
    have hp := (full_deletion_count_constraints hF h t hh ht hchi D).1
    rw [hR] at hp
    have hp' : a*(a+4) <= m^2 := by dsimp [a,m]; nlinarith only [hp]
    by_contra hn
    have h0 : 0 <= a-m := by omega
    have h1 : 0 <= a+m := by omega
    nlinarith only [hp',mul_nonneg h0 h1,ha]
  have he : (Finset.univ.sum fun z : regularState (F := F) =>
      (fibreDeletionCount h hh D z)^2)=a^2+(m-a)^2 := by
    have hc := ((deletion_zero_slack_iff hF h t hh ht hchi D).mp hB).1
    unfold deletionCapSlack at hc
    change a^2+(m-a)^2-
      (Finset.univ.sum fun z : regularState (F := F) =>
        (fibreDeletionCount h hh D z)^2)=0 at hc
    linarith only [hc]
  have hc0 (z : regularState (F := F))
      (_ : Membership.mem (Finset.univ : Finset (regularState (F := F))) z) :
      0 <= fibreDeletionCount h hh D z := (fibreDeletionCount_bounds h hh D z).1
  have hca (z : regularState (F := F))
      (_ : Membership.mem (Finset.univ : Finset (regularState (F := F))) z) :
      fibreDeletionCount h hh D z <= a := (fibreDeletionCount_bounds h hh D z).2
  have hm' : a < Finset.univ.sum (fibreDeletionCount h hh D) := by
    rw [sum_fibreDeletionCount h hh D]
    exact hlarge
  have hs' : (Finset.univ.sum (fibreDeletionCount h hh D)-a)^2=4*a := by
    rw [sum_fibreDeletionCount h hh D]
    exact hs
  have he' : (Finset.univ.sum fun z : regularState (F := F) =>
      (fibreDeletionCount h hh D z)^2)=
      a^2+(Finset.univ.sum (fibreDeletionCount h hh D)-a)^2 := by
    rw [sum_fibreDeletionCount h hh D]
    exact he
  have hsat := cap_equality_forces_saturated_count Finset.univ
    (fibreDeletionCount h hh D) a hc0 hca ha hm' hs' he'
  exact Exists.intro hsat.choose hsat.choose_spec.2

theorem strict_deletion_slack (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 7 < Fintype.card F)
    (D : Finset (shapeState h)) : 1 <= deletionSlack h t D := by
  have hb := (deletion_slack_budgets hF h t hh ht hchi D).1
  have hne : Not (deletionSlack h t D=0) := by
    intro hB
    by_cases hc : ringChar F=3
    . have hR := zero_slack_retainedWave hF h t hh ht hchi D hB
      have hs := hB
      unfold deletionSlack at hs
      rw [hR] at hs
      have he : ((D.card : Int)-((Fintype.card F : Int)-3))^2 =
          4*((Fintype.card F : Int)-3) := by linarith only [hs]
      have h9 := card_mod_nine_of_char_three hc hq
      have hr : (4*((Fintype.card F : Int)-3))%9=6 := by omega
      have hm : (((D.card : Int)-((Fintype.card F : Int)-3))^2)%9=6 := by
        rw [he,hr]
      exact square_mod_nine_ne_six _ hm
    . have hsat := zero_slack_saturated_fibre hF h t hh ht hchi hq D hB
      let z := hsat.choose
      have hcz : fibreDeletionCount h hh D z=(Fintype.card F : Int)-3 :=
        hsat.choose_spec
      have hp := small_slack_phase_purity hF h t hh ht hchi D
        (show deletionSlack h t D < 4 from by rw [hB]; norm_num) z
      have hm : positiveFibreDeletionCount h hh D z*negativeFibreDeletionCount h hh D z=0 := by
        rcases hp with hp | hp
        . rw [hp,zero_mul]
        . rw [hp,mul_zero]
      have hid := fibreDeletion_mixed_pair_identity h hh D z
      rw [hm,mul_zero,add_zero,hcz] at hid
      have he := zero_slack_fibre_balance hF h t hh ht hchi D hB z
      rw [retainedFibrePhase_eq hF h hh D z] at he
      have hd := sub_eq_zero.mp he
      rw [hd] at hid
      have htbound := trace_square_lt_cap_square hF (cast_three_ne_zero_of_char_ne hc) hq z
      nlinarith only [hid,htbound]
  omega

theorem strict_deletion_count_bound (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 7 < Fintype.card F)
    (D : Finset (shapeState h)) :
    4*((Fintype.card F : Int)-3)+2*retainedWave h t D+1 <=
      ((D.card : Int)-((Fintype.card F : Int)-3))^2 := by
  have hb := strict_deletion_slack hF h t hh ht hchi hq D
  unfold deletionSlack at hb
  linarith only [hb]

theorem strict_deletion_height_sqrt_bound (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 7 < Fintype.card F)
    (D : Finset (shapeState h)) (hR : 0 <= retainedWave h t D) :
    ((Fintype.card F : Real)-3)+
      Real.sqrt (4*((Fintype.card F : Real)-3)+2*(retainedWave h t D : Real)+1) <=
        (D.card : Real) := by
  have hi := strict_deletion_count_bound hF h t hh ht hchi hq D
  have hcast : 4*((Fintype.card F : Real)-3)+2*(retainedWave h t D : Real)+1 <=
      ((D.card : Real)-((Fintype.card F : Real)-3))^2 := by exact_mod_cast hi
  have hold := deletion_height_sqrt_bound hF h t hh ht hchi (by omega) D hR
  let a : Real := (Fintype.card F : Real)-3
  let m : Real := D.card
  let r : Real := retainedWave h t D
  change a+Real.sqrt (4*a+2*r+1) <= m
  change a+Real.sqrt (4*a+2*r) <= m at hold
  change 4*a+2*r+1 <= (m-a)^2 at hcast
  have hqr : (7 : Real) < (Fintype.card F : Real) := by exact_mod_cast hq
  have ha : 0 < a := by dsimp only [a]; linarith only [hqr]
  have hr : 0 <= r := by
    change (0 : Real) <= (retainedWave h t D : Real)
    exact_mod_cast hR
  have hma : 0 <= m-a := by
    have hs := Real.sqrt_nonneg (4*a+2*r)
    linarith only [hold,hs]
  have hrad : 0 < 4*a+2*r+1 := by linarith only [ha,hr]
  have hn := Real.sqrt_nonneg (4*a+2*r+1)
  have hs := Real.sq_sqrt hrad.le
  have hpos : 0 < Real.sqrt (4*a+2*r+1) := by nlinarith only [hn,hs,hrad]
  by_contra hc
  have hlt : m-a < Real.sqrt (4*a+2*r+1) := by linarith only [hc]
  have hp := mul_pos (sub_pos.mpr hlt)
    (show 0 < Real.sqrt (4*a+2*r+1)+(m-a) from by linarith only [hpos,hma])
  nlinarith only [hp,hcast,hs]

theorem square_shift_deletion_count (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1)
    (s : Nat) (hs : 3 <= s) (hq : Fintype.card F=s^2+3)
    (D : Finset (shapeState h)) (hR : 0 <= retainedWave h t D) :
    s^2+2*s+1 <= D.card := by
  have hq7 : 7 < Fintype.card F := by rw [hq]; nlinarith only [hs]
  have hqI : (Fintype.card F : Int)=(s : Int)^2+3 := by exact_mod_cast hq
  let k : Int := s
  let m : Int := D.card
  have hk : 3 <= k := by dsimp only [k]; exact_mod_cast hs
  have hm0 : 0 <= m := by dsimp only [m]; exact_mod_cast (Nat.zero_le D.card)
  have hk2 : 0 < k^2 := pow_pos (show 0 < k from by omega) 2
  have hi := strict_deletion_count_bound hF h t hh ht hchi hq7 D
  have hp := (full_deletion_count_constraints hF h t hh ht hchi D).1
  rw [hqI] at hi hp
  have hi' : 4*k^2+2*retainedWave h t D+1 <= (m-k^2)^2 := by
    dsimp only [k,m]
    nlinarith only [hi]
  have hp' : k^2*(k^2+4)+2*retainedWave h t D <= m^2 := by
    dsimp only [k,m]
    nlinarith only [hp]
  have hma : 0 <= m-k^2 := by
    by_contra hn
    have hf := mul_nonneg
      (show 0 <= k^2-m from by omega)
      (add_nonneg (sq_nonneg k) hm0)
    nlinarith only [hp',hR,hf,hk2]
  by_contra hn
  have hmleN : D.card <= s^2+2*s := by omega
  have hmle : m <= k^2+2*k := by dsimp only [m,k]; exact_mod_cast hmleN
  have hf := mul_nonneg
    (show 0 <= 2*k-(m-k^2) from by linarith only [hmle])
    (show 0 <= 2*k+(m-k^2) from by linarith only [hk,hma])
  nlinarith only [hi',hR,hf]

end FiniteField.QuadraticTripleTwist

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticTripleLaw
/-!
# Compensated waves of common-scale quadratic triples

Two distinct three-shift shapes cover the regular split-cubic trace family.
The actual compensated count retains at least the full regular second moment.
Every exceptional constant is kept explicitly in the admissible domain.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticTripleTwist
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def traceSquare (z : F) : Int := (splitCubicPointTrace z (z+1)) ^ 2

def regularTraceSquare (z : F) : Int :=
  if z = 0 then 0 else if z+1 = 0 then 0 else traceSquare z

def puncturedTraceSquare (alpha z : F) : Int :=
  if z = alpha then 0 else regularTraceSquare z

theorem traceSquare_zero (hF : Not (ringChar F = 2)) :
    traceSquare (0 : F) = 1 := by
  unfold traceSquare
  simp only [zero_add,splitCubicPointTrace_zero_left hF]
  exact quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : Not ((1 : F) = 0)))

theorem traceSquare_neg_one (hF : Not (ringChar F = 2)) :
    traceSquare (-1 : F) = 1 := by
  unfold traceSquare
  rw [show (-1 : F)+1=0 by ring,splitCubicPointTrace_comm hF,
    splitCubicPointTrace_zero_left hF]
  simp

theorem regularTraceSquare_nonneg (z : F) : 0 <= regularTraceSquare z := by
  unfold regularTraceSquare
  split_ifs
  . exact le_rfl
  . exact le_rfl
  . exact sq_nonneg _

theorem sum_regularTraceSquare (hF : Not (ringChar F = 2)) :
    (Finset.univ.sum fun z : F => regularTraceSquare z) =
      ((Fintype.card F : Int)-3) * ((Fintype.card F : Int)+1) := by
  have hshift (z : F) : z+1=0 <-> z = -1 := by
    constructor
    . intro he
      calc
        z = (z+1)-1 := by ring
        _ = -1 := by rw [he]; ring
    . intro he
      rw [he]
      ring
  have hpoint (z : F) :
      traceSquare z = regularTraceSquare z +
        (if z=0 then 1 else 0) + (if z+1=0 then 1 else 0) := by
    by_cases hz0 : z=0
    . subst z
      simp [regularTraceSquare,traceSquare_zero hF]
    . by_cases hz1 : z+1=0
      . have he := (hshift z).mp hz1
        subst z
        simp [regularTraceSquare,traceSquare_neg_one hF]
      . simp [regularTraceSquare,hz0,hz1]
  have hs := sum_splitCubicPointTrace_square hF (1 : F) one_ne_zero
  change (Finset.univ.sum fun z : F => traceSquare z) =
    (Fintype.card F : Int)^2 - 2*(Fintype.card F : Int)-1 at hs
  have hp :
      (Finset.univ.sum fun z : F => traceSquare z) =
        Finset.univ.sum (fun z : F => regularTraceSquare z +
          (if z=0 then 1 else 0) + (if z+1=0 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro z _
    exact hpoint z
  have h0 : (Finset.univ.sum fun z : F => if z=0 then (1 : Int) else 0) = 1 := by simp
  have h1 : (Finset.univ.sum fun z : F => if z+1=0 then (1 : Int) else 0) = 1 := by
    simp_rw [hshift]
    simp
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,h0,h1,hs] at hp
  nlinarith only [hp]

theorem two_puncture_energy_lower (hF : Not (ringChar F = 2)) (alpha beta : F)
    (hab : Not (alpha = beta)) :
    ((Fintype.card F : Int)-3) * ((Fintype.card F : Int)+1) <=
      (Finset.univ.sum fun z : F => puncturedTraceSquare alpha z) +
        (Finset.univ.sum fun z : F => puncturedTraceSquare beta z) := by
  have hp (z : F) :
      regularTraceSquare z <= puncturedTraceSquare alpha z + puncturedTraceSquare beta z := by
    unfold puncturedTraceSquare
    by_cases hza : z=alpha
    . subst z
      simp [hab]
    . by_cases hzb : z=beta
      . subst z
        simp [Ne.symm hab]
      . simp only [ite_eq_right hza,ite_eq_right hzb]
        exact le_add_of_nonneg_right (regularTraceSquare_nonneg z)
  have hs := Finset.sum_le_sum (fun z (_ : Membership.mem (Finset.univ : Finset F) z) => hp z)
  rw [Finset.sum_add_distrib,sum_regularTraceSquare hF] at hs
  exact hs


def compensatedWave (h k t x : F) : Int :=
  4 * twistTotal x (x+h) (x+k) t - (Fintype.card F : Int) - 1 +
    totalCorrection x (x+h) (x+k)

def waveSquare (h k t x : F) : Int :=
  if admissible h k x then (compensatedWave h k t x) ^ 2 else 0

theorem compensatedWave_eq_trace (hF : Not (ringChar F = 2)) (h k t x : F)
    (hh : Not (h = 0)) (hk : Not (k = 0)) (hhk : Not (h = k))
    (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1)
    (hx : admissible h k x) :
    compensatedWave h k t x = splitCubicPointTrace (h*(x+k)) (k*(x+h)) := by
  have hab : Not (x = x+h) := by
    intro he
    apply hh
    calc
      h = (x+h)-x := by ring
      _ = 0 := by rw [<- he]; ring
  have hac : Not (x = x+k) := by
    intro he
    apply hk
    calc
      k = (x+k)-x := by ring
      _ = 0 := by rw [<- he]; ring
  have hbc : Not (x+h = x+k) := by
    intro he
    exact hhk (add_left_cancel he)
  have hi := four_twistTotal_eq_trace hF x (x+h) (x+k) t
    hx.1 hx.2.1 hx.2.2 hab hac hbc ht hchi
  have hA : (x+k)*((x+h)-x) = h*(x+k) := by ring
  have hB : (x+h)*((x+k)-x) = k*(x+h) := by ring
  rw [hA,hB] at hi
  unfold compensatedWave
  linarith only [hi]

theorem regularTraceSquare_eq_ite (z : F) :
    regularTraceSquare z = if regular z then traceSquare z else 0 := by
  by_cases hz0 : z=0
  . simp [regularTraceSquare,regular,hz0]
  . by_cases hz1 : z+1=0
    . simp [regularTraceSquare,regular,hz0,hz1]
    . simp [regularTraceSquare,regular,hz0,hz1]

theorem waveSquare_transport (hF : Not (ringChar F = 2)) (h k t x : F)
    (hh : Not (h = 0)) (hk : Not (k = 0)) (hhk : Not (h = k))
    (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    waveSquare h k t x =
      puncturedTraceSquare (h/(k-h)) (shapeParameter h k x) := by
  have hiff := shapeParameter_admissible_iff h k hh hk hhk x
  unfold waveSquare puncturedTraceSquare
  by_cases hx : admissible h k x
  . have himage := hiff.mp hx
    rw [ite_eq_left hx,ite_eq_right himage.2,regularTraceSquare_eq_ite,
      ite_eq_left himage.1,compensatedWave_eq_trace hF h k t x hh hk hhk ht hchi hx]
    unfold traceSquare
    exact shapeParameter_trace_square hF h k x hhk hx.1
  . rw [ite_eq_right hx]
    by_cases hz : shapeParameter h k x = h/(k-h)
    . rw [ite_eq_left hz]
    . have hnr : Not (regular (shapeParameter h k x)) := by
        intro hr
        exact hx (hiff.mpr (And.intro hr hz))
      rw [ite_eq_right hz,regularTraceSquare_eq_ite,ite_eq_right hnr]

theorem sum_waveSquare_transport (hF : Not (ringChar F = 2)) (h k t : F)
    (hh : Not (h = 0)) (hk : Not (k = 0)) (hhk : Not (h = k))
    (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    (Finset.univ.sum fun x : F => waveSquare h k t x) =
      Finset.univ.sum (fun z : F => puncturedTraceSquare (h/(k-h)) z) := by
  have hp (x : F) := waveSquare_transport hF h k t x hh hk hhk ht hchi
  simp_rw [hp]
  change (Finset.univ.sum fun x : F =>
    puncturedTraceSquare (h/(k-h)) (shapeEquiv h k hh hk hhk x)) = _
  exact Equiv.sum_comp (shapeEquiv h k hh hk hhk)
    (fun z : F => puncturedTraceSquare (h/(k-h)) z)

theorem shape_omitted_ne (h k1 k2 : F) (hh : Not (h = 0))
    (hh1 : Not (h = k1)) (hh2 : Not (h = k2)) (hk12 : Not (k1 = k2)) :
    Not (h/(k1-h) = h/(k2-h)) := by
  have hd1 : Not (k1-h = 0) := sub_ne_zero.mpr (Ne.symm hh1)
  have hd2 : Not (k2-h = 0) := sub_ne_zero.mpr (Ne.symm hh2)
  intro he
  have hc : h*(k2-h) = h*(k1-h) := (div_eq_div_iff hd1 hd2).mp he
  have hz : h*(k1-k2)=0 := by
    calc
      _ = h*(k1-h)-h*(k2-h) := by ring
      _ = 0 := by rw [hc]; ring
  exact hk12 (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hh))

theorem two_shape_wave_energy (hF : Not (ringChar F = 2)) (h k1 k2 t : F)
    (hh : Not (h = 0)) (hk1 : Not (k1 = 0)) (hk2 : Not (k2 = 0))
    (hh1 : Not (h = k1)) (hh2 : Not (h = k2)) (hk12 : Not (k1 = k2))
    (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    ((Fintype.card F : Int)-3) * ((Fintype.card F : Int)+1) <=
      (Finset.univ.sum fun x : F => waveSquare h k1 t x) +
        (Finset.univ.sum fun x : F => waveSquare h k2 t x) := by
  have hs := two_puncture_energy_lower hF (h/(k1-h)) (h/(k2-h))
    (shape_omitted_ne h k1 k2 hh hh1 hh2 hk12)
  rw [<- sum_waveSquare_transport hF h k1 t hh hk1 hh1 ht hchi,
    <- sum_waveSquare_transport hF h k2 t hh hk2 hh2 ht hchi] at hs
  exact hs

def admissibleWeight (h k x : F) : Int := if admissible h k x then 1 else 0

theorem sum_admissibleWeight (h k : F)
    (hh : Not (h = 0)) (hk : Not (k = 0)) (hhk : Not (h = k)) :
    (Finset.univ.sum fun x : F => admissibleWeight h k x) =
      (Fintype.card F : Int)-3 := by
  have hshift (x a : F) : x+a=0 <-> x = -a := by
    constructor
    . intro he
      calc
        x = (x+a)-a := by ring
        _ = -a := by rw [he]; ring
    . intro he
      rw [he]
      ring
  have hp (x : F) :
      (1 : Int) = admissibleWeight h k x +
        (if x=0 then 1 else 0) + (if x+h=0 then 1 else 0) +
        (if x+k=0 then 1 else 0) := by
    unfold admissibleWeight admissible
    by_cases hx0 : x=0
    . subst x
      simp [hh,hk]
    . by_cases hxh : x+h=0
      . have hxk : Not (x+k=0) := by
          intro he
          exact hhk (add_left_cancel (hxh.trans he.symm))
        simp [hx0,hxh,hxk]
      . by_cases hxk : x+k=0
        . simp [hx0,hxh,hxk]
        . simp [hx0,hxh,hxk]
  have h0 : (Finset.univ.sum fun x : F => if x=0 then (1 : Int) else 0) = 1 := by simp
  have hh0 : (Finset.univ.sum fun x : F => if x+h=0 then (1 : Int) else 0) = 1 := by
    simp_rw [hshift]
    simp
  have hk0 : (Finset.univ.sum fun x : F => if x+k=0 then (1 : Int) else 0) = 1 := by
    simp_rw [hshift]
    simp
  have hs : (Finset.univ.sum fun _x : F => (1 : Int)) =
      Finset.univ.sum (fun x : F => admissibleWeight h k x +
        (if x=0 then 1 else 0) + (if x+h=0 then 1 else 0) +
        (if x+k=0 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro x _
    exact hp x
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    Finset.sum_add_distrib,h0,hh0,hk0] at hs
  linarith only [hs]

theorem two_shape_wave_witness (hF : Not (ringChar F = 2)) (h k1 k2 t : F)
    (hq : 3 < (Fintype.card F : Int))
    (hh : Not (h = 0)) (hk1 : Not (k1 = 0)) (hk2 : Not (k2 = 0))
    (hh1 : Not (h = k1)) (hh2 : Not (h = k2)) (hk12 : Not (k1 = k2))
    (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    (Exists fun x : F => admissible h k1 x /\
      (Fintype.card F : Int)+1 <= 2*(compensatedWave h k1 t x)^2) \/
    (Exists fun x : F => admissible h k2 x /\
      (Fintype.card F : Int)+1 <= 2*(compensatedWave h k2 t x)^2) := by
  by_contra hn
  have hb (k : F)
      (hnot : Not (Exists fun x : F => admissible h k x /\
        (Fintype.card F : Int)+1 <= 2*(compensatedWave h k t x)^2)) (x : F) :
      2*waveSquare h k t x <= (Fintype.card F : Int)*admissibleWeight h k x := by
    by_cases hx : admissible h k x
    . have hlt : Not ((Fintype.card F : Int)+1 <=
          2*(compensatedWave h k t x)^2) := by
        intro he
        exact hnot (Exists.intro x (And.intro hx he))
      simp only [waveSquare,admissibleWeight,ite_eq_left hx,mul_one]
      linarith only [hlt]
    . simp [waveSquare,admissibleWeight,hx]
  have hn1 : Not (Exists fun x : F => admissible h k1 x /\
      (Fintype.card F : Int)+1 <= 2*(compensatedWave h k1 t x)^2) :=
    fun he => hn (Or.inl he)
  have hn2 : Not (Exists fun x : F => admissible h k2 x /\
      (Fintype.card F : Int)+1 <= 2*(compensatedWave h k2 t x)^2) :=
    fun he => hn (Or.inr he)
  have hs1 := Finset.sum_le_sum
    (fun x (_ : Membership.mem (Finset.univ : Finset F) x) => hb k1 hn1 x)
  have hs2 := Finset.sum_le_sum
    (fun x (_ : Membership.mem (Finset.univ : Finset F) x) => hb k2 hn2 x)
  rw [<- Finset.mul_sum,<- Finset.mul_sum,sum_admissibleWeight h k1 hh hk1 hh1] at hs1
  rw [<- Finset.mul_sum,<- Finset.mul_sum,sum_admissibleWeight h k2 hh hk2 hh2] at hs2
  have he := two_shape_wave_energy hF h k1 k2 t hh hk1 hk2 hh1 hh2 hk12 ht hchi
  nlinarith only [hs1,hs2,he,hq]

theorem scaled_wave_floor (Q D W : Real)
    (hQ : 3 < Q) (hD0 : 0 < D) (hD : D <= Q-3)
    (hW : Q+1 <= 2*W^2) :
    Q+1 <= 2*(Q-3)^2*(W/D)^2 := by
  have hd : Not (D=0) := ne_of_gt hD0
  have hd2 : D^2 <= (Q-3)^2 := by
    have hp : 0 <= (Q-3-D)*(Q-3+D) :=
      mul_nonneg (sub_nonneg.mpr hD) (by linarith only [hQ,hD0])
    nlinarith only [hp]
  have he : 2*W^2 = 2*D^2*(W/D)^2 := by
    field_simp [hd]
    <;> ring
  calc
    Q+1 <= 2*W^2 := hW
    _ = 2*D^2*(W/D)^2 := he
    _ <= 2*(Q-3)^2*(W/D)^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd2 (by norm_num)) (sq_nonneg _)


theorem two_shape_density_wave (hF : Not (ringChar F = 2)) (h k1 k2 t : F)
    (hq : 11 <= (Fintype.card F : Int))
    (hh : Not (h = 0)) (hk1 : Not (k1 = 0)) (hk2 : Not (k2 = 0))
    (hh1 : Not (h = k1)) (hh2 : Not (h = k2)) (hk12 : Not (k1 = k2))
    (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    (Exists fun x : F => admissible h k1 x /\
      (Fintype.card F : Real)+1 <= 2*((Fintype.card F : Real)-3)^2 *
        (density h k1 t x-background h k1 x)^2) \/
    (Exists fun x : F => admissible h k2 x /\
      (Fintype.card F : Real)+1 <= 2*((Fintype.card F : Real)-3)^2 *
        (density h k2 t x-background h k2 x)^2) := by
  have hq3 : 3 < (Fintype.card F : Int) := by linarith only [hq]
  have hqr : (3 : Real) < (Fintype.card F : Real) := by exact_mod_cast hq3
  have hp (k : F) (hk : Not (k=0)) (hhk : Not (h=k)) (x : F)
      (hw : (Fintype.card F : Int)+1 <= 2*(compensatedWave h k t x)^2) :
      (Fintype.card F : Real)+1 <= 2*((Fintype.card F : Real)-3)^2 *
        (density h k t x-background h k x)^2 := by
    have hd := shapeDenominator_bounds h k hq hh hk hhk
    have hd0 : (0 : Real) < (shapeDenominator h k : Real) := by exact_mod_cast hd.1
    have hdu : (shapeDenominator h k : Real) <= (Fintype.card F : Real)-3 := by
      exact_mod_cast hd.2
    rw [density_sub_background]
    apply scaled_wave_floor _ _ _ hqr hd0 hdu
    unfold compensatedWave at hw
    exact_mod_cast hw
  rcases two_shape_wave_witness hF h k1 k2 t hq3 hh hk1 hk2 hh1 hh2 hk12 ht hchi
    with hleft | hright
  . exact Or.inl (hleft.elim fun x hx =>
      Exists.intro x (And.intro hx.1 (hp k1 hk1 hh1 x hx.2)))
  . exact Or.inr (hright.elim fun x hx =>
      Exists.intro x (And.intro hx.1 (hp k2 hk2 hh2 x hx.2)))

end FiniteField.QuadraticTripleTwist

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistAverage
/-!
# Common-scale quadratic triple counts

The actual count of three irreducible monic quadratics is pushed through
the exact square fibers, retaining every zero-discriminant mask. A reciprocal
change of variables identifies the resulting quartic character sum with an
actual split-cubic point trace. No Hasse bound or RH hypothesis is used.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticTripleTwist
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def characterMask (x : F) : Int :=
  1 - (quadraticChar F) x - (if x = 0 then 1 else 0)

def twistedMask (epsilon : Int) (x a : F) : Int :=
  1 - epsilon * (quadraticChar F) (x - a) - (if x = a then 1 else 0)

def tripleCount (a b c : F) : Int :=
  Finset.univ.sum fun z : F =>
    if Irreducible (monicQuadratic z a) /\
      Irreducible (monicQuadratic z b) /\
      Irreducible (monicQuadratic z c) then 1 else 0

theorem eight_nonsquare_triple_indicator (a b c : F) :
    8 * (if Not (IsSquare a) /\ Not (IsSquare b) /\ Not (IsSquare c)
      then (1 : Int) else 0) =
        characterMask a * characterMask b * characterMask c := by
  have hp :
      (if Not (IsSquare a) /\ Not (IsSquare b) /\ Not (IsSquare c)
        then (1 : Int) else 0) =
      (if IsSquare a then 0 else 1) *
        (if IsSquare b then 0 else 1) * (if IsSquare c then 0 else 1) := by
    by_cases ha : IsSquare a <;> by_cases hb : IsSquare b <;>
      by_cases hc : IsSquare c <;> simp [ha,hb,hc]
  rw [hp]
  calc
    _ = (2 * (if IsSquare a then (0 : Int) else 1)) *
        (2 * (if IsSquare b then (0 : Int) else 1)) *
        (2 * (if IsSquare c then (0 : Int) else 1)) := by ring
    _ = _ := by
      unfold characterMask
      rw [twice_nonsquare_indicator, twice_nonsquare_indicator, twice_nonsquare_indicator]

theorem tripleCount_eight_masks (hF : Not (ringChar F = 2)) (a b c : F) :
    8 * tripleCount a b c =
      Finset.univ.sum fun z : F =>
        characterMask (z ^ 2 - 4 * a) *
          characterMask (z ^ 2 - 4 * b) * characterMask (z ^ 2 - 4 * c) := by
  unfold tripleCount
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [monicQuadratic_irreducible_iff_nonsquare hF]
  exact eight_nonsquare_triple_indicator _ _ _

theorem tripleCount_scaled_character (hF : Not (ringChar F = 2))
    (u a b c : F) (hu : Not (u = 0)) :
    8 * tripleCount (u * a) (u * b) (u * c) =
      Finset.univ.sum fun x : F =>
        ((quadraticChar F) u * (quadraticChar F) x + 1) *
          (twistedMask ((quadraticChar F) u) x a *
            twistedMask ((quadraticChar F) u) x b *
              twistedMask ((quadraticChar F) u) x c) := by
  have h2 := two_ne_zero_of_odd (F := F) hF
  have hfour : Not ((4 : F) = 0) := by
    rw [show (4 : F) = (2 : F) ^ 2 by ring]
    exact pow_ne_zero 2 h2
  have h4u : Not ((4 : F) * u = 0) := mul_ne_zero hfour hu
  have hchi4 : (quadraticChar F) (4 : F) = 1 := by
    rw [show (4 : F) = (2 : F) ^ 2 by ring, map_pow, quadraticChar_sq_one h2]
  have hchi4u : (quadraticChar F) ((4 : F) * u) = (quadraticChar F) u := by
    rw [map_mul, hchi4, one_mul]
  have hm (x d : F) :
      characterMask ((4 * u) * x - 4 * (u * d)) =
        twistedMask ((quadraticChar F) u) x d := by
    have he : (4 * u) * x - 4 * (u * d) = (4 * u) * (x - d) := by ring
    unfold characterMask twistedMask
    simp only [he, map_mul, hchi4u, mul_eq_zero, h4u, false_or, sub_eq_zero]
  let e : Equiv F F :=
    { toFun := fun x => (4 * u) * x
      invFun := fun x => x / (4 * u)
      left_inv := by intro x; field_simp [h4u]
      right_inv := by intro x; field_simp [h4u] }
  let g : F -> Int := fun x =>
    ((quadraticChar F) x + 1) *
      (characterMask (x - 4 * (u * a)) *
        characterMask (x - 4 * (u * b)) *
          characterMask (x - 4 * (u * c)))
  calc
    _ = Finset.univ.sum g := by
      rw [tripleCount_eight_masks hF]
      exact quadraticChar_square_pushforward hF
        (fun x => characterMask (x - 4 * (u * a)) *
          characterMask (x - 4 * (u * b)) *
            characterMask (x - 4 * (u * c)))
    _ = Finset.univ.sum (fun x : F => g (e x)) := (Equiv.sum_comp e g).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      change ((quadraticChar F) ((4 * u) * x) + 1) *
        (characterMask ((4 * u) * x - 4 * (u * a)) *
          characterMask ((4 * u) * x - 4 * (u * b)) *
            characterMask ((4 * u) * x - 4 * (u * c))) = _
      simp only [map_mul, hchi4u, hm]

def quarticCharacterSum (a b c : F) : Int :=
  Finset.univ.sum fun x : F =>
    (quadraticChar F) (x * (x - a) * (x - b) * (x - c))

theorem quarticCharacterSum_eq_trace (hF : Not (ringChar F = 2))
    (a b c : F) (ha : Not (a = 0)) (hb : Not (b = 0)) (hc : Not (c = 0)) :
    quarticCharacterSum a b c =
      -1 - splitCubicPointTrace (c * (b - a)) (b * (c - a)) := by
  have habc : Not (a * b * c = 0) := mul_ne_zero (mul_ne_zero ha hb) hc
  let k : F := -(a * b * c)
  have hk : Not (k = 0) := neg_ne_zero.mpr habc
  let e : Equiv F F :=
    { toFun := fun x => k / x
      invFun := fun x => k / x
      left_inv := by
        intro x
        by_cases hx : x = 0
        . simp [hx]
        . field_simp [hx,hk]
      right_inv := by
        intro x
        by_cases hx : x = 0
        . simp [hx]
        . field_simp [hx,hk] }
  let f : F -> Int := fun x =>
    (quadraticChar F) ((x + b * c) * (x + a * c) * (x + a * b))
  let g : F -> Int := fun x =>
    (quadraticChar F) (x * (x - a) * (x - b) * (x - c))
  have hf0 : f 0 = 1 := by
    have he : (b * c) * (a * c) * (a * b) = (a * b * c) ^ 2 := by ring
    dsimp [f]
    simp only [zero_add]
    rw [he, map_pow, quadraticChar_sq_one habc]
  have hp (x : F) : g x = f (e x) - (if x = 0 then 1 else 0) := by
    by_cases hx : x = 0
    . subst x
      simp only [g, zero_mul, map_zero, ite_true]
      have he0 : e 0 = 0 := by simp [e]
      rw [he0,hf0]
      norm_num
    . have hs : Not (a * b * c / x ^ 2 = 0) :=
        div_ne_zero habc (pow_ne_zero 2 hx)
      have he :
          (e x + b * c) * (e x + a * c) * (e x + a * b) =
            (a * b * c / x ^ 2) ^ 2 * (x * (x - a) * (x - b) * (x - c)) := by
        dsimp [e,k]
        field_simp [hx]
        <;> ring
      have hchi : f (e x) = g x := by
        dsimp [f,g]
        rw [he,map_mul,map_pow,quadraticChar_sq_one hs,one_mul]
      simp only [ite_eq_right hx, sub_zero]
      exact hchi.symm
  have hg :
      (Finset.univ.sum g) = (Finset.univ.sum f) - 1 := by
    calc
      _ = Finset.univ.sum (fun x : F => f (e x) - (if x = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact hp x
      _ = _ := by
        rw [Finset.sum_sub_distrib,Equiv.sum_comp e f]
        simp
  let shift : Equiv F F :=
    { toFun := fun x => x + b * c
      invFun := fun x => x - b * c
      left_inv := by intro x; ring
      right_inv := by intro x; ring }
  have hsumf :
      (Finset.univ.sum f) = Finset.univ.sum (fun x : F =>
        (quadraticChar F) (x * (x - c * (b - a)) * (x - b * (c - a)))) := by
    calc
      _ = Finset.univ.sum (fun x : F =>
          (quadraticChar F)
            (shift x * (shift x - c * (b - a)) * (shift x - b * (c - a)))) := by
        apply Finset.sum_congr rfl
        intro x _
        unfold f
        congr 1
        dsimp [shift]
        ring
      _ = _ := Equiv.sum_comp shift (fun x : F =>
        (quadraticChar F) (x * (x - c * (b - a)) * (x - b * (c - a))))
  rw [splitCubicPointTrace_eq hF]
  unfold quarticCharacterSum
  dsimp only [g] at hg
  linarith only [hg,hsumf]

def symmetricMask (r : Int) (x a b c : F) : Int :=
  (r + 1) * (twistedMask 1 x a * twistedMask 1 x b * twistedMask 1 x c) +
    (-r + 1) * (twistedMask (-1) x a * twistedMask (-1) x b * twistedMask (-1) x c)

def basePolynomial (r : Int) (x a b c : F) : Int :=
  1 + (quadraticChar F) (x-a) * (quadraticChar F) (x-b) +
    (quadraticChar F) (x-a) * (quadraticChar F) (x-c) +
    (quadraticChar F) (x-b) * (quadraticChar F) (x-c) -
    r * ((quadraticChar F) (x-a) + (quadraticChar F) (x-b) +
      (quadraticChar F) (x-c) +
        (quadraticChar F) (x-a) * (quadraticChar F) (x-b) * (quadraticChar F) (x-c))

def rootCorrection (r : Int) (a b c : F) : Int :=
  1 + (quadraticChar F) (a-b) * (quadraticChar F) (a-c) -
    r * ((quadraticChar F) (a-b) + (quadraticChar F) (a-c))

def totalCorrection (a b c : F) : Int :=
  rootCorrection ((quadraticChar F) a) a b c +
    rootCorrection ((quadraticChar F) b) b a c +
      rootCorrection ((quadraticChar F) c) c a b

def twistTotal (a b c t : F) : Int :=
  tripleCount a b c + tripleCount (t*a) (t*b) (t*c)

theorem symmetricMask_corrected (r : Int) (x a b c : F)
    (hab : Not (a = b)) (hac : Not (a = c)) (hbc : Not (b = c)) :
    symmetricMask r x a b c =
      2 * basePolynomial r x a b c -
        (if x = a then 2 * rootCorrection r a b c else 0) -
        (if x = b then 2 * rootCorrection r b a c else 0) -
        (if x = c then 2 * rootCorrection r c a b else 0) := by
  by_cases hxa : x = a
  . subst x
    simp [symmetricMask,twistedMask,basePolynomial,rootCorrection,
      hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
    <;> ring
  . by_cases hxb : x = b
    . subst x
      simp [symmetricMask,twistedMask,basePolynomial,rootCorrection,
        hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
      <;> ring
    . by_cases hxc : x = c
      . subst x
        simp [symmetricMask,twistedMask,basePolynomial,rootCorrection,
          hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
        <;> ring
      . simp [symmetricMask,twistedMask,basePolynomial,hxa,hxb,hxc]
        <;> ring

theorem sum_basePolynomial_wave (hF : Not (ringChar F = 2)) (a b c : F)
    (ha : Not (a = 0)) (hb : Not (b = 0)) (hc : Not (c = 0))
    (hab : Not (a = b)) (hac : Not (a = c)) (hbc : Not (b = c)) :
    (Finset.univ.sum fun x : F => basePolynomial ((quadraticChar F) x) x a b c) =
      (Fintype.card F : Int) - quarticCharacterSum a b c := by
  have hAB := quadraticChar_sum_mul_sub hF a b hab
  have hAC := quadraticChar_sum_mul_sub hF a c hac
  have hBC := quadraticChar_sum_mul_sub hF b c hbc
  have h0A := quadraticChar_sum_mul_sub hF (0 : F) a (Ne.symm ha)
  have h0B := quadraticChar_sum_mul_sub hF (0 : F) b (Ne.symm hb)
  have h0C := quadraticChar_sum_mul_sub hF (0 : F) c (Ne.symm hc)
  simp only [sub_zero,map_mul] at hAB hAC hBC h0A h0B h0C
  have hQ :
      (Finset.univ.sum fun x : F => (quadraticChar F) x *
        (quadraticChar F) (x-a) * (quadraticChar F) (x-b) * (quadraticChar F) (x-c)) =
      quarticCharacterSum a b c := by
    unfold quarticCharacterSum
    simp only [map_mul]
  have hp (x : F) :
      basePolynomial ((quadraticChar F) x) x a b c =
      1 + (quadraticChar F) (x-a) * (quadraticChar F) (x-b) +
        (quadraticChar F) (x-a) * (quadraticChar F) (x-c) +
        (quadraticChar F) (x-b) * (quadraticChar F) (x-c) -
        (quadraticChar F) x * (quadraticChar F) (x-a) -
        (quadraticChar F) x * (quadraticChar F) (x-b) -
        (quadraticChar F) x * (quadraticChar F) (x-c) -
        (quadraticChar F) x * (quadraticChar F) (x-a) *
          (quadraticChar F) (x-b) * (quadraticChar F) (x-c) := by
    unfold basePolynomial
    ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [hAB,hAC,hBC,h0A,h0B,h0C,hQ]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  ring

theorem sum_basePolynomial_zero (hF : Not (ringChar F = 2)) (a b c : F)
    (hab : Not (a = b)) (hac : Not (a = c)) (hbc : Not (b = c)) :
    (Finset.univ.sum fun x : F => basePolynomial 0 x a b c) =
      (Fintype.card F : Int) - 3 := by
  have hAB := quadraticChar_sum_mul_sub hF a b hab
  have hAC := quadraticChar_sum_mul_sub hF a c hac
  have hBC := quadraticChar_sum_mul_sub hF b c hbc
  simp only [map_mul] at hAB hAC hBC
  simp only [basePolynomial,zero_mul,sub_zero,Finset.sum_add_distrib]
  rw [hAB,hAC,hBC]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  ring

theorem eight_twistTotal_masks (hF : Not (ringChar F = 2)) (a b c t : F)
    (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    8 * twistTotal a b c t =
      Finset.univ.sum fun x : F => symmetricMask ((quadraticChar F) x) x a b c := by
  have hp := tripleCount_scaled_character hF (1 : F) a b c one_ne_zero
  have hm := tripleCount_scaled_character hF t a b c ht
  simp only [one_mul,map_one] at hp
  rw [hchi] at hm
  simp only [neg_one_mul] at hm
  unfold twistTotal
  rw [mul_add,hp,hm,<- Finset.sum_add_distrib]
  rfl

theorem sum_symmetricMask_wave (hF : Not (ringChar F = 2)) (a b c : F)
    (ha : Not (a = 0)) (hb : Not (b = 0)) (hc : Not (c = 0))
    (hab : Not (a = b)) (hac : Not (a = c)) (hbc : Not (b = c)) :
    (Finset.univ.sum fun x : F => symmetricMask ((quadraticChar F) x) x a b c) =
      2 * ((Fintype.card F : Int) - quarticCharacterSum a b c) -
        2 * totalCorrection a b c := by
  have hp (x : F) := symmetricMask_corrected ((quadraticChar F) x) x a b c hab hac hbc
  simp_rw [hp]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    <- Finset.mul_sum,sum_basePolynomial_wave hF a b c ha hb hc hab hac hbc]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold totalCorrection
  ring

theorem four_twistTotal_eq_trace (hF : Not (ringChar F = 2)) (a b c t : F)
    (ha : Not (a = 0)) (hb : Not (b = 0)) (hc : Not (c = 0))
    (hab : Not (a = b)) (hac : Not (a = c)) (hbc : Not (b = c))
    (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    4 * twistTotal a b c t =
      (Fintype.card F : Int) + 1 +
        splitCubicPointTrace (c*(b-a)) (b*(c-a)) - totalCorrection a b c := by
  have hi := (eight_twistTotal_masks hF a b c t ht hchi).trans
    (sum_symmetricMask_wave hF a b c ha hb hc hab hac hbc)
  rw [quarticCharacterSum_eq_trace hF a b c ha hb hc] at hi
  linarith only [hi]

def reciprocalAffineEquiv (alpha beta : F) (hb : Not (beta = 0)) : Equiv F F :=
  { toFun := fun x => alpha + beta / x
    invFun := fun y => beta / (y - alpha)
    left_inv := by
      intro x
      change beta / (alpha + beta / x - alpha) = x
      have he : alpha + beta / x - alpha = beta / x := by ring
      rw [he]
      by_cases hx : x = 0
      . simp [hx]
      . field_simp [hx,hb]
    right_inv := by
      intro y
      change alpha + beta / (beta / (y - alpha)) = y
      by_cases hy : y = alpha
      . simp [hy]
      . have hd : Not (y - alpha = 0) := sub_ne_zero.mpr hy
        field_simp [hd,hb]
        <;> ring }

def shapeParameter (h k x : F) : F :=
  h / (k-h) + (h*k / (k-h)) / x

def shapeEquiv (h k : F) (hh : Not (h = 0)) (hk : Not (k = 0))
    (hhk : Not (h = k)) : Equiv F F :=
  reciprocalAffineEquiv (h / (k-h)) (h*k / (k-h))
    (div_ne_zero (mul_ne_zero hh hk) (sub_ne_zero.mpr (Ne.symm hhk)))

def admissible (h k x : F) : Prop :=
  Not (x = 0) /\ Not (x+h = 0) /\ Not (x+k = 0)

def regular (z : F) : Prop := Not (z = 0) /\ Not (z+1 = 0)

theorem shapeEquiv_apply (h k : F) (hh : Not (h = 0)) (hk : Not (k = 0))
    (hhk : Not (h = k)) (x : F) :
    shapeEquiv h k hh hk hhk x = shapeParameter h k x := rfl

theorem shapeParameter_trace (hF : Not (ringChar F = 2)) (h k x : F)
    (hhk : Not (h = k)) (hx : Not (x = 0)) :
    splitCubicPointTrace (h*(x+k)) (k*(x+h)) =
      (quadraticChar F) ((k-h)*x) *
        splitCubicPointTrace (shapeParameter h k x) (shapeParameter h k x + 1) := by
  have hd : Not (k-h = 0) := sub_ne_zero.mpr (Ne.symm hhk)
  have hdelta : Not ((k-h)*x = 0) := mul_ne_zero hd hx
  have hA : ((k-h)*x) * shapeParameter h k x = h*(x+k) := by
    unfold shapeParameter
    field_simp [hd,hx]
    <;> ring
  have hB : ((k-h)*x) * (shapeParameter h k x + 1) = k*(x+h) := by
    unfold shapeParameter
    field_simp [hd,hx]
    <;> ring
  have hs := splitCubicPointTrace_scale hF ((k-h)*x) hdelta
    (shapeParameter h k x) (shapeParameter h k x + 1)
  rw [hA,hB] at hs
  exact hs

theorem shapeParameter_trace_square (hF : Not (ringChar F = 2)) (h k x : F)
    (hhk : Not (h = k)) (hx : Not (x = 0)) :
    (splitCubicPointTrace (h*(x+k)) (k*(x+h))) ^ 2 =
      (splitCubicPointTrace (shapeParameter h k x) (shapeParameter h k x + 1)) ^ 2 := by
  rw [shapeParameter_trace hF h k x hhk hx,mul_pow,
    quadraticChar_sq_one (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hhk)) hx),one_mul]

theorem shapeParameter_admissible_iff (h k : F) (hh : Not (h = 0)) (hk : Not (k = 0))
    (hhk : Not (h = k)) (x : F) :
    admissible h k x <->
      regular (shapeParameter h k x) /\ Not (shapeParameter h k x = h/(k-h)) := by
  let e := shapeEquiv h k hh hk hhk
  have hd : Not (k-h = 0) := sub_ne_zero.mpr (Ne.symm hhk)
  have hplus (a b : F) : a+b=0 <-> a = -b := by
    constructor
    . intro he
      calc
        a = (a+b)-b := by ring
        _ = -b := by rw [he]; ring
    . intro he
      rw [he]
      ring
  have e0 : e 0 = h/(k-h) := by
    change shapeParameter h k 0 = _
    simp [shapeParameter]
  have eh : e (-h) = -1 := by
    change shapeParameter h k (-h) = _
    unfold shapeParameter
    field_simp [hd,hh]
    <;> ring
  have ek : e (-k) = 0 := by
    change shapeParameter h k (-k) = _
    unfold shapeParameter
    field_simp [hd,hk]
    <;> ring
  have h0 : e x = h/(k-h) <-> x = 0 := by
    rw [<- e0,e.injective.eq_iff]
  have hH : e x = -1 <-> x = -h := by
    rw [<- eh,e.injective.eq_iff]
  have hK : e x = 0 <-> x = -k := by
    rw [<- ek,e.injective.eq_iff]
  change (Not (x = 0) /\ Not (x+h = 0) /\ Not (x+k = 0)) <->
    (Not (e x = 0) /\ Not (e x+1 = 0)) /\ Not (e x = h/(k-h))
  simp only [hplus,h0,hH,hK]
  constructor
  . intro hs
    exact And.intro (And.intro hs.2.2 hs.2.1) hs.1
  . intro hs
    exact And.intro hs.2 (And.intro hs.1.2 hs.1.1)

set_option maxHeartbeats 1600000 in
theorem tripleCount_scaled_linear_average (hF : Not (ringChar F = 2))
    (u h k : F) (hu : Not (u = 0)) :
    8 * (Finset.univ.sum fun x : F =>
      tripleCount (u*x) (u*(x+h)) (u*(x+k))) =
      (Fintype.card F : Int) *
        (Finset.univ.sum fun y : F => twistedMask ((quadraticChar F) u) y 0 *
          twistedMask ((quadraticChar F) u) y h * twistedMask ((quadraticChar F) u) y k) := by
  have h2 := two_ne_zero_of_odd (F := F) hF
  have hfour : Not ((4 : F) = 0) := by
    rw [show (4 : F) = (2 : F)^2 by ring]
    exact pow_ne_zero 2 h2
  have h4u : Not ((4 : F)*u = 0) := mul_ne_zero hfour hu
  have hchi4 : (quadraticChar F) (4 : F) = 1 := by
    rw [show (4 : F) = (2 : F)^2 by ring,map_pow,quadraticChar_sq_one h2]
  have hchi4u : (quadraticChar F) ((4 : F)*u) = (quadraticChar F) u := by
    rw [map_mul,hchi4,one_mul]
  have hm (z y d : F) :
      characterMask (z^2 - 4*(u*((z^2/(4*u)-y)+d))) =
        twistedMask ((quadraticChar F) u) y d := by
    have he : z^2 - 4*(u*((z^2/(4*u)-y)+d)) = (4*u)*(y-d) := by
      field_simp [h4u]
      <;> ring
    unfold characterMask twistedMask
    simp only [he,map_mul,hchi4u,mul_eq_zero,h4u,false_or,sub_eq_zero]
  let g : F -> F -> Int := fun z x =>
    characterMask (z^2 - 4*(u*x)) *
      characterMask (z^2 - 4*(u*(x+h))) * characterMask (z^2 - 4*(u*(x+k)))
  have hs (z : F) :
      (Finset.univ.sum (g z)) =
        Finset.univ.sum (fun y : F => twistedMask ((quadraticChar F) u) y 0 *
          twistedMask ((quadraticChar F) u) y h * twistedMask ((quadraticChar F) u) y k) := by
    let e : Equiv F F :=
      { toFun := fun y => z^2/(4*u)-y
        invFun := fun y => z^2/(4*u)-y
        left_inv := by intro y; ring
        right_inv := by intro y; ring }
    calc
      _ = Finset.univ.sum (fun y : F => g z (e y)) := (Equiv.sum_comp e (g z)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y _
        have hm0 :
            characterMask (z^2 - 4*(u*(z^2/(4*u)-y))) =
              twistedMask ((quadraticChar F) u) y 0 := by
          simpa only [add_zero] using hm z y (0 : F)
        change characterMask (z^2 - 4*(u*(z^2/(4*u)-y))) *
          characterMask (z^2 - 4*(u*((z^2/(4*u)-y)+h))) *
            characterMask (z^2 - 4*(u*((z^2/(4*u)-y)+k))) = _
        rw [hm0,hm,hm]
  calc
    _ = Finset.univ.sum (fun z : F => Finset.univ.sum (g z)) := by
      rw [Finset.mul_sum]
      simp_rw [tripleCount_eight_masks hF]
      exact Finset.sum_comm
    _ = Finset.univ.sum (fun _z : F =>
        Finset.univ.sum fun y : F => twistedMask ((quadraticChar F) u) y 0 *
          twistedMask ((quadraticChar F) u) y h * twistedMask ((quadraticChar F) u) y k) := by
      simp_rw [hs]
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

end FiniteField.QuadraticTripleTwist

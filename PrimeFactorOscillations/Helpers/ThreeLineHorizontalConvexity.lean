/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.ThreeLineWindowProfile

/-! # Exact nonlinear horizontal charging for the signed three-line kernel -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def threeLineHorizontalProfile (x : Real) : Real :=
  threeLineWeight1 * (threeLineRadius1 / (threeLineRadius1 ^ 2 - x)) +
    threeLineWeight2 * (threeLineRadius2 / (threeLineRadius2 ^ 2 - x)) +
    threeLineWeight3 * (threeLineRadius3 / (threeLineRadius3 ^ 2 - x))

def threeLineHorizontalSlope (z : Real) : Real :=
  threeLineWeight1 * (threeLineRadius1 / (threeLineRadius1 ^ 2 - z) ^ 2) +
    threeLineWeight2 * (threeLineRadius2 / (threeLineRadius2 ^ 2 - z) ^ 2) +
    threeLineWeight3 * (threeLineRadius3 / (threeLineRadius3 ^ 2 - z) ^ 2)

def threeLineHorizontalFactor (a x z : Real) : Real :=
  (a ^ 2 - x) * (a ^ 2 - z) ^ 2

def threeLineHorizontalRemainder (x z : Real) : Real :=
  threeLineWeight1 * (threeLineRadius1 / threeLineHorizontalFactor threeLineRadius1 x z) +
    threeLineWeight2 * (threeLineRadius2 / threeLineHorizontalFactor threeLineRadius2 x z) +
    threeLineWeight3 * (threeLineRadius3 / threeLineHorizontalFactor threeLineRadius3 x z)

def threeLineHorizontalRemainderDen (x z : Real) : Real :=
  threeLineHorizontalFactor threeLineRadius1 x z *
    threeLineHorizontalFactor threeLineRadius2 x z *
    threeLineHorizontalFactor threeLineRadius3 x z

def threeLineHorizontalRemainderNum (x z : Real) : Real :=
  threeLineWeight1 * threeLineRadius1 * threeLineHorizontalFactor threeLineRadius2 x z *
    threeLineHorizontalFactor threeLineRadius3 x z +
  threeLineWeight2 * threeLineRadius2 * threeLineHorizontalFactor threeLineRadius1 x z *
    threeLineHorizontalFactor threeLineRadius3 x z +
  threeLineWeight3 * threeLineRadius3 * threeLineHorizontalFactor threeLineRadius1 x z *
    threeLineHorizontalFactor threeLineRadius2 x z

def threeLineHorizontalVarianceCoefficient : Real :=
  8724025982765199771011463287 / 269181019586315111382051840

def threeLineHorizontalTangentCertificate (X Z : Real) : Real :=
  (((((162897032882888075284714738284909352885779534075949099791100674048 : Real) * X ^ (0 : Nat) * (1 - X) ^ (3 : Nat) * Z ^ (1 : Nat) * (1 - Z) ^ (5 : Nat) +
    ((649449367358944008811135850910912487745725911728896280417654538240 : Real) * X ^ (0 : Nat) * (1 - X) ^ (3 : Nat) * Z ^ (2 : Nat) * (1 - Z) ^ (4 : Nat) +
    (1032669415372013885208710733909806647057740507010148874319293972480 : Real) * X ^ (0 : Nat) * (1 - X) ^ (3 : Nat) * Z ^ (3 : Nat) * (1 - Z) ^ (3 : Nat))) +
    ((818479628767625069605332642235468502613259183181381338151185428480 : Real) * X ^ (0 : Nat) * (1 - X) ^ (3 : Nat) * Z ^ (4 : Nat) * (1 - Z) ^ (2 : Nat) +
    ((323282804010646837197042591945168714158229985637111876059603722240 : Real) * X ^ (0 : Nat) * (1 - X) ^ (3 : Nat) * Z ^ (5 : Nat) * (1 - Z) ^ (1 : Nat) +
    (50887375665861953576851511269639925474434771031682231601158402048 : Real) * X ^ (0 : Nat) * (1 - X) ^ (3 : Nat) * Z ^ (6 : Nat) * (1 - Z) ^ (0 : Nat)))) +
    (((81448516441444037642357369142454676442889767037974549895550337024 : Real) * X ^ (1 : Nat) * (1 - X) ^ (2 : Nat) * Z ^ (0 : Nat) * (1 - Z) ^ (6 : Nat) +
    ((764524572762276632871122894239865562591444638925384055482312818688 : Real) * X ^ (1 : Nat) * (1 - X) ^ (2 : Nat) * Z ^ (1 : Nat) * (1 - Z) ^ (5 : Nat) +
    (2276173129435572509992135467893955361011042064170610376664471982080 : Real) * X ^ (1 : Nat) * (1 - X) ^ (2 : Nat) * Z ^ (2 : Nat) * (1 - Z) ^ (4 : Nat))) +
    (((3218105819559223572597910396411193499716846973658214246052806161920 : Real) * X ^ (1 : Nat) * (1 - X) ^ (2 : Nat) * Z ^ (3 : Nat) * (1 - Z) ^ (3 : Nat) +
    (2396612666835281344291479330573711476990761490263279071969962974800 : Real) * X ^ (1 : Nat) * (1 - X) ^ (2 : Nat) * Z ^ (4 : Nat) * (1 - Z) ^ (2 : Nat)) +
    ((911761715977791673234341959990826128785976851712208842994883320864 : Real) * X ^ (1 : Nat) * (1 - X) ^ (2 : Nat) * Z ^ (5 : Nat) * (1 - Z) ^ (1 : Nat) +
    (140090289381854495375690443483191939559947027011565216312517007568 : Real) * X ^ (1 : Nat) * (1 - X) ^ (2 : Nat) * Z ^ (6 : Nat) * (1 - Z) ^ (0 : Nat))))) +
    ((((133593540488902846187787201895489853225001796133102126338249064448 : Real) * X ^ (2 : Nat) * (1 - X) ^ (1 : Nat) * Z ^ (0 : Nat) * (1 - Z) ^ (6 : Nat) +
    ((924206325538768787694112156984600758535919328059327469913896517632 : Real) * X ^ (2 : Nat) * (1 - X) ^ (1 : Nat) * Z ^ (1 : Nat) * (1 - Z) ^ (5 : Nat) +
    (2418146243451763449424702393428930857689037055828855467372063005440 : Real) * X ^ (2 : Nat) * (1 - X) ^ (1 : Nat) * Z ^ (2 : Nat) * (1 - Z) ^ (4 : Nat))) +
    (((3186227456545445503809031211798903456425191815730862689136962314400 : Real) * X ^ (2 : Nat) * (1 - X) ^ (1 : Nat) * Z ^ (3 : Nat) * (1 - Z) ^ (3 : Nat) +
    (2272109304745002224266642496520292568916104721825495912630945667035 : Real) * X ^ (2 : Nat) * (1 - X) ^ (1 : Nat) * Z ^ (4 : Nat) * (1 - Z) ^ (2 : Nat)) +
    ((840027607105622356683968334283241758546992011112736507137158836158 : Real) * X ^ (2 : Nat) * (1 - X) ^ (1 : Nat) * Z ^ (5 : Nat) * (1 - Z) ^ (1 : Nat) +
    (126567896707499144913908861729990991379108675655992874202228681267 : Real) * X ^ (2 : Nat) * (1 - X) ^ (1 : Nat) * Z ^ (6 : Nat) * (1 - Z) ^ (0 : Nat)))) +
    (((54231544916622548757299288462602944260910589475410702202698727424 : Real) * X ^ (3 : Nat) * (1 - X) ^ (0 : Nat) * Z ^ (0 : Nat) * (1 - Z) ^ (6 : Nat) +
    ((331146369545239390433967235699041158958361918945205732782684372992 : Real) * X ^ (3 : Nat) * (1 - X) ^ (0 : Nat) * Z ^ (1 : Nat) * (1 - Z) ^ (5 : Nat) +
    (805852974294587842689785102268590767086870273245313708775245561600 : Real) * X ^ (3 : Nat) * (1 - X) ^ (0 : Nat) * Z ^ (2 : Nat) * (1 - Z) ^ (4 : Nat))) +
    (((1013536467309515580388044982530105979734846393775573306197200124960 : Real) * X ^ (3 : Nat) * (1 - X) ^ (0 : Nat) * Z ^ (3 : Nat) * (1 - Z) ^ (3 : Nat) +
    (700194382316520169093365054108004758393390059579498686193613433215 : Real) * X ^ (3 : Nat) * (1 - X) ^ (0 : Nat) * Z ^ (4 : Nat) * (1 - Z) ^ (2 : Nat)) +
    ((253135793414998289827817723459981982758217351311985748404457362534 : Real) * X ^ (3 : Nat) * (1 - X) ^ (0 : Nat) * Z ^ (5 : Nat) * (1 - Z) ^ (1 : Nat) +
    (37530468824846874813723019000311986185373140352803836208877888247 : Real) * X ^ (3 : Nat) * (1 - X) ^ (0 : Nat) * Z ^ (6 : Nat) * (1 - Z) ^ (0 : Nat))))))

theorem threeLineHorizontalVarianceCoefficient_pos :
    0 < threeLineHorizontalVarianceCoefficient := by
  norm_num [threeLineHorizontalVarianceCoefficient]

theorem threeLineHorizontalSlope_zero :
    threeLineHorizontalSlope 0 = (9127021347318871247 / 1372823364650976000 : Real) := by
  norm_num [threeLineHorizontalSlope, threeLineWeight1, threeLineWeight2, threeLineWeight3,
    threeLineRadius1, threeLineRadius2, threeLineRadius3]

theorem threeLineHorizontalSlope_zero_gt :
    (13 / 2 : Real) < threeLineHorizontalSlope 0 := by
  rw [threeLineHorizontalSlope_zero]
  norm_num

theorem threeLineHorizontalProfile_zero :
    threeLineHorizontalProfile 0 = threeLineCharge := by
  norm_num [threeLineHorizontalProfile, threeLineCharge,
    threeLineWeight1, threeLineWeight2, threeLineWeight3,
    threeLineRadius1, threeLineRadius2, threeLineRadius3]

theorem threeLineHorizontal_denominators_pos (x : Real) (hx : x <= 9 / 64) :
    And (0 < threeLineRadius1 ^ 2 - x)
      (And (0 < threeLineRadius2 ^ 2 - x) (0 < threeLineRadius3 ^ 2 - x)) := by
  norm_num [threeLineRadius1, threeLineRadius2, threeLineRadius3]
  constructor
  case left => linarith
  case right => constructor <;> linarith

theorem threeLineHorizontalRemainderDen_pos (x z : Real)
    (hx : x <= 9 / 64) (hz : z <= 9 / 64) :
    0 < threeLineHorizontalRemainderDen x z := by
  have hxD := threeLineHorizontal_denominators_pos x hx
  have hzD := threeLineHorizontal_denominators_pos z hz
  have h1x := hxD.1
  have h2x := hxD.2.1
  have h3x := hxD.2.2
  have h1z := hzD.1
  have h2z := hzD.2.1
  have h3z := hzD.2.2
  unfold threeLineHorizontalRemainderDen threeLineHorizontalFactor
  positivity

theorem threeLineHorizontalTangentCertificate_identity (x z : Real) :
    (743392281267463253945801192243200000000000000000000000000000000000 : Real) *
      (threeLineHorizontalRemainderNum x z - threeLineHorizontalVarianceCoefficient *
        threeLineHorizontalRemainderDen x z) =
      threeLineHorizontalTangentCertificate (64 * x / 9) (64 * z / 9) := by
  unfold threeLineHorizontalRemainderNum threeLineHorizontalRemainderDen
    threeLineHorizontalFactor threeLineHorizontalVarianceCoefficient
    threeLineHorizontalTangentCertificate threeLineWeight1 threeLineWeight2 threeLineWeight3
    threeLineRadius1 threeLineRadius2 threeLineRadius3
  ring

theorem threeLineHorizontalTangentCertificate_nonneg (X Z : Real)
    (hX : And (0 <= X) (X <= 1)) (hZ : And (0 <= Z) (Z <= 1)) :
    0 <= threeLineHorizontalTangentCertificate X Z := by
  have hX0 := hX.1
  have hZ0 := hZ.1
  have hX1 : 0 <= 1 - X := by linarith [hX.2]
  have hZ1 : 0 <= 1 - Z := by linarith [hZ.2]
  unfold threeLineHorizontalTangentCertificate
  positivity

theorem threeLineHorizontalRemainder_mul_den (x z : Real)
    (hx : x <= 9 / 64) (hz : z <= 9 / 64) :
    threeLineHorizontalRemainder x z * threeLineHorizontalRemainderDen x z =
      threeLineHorizontalRemainderNum x z := by
  have hxD := threeLineHorizontal_denominators_pos x hx
  have hzD := threeLineHorizontal_denominators_pos z hz
  unfold threeLineHorizontalRemainder threeLineHorizontalRemainderDen
    threeLineHorizontalRemainderNum threeLineHorizontalFactor
  field_simp [ne_of_gt hxD.1, ne_of_gt hxD.2.1, ne_of_gt hxD.2.2,
    ne_of_gt hzD.1, ne_of_gt hzD.2.1, ne_of_gt hzD.2.2]
  <;> ring

theorem threeLineHorizontalRemainder_ge (x z : Real)
    (hx : And (0 <= x) (x <= 9 / 64)) (hz : And (0 <= z) (z <= 9 / 64)) :
    threeLineHorizontalVarianceCoefficient <= threeLineHorizontalRemainder x z := by
  have hX : And (0 <= 64 * x / 9) (64 * x / 9 <= 1) := by constructor <;> linarith [hx.1, hx.2]
  have hZ : And (0 <= 64 * z / 9) (64 * z / 9 <= 1) := by constructor <;> linarith [hz.1, hz.2]
  have hc := threeLineHorizontalTangentCertificate_nonneg _ _ hX hZ
  rw [<- threeLineHorizontalTangentCertificate_identity x z] at hc
  have hd := threeLineHorizontalRemainderDen_pos x z hx.2 hz.2
  have hm := threeLineHorizontalRemainder_mul_den x z hx.2 hz.2
  nlinarith

theorem threeLineHorizontalRemainder_zero :
    threeLineHorizontalRemainder 0 0 = threeLineHorizontalVarianceCoefficient := by
  norm_num [threeLineHorizontalRemainder, threeLineHorizontalFactor,
    threeLineHorizontalVarianceCoefficient, threeLineWeight1, threeLineWeight2, threeLineWeight3,
    threeLineRadius1, threeLineRadius2, threeLineRadius3]

theorem threeLineHorizontalRemainder_optimal_floor (b : Real) :
    (forall x z : Real, And (0 <= x) (x <= 9 / 64) ->
      And (0 <= z) (z <= 9 / 64) -> b <= threeLineHorizontalRemainder x z) <->
      b <= threeLineHorizontalVarianceCoefficient := by
  constructor
  case mp =>
    intro h
    have h0 := h 0 0 (by norm_num) (by norm_num)
    rw [threeLineHorizontalRemainder_zero] at h0
    exact h0
  case mpr =>
    intro h x z hx hz
    exact h.trans (threeLineHorizontalRemainder_ge x z hx hz)

theorem threeLineHorizontal_one_tangent (a x z : Real)
    (hx : Not (a ^ 2 - x = 0)) (hz : Not (a ^ 2 - z = 0)) :
    a / (a ^ 2 - x) - a / (a ^ 2 - z) -
      (a / (a ^ 2 - z) ^ 2) * (x - z) =
      (a / ((a ^ 2 - x) * (a ^ 2 - z) ^ 2)) * (x - z) ^ 2 := by
  field_simp
  <;> ring

theorem threeLineHorizontal_tangent_identity (x z : Real)
    (hx : x <= 9 / 64) (hz : z <= 9 / 64) :
    threeLineHorizontalProfile x - threeLineHorizontalProfile z -
      threeLineHorizontalSlope z * (x - z) =
      threeLineHorizontalRemainder x z * (x - z) ^ 2 := by
  have hxD := threeLineHorizontal_denominators_pos x hx
  have hzD := threeLineHorizontal_denominators_pos z hz
  have h1 := congrArg (fun q : Real => threeLineWeight1 * q)
    (threeLineHorizontal_one_tangent threeLineRadius1 x z (ne_of_gt hxD.1) (ne_of_gt hzD.1))
  have h2 := congrArg (fun q : Real => threeLineWeight2 * q)
    (threeLineHorizontal_one_tangent threeLineRadius2 x z (ne_of_gt hxD.2.1) (ne_of_gt hzD.2.1))
  have h3 := congrArg (fun q : Real => threeLineWeight3 * q)
    (threeLineHorizontal_one_tangent threeLineRadius3 x z (ne_of_gt hxD.2.2) (ne_of_gt hzD.2.2))
  unfold threeLineHorizontalProfile threeLineHorizontalSlope threeLineHorizontalRemainder
    threeLineHorizontalFactor
  nlinarith only [h1, h2, h3]

theorem threeLineHorizontal_strong_tangent (x z : Real)
    (hx : And (0 <= x) (x <= 9 / 64)) (hz : And (0 <= z) (z <= 9 / 64)) :
    threeLineHorizontalProfile z + threeLineHorizontalSlope z * (x - z) +
      threeLineHorizontalVarianceCoefficient * (x - z) ^ 2 <= threeLineHorizontalProfile x := by
  have hi := threeLineHorizontal_tangent_identity x z hx.2 hz.2
  have hg := threeLineHorizontalRemainder_ge x z hx hz
  have hm := mul_nonneg (sub_nonneg.mpr hg) (sq_nonneg (x - z))
  nlinarith

theorem threeLineHorizontal_quartic_charge (x : Real)
    (hx : And (0 <= x) (x <= 9 / 64)) :
    threeLineCharge + threeLineHorizontalSlope 0 * x +
      threeLineHorizontalVarianceCoefficient * x ^ 2 <= threeLineHorizontalProfile x := by
  have h := threeLineHorizontal_strong_tangent x 0 hx (by norm_num)
  simpa only [threeLineHorizontalProfile_zero, sub_zero] using h

theorem threeLineKernel_horizontal_profile (u : Real) (hu : abs u <= 3 / 8) :
    threeLineKernel u 0 = threeLineHorizontalProfile (u ^ 2) := by
  have hm (r : Real) (hr : abs u < r) :
      Complex.pairedResolventMean r u 0 = r / (r ^ 2 - u ^ 2) := by
    have hMinus : 0 < r - u := by linarith [le_abs_self u]
    have hPlus : 0 < r + u := by linarith [neg_abs_le u]
    have hSquare : 0 < r ^ 2 - u ^ 2 := by nlinarith [mul_pos hMinus hPlus]
    unfold Complex.pairedResolventMean
    norm_num only [show (0 : Real) ^ 2 = 0 by norm_num, add_zero]
    field_simp [ne_of_gt hMinus, ne_of_gt hPlus, ne_of_gt hSquare]
    <;> ring
  have h1 : abs u < threeLineRadius1 := by norm_num [threeLineRadius1]; linarith
  have h2 : abs u < threeLineRadius2 := by norm_num [threeLineRadius2]; linarith
  have h3 : abs u < threeLineRadius3 := by norm_num [threeLineRadius3]; linarith
  unfold threeLineKernel threeLineHorizontalProfile
  rw [hm _ h1, hm _ h2, hm _ h3]

theorem threeLineHorizontal_mean_bounds {Iota : Type*} (S : Finset Iota)
    (x : Iota -> Real) (z : Real)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 9 / 64))
    (hN : 0 < (S.card : Real))
    (hCenter : Finset.sum S x = (S.card : Real) * z) :
    And (0 <= z) (z <= 9 / 64) := by
  classical
  have hLower : 0 <= Finset.sum S x := Finset.sum_nonneg (fun i hi => (hx i hi).1)
  have hUpper : Finset.sum S x <= (S.card : Real) * (9 / 64 : Real) := by
    calc
      _ <= Finset.sum S (fun _ => (9 / 64 : Real)) :=
        Finset.sum_le_sum (fun i hi => (hx i hi).2)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  constructor <;> nlinarith

theorem threeLineHorizontal_centered_charge {Iota : Type*} (S : Finset Iota)
    (x : Iota -> Real) (z : Real)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 9 / 64))
    (hz : And (0 <= z) (z <= 9 / 64))
    (hCenter : Finset.sum S x = (S.card : Real) * z) :
    (S.card : Real) * threeLineHorizontalProfile z + threeLineHorizontalVarianceCoefficient *
      Finset.sum S (fun i => (x i - z) ^ 2) <=
      Finset.sum S (fun i => threeLineHorizontalProfile (x i)) := by
  classical
  have hDeviation : Finset.sum S (fun i => x i - z) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hCenter]
    ring
  have hLocal : Finset.sum S (fun i => threeLineHorizontalProfile z +
      threeLineHorizontalSlope z * (x i - z) +
      threeLineHorizontalVarianceCoefficient * (x i - z) ^ 2) <=
      Finset.sum S (fun i => threeLineHorizontalProfile (x i)) := by
    exact Finset.sum_le_sum (fun i hi => threeLineHorizontal_strong_tangent (x i) z (hx i hi) hz)
  have hSum : Finset.sum S (fun i => threeLineHorizontalProfile z +
      threeLineHorizontalSlope z * (x i - z) +
      threeLineHorizontalVarianceCoefficient * (x i - z) ^ 2) =
      (S.card : Real) * threeLineHorizontalProfile z + threeLineHorizontalVarianceCoefficient *
        Finset.sum S (fun i => (x i - z) ^ 2) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      <- Finset.mul_sum, hDeviation, mul_zero, add_zero]
  rw [hSum] at hLocal
  exact hLocal

theorem threeLineHorizontal_jensen_eq_iff {Iota : Type*} (S : Finset Iota)
    (x : Iota -> Real) (z : Real)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 9 / 64))
    (hz : And (0 <= z) (z <= 9 / 64))
    (hCenter : Finset.sum S x = (S.card : Real) * z) :
    Finset.sum S (fun i => threeLineHorizontalProfile (x i)) =
      (S.card : Real) * threeLineHorizontalProfile z <->
      (forall i, Membership.mem S i -> x i = z) := by
  classical
  constructor
  case mp =>
    intro hEqual
    have hStrong := threeLineHorizontal_centered_charge S x z hx hz hCenter
    have hVariance : 0 <= Finset.sum S (fun i => (x i - z) ^ 2) :=
      Finset.sum_nonneg (fun i _ => sq_nonneg (x i - z))
    have hZero : Finset.sum S (fun i => (x i - z) ^ 2) = 0 := by
      have hSigma := threeLineHorizontalVarianceCoefficient_pos
      nlinarith
    intro i hi
    have hOne : (x i - z) ^ 2 <= Finset.sum S (fun j => (x j - z) ^ 2) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j - z)) hi
    have hSq : (x i - z) ^ 2 = 0 := le_antisymm (hOne.trans (le_of_eq hZero)) (sq_nonneg _)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hSq)
  case mpr =>
    intro h
    calc
      _ = Finset.sum S (fun _ => threeLineHorizontalProfile z) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [h i hi]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end PrimeFactorOscillations

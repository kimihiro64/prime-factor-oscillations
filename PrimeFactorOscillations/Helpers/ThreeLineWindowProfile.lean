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
import PrimeFactorOscillations.Helpers.ThreeLineClusterCertificate

/-! # The exact signed three-line window profile and its minimizers -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def threeLineAxisDen (y : Real) : Real :=
  (threeLineRadius1 ^ 2 + y) * (threeLineRadius2 ^ 2 + y) * (threeLineRadius3 ^ 2 + y)

def threeLineAxisNum (y : Real) : Real :=
  (2206764786659391 / 12500000000000000 : Real) + (15528997371327 / 1000000000000000 : Real) * y + (1001493 / 10000000000 : Real) * y ^ 2

def threeLineAxisRational (y : Real) : Real :=
  threeLineWeight1 * (threeLineRadius1 / (threeLineRadius1 ^ 2 + y)) +
    threeLineWeight2 * (threeLineRadius2 / (threeLineRadius2 ^ 2 + y)) +
    threeLineWeight3 * (threeLineRadius3 / (threeLineRadius3 ^ 2 + y))

def threeLineAxisDifference (y z : Real) : Real :=
  ((((25880280540752929785242049 / 125000000000000000000000000 : Real) * y ^ (0 : Nat) * z ^ (0 : Nat) +
    (481074701591677041743391 / 1250000000000000000000000 : Real) * y ^ (1 : Nat) * z ^ (0 : Nat)) +
    ((481074701591677041743391 / 1250000000000000000000000 : Real) * y ^ (0 : Nat) * z ^ (1 : Nat) +
    (2206764786659391 / 12500000000000000 : Real) * y ^ (2 : Nat) * z ^ (0 : Nat))) +
    (((2206764786659391 / 12500000000000000 : Real) * y ^ (0 : Nat) * z ^ (2 : Nat) +
    (21027694354319346492327 / 100000000000000000000000 : Real) * y ^ (1 : Nat) * z ^ (1 : Nat)) +
    ((15528997371327 / 1000000000000000 : Real) * y ^ (2 : Nat) * z ^ (1 : Nat) +
    ((15528997371327 / 1000000000000000 : Real) * y ^ (1 : Nat) * z ^ (2 : Nat) +
    (1001493 / 10000000000 : Real) * y ^ (2 : Nat) * z ^ (2 : Nat)))))

def threeLineExactWindowCharge (h : Real) : Real := threeLineKernel 0 h

theorem threeLineAxisDen_pos (y : Real) (hy : 0 <= y) : 0 < threeLineAxisDen y := by
  unfold threeLineAxisDen
  exact mul_pos (mul_pos
    (add_pos_of_pos_of_nonneg (by norm_num [threeLineRadius1]) hy)
    (add_pos_of_pos_of_nonneg (by norm_num [threeLineRadius2]) hy))
    (add_pos_of_pos_of_nonneg (by norm_num [threeLineRadius3]) hy)

theorem threeLineAxisRational_mul_den (y : Real) (hy : 0 <= y) :
    threeLineAxisRational y * threeLineAxisDen y = threeLineAxisNum y := by
  have h1 : 0 < threeLineRadius1 ^ 2 + y :=
    add_pos_of_pos_of_nonneg (by norm_num [threeLineRadius1]) hy
  have h2 : 0 < threeLineRadius2 ^ 2 + y :=
    add_pos_of_pos_of_nonneg (by norm_num [threeLineRadius2]) hy
  have h3 : 0 < threeLineRadius3 ^ 2 + y :=
    add_pos_of_pos_of_nonneg (by norm_num [threeLineRadius3]) hy
  unfold threeLineAxisRational threeLineAxisDen threeLineAxisNum
  field_simp [h1.ne', h2.ne', h3.ne']
  norm_num [threeLineRadius1, threeLineRadius2, threeLineRadius3,
    threeLineWeight1, threeLineWeight2, threeLineWeight3] <;> ring

theorem threeLineKernel_axis_formula (v : Real) :
    threeLineKernel 0 v = threeLineAxisRational (v ^ 2) := by
  have hm (r : Real) : Complex.pairedResolventMean r 0 v = r / (r ^ 2 + v ^ 2) := by
    unfold Complex.pairedResolventMean
    simp only [sub_zero, add_zero]
    ring
  unfold threeLineKernel threeLineAxisRational
  simp only [hm]

theorem threeLineAxisDifference_pos (y z : Real) (hy : 0 <= y) (hz : 0 <= z) :
    0 < threeLineAxisDifference y z := by
  unfold threeLineAxisDifference
  positivity

theorem threeLineAxis_difference_identity (y z : Real) (hy : 0 <= y) (hz : 0 <= z) :
    (threeLineAxisRational y - threeLineAxisRational z) *
      (threeLineAxisDen y * threeLineAxisDen z) = (z - y) * threeLineAxisDifference y z := by
  have h1 := threeLineAxisRational_mul_den y hy
  have h2 := threeLineAxisRational_mul_den z hz
  calc
    _ = (threeLineAxisRational y * threeLineAxisDen y) * threeLineAxisDen z -
        (threeLineAxisRational z * threeLineAxisDen z) * threeLineAxisDen y := by ring
    _ = threeLineAxisNum y * threeLineAxisDen z - threeLineAxisNum z * threeLineAxisDen y := by
      rw [h1, h2]
    _ = _ := by
      unfold threeLineAxisNum threeLineAxisDen threeLineAxisDifference
        threeLineRadius1 threeLineRadius2 threeLineRadius3
      ring

theorem threeLineAxisRational_strictAnti (y z : Real) (hy : 0 <= y) (hz : 0 <= z)
    (hyz : y < z) : threeLineAxisRational z < threeLineAxisRational y := by
  have hd := mul_pos (threeLineAxisDen_pos y hy) (threeLineAxisDen_pos z hz)
  have hp : 0 < (threeLineAxisRational y - threeLineAxisRational z) *
      (threeLineAxisDen y * threeLineAxisDen z) := by
    rw [threeLineAxis_difference_identity y z hy hz]
    exact mul_pos (sub_pos.mpr hyz) (threeLineAxisDifference_pos y z hy hz)
  have hs : 0 * (threeLineAxisDen y * threeLineAxisDen z) <
      (threeLineAxisRational y - threeLineAxisRational z) *
        (threeLineAxisDen y * threeLineAxisDen z) := by simpa using hp
  exact sub_pos.mp ((mul_lt_mul_iff_of_pos_right hd).mp hs)

theorem threeLineAxisRational_anti (y z : Real) (hy : 0 <= y) (hz : 0 <= z)
    (hyz : y <= z) : threeLineAxisRational z <= threeLineAxisRational y := by
  by_cases heq : y = z
  case pos => rw [heq]
  case neg =>
    have hlt : y < z := by
      apply lt_of_le_of_ne hyz
      intro hh
      apply heq
      linarith only [hh]
    exact (threeLineAxisRational_strictAnti y z hy hz hlt).le

theorem threeLineExactWindowCharge_pos (h : Real) : 0 < threeLineExactWindowCharge h := by
  exact threeLineKernel_pos 0 h (by norm_num)

theorem threeLineExactWindowCharge_eq_axis (h : Real) :
    threeLineExactWindowCharge h = threeLineAxisRational (h ^ 2) :=
  threeLineKernel_axis_formula h

def threeLineWindowTransverse (x y : Real) : Real :=
  threeLineAxisDen y * (
    threeLineWeight1 * threeLineRadius1 * (threeLineRadius1 ^ 2 - x - 3 * y) *
      (threeLinePolynomialDen threeLineRadius2 x y * (threeLineRadius2 ^ 2 + y)) *
      (threeLinePolynomialDen threeLineRadius3 x y * (threeLineRadius3 ^ 2 + y)) +
    threeLineWeight2 * threeLineRadius2 * (threeLineRadius2 ^ 2 - x - 3 * y) *
      (threeLinePolynomialDen threeLineRadius1 x y * (threeLineRadius1 ^ 2 + y)) *
      (threeLinePolynomialDen threeLineRadius3 x y * (threeLineRadius3 ^ 2 + y)) +
    threeLineWeight3 * threeLineRadius3 * (threeLineRadius3 ^ 2 - x - 3 * y) *
      (threeLinePolynomialDen threeLineRadius1 x y * (threeLineRadius1 ^ 2 + y)) *
      (threeLinePolynomialDen threeLineRadius2 x y * (threeLineRadius2 ^ 2 + y)))

def threeLineWindowTransverseCertificate (X Y : Real) : Real :=
  (40321255493226389739445755074329909385682279296615625 : Real) +
  (((((((3340120416617779389106453620899766047723225080729746231 : Real) * X ^ (0 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat) +
    (33225182971960448007149685781267054021991075214276382758 : Real) * X ^ (0 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat)) +
    ((148470553623391891947653413546438677591298724003648956587 : Real) * X ^ (0 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat) +
    (392432324304838218127917294667988797066631467283798802888 : Real) * X ^ (0 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat))) +
    (((679337919202264034764170666003827963058760066859040836382 : Real) * X ^ (0 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat) +
    (804636881914307720462572591571046036208002903306869227044 : Real) * X ^ (0 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat)) +
    ((660255982985870777173269916694046862694942803892651256990 : Real) * X ^ (0 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat) +
    (370532229406013697117182311826979136499787484407074349000 : Real) * X ^ (0 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat)))) +
    ((((136065298601189003212945431434608634026653711611110504875 : Real) * X ^ (0 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat) +
    (29513662841666879888722567519714165889236165112911923750 : Real) * X ^ (0 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat)) +
    ((2870406609453477111160584812007246766270563877749384375 : Real) * X ^ (0 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat) +
    (12615942037811474476295501940878756793500460708929447955 : Real) * X ^ (1 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat))) +
    (((124920064244932509863898478222398522177217768294491852990 : Real) * X ^ (1 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat) +
    (555344136739792059618724344039526570263070827562473032535 : Real) * X ^ (1 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat)) +
    ((1459349096719821559928247139833698474653111689512255710440 : Real) * X ^ (1 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat) +
    (2509730998997815531677906991365242560712381261324862053910 : Real) * X ^ (1 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat))))) +
    (((((2950615342357070058827125446686712273701988856374066064020 : Real) * X ^ (1 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat) +
    (2400820794369287204811023418892178677671063612390871548150 : Real) * X ^ (1 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat)) +
    ((1334430653911429307060701141867407570413640380646864690600 : Real) * X ^ (1 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat) +
    (484655757639410657851216092737571399430677504291101172375 : Real) * X ^ (1 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat))) +
    (((103800272276532219677380164997942217315321088636798558750 : Real) * X ^ (1 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat) +
    (9947799725668726895996096356930895890586117186239621875 : Real) * X ^ (1 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat)) +
    ((18782163585213159424464005615587106908631106702924009510 : Real) * X ^ (2 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat) +
    (184808670870943277722953065820461910875943152625516544380 : Real) * X ^ (2 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat)))) +
    ((((815711215457541715899370015961765253594226525237491444270 : Real) * X ^ (2 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat) +
    (2126057640446595075839115899910075723737926643679584012880 : Real) * X ^ (2 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat)) +
    ((3622135083129318427547959668287394935927310134112581276820 : Real) * X ^ (2 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat) +
    (4212639665139258189498304326469094527148039803981259015640 : Real) * X ^ (2 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat))) +
    (((3385042563693431206718471043917519311759550912673947957700 : Real) * X ^ (2 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat) +
    (1854217192726817815146724846593509660321035561502479052400 : Real) * X ^ (2 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat)) +
    ((661977807057860796760764301059154302370967056336139415750 : Real) * X ^ (2 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat) +
    ((138916302336421676609380757982344508928761253172260747500 : Real) * X ^ (2 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat) +
    (12990638596670728413070009382405025451020679898015268750 : Real) * X ^ (2 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat))))))) +
    ((((((13728917942886597365544533541763327562186804307548803110 : Real) * X ^ (3 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat) +
    (133890089253495186616768325641726655267096565662934342780 : Real) * X ^ (3 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat)) +
    ((584908277214126958413256531649552596146636309583414828470 : Real) * X ^ (3 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat) +
    (1506323179319569149514264453764062732732495920263234086130 : Real) * X ^ (3 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat))) +
    (((2530497310394270425104329556100106102165180745693495339570 : Real) * X ^ (3 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat) +
    (2894595561813168347459186907190491698205882681874302839490 : Real) * X ^ (3 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat)) +
    ((2280328476812153774939099434752216773650030512637607747850 : Real) * X ^ (3 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat) +
    (1219559400362175182194775107153387186428990455600798347350 : Real) * X ^ (3 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat)))) +
    ((((422800211841048092271949402419678905184996067775587668000 : Real) * X ^ (3 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat) +
    (85524521767406258371716153705107504155351871022428096250 : Real) * X ^ (3 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat)) +
    ((7629558311328276010151636439797677080787054426043325000 : Real) * X ^ (3 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat) +
    (4902361814852411756513685026194223162498805938394638355 : Real) * X ^ (4 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat))) +
    (((47190426451370172945767319162237816249007033055904550590 : Real) * X ^ (4 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat) +
    (202990725255459052406953058407575733130423234857877671335 : Real) * X ^ (4 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat)) +
    ((513173516251091012327730383184171103775462938051338710940 : Real) * X ^ (4 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat) +
    (842960411734541677461375983582211258847034234623803382410 : Real) * X ^ (4 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat))))) +
    (((((938000124962618576842943120087931275510721678833153002920 : Real) * X ^ (4 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat) +
    (713814488736718174450699786547458730607705549775476530250 : Real) * X ^ (4 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat)) +
    ((365160081246353726177795152239287373399170340625152804900 : Real) * X ^ (4 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat) +
    (119340989627081813141042490882492457196958696159421753875 : Real) * X ^ (4 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat))) +
    (((22242504428359616235404958992427522153355657506802316250 : Real) * X ^ (4 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat) +
    (1757676171139975286866002944292490643097126717377409375 : Real) * X ^ (4 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat)) +
    ((678887578368676051337380227914562388165872705570143031 : Real) * X ^ (5 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat) +
    (6405006349232346407235011054348127950673801938271281958 : Real) * X ^ (5 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat)))) +
    ((((26878412068240331818285838903637629971976210234380211187 : Real) * X ^ (5 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat) +
    (65878403544236190641966152275396680019807115997044230138 : Real) * X ^ (5 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat)) +
    ((104004724124095342507382762379382406030752999866130602132 : Real) * X ^ (5 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat) +
    (109821704100031123474838749166278923661850001193224842094 : Real) * X ^ (5 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat))) +
    (((77757343915210244403371114432867449418976845415158948940 : Real) * X ^ (5 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat) +
    (35799744954313172892171010376479285519925416497980668350 : Real) * X ^ (5 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat)) +
    ((9882574574412249056534776289690548538155769969670334125 : Real) * X ^ (5 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat) +
    ((1337404568007236815678380371229948605157044843685832500 : Real) * X ^ (5 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat) +
    (40321255493226389739445755074329909385682279296615625 : Real) * X ^ (5 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat))))))))

theorem threeLineWindowTransverseCertificate_identity (X Y : Real) :
    (524288000000000000000000000000000000000000000000000000000 : Real) *
      threeLineWindowTransverse ((9 / 64 : Real) * X) ((9 / 400 : Real) * Y) =
        threeLineWindowTransverseCertificate X Y := by
  unfold threeLineWindowTransverse threeLineAxisDen threeLinePolynomialDen
    threeLineRadius1 threeLineRadius2 threeLineRadius3 threeLineWeight1 threeLineWeight2
    threeLineWeight3 threeLineWindowTransverseCertificate
  ring

theorem threeLineWindowTransverseCertificate_pos (X Y : Real)
    (hX : 0 <= X) (hX1 : X <= 1) (hY : 0 <= Y) (hY1 : Y <= 1) :
    0 < threeLineWindowTransverseCertificate X Y := by
  have hq : 0 <= 1 - X := sub_nonneg.mpr hX1
  have hr : 0 <= 1 - Y := sub_nonneg.mpr hY1
  unfold threeLineWindowTransverseCertificate
  positivity

theorem threeLineWindowTransverse_pos (x y : Real)
    (hx : 0 <= x) (hxMax : x <= 9 / 64) (hy : 0 <= y) (hyMax : y <= 9 / 400) :
    0 < threeLineWindowTransverse x y := by
  have hX : 0 <= (64 / 9 : Real) * x := mul_nonneg (by norm_num) hx
  have hX1 : (64 / 9 : Real) * x <= 1 := by nlinarith only [hxMax]
  have hY : 0 <= (400 / 9 : Real) * y := mul_nonneg (by norm_num) hy
  have hY1 : (400 / 9 : Real) * y <= 1 := by nlinarith only [hyMax]
  have hc := threeLineWindowTransverseCertificate_pos ((64 / 9 : Real) * x)
    ((400 / 9 : Real) * y) hX hX1 hY hY1
  have hid := threeLineWindowTransverseCertificate_identity ((64 / 9 : Real) * x)
    ((400 / 9 : Real) * y)
  have heX : (9 / 64 : Real) * ((64 / 9 : Real) * x) = x := by ring
  have heY : (9 / 400 : Real) * ((400 / 9 : Real) * y) = y := by ring
  rw [heX, heY] at hid
  have hp : 0 < (524288000000000000000000000000000000000000000000000000000 : Real) * threeLineWindowTransverse x y := by
    rw [hid]
    exact hc
  by_contra hn
  have hv : threeLineWindowTransverse x y <= 0 := le_of_not_gt hn
  have hbad : (524288000000000000000000000000000000000000000000000000000 : Real) * threeLineWindowTransverse x y <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num) hv
  exact (not_lt_of_ge hbad) hp

theorem threeLineWindowDen_pos (u v : Real) (hu : abs u <= 3 / 8) :
    0 < threeLineClusterDen (u ^ 2) (v ^ 2) := by
  have h1 : abs u < threeLineRadius1 := hu.trans_lt (by norm_num [threeLineRadius1])
  have h2 : abs u < threeLineRadius2 := hu.trans_lt (by norm_num [threeLineRadius2])
  have h3 : abs u < threeLineRadius3 := hu.trans_lt (by norm_num [threeLineRadius3])
  unfold threeLineClusterDen
  simp only [threeLinePolynomialDen_eq]
  exact mul_pos (mul_pos (Complex.pairedResolventDen_pos _ _ _ h1)
    (Complex.pairedResolventDen_pos _ _ _ h2)) (Complex.pairedResolventDen_pos _ _ _ h3)

theorem threeLineWindow_transverse_identity (u v : Real) (hu : abs u <= 3 / 8) :
    (threeLineKernel u v - threeLineKernel 0 v) *
      (threeLineClusterDen (u ^ 2) (v ^ 2) * threeLineClusterDen 0 (v ^ 2)) =
        u ^ 2 * threeLineWindowTransverse (u ^ 2) (v ^ 2) := by
  have hMul (a b : Real) (ha : abs a < threeLineRadius1) :
      threeLineKernel a b * threeLineClusterDen (a ^ 2) (b ^ 2) =
        threeLineNumerator (a ^ 2) (b ^ 2) := by
    unfold threeLineClusterDen
    simp only [threeLinePolynomialDen_eq]
    exact threeLineKernel_mul_den a b ha
  have h1 : abs u < threeLineRadius1 := hu.trans_lt (by norm_num [threeLineRadius1])
  have hP := hMul u v h1
  have hZ : threeLineKernel 0 v * threeLineClusterDen 0 (v ^ 2) =
      threeLineNumerator 0 (v ^ 2) := by
    simpa only [show (0 : Real) ^ 2 = 0 by norm_num] using
      hMul 0 v (by norm_num [threeLineRadius1])
  calc
    _ = (threeLineKernel u v * threeLineClusterDen (u ^ 2) (v ^ 2)) *
        threeLineClusterDen 0 (v ^ 2) -
        (threeLineKernel 0 v * threeLineClusterDen 0 (v ^ 2)) *
          threeLineClusterDen (u ^ 2) (v ^ 2) := by ring
    _ = threeLineNumerator (u ^ 2) (v ^ 2) * threeLineClusterDen 0 (v ^ 2) -
        threeLineNumerator 0 (v ^ 2) * threeLineClusterDen (u ^ 2) (v ^ 2) := by rw [hP, hZ]
    _ = _ := by
      unfold threeLineWindowTransverse threeLineAxisDen threeLineNumerator
        threeLineClusterDen threeLinePolynomialDen threeLineRadius1 threeLineRadius2
        threeLineRadius3 threeLineWeight1 threeLineWeight2 threeLineWeight3
      ring

theorem threeLineKernel_axis_strict_min (u v : Real) (hu : abs u <= 3 / 8)
    (hv : v ^ 2 <= 9 / 400) (hu0 : Not (u = 0)) :
    threeLineKernel 0 v < threeLineKernel u v := by
  have hx : u ^ 2 <= (9 / 64 : Real) := by
    have hab := abs_le.mp hu
    have hm : 0 <= (3 / 8 - u) * (3 / 8 + u) :=
      mul_nonneg (by linarith only [hab.2]) (by linarith only [hab.1])
    nlinarith only [hm]
  have hq := threeLineWindowTransverse_pos (u ^ 2) (v ^ 2) (sq_nonneg u) hx
    (sq_nonneg v) hv
  have hd0 : 0 < threeLineClusterDen 0 (v ^ 2) := by
    simpa only [show (0 : Real) ^ 2 = 0 by norm_num] using
      threeLineWindowDen_pos 0 v (by norm_num)
  have hd := mul_pos (threeLineWindowDen_pos u v hu) hd0
  have hp : 0 < (threeLineKernel u v - threeLineKernel 0 v) *
      (threeLineClusterDen (u ^ 2) (v ^ 2) * threeLineClusterDen 0 (v ^ 2)) := by
    rw [threeLineWindow_transverse_identity u v hu]
    exact mul_pos (sq_pos_of_ne_zero hu0) hq
  have hs : 0 * (threeLineClusterDen (u ^ 2) (v ^ 2) * threeLineClusterDen 0 (v ^ 2)) <
      (threeLineKernel u v - threeLineKernel 0 v) *
        (threeLineClusterDen (u ^ 2) (v ^ 2) * threeLineClusterDen 0 (v ^ 2)) := by
    simpa using hp
  exact sub_pos.mp ((mul_lt_mul_iff_of_pos_right hd).mp hs)

theorem threeLineKernel_axis_min (u v : Real) (hu : abs u <= 3 / 8)
    (hv : v ^ 2 <= 9 / 400) : threeLineKernel 0 v <= threeLineKernel u v := by
  by_cases hu0 : u = 0
  case pos => rw [hu0]
  case neg => exact (threeLineKernel_axis_strict_min u v hu hv hu0).le

theorem threeLineKernel_rectangle_min (h u v : Real) (_h0 : 0 <= h) (hMax : h <= 3 / 20)
    (hu : abs u <= 3 / 8) (hv : abs v <= h) :
    threeLineExactWindowCharge h <= threeLineKernel u v := by
  have hv2 : v ^ 2 <= h ^ 2 := by
    have hab := abs_le.mp hv
    have hm : 0 <= (h - v) * (h + v) :=
      mul_nonneg (by linarith only [hab.2]) (by linarith only [hab.1])
    nlinarith only [hm]
  have hvMax : v ^ 2 <= (9 / 400 : Real) := by
    have hab := abs_le.mp (hv.trans hMax)
    have hm : 0 <= (3 / 20 - v) * (3 / 20 + v) :=
      mul_nonneg (by linarith only [hab.2]) (by linarith only [hab.1])
    nlinarith only [hm]
  have hAxis := threeLineAxisRational_anti (v ^ 2) (h ^ 2) (sq_nonneg v) (sq_nonneg h) hv2
  rw [<- threeLineKernel_axis_formula v, <- threeLineKernel_axis_formula h] at hAxis
  exact hAxis.trans (threeLineKernel_axis_min u v hu hvMax)

theorem threeLineKernel_rectangle_eq_iff (h u v : Real) (_h0 : 0 <= h) (hMax : h <= 3 / 20)
    (hu : abs u <= 3 / 8) (hv : abs v <= h) :
    threeLineKernel u v = threeLineExactWindowCharge h <-> And (u = 0) (v ^ 2 = h ^ 2) := by
  have hv2 : v ^ 2 <= h ^ 2 := by
    have hab := abs_le.mp hv
    have hm : 0 <= (h - v) * (h + v) :=
      mul_nonneg (by linarith only [hab.2]) (by linarith only [hab.1])
    nlinarith only [hm]
  have hvMax : v ^ 2 <= (9 / 400 : Real) := by
    have hab := abs_le.mp (hv.trans hMax)
    have hm : 0 <= (3 / 20 - v) * (3 / 20 + v) :=
      mul_nonneg (by linarith only [hab.2]) (by linarith only [hab.1])
    nlinarith only [hm]
  constructor
  case mp =>
    intro heq
    have hAxis := threeLineAxisRational_anti (v ^ 2) (h ^ 2) (sq_nonneg v) (sq_nonneg h) hv2
    rw [<- threeLineKernel_axis_formula v, <- threeLineKernel_axis_formula h] at hAxis
    have hu0 : u = 0 := by
      by_contra hn
      have hs := threeLineKernel_axis_strict_min u v hu hvMax hn
      change threeLineKernel u v = threeLineKernel 0 h at heq
      linarith only [hs, hAxis, heq]
    have hSq : v ^ 2 = h ^ 2 := by
      by_contra hn
      have hlt : v ^ 2 < h ^ 2 := by
        apply lt_of_le_of_ne hv2
        intro hh
        apply hn
        linarith only [hh]
      have hs := threeLineAxisRational_strictAnti (v ^ 2) (h ^ 2)
        (sq_nonneg v) (sq_nonneg h) hlt
      change threeLineKernel u v = threeLineKernel 0 h at heq
      rw [hu0, threeLineKernel_axis_formula v, threeLineKernel_axis_formula h] at heq
      linarith only [hs, heq]
    exact And.intro hu0 hSq
  case mpr =>
    intro hp
    change threeLineKernel u v = threeLineKernel 0 h
    rw [hp.1, threeLineKernel_axis_formula v, threeLineKernel_axis_formula h, hp.2]

theorem threeLineKernel_optimal_window_charge (h q : Real) (h0 : 0 <= h)
    (hMax : h <= 3 / 20) :
    (forall u v : Real, abs u <= 3 / 8 -> abs v <= h -> q <= threeLineKernel u v) <->
      q <= threeLineExactWindowCharge h := by
  constructor
  case mp =>
    intro hq
    exact hq 0 h (by norm_num) (by rw [abs_of_nonneg h0])
  case mpr =>
    intro hq u v hu hv
    exact hq.trans (threeLineKernel_rectangle_min h u v h0 hMax hu hv)

end PrimeFactorOscillations

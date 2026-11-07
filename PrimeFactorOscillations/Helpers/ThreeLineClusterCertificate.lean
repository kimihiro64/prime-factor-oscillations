/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.ThreeLineResolventCertificate

/-! # A complete bivariate certificate for the signed three-line cluster charge -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def threeLineClusterDen (x y : Real) : Real :=
  threeLinePolynomialDen threeLineRadius1 x y *
    threeLinePolynomialDen threeLineRadius2 x y *
    threeLinePolynomialDen threeLineRadius3 x y

def threeLineClusterDefect (x y : Real) : Real :=
  threeLineNumerator x y -
    (threeLineCharge + (13 / 2 : Real) * x - 48 * y) * threeLineClusterDen x y

def threeLineClusterCertificate (X Y : Real) : Real :=
  (((((((1435847826288335768930567676541692542976 : Real) * X ^ (0 : Nat) * (1 - X) ^ (10 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat) +
    ((13775229486027805707173063449711074115584 : Real) * X ^ (0 : Nat) * (1 - X) ^ (10 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat) +
    (58703699435063998238322139814433185857536 : Real) * X ^ (0 : Nat) * (1 - X) ^ (10 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat))) +
    (((145851539229914668041239168227723535376384 : Real) * X ^ (0 : Nat) * (1 - X) ^ (10 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat) +
    (232828707752803397883075635228411199307776 : Real) * X ^ (0 : Nat) * (1 - X) ^ (10 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat)) +
    ((247650721799241024608082631995842543230976 : Real) * X ^ (0 : Nat) * (1 - X) ^ (10 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat) +
    (175518748129376457096606515102885359222784 : Real) * X ^ (0 : Nat) * (1 - X) ^ (10 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat)))) +
    ((((79927686945942672738912178068547540033536 : Real) * X ^ (0 : Nat) * (1 - X) ^ (10 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat) +
    (21221022722370527521146591843875450077184 : Real) * X ^ (0 : Nat) * (1 - X) ^ (10 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat)) +
    ((2502848404776545412674407924322194251776 : Real) * X ^ (0 : Nat) * (1 - X) ^ (10 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat) +
    (17386041839141102685814931482663059456 : Real) * X ^ (1 : Nat) * (1 - X) ^ (9 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat))) +
    (((10873310130038595689651906815520615915520 : Real) * X ^ (1 : Nat) * (1 - X) ^ (9 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat) +
    (104932287729368786175003571317105242972160 : Real) * X ^ (1 : Nat) * (1 - X) ^ (9 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat)) +
    ((452015442466300105995226550059136918753280 : Real) * X ^ (1 : Nat) * (1 - X) ^ (9 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat) +
    (1135924037590995689280299269989775482470400 : Real) * X ^ (1 : Nat) * (1 - X) ^ (9 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat))))) +
    ((((1833783887297948563102453526688704693071872 : Real) * X ^ (1 : Nat) * (1 - X) ^ (9 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat) +
    ((1971725522694481336341376966613554739486720 : Real) * X ^ (1 : Nat) * (1 - X) ^ (9 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat) +
    (1411939873040516710305766360324970956943360 : Real) * X ^ (1 : Nat) * (1 - X) ^ (9 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat))) +
    (((649321820237816712895348026138949953454080 : Real) * X ^ (1 : Nat) * (1 - X) ^ (9 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat) +
    (174015175007133557661866532350360023347200 : Real) * X ^ (1 : Nat) * (1 - X) ^ (9 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat)) +
    ((20706633647435866960251227247825126588416 : Real) * X ^ (1 : Nat) * (1 - X) ^ (9 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat) +
    (657650302994114246236600720014550331904 : Real) * X ^ (2 : Nat) * (1 - X) ^ (8 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat)))) +
    ((((40879284896831854066011971550208069493760 : Real) * X ^ (2 : Nat) * (1 - X) ^ (8 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat) +
    (370647305019701321474424711444589917884160 : Real) * X ^ (2 : Nat) * (1 - X) ^ (8 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat)) +
    ((1580980735675728281278096026475884506726400 : Real) * X ^ (2 : Nat) * (1 - X) ^ (8 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat) +
    (3985473304155415953680878356949157234104320 : Real) * X ^ (2 : Nat) * (1 - X) ^ (8 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat))) +
    (((6483485099127239501886976513867854092310528 : Real) * X ^ (2 : Nat) * (1 - X) ^ (8 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat) +
    (7037025026321071526512760604759736620034560 : Real) * X ^ (2 : Nat) * (1 - X) ^ (8 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat)) +
    ((5089696647200932286636653809768896107560960 : Real) * X ^ (2 : Nat) * (1 - X) ^ (8 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat) +
    (2364222113907391925341896164141343691353600 : Real) * X ^ (2 : Nat) * (1 - X) ^ (8 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat)))))) +
    (((((639844950178538368192244659844419157099520 : Real) * X ^ (2 : Nat) * (1 - X) ^ (8 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat) +
    ((76861317372695450803786543492419919482624 : Real) * X ^ (2 : Nat) * (1 - X) ^ (8 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat) +
    (3976432714679260747692425618268304194816 : Real) * X ^ (3 : Nat) * (1 - X) ^ (7 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat))) +
    (((100452518512763506067648494601509125948480 : Real) * X ^ (3 : Nat) * (1 - X) ^ (7 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat) +
    (803349934489868322051201301615256254545600 : Real) * X ^ (3 : Nat) * (1 - X) ^ (7 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat)) +
    ((3310313137342179362592523556766425039197440 : Real) * X ^ (3 : Nat) * (1 - X) ^ (7 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat) +
    (8284022932463869980227961523690519165866240 : Real) * X ^ (3 : Nat) * (1 - X) ^ (7 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat)))) +
    ((((13520348462000571531858192599588002214189952 : Real) * X ^ (3 : Nat) * (1 - X) ^ (7 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat) +
    (14789832877767312945959674456292968125271680 : Real) * X ^ (3 : Nat) * (1 - X) ^ (7 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat)) +
    ((10802102469093381193985568234397137482860800 : Real) * X ^ (3 : Nat) * (1 - X) ^ (7 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat) +
    (5070579686492304603159706005655843892106240 : Real) * X ^ (3 : Nat) * (1 - X) ^ (7 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat))) +
    (((1386877936609691721408244597821427431359040 : Real) * X ^ (3 : Nat) * (1 - X) ^ (7 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat) +
    (168332659630552203765941770301645551571136 : Real) * X ^ (3 : Nat) * (1 - X) ^ (7 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat)) +
    ((11183214666950463932447398711242303533454 : Real) * X ^ (4 : Nat) * (1 - X) ^ (6 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat) +
    (173525309123568116980327912624447790880300 : Real) * X ^ (4 : Nat) * (1 - X) ^ (6 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat))))) +
    ((((1181568672744119964991728638004388005045270 : Real) * X ^ (4 : Nat) * (1 - X) ^ (6 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat) +
    ((4587010275521402446902654396442456357485840 : Real) * X ^ (4 : Nat) * (1 - X) ^ (6 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat) +
    (11257572413660456894479219263175479613053180 : Real) * X ^ (4 : Nat) * (1 - X) ^ (6 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat))) +
    (((18340308780072083263884067031935661293164168 : Real) * X ^ (4 : Nat) * (1 - X) ^ (6 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat) +
    (20189230706675211551356108688544462337751100 : Real) * X ^ (4 : Nat) * (1 - X) ^ (6 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat)) +
    ((14893629182076877699658192735986046441026320 : Real) * X ^ (4 : Nat) * (1 - X) ^ (6 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat) +
    (7071964319543116712009319822058720211036790 : Real) * X ^ (4 : Nat) * (1 - X) ^ (6 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat)))) +
    ((((1957436319019305756040247712142024117870380 : Real) * X ^ (4 : Nat) * (1 - X) ^ (6 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat) +
    (240390538523381696696665978636343530007214 : Real) * X ^ (4 : Nat) * (1 - X) ^ (6 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat)) +
    ((18170199061297069792264357664937309720381 : Real) * X ^ (5 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat) +
    (212059732052930138203813175139726317644962 : Real) * X ^ (5 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat))) +
    (((1222350673984363287837317255319858682165113 : Real) * X ^ (5 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat) +
    (4372096494678424960725319956522925693507992 : Real) * X ^ (5 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat)) +
    ((10381986441324116495552724184253994666829578 : Real) * X ^ (5 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat) +
    (16789217926566051979068115458864500664826764 : Real) * X ^ (5 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat))))))) +
    ((((((18578915631953058325522410094393555824897162 : Real) * X ^ (5 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat) +
    ((13858878983497142681917953501674263400648088 : Real) * X ^ (5 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat) +
    (6670224717403719400481905911629906859231417 : Real) * X ^ (5 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat))) +
    (((1872598358505214166984982854302937334114978 : Real) * X ^ (5 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat) +
    (233203831573209347713563143242100067899133 : Real) * X ^ (5 : Nat) * (1 - X) ^ (5 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat)) +
    ((18438698474708211172663650782479899051831 : Real) * X ^ (6 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat) +
    (180272920014395109350292902678476283734470 : Real) * X ^ (6 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat)))) +
    ((((889085009149803791540638229144456089445835 : Real) * X ^ (6 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat) +
    (2874487284998485823505479907366104864145480 : Real) * X ^ (6 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat)) +
    ((6502817564338131564520065067496411137345950 : Real) * X ^ (6 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat) +
    (10373873952858694365347400007452728496505572 : Real) * X ^ (6 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat))) +
    (((11540478699170137011405483815686452355880670 : Real) * X ^ (6 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat) +
    (8730950686865800341428214881328198021785160 : Real) * X ^ (6 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat)) +
    ((4276392347021599705842653661803980234618155 : Real) * X ^ (6 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat) +
    (1222582834688219688766735175395427272407750 : Real) * X ^ (6 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat))))) +
    ((((154955361271215043916618449307155222235991 : Real) * X ^ (6 : Nat) * (1 - X) ^ (4 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat) +
    ((11909751902478525826565523601745700696354 : Real) * X ^ (7 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat) +
    (103344144888847578791481490840428190301460 : Real) * X ^ (7 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat))) +
    (((441914982371163628244169536834822144913210 : Real) * X ^ (7 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat) +
    (1266275160124561340480515576810145553615600 : Real) * X ^ (7 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat)) +
    ((2673082339756188652883548885614865976827620 : Real) * X ^ (7 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat) +
    (4174012256856127601017168688244143947675128 : Real) * X ^ (7 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat)))) +
    ((((4679726348372461991132295656442629150332260 : Real) * X ^ (7 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat) +
    (3616300119718807757587339931634858497963760 : Real) * X ^ (7 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat)) +
    ((1817038977750283276438664644282145304109050 : Real) * X ^ (7 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat) +
    (532909697213021848592011067359869416492820 : Real) * X ^ (7 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat))) +
    (((69168978648790051943272508113237329170274 : Real) * X ^ (7 : Nat) * (1 - X) ^ (3 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat) +
    (4767611498538405883252717447699100918316 : Real) * X ^ (8 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat)) +
    ((37821522411107756403776401621204889360280 : Real) * X ^ (8 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat) +
    (141112656018124346254598344421150700534300 : Real) * X ^ (8 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat)))))) +
    (((((347717323820280617882016366075814395102240 : Real) * X ^ (8 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat) +
    ((659794994893395743826818299082741784172440 : Real) * X ^ (8 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat) +
    (995003638294778926523880708189145009828752 : Real) * X ^ (8 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat))) +
    (((1134628601658025013568173698132557944283480 : Real) * X ^ (8 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat) +
    (911685834751444598030296524767234167572000 : Real) * X ^ (8 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat)) +
    ((478339074937099066701548198173477330548540 : Real) * X ^ (8 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat) +
    (146049224826888919987619620850861434905240 : Real) * X ^ (8 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat)))) +
    ((((19634605099318242593198364246633036311436 : Real) * X ^ (8 : Nat) * (1 - X) ^ (2 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat) +
    (1078752928337332422699563211742274310129 : Real) * X ^ (9 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat)) +
    ((7920821367857511234176367099917556311850 : Real) * X ^ (9 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat) +
    (25569672089367623636713619235783059218845 : Real) * X ^ (9 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat))) +
    (((50689423161620126637017989279921632539640 : Real) * X ^ (9 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat) +
    (77940463189333920935939311218314254718130 : Real) * X ^ (9 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat)) +
    ((108903015918604402346818804660823592091068 : Real) * X ^ (9 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat) +
    (131146615104649589278794613445581623417650 : Real) * X ^ (9 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat))))) +
    ((((116238750668124190779242432962968031510520 : Real) * X ^ (9 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat) +
    ((66892528081929889052323303893994762639965 : Real) * X ^ (9 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat) +
    (22014515677322902517630963832157274540330 : Real) * X ^ (9 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat))) +
    (((3138495399910778188416146830372112688689 : Real) * X ^ (9 : Nat) * (1 - X) ^ (1 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat) +
    (105347705440134657307317366740398145631 : Real) * X ^ (10 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (0 : Nat) * (1 - Y) ^ (10 : Nat)) +
    ((715642680246157417431678346223080110486 : Real) * X ^ (10 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (1 : Nat) * (1 - Y) ^ (9 : Nat) +
    (1928678246354417975842297858529596789779 : Real) * X ^ (10 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (2 : Nat) * (1 - Y) ^ (8 : Nat)))) +
    ((((2490338322124728624034793263861528296456 : Real) * X ^ (10 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (3 : Nat) * (1 - Y) ^ (7 : Nat) +
    (1446398047189914332253019835956242659694 : Real) * X ^ (10 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (4 : Nat) * (1 - Y) ^ (6 : Nat)) +
    ((765370533704621867349181372375020737988 : Real) * X ^ (10 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (5 : Nat) * (1 - Y) ^ (5 : Nat) +
    (2333240268278060783942348069237662224686 : Real) * X ^ (10 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (6 : Nat) * (1 - Y) ^ (4 : Nat))) +
    (((3979096993541151725905994040938272759304 : Real) * X ^ (10 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (7 : Nat) * (1 - Y) ^ (3 : Nat) +
    (3212187610903799393617867354771763950131 : Real) * X ^ (10 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (8 : Nat) * (1 - Y) ^ (2 : Nat)) +
    ((1281331577060936656742255590144047494294 : Real) * X ^ (10 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (9 : Nat) * (1 - Y) ^ (1 : Nat) +
    (205928228511269148501052128306285628607 : Real) * X ^ (10 : Nat) * (1 - X) ^ (0 : Nat) * Y ^ (10 : Nat) * (1 - Y) ^ (0 : Nat))))))))

theorem threeLineClusterCertificate_identity (X Y : Real) :
    (26759767523328000000000000000000000000000 : Real) *
      threeLineClusterDefect ((9 / 64 : Real) * X) ((1 / 24 : Real) * Y) =
        threeLineClusterCertificate X Y := by
  unfold threeLineClusterDefect threeLineClusterDen threeLineNumerator
    threeLinePolynomialDen threeLineRadius1 threeLineRadius2 threeLineRadius3
    threeLineWeight1 threeLineWeight2 threeLineWeight3 threeLineCharge
    threeLineClusterCertificate
  ring

theorem threeLineClusterCertificate_nonneg (X Y : Real)
    (hX : 0 <= X) (hX1 : X <= 1) (hY : 0 <= Y) (hY1 : Y <= 1) :
    0 <= threeLineClusterCertificate X Y := by
  have hq : 0 <= 1 - X := sub_nonneg.mpr hX1
  have hr : 0 <= 1 - Y := sub_nonneg.mpr hY1
  unfold threeLineClusterCertificate
  positivity

theorem threeLineClusterDefect_nonneg (x y : Real)
    (hx : 0 <= x) (hxMax : x <= 9 / 64) (hy : 0 <= y) (hyMax : y <= 1 / 24) :
    0 <= threeLineClusterDefect x y := by
  have hX : 0 <= (64 / 9 : Real) * x := mul_nonneg (by norm_num) hx
  have hX1 : (64 / 9 : Real) * x <= 1 := by nlinarith only [hxMax]
  have hY : 0 <= (24 : Real) * y := mul_nonneg (by norm_num) hy
  have hY1 : (24 : Real) * y <= 1 := by nlinarith only [hyMax]
  have hc := threeLineClusterCertificate_nonneg ((64 / 9 : Real) * x) (24 * y)
    hX hX1 hY hY1
  have hid := threeLineClusterCertificate_identity ((64 / 9 : Real) * x) (24 * y)
  have heX : (9 / 64 : Real) * ((64 / 9 : Real) * x) = x := by ring
  have heY : (1 / 24 : Real) * (24 * y) = y := by ring
  rw [heX, heY] at hid
  have hScaled : 0 <= (26759767523328000000000000000000000000000 : Real) *
      threeLineClusterDefect x y := by rw [hid]; exact hc
  by_contra hn
  have hd : threeLineClusterDefect x y < 0 := lt_of_not_ge hn
  have hbad : (26759767523328000000000000000000000000000 : Real) * threeLineClusterDefect x y < 0 :=
    mul_neg_of_pos_of_neg (by norm_num) hd
  exact (not_lt_of_ge hScaled) hbad

theorem threeLineKernel_cluster_charge (u v : Real) (hu : abs u <= 3 / 8) :
    threeLineCharge + (13 / 2 : Real) * u ^ 2 - 48 * v ^ 2 <= threeLineKernel u v := by
  have hx : u ^ 2 <= (9 / 64 : Real) := by
    have hab := abs_le.mp hu
    have hm : 0 <= (3 / 8 - u) * (3 / 8 + u) :=
      mul_nonneg (by linarith only [hab.2]) (by linarith only [hab.1])
    nlinarith only [hm]
  by_cases hy : v ^ 2 <= (1 / 24 : Real)
  case pos =>
    have h1 : abs u < threeLineRadius1 := hu.trans_lt (by norm_num [threeLineRadius1])
    have h2 : abs u < threeLineRadius2 := hu.trans_lt (by norm_num [threeLineRadius2])
    have h3 : abs u < threeLineRadius3 := hu.trans_lt (by norm_num [threeLineRadius3])
    have hd : 0 < threeLineClusterDen (u ^ 2) (v ^ 2) := by
      unfold threeLineClusterDen
      simp only [threeLinePolynomialDen_eq]
      exact mul_pos (mul_pos (Complex.pairedResolventDen_pos _ _ _ h1)
        (Complex.pairedResolventDen_pos _ _ _ h2)) (Complex.pairedResolventDen_pos _ _ _ h3)
    have hid : threeLineKernel u v * threeLineClusterDen (u ^ 2) (v ^ 2) =
        threeLineNumerator (u ^ 2) (v ^ 2) := by
      unfold threeLineClusterDen
      simp only [threeLinePolynomialDen_eq]
      exact threeLineKernel_mul_den u v h1
    have hDef := threeLineClusterDefect_nonneg (u ^ 2) (v ^ 2)
      (sq_nonneg u) hx (sq_nonneg v) hy
    unfold threeLineClusterDefect at hDef
    have hMul : (threeLineCharge + (13 / 2 : Real) * u ^ 2 - 48 * v ^ 2) *
        threeLineClusterDen (u ^ 2) (v ^ 2) <=
        threeLineKernel u v * threeLineClusterDen (u ^ 2) (v ^ 2) := by
      nlinarith only [hDef, hid]
    exact (mul_le_mul_iff_of_pos_right hd).mp hMul
  case neg =>
    have hcap : threeLineCharge + (13 / 2 : Real) * (9 / 64 : Real) < 2 := by
      norm_num [threeLineCharge]
    have hv : (1 / 24 : Real) < v ^ 2 := lt_of_not_ge hy
    have hTarget : threeLineCharge + (13 / 2 : Real) * u ^ 2 - 48 * v ^ 2 <= 0 := by
      nlinarith only [hcap, hx, hv]
    exact hTarget.trans (threeLineKernel_pos u v hu).le

end PrimeFactorOscillations

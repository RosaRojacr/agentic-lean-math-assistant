import NearOneScalarCell

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace NearOneScalarStress
open Real Set
open NearOneScalarNormalization
open NearOneScalarInterval
open NearOneScalarCell
noncomputable section

/-- Exact kernel-replayed scalar stress rectangle from the frozen round-218 manifest. -/
namespace Band10Cell33
def wholeBox : Box3 := { t := ⟨(1552 / 63167 : ℚ), (1568 / 63167 : ℚ), by norm_num⟩, e4 := ⟨(-1 / 8192 : ℚ), (1 / 8192 : ℚ), by norm_num⟩, e3 := ⟨(-1 / 2048 : ℚ), (1 / 2048 : ℚ), by norm_num⟩ }
def centerBox : Box3 := { t := ⟨(120 / 4859 : ℚ), (120 / 4859 : ℚ), by norm_num⟩, e4 := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩, e3 := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩ }
def aAt (t e4 : ℝ) : ℝ := ((491917184095198310245273393110183773 / 1329227995784915872903807060280344576 : ℚ) : ℝ) + ((-671117650156227431961044002113308227 / 1329227995784915872903807060280344576 : ℚ) : ℝ) * t + t ^ 2 * e4
def bAt (t e3 : ℝ) : ℝ := ((122957918479022181365483813559522903 / 166153499473114484112975882535043072 : ℚ) : ℝ) + ((-96815668088139366807758752083030455 / 166153499473114484112975882535043072 : ℚ) : ℝ) * t + t ^ 2 * e3

def tCenter : ℚ := (120 / 4859 : ℚ)
def tDisp : LeanSuffixReflective.QInterval := ⟨(-8 / 63167 : ℚ), (8 / 63167 : ℚ), by norm_num⟩
def zeroDisp : LeanSuffixReflective.QInterval := LeanSuffixReflective.QInterval.point 0
def e4LoDisp : LeanSuffixReflective.QInterval := LeanSuffixReflective.QInterval.point (-1 / 8192 : ℚ)
def e4HiDisp : LeanSuffixReflective.QInterval := LeanSuffixReflective.QInterval.point (1 / 8192 : ℚ)
def e3LoDisp : LeanSuffixReflective.QInterval := LeanSuffixReflective.QInterval.point (-1 / 2048 : ℚ)
def e3HiDisp : LeanSuffixReflective.QInterval := LeanSuffixReflective.QInterval.point (1 / 2048 : ℚ)
def e4FullDisp : LeanSuffixReflective.QInterval := wholeBox.e4
def e3FullDisp : LeanSuffixReflective.QInterval := wholeBox.e3

@[simp] private abbrev wJ0 : NearOneScalarInterval.Jet3 wholeBox := NearOneScalarInterval.Jet3.tVar wholeBox
@[simp] private abbrev wJ1 : NearOneScalarInterval.Jet3 wholeBox := NearOneScalarInterval.Jet3.e4Var wholeBox
@[simp] private abbrev wJ2 : NearOneScalarInterval.Jet3 wholeBox := NearOneScalarInterval.Jet3.e3Var wholeBox
private abbrev wQ4_wJ3v : LeanSuffixReflective.QInterval := ⟨(226620612917872166771062532655 / 633825300114114700748351602688 : ℚ), (453403533506232312558727281127 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d0 : LeanSuffixReflective.QInterval := ⟨(-160008837153636000061139565939 / 316912650057057350374175801344 : ℚ), (-640019983867274069139146879435 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d1 : LeanSuffixReflective.QInterval := ⟨(765248518525921256689725867 / 1267650600228229401496703205376 : ℚ), (390554085020881483114471635 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ3 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (491917184095198310245273393110183773 / 1329227995784915872903807060280344576 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-671117650156227431961044002113308227 / 1329227995784915872903807060280344576 : ℚ)).mul (wJ0))).add (((wJ0).mul (wJ0)).mul (wJ1))).widenAll wQ4_wJ3v wQ4_wJ3d0 wQ4_wJ3d1 wQ4_wJ3d2 (by
    norm_num [wJ0, wJ1, wQ4_wJ3v, wQ4_wJ3d0, wQ4_wJ3d1, wQ4_wJ3d2])
private abbrev wQ5_wJ4v : LeanSuffixReflective.QInterval := ⟨(459879320674525011156397175781 / 633825300114114700748351602688 : ℚ), (459973250279428314732602673427 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d0 : LeanSuffixReflective.QInterval := ⟨(-369337829072752745160887580927 / 633825300114114700748351602688 : ℚ), (-369307099578212882950064812285 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d2 : LeanSuffixReflective.QInterval := ⟨(765248518525921256689725867 / 1267650600228229401496703205376 : ℚ), (390554085020881483114471635 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ4 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (122957918479022181365483813559522903 / 166153499473114484112975882535043072 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-96815668088139366807758752083030455 / 166153499473114484112975882535043072 : ℚ)).mul (wJ0))).add (((wJ0).mul (wJ0)).mul (wJ2))).widenAll wQ5_wJ4v wQ5_wJ4d0 wQ5_wJ4d1 wQ5_wJ4d2 (by
    norm_num [wJ0, wJ2, wQ5_wJ4v, wQ5_wJ4d0, wQ5_wJ4d1, wQ5_wJ4d2])
private abbrev wQ6_wJ5v : LeanSuffixReflective.QInterval := ⟨(765248518525921256689725867 / 1267650600228229401496703205376 : ℚ), (390554085020881483114471635 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d0 : LeanSuffixReflective.QInterval := ⟨(15572955273752212635734508325 / 316912650057057350374175801344 : ℚ), (31467002408818903882515088987 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ5 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ6_wJ5v wQ6_wJ5d0 wQ6_wJ5d1 wQ6_wJ5d2 (by
    norm_num [wJ0, wQ6_wJ5v, wQ6_wJ5d0, wQ6_wJ5d1, wQ6_wJ5d2])
private abbrev wQ7_wJ6v : LeanSuffixReflective.QInterval := ⟨(765248518525921256689725867 / 1267650600228229401496703205376 : ℚ), (390554085020881483114471635 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d0 : LeanSuffixReflective.QInterval := ⟨(15572955273752212635734508325 / 316912650057057350374175801344 : ℚ), (31467002408818903882515088987 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ6 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ7_wJ6v wQ7_wJ6d0 wQ7_wJ6d1 wQ7_wJ6d2 (by
    norm_num [wJ0, wQ7_wJ6v, wQ7_wJ6d0, wQ7_wJ6d1, wQ7_wJ6d2])
private abbrev wQ8_wJ7v : LeanSuffixReflective.QInterval := ⟨(5064181544783090092120599749 / 39614081257132168796771975168 : ℚ), (81084947287101504682201776831 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d0 : LeanSuffixReflective.QInterval := ⟨(-457845858438406507942703593497 / 1267650600228229401496703205376 : ℚ), (-457670973366240863549092876839 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d1 : LeanSuffixReflective.QInterval := ⟨(8550319793936859403813525 / 19807040628566084398385987584 : ℚ), (558761545624258569588372593 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ7 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ3).mul (wJ3)).widenAll wQ8_wJ7v wQ8_wJ7d0 wQ8_wJ7d1 wQ8_wJ7d2 (by
    norm_num [wJ3, wQ8_wJ7v, wQ8_wJ7d0, wQ8_wJ7d1, wQ8_wJ7d2])
private abbrev wQ9_wJ8v : LeanSuffixReflective.QInterval := ⟨(1267371219455417272211909019079 / 1267650600228229401496703205376 : ℚ), (39605530937338231937368161643 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d0 : LeanSuffixReflective.QInterval := ⟨(-22123387795094804903314726881 / 1267650600228229401496703205376 : ℚ), (-10938851962729795483472285645 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d1 : LeanSuffixReflective.QInterval := ⟨(-240653841522318186026349 / 633825300114114700748351602688 : ℚ), (-461961123199629407462133 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ8 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ6).mul (wJ3)).neg)).widenAll wQ9_wJ8v wQ9_wJ8d0 wQ9_wJ8d1 wQ9_wJ8d2 (by
    norm_num [wJ6, wJ3, wQ9_wJ8v, wQ9_wJ8d0, wQ9_wJ8d1, wQ9_wJ8d2])
private abbrev wQ10_wJ9v : LeanSuffixReflective.QInterval := ⟨(453191262450895261127832882053 / 633825300114114700748351602688 : ℚ), (906709239237549515939127074511 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d0 : LeanSuffixReflective.QInterval := ⟨(-1287845527998933753265491662729 / 1267650600228229401496703205376 : ℚ), (-1287721106182768551838842185369 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d1 : LeanSuffixReflective.QInterval := ⟨(1530152736178783571052390243 / 1267650600228229401496703205376 : ℚ), (780942998482873032096316125 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ9 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ3)).add (((wJ6).mul (wJ7)).neg)).widenAll wQ10_wJ9v wQ10_wJ9d0 wQ10_wJ9d1 wQ10_wJ9d2 (by
    norm_num [wJ3, wJ6, wJ7, wQ10_wJ9v, wQ10_wJ9d0, wQ10_wJ9d1, wQ10_wJ9d2])
private abbrev wQ11_wJ10v : LeanSuffixReflective.QInterval := ⟨(968674807957922572428011259539 / 1267650600228229401496703205376 : ℚ), (484821862681435184170264652591 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d0 : LeanSuffixReflective.QInterval := ⟨(1247530880442754820322711553605 / 1267650600228229401496703205376 : ℚ), (1247657652341075150505874053809 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d1 : LeanSuffixReflective.QInterval := ⟨(1530152736178783571052390243 / 1267650600228229401496703205376 : ℚ), (780942998482873032096316125 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ10 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ3)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ0))).add (((wJ6).mul (wJ7)).neg)).add (((wJ0).mul (wJ0)).mul ((wJ0).mul (wJ0)))).widenAll wQ11_wJ10v wQ11_wJ10d0 wQ11_wJ10d1 wQ11_wJ10d2 (by
    norm_num [wJ3, wJ0, wJ6, wJ7, wQ11_wJ10v, wQ11_wJ10d0, wQ11_wJ10d1, wQ11_wJ10d2])
private abbrev wQ11_root11 : LeanSuffixReflective.QInterval := ⟨(1071903144751489586652606086841 / 1267650600228229401496703205376 : ℚ), (536048158133194431511715497151 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11v : LeanSuffixReflective.QInterval := ⟨(1071903144751489586652606086841 / 1267650600228229401496703205376 : ℚ), (536048158133194431511715497151 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d0 : LeanSuffixReflective.QInterval := ⟨(-761513838522965441679369405553 / 1267650600228229401496703205376 : ℚ), (-190325767425445192399368671953 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d1 : LeanSuffixReflective.QInterval := ⟨(226157273025264307699324883 / 316912650057057350374175801344 : ℚ), (461778130616624224120617535 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ11 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ9).sqrt wQ11_root11 (by norm_num [wQ11_root11]) (by norm_num [wJ9, wQ11_root11]) (by norm_num [wJ9, wQ11_root11])).widenAll wQ12_wJ11v wQ12_wJ11d0 wQ12_wJ11d1 wQ12_wJ11d2 (by
    norm_num [wJ9, wQ11_root11, NearOneScalarInterval.Jet3.sqrt, wQ12_wJ11v, wQ12_wJ11d0, wQ12_wJ11d1, wQ12_wJ11d2])
private abbrev wQ12_root12 : LeanSuffixReflective.QInterval := ⟨(1108125083974650126842738223711 / 1267650600228229401496703205376 : ℚ), (554339573380743548926154315909 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12v : LeanSuffixReflective.QInterval := ⟨(1108125083974650126842738223711 / 1267650600228229401496703205376 : ℚ), (554339573380743548926154315909 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d0 : LeanSuffixReflective.QInterval := ⟨(356603006833844443212301090769 / 633825300114114700748351602688 : ℚ), (178408781953185236982651577799 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d1 : LeanSuffixReflective.QInterval := ⟨(437389627135107201046800207 / 633825300114114700748351602688 : ℚ), (893367432149468419663821089 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ12 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ10).sqrt wQ12_root12 (by norm_num [wQ12_root12]) (by norm_num [wJ10, wQ12_root12]) (by norm_num [wJ10, wQ12_root12])).widenAll wQ13_wJ12v wQ13_wJ12d0 wQ13_wJ12d1 wQ13_wJ12d2 (by
    norm_num [wJ10, wQ12_root12, NearOneScalarInterval.Jet3.sqrt, wQ13_wJ12v, wQ13_wJ12d0, wQ13_wJ12d1, wQ13_wJ12d2])
private abbrev wQ14_wJ13v : LeanSuffixReflective.QInterval := ⟨(1267669402224536844145402406771 / 1267650600228229401496703205376 : ℚ), (1267669989745075626334530662483 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d0 : LeanSuffixReflective.QInterval := ⟨(2295745555577763770069177601 / 1267650600228229401496703205376 : ℚ), (1171662255062644449343414905 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ13 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0))).widenAll wQ14_wJ13v wQ14_wJ13d0 wQ14_wJ13d1 wQ14_wJ13d2 (by
    norm_num [wJ0, wQ14_wJ13v, wQ14_wJ13d0, wQ14_wJ13d1, wQ14_wJ13d2])
private abbrev wQ15_wJ14v : LeanSuffixReflective.QInterval := ⟨(1090022063682450893262530589127 / 633825300114114700748351602688 : ℚ), (272598982677299452494376585827 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d0 : LeanSuffixReflective.QInterval := ⟨(-46378230458577657272428238649 / 1267650600228229401496703205376 : ℚ), (-45697402406656466350710842177 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d1 : LeanSuffixReflective.QInterval := ⟨(1779421763974549876108904505 / 1267650600228229401496703205376 : ℚ), (1816937819759245537905642545 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ14 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ12).add ((wJ13).mul (wJ11))).widenAll wQ15_wJ14v wQ15_wJ14d0 wQ15_wJ14d1 wQ15_wJ14d2 (by
    norm_num [wJ12, wJ13, wJ11, wQ15_wJ14v, wQ15_wJ14d0, wQ15_wJ14d1, wQ15_wJ14d2])
private abbrev wQ16_wJ15v : LeanSuffixReflective.QInterval := ⟨(1611426430315896816718653569183 / 1267650600228229401496703205376 : ℚ), (201634471214997727121007293149 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d0 : LeanSuffixReflective.QInterval := ⟨(-142584183243885795271132865563 / 1267650600228229401496703205376 : ℚ), (-70160096820723773008420375897 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d1 : LeanSuffixReflective.QInterval := ⟨(3947352615211171792587774367 / 1267650600228229401496703205376 : ℚ), (126041628865673266785105225 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ15 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ11).mul (wJ12)).mul (wJ14)).widenAll wQ16_wJ15v wQ16_wJ15d0 wQ16_wJ15d1 wQ16_wJ15d2 (by
    norm_num [wJ11, wJ12, wJ14, wQ16_wJ15v, wQ16_wJ15d0, wQ16_wJ15d1, wQ16_wJ15d2])
private abbrev wQ17_wJ16v : LeanSuffixReflective.QInterval := ⟨(2180076462127828887392712289371 / 1267650600228229401496703205376 : ℚ), (2180825218007764543102608741209 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d0 : LeanSuffixReflective.QInterval := ⟨(-2651926736741109536265079089 / 79228162514264337593543950336 : ℚ), (-2604172620703175971295706685 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d1 : LeanSuffixReflective.QInterval := ⟨(1779448156642552880239790029 / 1267650600228229401496703205376 : ℚ), (227120701371395032257027473 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ16 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ13).mul (wJ14)).widenAll wQ17_wJ16v wQ17_wJ16d0 wQ17_wJ16d1 wQ17_wJ16d2 (by
    norm_num [wJ13, wJ14, wQ17_wJ16v, wQ17_wJ16d0, wQ17_wJ16d1, wQ17_wJ16d2])
private abbrev wQ18_wJ17v : LeanSuffixReflective.QInterval := ⟨(2180040180745655685684525290645 / 1267650600228229401496703205376 : ℚ), (545207028100261998285954660667 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d0 : LeanSuffixReflective.QInterval := ⟨(-45267927178985873800164987147 / 1267650600228229401496703205376 : ℚ), (-42907185748354323212902650569 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d1 : LeanSuffixReflective.QInterval := ⟨(55604746329159348375003397 / 39614081257132168796771975168 : ℚ), (227129451261359757813869567 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ17 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ11).add (wJ12)).mul (((wJ8).mul (wJ8)).add ((wJ6).mul ((wJ11).mul (wJ12))))).widenAll wQ18_wJ17v wQ18_wJ17d0 wQ18_wJ17d1 wQ18_wJ17d2 (by
    norm_num [wJ11, wJ12, wJ8, wJ6, wQ18_wJ17v, wQ18_wJ17d0, wQ18_wJ17d1, wQ18_wJ17d2])
private abbrev wQ19_wJ18v : LeanSuffixReflective.QInterval := ⟨(2534202594221683135384985638643 / 1267650600228229401496703205376 : ℚ), (2534226258782795051638144074553 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d0 : LeanSuffixReflective.QInterval := ⟨(-86180393595189136129346614165 / 1267650600228229401496703205376 : ℚ), (-85149864761473328696323212005 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d1 : LeanSuffixReflective.QInterval := ⟨(-962414955103931758148843 / 633825300114114700748351602688 : ℚ), (-1847450942345224394892925 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ18 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul (wJ8)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).widenAll wQ19_wJ18v wQ19_wJ18d0 wQ19_wJ18d1 wQ19_wJ18d2 (by
    norm_num [wJ8, wJ0, wQ19_wJ18v, wQ19_wJ18d0, wQ19_wJ18d1, wQ19_wJ18d2])
private abbrev wQ20_wJ19v : LeanSuffixReflective.QInterval := ⟨(498097508630342576598485793273 / 633825300114114700748351602688 : ℚ), (997214650341792731991980911511 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d0 : LeanSuffixReflective.QInterval := ⟨(2708069429197721423908411109 / 39614081257132168796771975168 : ℚ), (44118376663943623540783902137 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d1 : LeanSuffixReflective.QInterval := ⟨(-2495986045519237263152095901 / 1267650600228229401496703205376 : ℚ), (-2437785676569258913051496381 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ19 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ15).invPos (by norm_num [wJ15])).widenAll wQ20_wJ19v wQ20_wJ19d0 wQ20_wJ19d1 wQ20_wJ19d2 (by
    norm_num [wJ15, NearOneScalarInterval.Jet3.invPos, wQ20_wJ19v, wQ20_wJ19d0, wQ20_wJ19d1, wQ20_wJ19d2])
private abbrev wQ21_wJ20v : LeanSuffixReflective.QInterval := ⟨(62235208893479248664845698027 / 39614081257132168796771975168 : ℚ), (996791841570571614559783183707 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d0 : LeanSuffixReflective.QInterval := ⟨(105446358200247748016913314243 / 1267650600228229401496703205376 : ℚ), (54741435160636495561883137939 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d1 : LeanSuffixReflective.QInterval := ⟨(-4991369739861266087313338629 / 1267650600228229401496703205376 : ℚ), (-2437455244382433494276051405 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ20 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ18).mul (wJ19)).widenAll wQ21_wJ20v wQ21_wJ20d0 wQ21_wJ20d1 wQ21_wJ20d2 (by
    norm_num [wJ18, wJ19, wQ21_wJ20v, wQ21_wJ20d0, wQ21_wJ20d1, wQ21_wJ20d2])
private abbrev wQ22_wJ21v : LeanSuffixReflective.QInterval := ⟨(736848616289830972919665720001 / 1267650600228229401496703205376 : ℚ), (368550844930127819212204662669 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d0 : LeanSuffixReflective.QInterval := ⟨(14078201050135993947473096511 / 1267650600228229401496703205376 : ℚ), (7173105028177122233512234495 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d1 : LeanSuffixReflective.QInterval := ⟨(-614330940006399109322694387 / 1267650600228229401496703205376 : ℚ), (-601232919151289449228967231 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ21 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ16).invPos (by norm_num [wJ16])).widenAll wQ22_wJ21v wQ22_wJ21d0 wQ22_wJ21d1 wQ22_wJ21d2 (by
    norm_num [wJ16, NearOneScalarInterval.Jet3.invPos, wQ22_wJ21v, wQ22_wJ21d0, wQ22_wJ21d1, wQ22_wJ21d2])
private abbrev wQ23_wJ22v : LeanSuffixReflective.QInterval := ⟨(368264661140489328475026592395 / 316912650057057350374175801344 : ℚ), (736789166313145690125735597703 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d0 : LeanSuffixReflective.QInterval := ⟨(-10983586535435414774749567345 / 633825300114114700748351602688 : ℚ), (-20814897877365072452826103859 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d1 : LeanSuffixReflective.QInterval := ⟨(-1229260172200359466335431781 / 1267650600228229401496703205376 : ℚ), (-1203018651070444328638707149 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ22 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ18).mul (wJ21)).widenAll wQ23_wJ22v wQ23_wJ22d0 wQ23_wJ22d1 wQ23_wJ22d2 (by
    norm_num [wJ18, wJ21, wQ23_wJ22v, wQ23_wJ22d0, wQ23_wJ22d1, wQ23_wJ22d2])
private abbrev wQ24_wJ23v : LeanSuffixReflective.QInterval := ⟨(368423819172475663898392807733 / 633825300114114700748351602688 : ℚ), (737113957096587578691082805855 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d0 : LeanSuffixReflective.QInterval := ⟨(1812159008940323483876314615 / 158456325028528675187087900672 : ℚ), (7652983010856585123476982299 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d1 : LeanSuffixReflective.QInterval := ⟨(-76796882035070282189577889 / 158456325028528675187087900672 : ℚ), (-300599397305469021866221171 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ23 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ17).invPos (by norm_num [wJ17])).widenAll wQ24_wJ23v wQ24_wJ23d0 wQ24_wJ23d1 wQ24_wJ23d2 (by
    norm_num [wJ17, NearOneScalarInterval.Jet3.invPos, wQ24_wJ23v, wQ24_wJ23d0, wQ24_wJ23d1, wQ24_wJ23d2])
private abbrev wQ25_wJ24v : LeanSuffixReflective.QInterval := ⟨(1473381411834706397076700445401 / 1267650600228229401496703205376 : ℚ), (736960494208237404244176984485 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d0 : LeanSuffixReflective.QInterval := ⟨(4594176932223795726505335505 / 1267650600228229401496703205376 : ℚ), (3266731149759601773099629113 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d1 : LeanSuffixReflective.QInterval := ⟨(-1229054040084510552644110231 / 1267650600228229401496703205376 : ℚ), (-1202678557378680755528261687 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ24 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).mul (wJ23)).widenAll wQ25_wJ24v wQ25_wJ24d0 wQ25_wJ24d1 wQ25_wJ24d2 (by
    norm_num [wJ8, wJ0, wJ23, wQ25_wJ24v, wQ25_wJ24d0, wQ25_wJ24d1, wQ25_wJ24d2])
private abbrev wQ26_wJ25v : LeanSuffixReflective.QInterval := ⟨(633962134765265773219785640085 / 633825300114114700748351602688 : ℚ), (158491255323507649635108372953 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d0 : LeanSuffixReflective.QInterval := ⟨(21887151169445560951238446321 / 1267650600228229401496703205376 : ℚ), (5533285670097526062789875301 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d1 : LeanSuffixReflective.QInterval := ⟨(462160607544868253485351 / 1267650600228229401496703205376 : ℚ), (1880937134666327896647 / 4951760157141521099596496896 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ25 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ8).invPos (by norm_num [wJ8])).widenAll wQ26_wJ25v wQ26_wJ25d0 wQ26_wJ25d1 wQ26_wJ25d2 (by
    norm_num [wJ8, NearOneScalarInterval.Jet3.invPos, wQ26_wJ25v, wQ26_wJ25d0, wQ26_wJ25d1, wQ26_wJ25d2])
private abbrev wQ27_wJ26v : LeanSuffixReflective.QInterval := ⟨(27232279750527309465302018353 / 1267650600228229401496703205376 : ℚ), (27526906754866722897226412243 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d0 : LeanSuffixReflective.QInterval := ⟨(1126361508497551642165867707873 / 1267650600228229401496703205376 : ℚ), (8805645241818499655759364881 / 9903520314283042199192993792 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d1 : LeanSuffixReflective.QInterval := ⟨(21507709917445244729117301 / 1267650600228229401496703205376 : ℚ), (5547870193707797235370891 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ26 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ0).mul (wJ12)).mul (wJ25)).widenAll wQ27_wJ26v wQ27_wJ26d0 wQ27_wJ26d1 wQ27_wJ26d2 (by
    norm_num [wJ0, wJ12, wJ25, wQ27_wJ26v, wQ27_wJ26d0, wQ27_wJ26d1, wQ27_wJ26d2])
private abbrev wQ28_wJ27v : LeanSuffixReflective.QInterval := ⟨(444721495981283128530212653 / 633825300114114700748351602688 : ℚ), (908209033183796184765241537 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d0 : LeanSuffixReflective.QInterval := ⟨(72404120647507734326917298981 / 1267650600228229401496703205376 : ℚ), (36589283320616587440510085309 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d1 : LeanSuffixReflective.QInterval := ⟨(-757325521685552529173775 / 1267650600228229401496703205376 : ℚ), (-726026544010807889526655 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ27 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ6).mul (wJ24)).widenAll wQ28_wJ27v wQ28_wJ27d0 wQ28_wJ27d1 wQ28_wJ27d2 (by
    norm_num [wJ6, wJ24, wQ28_wJ27v, wQ28_wJ27d0, wQ28_wJ27d1, wQ28_wJ27d2])
private abbrev wQ29_wJ28v : LeanSuffixReflective.QInterval := ⟨(1267451352213738472515701196869 / 1267650600228229401496703205376 : ℚ), (1267462907297039198964045094231 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d0 : LeanSuffixReflective.QInterval := ⟨(-16370051326502368350497790429 / 1267650600228229401496703205376 : ℚ), (-15473285716293887363796661535 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d1 : LeanSuffixReflective.QInterval := ⟨(-322303609395315693597171 / 1267650600228229401496703205376 : ℚ), (-295428593309613931168867 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ28 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ26).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ26]) (by norm_num [wJ26])).widenAll wQ29_wJ28v wQ29_wJ28d0 wQ29_wJ28d1 wQ29_wJ28d2 (by
    norm_num [wJ26, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ29_wJ28v, wQ29_wJ28d0, wQ29_wJ28d1, wQ29_wJ28d2])
private abbrev wQ30_wJ29v : LeanSuffixReflective.QInterval := ⟨(1267650383332593803869639879419 / 1267650600228229401496703205376 : ℚ), (316912600001055163726942825823 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d0 : LeanSuffixReflective.QInterval := ⟨(-8739077063416763944377877 / 316912650057057350374175801344 : ℚ), (-4074283828287415690619203 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d1 : LeanSuffixReflective.QInterval := ⟨(163417620322996982635 / 633825300114114700748351602688 : ℚ), (361763089924922743141 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ29 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ27).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ27]) (by norm_num [wJ27])).widenAll wQ30_wJ29v wQ30_wJ29d0 wQ30_wJ29d1 wQ30_wJ29d2 (by
    norm_num [wJ27, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ30_wJ29v, wQ30_wJ29d0, wQ30_wJ29d1, wQ30_wJ29d2])
private abbrev wQ31_wJ30v : LeanSuffixReflective.QInterval := ⟨(633962134765265773219785640085 / 633825300114114700748351602688 : ℚ), (158491255323507649635108372953 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d0 : LeanSuffixReflective.QInterval := ⟨(21887151169445560951238446321 / 1267650600228229401496703205376 : ℚ), (5533285670097526062789875301 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d1 : LeanSuffixReflective.QInterval := ⟨(462160607544868253485351 / 1267650600228229401496703205376 : ℚ), (1880937134666327896647 / 4951760157141521099596496896 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ30 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ8).invPos (by norm_num [wJ8])).widenAll wQ31_wJ30v wQ31_wJ30d0 wQ31_wJ30d1 wQ31_wJ30d2 (by
    norm_num [wJ8, NearOneScalarInterval.Jet3.invPos, wQ31_wJ30v, wQ31_wJ30d0, wQ31_wJ30d1, wQ31_wJ30d2])
private abbrev wQ32_wJ31v : LeanSuffixReflective.QInterval := ⟨(1474050145998383488831376718519 / 1267650600228229401496703205376 : ℚ), (1474603957268875566328772926803 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d0 : LeanSuffixReflective.QInterval := ⟨(29721412231312876847311481333 / 633825300114114700748351602688 : ℚ), (61984761731348057806692095751 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d1 : LeanSuffixReflective.QInterval := ⟨(-1228525282928108215353133665 / 1267650600228229401496703205376 : ℚ), (-601063653693248260845743623 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ31 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ6).mul (wJ12)).mul (wJ30)).mul (wJ28)).add ((wJ24).mul (wJ29))).widenAll wQ32_wJ31v wQ32_wJ31d0 wQ32_wJ31d1 wQ32_wJ31d2 (by
    norm_num [wJ6, wJ12, wJ30, wJ28, wJ24, wJ29, wQ32_wJ31v, wQ32_wJ31d0, wQ32_wJ31d1, wQ32_wJ31d2])
private abbrev wQ33_wJ32v : LeanSuffixReflective.QInterval := ⟨(459879320674525011156397175781 / 316912650057057350374175801344 : ℚ), (459973250279428314732602673427 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d0 : LeanSuffixReflective.QInterval := ⟨(-369337829072752745160887580927 / 316912650057057350374175801344 : ℚ), (-369307099578212882950064812285 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d2 : LeanSuffixReflective.QInterval := ⟨(765248518525921256689725867 / 633825300114114700748351602688 : ℚ), (390554085020881483114471635 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ32 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ4)).widenAll wQ33_wJ32v wQ33_wJ32d0 wQ33_wJ32d1 wQ33_wJ32d2 (by
    norm_num [wJ4, wQ33_wJ32v, wQ33_wJ32d0, wQ33_wJ32d1, wQ33_wJ32d2])
private abbrev wQ34_wJ33v : LeanSuffixReflective.QInterval := ⟨(765248518525921256689725867 / 1267650600228229401496703205376 : ℚ), (390554085020881483114471635 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d0 : LeanSuffixReflective.QInterval := ⟨(15572955273752212635734508325 / 316912650057057350374175801344 : ℚ), (31467002408818903882515088987 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ33 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ34_wJ33v wQ34_wJ33d0 wQ34_wJ33d1 wQ34_wJ33d2 (by
    norm_num [wJ0, wQ34_wJ33v, wQ34_wJ33d0, wQ34_wJ33d1, wQ34_wJ33d2])
private abbrev wQ35_wJ34v : LeanSuffixReflective.QInterval := ⟨(20854424470945095679132787043 / 9903520314283042199192993792 : ℚ), (1335228435561214119275750231133 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d0 : LeanSuffixReflective.QInterval := ⟨(-4288513485571639042279763367245 / 1267650600228229401496703205376 : ℚ), (-66988765691323023508204488303 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d2 : LeanSuffixReflective.QInterval := ⟨(1110469931646865038130121337 / 316912650057057350374175801344 : ℚ), (2267431506626442774834574865 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ34 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ32).mul (wJ32)).widenAll wQ35_wJ34v wQ35_wJ34d0 wQ35_wJ34d1 wQ35_wJ34d2 (by
    norm_num [wJ32, wQ35_wJ34v, wQ35_wJ34d0, wQ35_wJ34d1, wQ35_wJ34d2])
private abbrev wQ36_wJ35v : LeanSuffixReflective.QInterval := ⟨(1266516884474916180109285917943 / 1267650600228229401496703205376 : ℚ), (1266540130296582536458573084039 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d0 : LeanSuffixReflective.QInterval := ⟨(-45225943226115753664505665947 / 633825300114114700748351602688 : ℚ), (-89482788294666845137378953555 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d2 : LeanSuffixReflective.QInterval := ⟨(-240653841522318186026349 / 316912650057057350374175801344 : ℚ), (-461961123199629407462133 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ35 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ33).mul (wJ32)).neg)).widenAll wQ36_wJ35v wQ36_wJ35d0 wQ36_wJ35d1 wQ36_wJ35d2 (by
    norm_num [wJ33, wJ32, wQ36_wJ35v, wQ36_wJ35d0, wQ36_wJ35d1, wQ36_wJ35d2])
private abbrev wQ37_wJ36v : LeanSuffixReflective.QInterval := ⟨(229836816754052237450273879811 / 79228162514264337593543950336 : ℚ), (28735738855299314115859363461 / 9903520314283042199192993792 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d0 : LeanSuffixReflective.QInterval := ⟨(-1542346240809582115040385387639 / 633825300114114700748351602688 : ℚ), (-3082985822728982534850018013009 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d2 : LeanSuffixReflective.QInterval := ⟨(1529099878186050042233883065 / 633825300114114700748351602688 : ℚ), (3121751230026429999327388971 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ36 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ32)).add (((wJ33).mul (wJ34)).neg)).widenAll wQ37_wJ36v wQ37_wJ36d0 wQ37_wJ36d1 wQ37_wJ36d2 (by
    norm_num [wJ32, wJ33, wJ34, wQ37_wJ36v, wQ37_wJ36d0, wQ37_wJ36d1, wQ37_wJ36d2])
private abbrev wQ38_wJ37v : LeanSuffixReflective.QInterval := ⟨(3739681351120967849376727572409 / 1267650600228229401496703205376 : ℚ), (233819316225227066201962547105 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d0 : LeanSuffixReflective.QInterval := ⟨(-17166127286796114265392736217 / 39614081257132168796771975168 : ℚ), (-547607064205138832505301773831 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d2 : LeanSuffixReflective.QInterval := ⟨(1529099878186050042233883065 / 633825300114114700748351602688 : ℚ), (3121751230026429999327388971 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ37 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ32)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ0))).add (((wJ33).mul (wJ34)).neg)).add (((wJ0).mul (wJ0)).mul ((wJ0).mul (wJ0)))).widenAll wQ38_wJ37v wQ38_wJ37d0 wQ38_wJ37d1 wQ38_wJ37d2 (by
    norm_num [wJ32, wJ0, wJ33, wJ34, wQ38_wJ37v, wQ38_wJ37d0, wQ38_wJ37d1, wQ38_wJ37d2])
private abbrev wQ38_root38 : LeanSuffixReflective.QInterval := ⟨(67471380357806603769816774893 / 39614081257132168796771975168 : ℚ), (269914344220242689935791971495 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38v : LeanSuffixReflective.QInterval := ⟨(67471380357806603769816774893 / 39614081257132168796771975168 : ℚ), (269914344220242689935791971495 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d0 : LeanSuffixReflective.QInterval := ⟨(-905548826569899344485896485795 / 1267650600228229401496703205376 : ℚ), (-904951170705606858024293325181 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d2 : LeanSuffixReflective.QInterval := ⟨(897675697817770808558756745 / 1267650600228229401496703205376 : ℚ), (458213935430887163597218049 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ38 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ36).sqrt wQ38_root38 (by norm_num [wQ38_root38]) (by norm_num [wJ36, wQ38_root38]) (by norm_num [wJ36, wQ38_root38])).widenAll wQ39_wJ38v wQ39_wJ38d0 wQ39_wJ38d1 wQ39_wJ38d2 (by
    norm_num [wJ36, wQ38_root38, NearOneScalarInterval.Jet3.sqrt, wQ39_wJ38v, wQ39_wJ38d0, wQ39_wJ38d1, wQ39_wJ38d2])
private abbrev wQ39_root39 : LeanSuffixReflective.QInterval := ⟨(2177294033751714206767581071475 / 1267650600228229401496703205376 : ℚ), (2177709609871300607270863010669 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39v : LeanSuffixReflective.QInterval := ⟨(2177294033751714206767581071475 / 1267650600228229401496703205376 : ℚ), (2177709609871300607270863010669 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d0 : LeanSuffixReflective.QInterval := ⟨(-159909695035210759229672941877 / 1267650600228229401496703205376 : ℚ), (-159381769837964638133739309769 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d2 : LeanSuffixReflective.QInterval := ⟨(890093137122177297052423745 / 1267650600228229401496703205376 : ℚ), (454381649786567533113667847 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ39 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ37).sqrt wQ39_root39 (by norm_num [wQ39_root39]) (by norm_num [wJ37, wQ39_root39]) (by norm_num [wJ37, wQ39_root39])).widenAll wQ40_wJ39v wQ40_wJ39d0 wQ40_wJ39d1 wQ40_wJ39d2 (by
    norm_num [wJ37, wQ39_root39, NearOneScalarInterval.Jet3.sqrt, wQ40_wJ39v, wQ40_wJ39d0, wQ40_wJ39d1, wQ40_wJ39d2])
private abbrev wQ41_wJ40v : LeanSuffixReflective.QInterval := ⟨(1267669402224536844145402406771 / 1267650600228229401496703205376 : ℚ), (1267669989745075626334530662483 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d0 : LeanSuffixReflective.QInterval := ⟨(2295745555577763770069177601 / 1267650600228229401496703205376 : ℚ), (1171662255062644449343414905 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ40 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0))).widenAll wQ41_wJ40v wQ41_wJ40d0 wQ41_wJ40d1 wQ41_wJ40d2 (by
    norm_num [wJ0, wQ41_wJ40v, wQ41_wJ40d0, wQ41_wJ40d1, wQ41_wJ40d2])
private abbrev wQ42_wJ41v : LeanSuffixReflective.QInterval := ⟨(542051278635379565962209895213 / 158456325028528675187087900672 : ℚ), (2168528695858339984595095552443 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d0 : LeanSuffixReflective.QInterval := ⟨(-530781109736477736880499650743 / 633825300114114700748351602688 : ℚ), (-1060354746317112291369515763473 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d2 : LeanSuffixReflective.QInterval := ⟨(223472768676171374827492895 / 158456325028528675187087900672 : ℚ), (1825205187778203535485551431 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ41 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ39).add ((wJ40).mul (wJ38))).widenAll wQ42_wJ41v wQ42_wJ41d0 wQ42_wJ41d1 wQ42_wJ41d2 (by
    norm_num [wJ39, wJ40, wJ38, wQ42_wJ41v, wQ42_wJ41d0, wQ42_wJ41d1, wQ42_wJ41d2])
private abbrev wQ43_wJ42v : LeanSuffixReflective.QInterval := ⟨(12685800680219798361969870951211 / 1267650600228229401496703205376 : ℚ), (793216927161228606344019371915 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d0 : LeanSuffixReflective.QInterval := ⟨(-2340194189460207532949205984815 / 316912650057057350374175801344 : ℚ), (-9347684183529993139392960525541 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d2 : LeanSuffixReflective.QInterval := ⟨(7845192840269694926117181005 / 633825300114114700748351602688 : ℚ), (16023599542865006548415094251 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ42 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ38).mul (wJ39)).mul (wJ41)).widenAll wQ43_wJ42v wQ43_wJ42d0 wQ43_wJ42d1 wQ43_wJ42d2 (by
    norm_num [wJ38, wJ39, wJ41, wQ43_wJ42v, wQ43_wJ42d0, wQ43_wJ42d1, wQ43_wJ42d2])
private abbrev wQ44_wJ43v : LeanSuffixReflective.QInterval := ⟨(4336474547412629947563743873215 / 1267650600228229401496703205376 : ℚ), (4337123729749687324870150217443 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d0 : LeanSuffixReflective.QInterval := ⟨(-1053725114098451735121145760889 / 1267650600228229401496703205376 : ℚ), (-131544146932301028127356246269 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d2 : LeanSuffixReflective.QInterval := ⟨(1787808666079946987769741135 / 1267650600228229401496703205376 : ℚ), (912616552722367760285834591 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ43 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ40).mul (wJ41)).widenAll wQ44_wJ43v wQ44_wJ43d0 wQ44_wJ43d1 wQ44_wJ43d2 (by
    norm_num [wJ40, wJ41, wQ44_wJ43v, wQ44_wJ43d0, wQ44_wJ43d1, wQ44_wJ43d2])
private abbrev wQ45_wJ44v : LeanSuffixReflective.QInterval := ⟨(4336283285285222962646936082875 / 1267650600228229401496703205376 : ℚ), (1084312353401385016759293934317 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d0 : LeanSuffixReflective.QInterval := ⟨(-1064290081660033823918035480637 / 1267650600228229401496703205376 : ℚ), (-524875641451722935063652282227 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d2 : LeanSuffixReflective.QInterval := ⟨(111716513982624357070011623 / 79228162514264337593543950336 : ℚ), (1825551857701283402006839791 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ44 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ38).add (wJ39)).mul (((wJ35).mul (wJ35)).add ((wJ33).mul ((wJ38).mul (wJ39))))).widenAll wQ45_wJ44v wQ45_wJ44d0 wQ45_wJ44d1 wQ45_wJ44d2 (by
    norm_num [wJ38, wJ39, wJ35, wJ33, wQ45_wJ44v, wQ45_wJ44d0, wQ45_wJ44d1, wQ45_wJ44d2])
private abbrev wQ46_wJ45v : LeanSuffixReflective.QInterval := ⟨(2530787133687489336489251777251 / 1267650600228229401496703205376 : ℚ), (2530880621848264998800490418033 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d0 : LeanSuffixReflective.QInterval := ⟨(-22450107731763716674259945067 / 79228162514264337593543950336 : ℚ), (-88818617721138980607580770397 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d2 : LeanSuffixReflective.QInterval := ⟨(-480889732202606932057249 / 158456325028528675187087900672 : ℚ), (-3692411151209088156189587 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ45 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ35).mul (wJ35)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).widenAll wQ46_wJ45v wQ46_wJ45d0 wQ46_wJ45d1 wQ46_wJ45d2 (by
    norm_num [wJ35, wJ0, wQ46_wJ45v, wQ46_wJ45d0, wQ46_wJ45d1, wQ46_wJ45d2])
private abbrev wQ47_wJ46v : LeanSuffixReflective.QInterval := ⟨(63307794076974379419592960777 / 633825300114114700748351602688 : ℚ), (31668045336006886117483015505 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d0 : LeanSuffixReflective.QInterval := ⟨(46628265005748407380321651939 / 633825300114114700748351602688 : ℚ), (46735324039855052753210656997 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d2 : LeanSuffixReflective.QInterval := ⟨(-160001276879805505015795909 / 1267650600228229401496703205376 : ℚ), (-156534056390918562086840593 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ46 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ42).invPos (by norm_num [wJ42])).widenAll wQ47_wJ46v wQ47_wJ46d0 wQ47_wJ46d1 wQ47_wJ46d2 (by
    norm_num [wJ42, NearOneScalarInterval.Jet3.invPos, wQ47_wJ46v, wQ47_wJ46d0, wQ47_wJ46d1, wQ47_wJ46d2])
private abbrev wQ48_wJ47v : LeanSuffixReflective.QInterval := ⟨(7899384434248771696456009009 / 39614081257132168796771975168 : ℚ), (252902628715774526952671056839 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d0 : LeanSuffixReflective.QInterval := ⟨(150287121992828746691801557275 / 1267650600228229401496703205376 : ℚ), (151129787509991945316974906425 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d2 : LeanSuffixReflective.QInterval := ⟨(-319829023757805653152533889 / 1267650600228229401496703205376 : ℚ), (-312879505311839749084004817 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ47 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ45).mul (wJ46)).widenAll wQ48_wJ47v wQ48_wJ47d0 wQ48_wJ47d1 wQ48_wJ47d2 (by
    norm_num [wJ45, wJ46, wQ48_wJ47v, wQ48_wJ47d0, wQ48_wJ47d1, wQ48_wJ47d2])
private abbrev wQ49_wJ48v : LeanSuffixReflective.QInterval := ⟨(370507770676796685894056332277 / 1267650600228229401496703205376 : ℚ), (370563236723659429011201179815 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d0 : LeanSuffixReflective.QInterval := ⟨(2809357748498029880185676991 / 39614081257132168796771975168 : ℚ), (22510900538451547674008482929 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d2 : LeanSuffixReflective.QInterval := ⟨(-155971003619133949345611925 / 1267650600228229401496703205376 : ℚ), (-152727255328767931695356381 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ48 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ43).invPos (by norm_num [wJ43])).widenAll wQ49_wJ48v wQ49_wJ48d0 wQ49_wJ48d1 wQ49_wJ48d2 (by
    norm_num [wJ43, NearOneScalarInterval.Jet3.invPos, wQ49_wJ48v, wQ49_wJ48d0, wQ49_wJ48d1, wQ49_wJ48d2])
private abbrev wQ50_wJ49v : LeanSuffixReflective.QInterval := ⟨(23115505437560325195842642047 / 39614081257132168796771975168 : ℚ), (369917118654157967288315974101 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d0 : LeanSuffixReflective.QInterval := ⟨(18618973716286083545897808837 / 316912650057057350374175801344 : ℚ), (18983475338026327976164821119 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d2 : LeanSuffixReflective.QInterval := ⟨(-312522702236674857950219203 / 1267650600228229401496703205376 : ℚ), (-305989867952313251748705911 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ49 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ45).mul (wJ48)).widenAll wQ50_wJ49v wQ50_wJ49d0 wQ50_wJ49d1 wQ50_wJ49d2 (by
    norm_num [wJ45, wJ48, wQ50_wJ49v, wQ50_wJ49d0, wQ50_wJ49d1, wQ50_wJ49d2])
private abbrev wQ51_wJ50v : LeanSuffixReflective.QInterval := ⟨(370497034184425279355003608117 / 1267650600228229401496703205376 : ℚ), (370579581299954776701616688253 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d0 : LeanSuffixReflective.QInterval := ⟨(44835989340039631804679614869 / 633825300114114700748351602688 : ℚ), (90954429610640099318152648033 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d2 : LeanSuffixReflective.QInterval := ⟨(-78006001748545588882811509 / 633825300114114700748351602688 : ℚ), (-76344490533833167211381403 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ50 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ44).invPos (by norm_num [wJ44])).widenAll wQ51_wJ50v wQ51_wJ50d0 wQ51_wJ50d1 wQ51_wJ50d2 (by
    norm_num [wJ44, NearOneScalarInterval.Jet3.invPos, wQ51_wJ50v, wQ51_wJ50d0, wQ51_wJ50d1, wQ51_wJ50d2])
private abbrev wQ52_wJ51v : LeanSuffixReflective.QInterval := ⟨(740336855100085231059584872831 / 1267650600228229401496703205376 : ℚ), (370257782888046048660324583047 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d0 : LeanSuffixReflective.QInterval := ⟨(31742593944272278319270430235 / 316912650057057350374175801344 : ℚ), (130128411886882179390247010013 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d2 : LeanSuffixReflective.QInterval := ⟨(-19519742141743701465596021 / 79228162514264337593543950336 : ℚ), (-152823593264865645015304269 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ51 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ35).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).mul (wJ50)).widenAll wQ52_wJ51v wQ52_wJ51d0 wQ52_wJ51d1 wQ52_wJ51d2 (by
    norm_num [wJ35, wJ0, wJ50, wQ52_wJ51v, wQ52_wJ51d0, wQ52_wJ51d1, wQ52_wJ51d2])
private abbrev wQ53_wJ52v : LeanSuffixReflective.QInterval := ⟨(1268762043791456975336366644875 / 1267650600228229401496703205376 : ℚ), (1268785330821080149808502730209 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d0 : LeanSuffixReflective.QInterval := ⟨(89639769514696845175364736973 / 1267650600228229401496703205376 : ℚ), (45306946982892067925420136285 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d2 : LeanSuffixReflective.QInterval := ⟨(462771549675026007380927 / 633825300114114700748351602688 : ℚ), (964339497316210011687767 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ52 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ35).invPos (by norm_num [wJ35])).widenAll wQ53_wJ52v wQ53_wJ52d0 wQ53_wJ52d1 wQ53_wJ52d2 (by
    norm_num [wJ35, NearOneScalarInterval.Jet3.invPos, wQ53_wJ52v, wQ53_wJ52d0, wQ53_wJ52d1, wQ53_wJ52d2])
private abbrev wQ54_wJ53v : LeanSuffixReflective.QInterval := ⟨(26771281694392968964826702711 / 633825300114114700748351602688 : ℚ), (54105866553795219810403204149 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d0 : LeanSuffixReflective.QInterval := ⟨(2179012951779152966790005549425 / 1267650600228229401496703205376 : ℚ), (2179603616237820138753072177425 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d2 : LeanSuffixReflective.QInterval := ⟨(21927635555215856145103973 / 1267650600228229401496703205376 : ℚ), (22619627441549281516521031 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ53 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ0).mul (wJ39)).mul (wJ52)).widenAll wQ54_wJ53v wQ54_wJ53d0 wQ54_wJ53d1 wQ54_wJ53d2 (by
    norm_num [wJ0, wJ39, wJ52, wQ54_wJ53v, wQ54_wJ53d0, wQ54_wJ53d1, wQ54_wJ53d2])
private abbrev wQ55_wJ54v : LeanSuffixReflective.QInterval := ⟨(446922583773067263282251325 / 1267650600228229401496703205376 : ℚ), (456295100847713160615990337 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d0 : LeanSuffixReflective.QInterval := ⟨(9114123168398226880075884041 / 316912650057057350374175801344 : ℚ), (18421974691353791727949752327 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d2 : LeanSuffixReflective.QInterval := ⟨(-192444575011813649050195 / 1267650600228229401496703205376 : ℚ), (-92255727501482603381773 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ54 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ33).mul (wJ51)).widenAll wQ55_wJ54v wQ55_wJ54d0 wQ55_wJ54d1 wQ55_wJ54d2 (by
    norm_num [wJ33, wJ51, wQ55_wJ54v, wQ55_wJ54d0, wQ55_wJ54d1, wQ55_wJ54d2])
private abbrev wQ56_wJ55v : LeanSuffixReflective.QInterval := ⟨(1266880817977765423649606891669 / 1267650600228229401496703205376 : ℚ), (1266925032035329535843174243653 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d0 : LeanSuffixReflective.QInterval := ⟨(-62416968555077159447723342535 / 1267650600228229401496703205376 : ℚ), (-58659590310811285664201321041 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d2 : LeanSuffixReflective.QInterval := ⟨(-80969342557783038691629 / 158456325028528675187087900672 : ℚ), (-295086310029297044263975 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ55 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ53).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ53]) (by norm_num [wJ53])).widenAll wQ56_wJ55v wQ56_wJ55d0 wQ56_wJ55d1 wQ56_wJ55d2 (by
    norm_num [wJ53, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ56_wJ55v, wQ56_wJ55d0, wQ56_wJ55d1, wQ56_wJ55d2])
private abbrev wQ57_wJ56v : LeanSuffixReflective.QInterval := ⟨(158456318184988776123050488305 / 158456325028528675187087900672 : ℚ), (316912637418877614172832920231 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d0 : LeanSuffixReflective.QInterval := ⟨(-4420939889671789478876303 / 633825300114114700748351602688 : ℚ), (-8246923383010152445978095 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d2 : LeanSuffixReflective.QInterval := ⟨(20869382929332263669 / 633825300114114700748351602688 : ℚ), (11545802125924799575 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ56 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ54).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ54]) (by norm_num [wJ54])).widenAll wQ57_wJ56v wQ57_wJ56d0 wQ57_wJ56d1 wQ57_wJ56d2 (by
    norm_num [wJ54, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ57_wJ56v, wQ57_wJ56d0, wQ57_wJ56d1, wQ57_wJ56d2])
private abbrev wQ58_wJ57v : LeanSuffixReflective.QInterval := ⟨(1268762043791456975336366644875 / 1267650600228229401496703205376 : ℚ), (1268785330821080149808502730209 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d0 : LeanSuffixReflective.QInterval := ⟨(89639769514696845175364736973 / 1267650600228229401496703205376 : ℚ), (45306946982892067925420136285 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d2 : LeanSuffixReflective.QInterval := ⟨(462771549675026007380927 / 633825300114114700748351602688 : ℚ), (964339497316210011687767 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ57 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ35).invPos (by norm_num [wJ35])).widenAll wQ58_wJ57v wQ58_wJ57d0 wQ58_wJ57d1 wQ58_wJ57d2 (by
    norm_num [wJ35, NearOneScalarInterval.Jet3.invPos, wQ58_wJ57v, wQ58_wJ57d0, wQ58_wJ57d1, wQ58_wJ57d2])
private abbrev wQ59_wJ58v : LeanSuffixReflective.QInterval := ⟨(741651553871146441926879143311 / 1267650600228229401496703205376 : ℚ), (2897882196067223248700032175 / 4951760157141521099596496896 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d0 : LeanSuffixReflective.QInterval := ⟨(58478375156973266146406739287 / 316912650057057350374175801344 : ℚ), (119106064844574841821550522909 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d2 : LeanSuffixReflective.QInterval := ⟨(-311778093466421482235719571 / 1267650600228229401496703205376 : ℚ), (-152543295596090296184423229 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ58 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ33).mul (wJ39)).mul (wJ57)).mul (wJ55)).add ((wJ51).mul (wJ56))).widenAll wQ59_wJ58v wQ59_wJ58d0 wQ59_wJ58d1 wQ59_wJ58d2 (by
    norm_num [wJ33, wJ39, wJ57, wJ55, wJ51, wJ56, wQ59_wJ58v, wQ59_wJ58d0, wQ59_wJ58d1, wQ59_wJ58d2])
private abbrev wQ60_wJ59v : LeanSuffixReflective.QInterval := ⟨(1267083742351572790802994561659 / 1267650600228229401496703205376 : ℚ), (316773841315601492244409536177 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d0 : LeanSuffixReflective.QInterval := ⟨(-45225943226115753664505665947 / 1267650600228229401496703205376 : ℚ), (-44741394147333422568689476777 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d2 : LeanSuffixReflective.QInterval := ⟨(-240653841522318186026349 / 633825300114114700748351602688 : ℚ), (-461961123199629407462133 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ59 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ5).mul (wJ4)).neg)).widenAll wQ60_wJ59v wQ60_wJ59d0 wQ60_wJ59d1 wQ60_wJ59d2 (by
    norm_num [wJ5, wJ4, wQ60_wJ59v, wQ60_wJ59d0, wQ60_wJ59d1, wQ60_wJ59d2])
private abbrev wQ61_wJ60v : LeanSuffixReflective.QInterval := ⟨(-1041769458265698568318445345 / 1267650600228229401496703205376 : ℚ), (521317010587472924696056067 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d0 : LeanSuffixReflective.QInterval := ⟨(-654023809636653546956895159 / 316912650057057350374175801344 : ℚ), (1309226282490437535216381969 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d1 : LeanSuffixReflective.QInterval := ⟨(-623790455027602718739242783 / 158456325028528675187087900672 : ℚ), (-4873804853275883737985135187 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ60 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul (wJ20)).add ((((NearOneScalarInterval.Jet3.pi).mul (NearOneScalarInterval.Jet3.rational (1 / 2 : ℚ))).add ((wJ5).mul (wJ31))).neg)).widenAll wQ61_wJ60v wQ61_wJ60d0 wQ61_wJ60d1 wQ61_wJ60d2 (by
    norm_num [wJ8, wJ20, wJ5, wJ31, wQ61_wJ60v, wQ61_wJ60d0, wQ61_wJ60d1, wQ61_wJ60d2])
private abbrev wQ62_wJ61v : LeanSuffixReflective.QInterval := ⟨(-1286733838039460818278959179 / 633825300114114700748351602688 : ℚ), (1286495510290272617699574843 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d0 : LeanSuffixReflective.QInterval := ⟨(-12219062025341216758425413313 / 1267650600228229401496703205376 : ℚ), (12219775217894824583281292185 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d1 : LeanSuffixReflective.QInterval := ⟨(-102513680572352906870161343 / 1267650600228229401496703205376 : ℚ), (102569371167048276670510923 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d2 : LeanSuffixReflective.QInterval := ⟨(3561235396064879751614939625 / 1267650600228229401496703205376 : ℚ), (460925194861144003101102539 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev wJ61 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.pi).mul ((wJ4).add ((wJ3).neg))).mul ((wJ8).add (wJ59))).add (((wJ8).mul (wJ8)).mul ((wJ58).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ59)).add (NearOneScalarInterval.Jet3.rational (1 : ℚ))).mul (wJ49))))).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul ((wJ59).mul (wJ59))).mul ((wJ31).add ((wJ8).mul (wJ22)))).neg)).widenAll wQ62_wJ61v wQ62_wJ61d0 wQ62_wJ61d1 wQ62_wJ61d2 (by
    norm_num [wJ4, wJ3, wJ8, wJ59, wJ58, wJ49, wJ31, wJ22, wQ62_wJ61v, wQ62_wJ61d0, wQ62_wJ61d1, wQ62_wJ61d2])
private abbrev wQ63_wJ62v : LeanSuffixReflective.QInterval := ⟨(-38857543919404290847439183 / 39614081257132168796771975168 : ℚ), (369183663832354963369387353 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d0 : LeanSuffixReflective.QInterval := ⟨(-23118610377483959894939051743 / 1267650600228229401496703205376 : ℚ), (-17985229788434433127878299031 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d1 : LeanSuffixReflective.QInterval := ⟨(883604715398580232263593279 / 633825300114114700748351602688 : ℚ), (931934162777268763894372935 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d2 : LeanSuffixReflective.QInterval := ⟨(-230763704690820117680289689 / 316912650057057350374175801344 : ℚ), (-445157860906380111302195247 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ62 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ3).add ((wJ4).neg)).mul (wJ20)).add ((wJ59).mul (wJ22))).add (((wJ8).mul (wJ49)).neg)).widenAll wQ63_wJ62v wQ63_wJ62d0 wQ63_wJ62d1 wQ63_wJ62d2 (by
    norm_num [wJ3, wJ4, wJ20, wJ59, wJ22, wJ8, wJ49, wQ63_wJ62v, wQ63_wJ62d0, wQ63_wJ62d1, wQ63_wJ62d2])
private abbrev wQ64_wJ63v : LeanSuffixReflective.QInterval := ⟨(466355107842817709754067070435 / 1267650600228229401496703205376 : ℚ), (58338159340389036990385035193 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d0 : LeanSuffixReflective.QInterval := ⟨(-98655674278231421182628282419 / 1267650600228229401496703205376 : ℚ), (-49289425270940882827785680407 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d1 : LeanSuffixReflective.QInterval := ⟨(-390554085020881483114471635 / 633825300114114700748351602688 : ℚ), (-765248518525921256689725867 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d2 : LeanSuffixReflective.QInterval := ⟨(765248518525921256689725867 / 1267650600228229401496703205376 : ℚ), (390554085020881483114471635 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ63 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ4).add ((wJ3).neg)).widenAll wQ64_wJ63v wQ64_wJ63d0 wQ64_wJ63d1 wQ64_wJ63d2 (by
    norm_num [wJ4, wJ3, wQ64_wJ63v, wQ64_wJ63d0, wQ64_wJ63d1, wQ64_wJ63d2])
def wholeModel : SourceJet.Model wholeBox :=
  { a := wJ3
    b := wJ4
    hFour := wJ8
    hThree := wJ59
    shapeThree := wJ35
    bSubA := wJ63
    fold := wJ60
    area := wJ61
    gap := wJ62 }
@[simp] theorem wholeA_value (s e4 e3 : ℝ) :
    wholeModel.a.value s e4 e3 = aAt s e4 := by
  simp [wholeModel, aAt, bAt, wJ0, wJ1, wJ2, wJ3, wJ4, wJ5, wJ6, wJ7, wJ8, wJ9, wJ10, wJ11, wJ12, wJ13, wJ14, wJ15, wJ16, wJ17, wJ18, wJ19, wJ20, wJ21, wJ22, wJ23, wJ24, wJ25, wJ26, wJ27, wJ28, wJ29, wJ30, wJ31, wJ32, wJ33, wJ34, wJ35, wJ36, wJ37, wJ38, wJ39, wJ40, wJ41, wJ42, wJ43, wJ44, wJ45, wJ46, wJ47, wJ48, wJ49, wJ50, wJ51, wJ52, wJ53, wJ54, wJ55, wJ56, wJ57, wJ58, wJ59, wJ60, wJ61, wJ62, wJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem wholeB_value (s e4 e3 : ℝ) :
    wholeModel.b.value s e4 e3 = bAt s e3 := by
  simp [wholeModel, aAt, bAt, wJ0, wJ1, wJ2, wJ3, wJ4, wJ5, wJ6, wJ7, wJ8, wJ9, wJ10, wJ11, wJ12, wJ13, wJ14, wJ15, wJ16, wJ17, wJ18, wJ19, wJ20, wJ21, wJ22, wJ23, wJ24, wJ25, wJ26, wJ27, wJ28, wJ29, wJ30, wJ31, wJ32, wJ33, wJ34, wJ35, wJ36, wJ37, wJ38, wJ39, wJ40, wJ41, wJ42, wJ43, wJ44, wJ45, wJ46, wJ47, wJ48, wJ49, wJ50, wJ51, wJ52, wJ53, wJ54, wJ55, wJ56, wJ57, wJ58, wJ59, wJ60, wJ61, wJ62, wJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem wholeFold_value (s e4 e3 : ℝ) :
    wholeModel.fold.value s e4 e3 = F s (aAt s e4) := by
  simp [wholeModel, aAt, bAt, wJ0, wJ1, wJ2, wJ3, wJ4, wJ5, wJ6, wJ7, wJ8, wJ9, wJ10, wJ11, wJ12, wJ13, wJ14, wJ15, wJ16, wJ17, wJ18, wJ19, wJ20, wJ21, wJ22, wJ23, wJ24, wJ25, wJ26, wJ27, wJ28, wJ29, wJ30, wJ31, wJ32, wJ33, wJ34, wJ35, wJ36, wJ37, wJ38, wJ39, wJ40, wJ41, wJ42, wJ43, wJ44, wJ45, wJ46, wJ47, wJ48, wJ49, wJ50, wJ51, wJ52, wJ53, wJ54, wJ55, wJ56, wJ57, wJ58, wJ59, wJ60, wJ61, wJ62, wJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem wholeArea_value (s e4 e3 : ℝ) :
    wholeModel.area.value s e4 e3 = E s (aAt s e4) (bAt s e3) := by
  simp [wholeModel, aAt, bAt, wJ0, wJ1, wJ2, wJ3, wJ4, wJ5, wJ6, wJ7, wJ8, wJ9, wJ10, wJ11, wJ12, wJ13, wJ14, wJ15, wJ16, wJ17, wJ18, wJ19, wJ20, wJ21, wJ22, wJ23, wJ24, wJ25, wJ26, wJ27, wJ28, wJ29, wJ30, wJ31, wJ32, wJ33, wJ34, wJ35, wJ36, wJ37, wJ38, wJ39, wJ40, wJ41, wJ42, wJ43, wJ44, wJ45, wJ46, wJ47, wJ48, wJ49, wJ50, wJ51, wJ52, wJ53, wJ54, wJ55, wJ56, wJ57, wJ58, wJ59, wJ60, wJ61, wJ62, wJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem wholeGap_value (s e4 e3 : ℝ) :
    wholeModel.gap.value s e4 e3 = J s (aAt s e4) (bAt s e3) := by
  simp [wholeModel, aAt, bAt, wJ0, wJ1, wJ2, wJ3, wJ4, wJ5, wJ6, wJ7, wJ8, wJ9, wJ10, wJ11, wJ12, wJ13, wJ14, wJ15, wJ16, wJ17, wJ18, wJ19, wJ20, wJ21, wJ22, wJ23, wJ24, wJ25, wJ26, wJ27, wJ28, wJ29, wJ30, wJ31, wJ32, wJ33, wJ34, wJ35, wJ36, wJ37, wJ38, wJ39, wJ40, wJ41, wJ42, wJ43, wJ44, wJ45, wJ46, wJ47, wJ48, wJ49, wJ50, wJ51, wJ52, wJ53, wJ54, wJ55, wJ56, wJ57, wJ58, wJ59, wJ60, wJ61, wJ62, wJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem wholeHFour_value (s e4 e3 : ℝ) :
    wholeModel.hFour.value s e4 e3 = hFour s (aAt s e4) := by
  simp [wholeModel, aAt, bAt, wJ0, wJ1, wJ2, wJ3, wJ4, wJ5, wJ6, wJ7, wJ8, wJ9, wJ10, wJ11, wJ12, wJ13, wJ14, wJ15, wJ16, wJ17, wJ18, wJ19, wJ20, wJ21, wJ22, wJ23, wJ24, wJ25, wJ26, wJ27, wJ28, wJ29, wJ30, wJ31, wJ32, wJ33, wJ34, wJ35, wJ36, wJ37, wJ38, wJ39, wJ40, wJ41, wJ42, wJ43, wJ44, wJ45, wJ46, wJ47, wJ48, wJ49, wJ50, wJ51, wJ52, wJ53, wJ54, wJ55, wJ56, wJ57, wJ58, wJ59, wJ60, wJ61, wJ62, wJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem wholeShape_value (s e4 e3 : ℝ) :
    wholeModel.shapeThree.value s e4 e3 = xCoord s (2 * bAt s e3) := by
  simp [wholeModel, aAt, bAt, wJ0, wJ1, wJ2, wJ3, wJ4, wJ5, wJ6, wJ7, wJ8, wJ9, wJ10, wJ11, wJ12, wJ13, wJ14, wJ15, wJ16, wJ17, wJ18, wJ19, wJ20, wJ21, wJ22, wJ23, wJ24, wJ25, wJ26, wJ27, wJ28, wJ29, wJ30, wJ31, wJ32, wJ33, wJ34, wJ35, wJ36, wJ37, wJ38, wJ39, wJ40, wJ41, wJ42, wJ43, wJ44, wJ45, wJ46, wJ47, wJ48, wJ49, wJ50, wJ51, wJ52, wJ53, wJ54, wJ55, wJ56, wJ57, wJ58, wJ59, wJ60, wJ61, wJ62, wJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem wholeBSubA_value (s e4 e3 : ℝ) :
    wholeModel.bSubA.value s e4 e3 = bAt s e3 - aAt s e4 := by
  simp [wholeModel, aAt, bAt, wJ0, wJ1, wJ2, wJ3, wJ4, wJ5, wJ6, wJ7, wJ8, wJ9, wJ10, wJ11, wJ12, wJ13, wJ14, wJ15, wJ16, wJ17, wJ18, wJ19, wJ20, wJ21, wJ22, wJ23, wJ24, wJ25, wJ26, wJ27, wJ28, wJ29, wJ30, wJ31, wJ32, wJ33, wJ34, wJ35, wJ36, wJ37, wJ38, wJ39, wJ40, wJ41, wJ42, wJ43, wJ44, wJ45, wJ46, wJ47, wJ48, wJ49, wJ50, wJ51, wJ52, wJ53, wJ54, wJ55, wJ56, wJ57, wJ58, wJ59, wJ60, wJ61, wJ62, wJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring

@[simp] private abbrev cJ0 : NearOneScalarInterval.Jet3 centerBox := NearOneScalarInterval.Jet3.tVar centerBox
@[simp] private abbrev cJ1 : NearOneScalarInterval.Jet3 centerBox := NearOneScalarInterval.Jet3.e4Var centerBox
@[simp] private abbrev cJ2 : NearOneScalarInterval.Jet3 centerBox := NearOneScalarInterval.Jet3.e3Var centerBox
private abbrev cQ4_cJ3v : LeanSuffixReflective.QInterval := ⟨(226661189835494161525213086609 / 633825300114114700748351602688 : ℚ), (453322379670988323050426173219 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d0 : LeanSuffixReflective.QInterval := ⟨(-160006916560227258672963142899 / 316912650057057350374175801344 : ℚ), (-640027666240909034691852571595 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d1 : LeanSuffixReflective.QInterval := ⟨(96644751424660417504606049 / 158456325028528675187087900672 : ℚ), (773158011397283340036848393 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ3 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (491917184095198310245273393110183773 / 1329227995784915872903807060280344576 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-671117650156227431961044002113308227 / 1329227995784915872903807060280344576 : ℚ)).mul (cJ0))).add (((cJ0).mul (cJ0)).mul (cJ1))).widenAll cQ4_cJ3v cQ4_cJ3d0 cQ4_cJ3d1 cQ4_cJ3d2 (by
    norm_num [cJ0, cJ1, cQ4_cJ3v, cQ4_cJ3d0, cQ4_cJ3d1, cQ4_cJ3d2])
private abbrev cQ5_cJ4v : LeanSuffixReflective.QInterval := ⟨(919852570953953325888999849207 / 1267650600228229401496703205376 : ℚ), (114981571369244165736124981151 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d0 : LeanSuffixReflective.QInterval := ⟨(-184661232162741407027738098303 / 316912650057057350374175801344 : ℚ), (-738644928650965628110952393211 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d2 : LeanSuffixReflective.QInterval := ⟨(96644751424660417504606049 / 158456325028528675187087900672 : ℚ), (773158011397283340036848393 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ4 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (122957918479022181365483813559522903 / 166153499473114484112975882535043072 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-96815668088139366807758752083030455 / 166153499473114484112975882535043072 : ℚ)).mul (cJ0))).add (((cJ0).mul (cJ0)).mul (cJ2))).widenAll cQ5_cJ4v cQ5_cJ4d0 cQ5_cJ4d1 cQ5_cJ4d2 (by
    norm_num [cJ0, cJ2, cQ5_cJ4v, cQ5_cJ4d0, cQ5_cJ4d1, cQ5_cJ4d2])
private abbrev cQ6_cJ5v : LeanSuffixReflective.QInterval := ⟨(96644751424660417504606049 / 158456325028528675187087900672 : ℚ), (773158011397283340036848393 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d0 : LeanSuffixReflective.QInterval := ⟨(62612912956323329153984105637 / 1267650600228229401496703205376 : ℚ), (31306456478161664576992052819 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ5 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ6_cJ5v cQ6_cJ5d0 cQ6_cJ5d1 cQ6_cJ5d2 (by
    norm_num [cJ0, cQ6_cJ5v, cQ6_cJ5d0, cQ6_cJ5d1, cQ6_cJ5d2])
private abbrev cQ7_cJ6v : LeanSuffixReflective.QInterval := ⟨(96644751424660417504606049 / 158456325028528675187087900672 : ℚ), (773158011397283340036848393 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d0 : LeanSuffixReflective.QInterval := ⟨(62612912956323329153984105637 / 1267650600228229401496703205376 : ℚ), (31306456478161664576992052819 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ6 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ7_cJ6v cQ7_cJ6d0 cQ7_cJ6d1 cQ7_cJ6d2 (by
    norm_num [cJ0, cQ7_cJ6v, cQ7_cJ6d0, cQ7_cJ6d1, cQ7_cJ6d2])
private abbrev cQ8_cJ7v : LeanSuffixReflective.QInterval := ⟨(2532997606378694243638287345 / 19807040628566084398385987584 : ℚ), (81055923404118215796425195041 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d0 : LeanSuffixReflective.QInterval := ⟨(-457758414918686579207999216805 / 1267650600228229401496703205376 : ℚ), (-228879207459343289603999608401 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d1 : LeanSuffixReflective.QInterval := ⟨(552975448479577838780816971 / 1267650600228229401496703205376 : ℚ), (552975448479577838780816973 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ7 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ3).mul (cJ3)).widenAll cQ8_cJ7v cQ8_cJ7d0 cQ8_cJ7d1 cQ8_cJ7d2 (by
    norm_num [cJ3, cQ8_cJ7v, cQ8_cJ7d0, cQ8_cJ7d1, cQ8_cJ7d2])
private abbrev cQ9_cJ8v : LeanSuffixReflective.QInterval := ⟨(1267374112503989612577312796889 / 1267650600228229401496703205376 : ℚ), (1267374112503989612577312796891 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d0 : LeanSuffixReflective.QInterval := ⟨(-5500133904563630082558678601 / 316912650057057350374175801344 : ℚ), (-11000267809127260165117357201 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d1 : LeanSuffixReflective.QInterval := ⟨(-471559994907254301558345 / 1267650600228229401496703205376 : ℚ), (-58944999363406787694793 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ8 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ6).mul (cJ3)).neg)).widenAll cQ9_cJ8v cQ9_cJ8d0 cQ9_cJ8d1 cQ9_cJ8d2 (by
    norm_num [cJ6, cJ3, cQ9_cJ8v, cQ9_cJ8d0, cQ9_cJ8d1, cQ9_cJ8d2])
private abbrev cQ10_cJ9v : LeanSuffixReflective.QInterval := ⟨(906545885036170589534326786835 / 1267650600228229401496703205376 : ℚ), (453272942518085294767163393419 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d0 : LeanSuffixReflective.QInterval := ⟨(-1287783310022198891732014447343 / 1267650600228229401496703205376 : ℚ), (-1287783310022198891732014447339 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d1 : LeanSuffixReflective.QInterval := ⟨(1545978755255687262558697713 / 1267650600228229401496703205376 : ℚ), (386494688813921815639674429 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ9 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ3)).add (((cJ6).mul (cJ7)).neg)).widenAll cQ10_cJ9v cQ10_cJ9d0 cQ10_cJ9d1 cQ10_cJ9d2 (by
    norm_num [cJ3, cJ6, cJ7, cQ10_cJ9v, cQ10_cJ9d0, cQ10_cJ9d1, cQ10_cJ9d2])
private abbrev cQ11_cJ10v : LeanSuffixReflective.QInterval := ⟨(1892889198344704738169164943 / 2475880078570760549798248448 : ℚ), (969159269552488825942612450819 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d0 : LeanSuffixReflective.QInterval := ⟨(1247594267434768389549767696529 / 1267650600228229401496703205376 : ℚ), (311898566858692097387441924133 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d1 : LeanSuffixReflective.QInterval := ⟨(1545978755255687262558697713 / 1267650600228229401496703205376 : ℚ), (386494688813921815639674429 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ10 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ3)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ0))).add (((cJ6).mul (cJ7)).neg)).add (((cJ0).mul (cJ0)).mul ((cJ0).mul (cJ0)))).widenAll cQ11_cJ10v cQ11_cJ10d0 cQ11_cJ10d1 cQ11_cJ10d2 (by
    norm_num [cJ3, cJ0, cJ6, cJ7, cQ11_cJ10v, cQ11_cJ10d0, cQ11_cJ10d1, cQ11_cJ10d2])
private abbrev cQ11_root11 : LeanSuffixReflective.QInterval := ⟨(133999967076752782306633426141 / 158456325028528675187087900672 : ℚ), (1071999736614022258453067409131 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11v : LeanSuffixReflective.QInterval := ⟨(133999967076752782306633426141 / 158456325028528675187087900672 : ℚ), (1071999736614022258453067409131 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d0 : LeanSuffixReflective.QInterval := ⟨(-761408436101747788791622667041 / 1267650600228229401496703205376 : ℚ), (-761408436101747788791622667035 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d1 : LeanSuffixReflective.QInterval := ⟨(114258475894662379794045671 / 158456325028528675187087900672 : ℚ), (914067807157299038352365371 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ11 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ9).sqrt cQ11_root11 (by norm_num [cQ11_root11]) (by norm_num [cJ9, cQ11_root11]) (by norm_num [cJ9, cQ11_root11])).widenAll cQ12_cJ11v cQ12_cJ11d0 cQ12_cJ11d1 cQ12_cJ11d2 (by
    norm_num [cJ9, cQ11_root11, NearOneScalarInterval.Jet3.sqrt, cQ12_cJ11v, cQ12_cJ11d0, cQ12_cJ11d1, cQ12_cJ11d2])
private abbrev cQ12_root12 : LeanSuffixReflective.QInterval := ⟨(1108402151642157735370556972267 / 1267650600228229401496703205376 : ℚ), (554201075821078867685278486135 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12v : LeanSuffixReflective.QInterval := ⟨(1108402151642157735370556972267 / 1267650600228229401496703205376 : ℚ), (554201075821078867685278486135 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d0 : LeanSuffixReflective.QInterval := ⟨(713420494362936925041684736847 / 1267650600228229401496703205376 : ℚ), (178355123590734231260421184213 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d1 : LeanSuffixReflective.QInterval := ⟨(884047768283592356612424717 / 1267650600228229401496703205376 : ℚ), (55252985517724522288276545 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ12 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ10).sqrt cQ12_root12 (by norm_num [cQ12_root12]) (by norm_num [cJ10, cQ12_root12]) (by norm_num [cJ10, cQ12_root12])).widenAll cQ13_cJ12v cQ13_cJ12d0 cQ13_cJ12d1 cQ13_cJ12d2 (by
    norm_num [cJ10, cQ12_root12, NearOneScalarInterval.Jet3.sqrt, cQ13_cJ12v, cQ13_cJ12d0, cQ13_cJ12d1, cQ13_cJ12d2])
private abbrev cQ14_cJ13v : LeanSuffixReflective.QInterval := ⟨(1267669694478356521068797138655 / 1267650600228229401496703205376 : ℚ), (39614677952448641283399910583 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d0 : LeanSuffixReflective.QInterval := ⟨(289934254273981252513818147 / 158456325028528675187087900672 : ℚ), (2319474034191850020110545177 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ13 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0))).widenAll cQ14_cJ13v cQ14_cJ13d0 cQ14_cJ13d1 cQ14_cJ13d2 (by
    norm_num [cJ0, cQ14_cJ13v, cQ14_cJ13d0, cQ14_cJ13d1, cQ14_cJ13d2])
private abbrev cQ15_cJ14v : LeanSuffixReflective.QInterval := ⟨(1090209017737294074586022466513 / 633825300114114700748351602688 : ℚ), (1090209017737294074586022466517 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d0 : LeanSuffixReflective.QInterval := ⟨(-46037927255195386007884825529 / 1267650600228229401496703205376 : ℚ), (-11509481813798846501971206379 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d1 : LeanSuffixReflective.QInterval := ⟨(1798129343776850741196786605 / 1267650600228229401496703205376 : ℚ), (449532335944212685299196653 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ14 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ12).add ((cJ13).mul (cJ11))).widenAll cQ15_cJ14v cQ15_cJ14d0 cQ15_cJ14d1 cQ15_cJ14d2 (by
    norm_num [cJ12, cJ13, cJ11, cQ15_cJ14v, cQ15_cJ14d0, cQ15_cJ14d1, cQ15_cJ14d2])
private abbrev cQ16_cJ15v : LeanSuffixReflective.QInterval := ⟨(1612251062032747064420082126153 / 1267650600228229401496703205376 : ℚ), (201531382754093383052510265771 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d0 : LeanSuffixReflective.QInterval := ⟨(-141452145646246187023965943697 / 1267650600228229401496703205376 : ℚ), (-141452145646246187023965943663 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d1 : LeanSuffixReflective.QInterval := ⟨(1995108129054374288952468979 / 633825300114114700748351602688 : ℚ), (3990216258108748577904937973 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ15 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ11).mul (cJ12)).mul (cJ14)).widenAll cQ16_cJ15v cQ16_cJ15d0 cQ16_cJ15d1 cQ16_cJ15d2 (by
    norm_num [cJ11, cJ12, cJ14, cQ16_cJ15v, cQ16_cJ15d0, cQ16_cJ15d1, cQ16_cJ15d2])
private abbrev cQ17_cJ16v : LeanSuffixReflective.QInterval := ⟨(1090225439236776478777061250203 / 633825300114114700748351602688 : ℚ), (2180450878473552957554122500417 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d0 : LeanSuffixReflective.QInterval := ⟨(-10512254352943666853000188631 / 316912650057057350374175801344 : ℚ), (-10512254352943666853000188627 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d1 : LeanSuffixReflective.QInterval := ⟨(449539107118273741050876573 / 316912650057057350374175801344 : ℚ), (449539107118273741050876575 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ16 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ13).mul (cJ14)).widenAll cQ17_cJ16v cQ17_cJ16d0 cQ17_cJ16d1 cQ17_cJ16d2 (by
    norm_num [cJ13, cJ14, cQ17_cJ16v, cQ17_cJ16d0, cQ17_cJ16d1, cQ17_cJ16d2])
private abbrev cQ18_cJ17v : LeanSuffixReflective.QInterval := ⟨(2180434182936217131368997416393 / 1267650600228229401496703205376 : ℚ), (272554272867027141421124677051 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d0 : LeanSuffixReflective.QInterval := ⟨(-22043926926916148387835547493 / 633825300114114700748351602688 : ℚ), (-44087853853832296775671094965 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d1 : LeanSuffixReflective.QInterval := ⟨(1798143112320198503917237931 / 1267650600228229401496703205376 : ℚ), (1798143112320198503917237941 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ17 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ11).add (cJ12)).mul (((cJ8).mul (cJ8)).add ((cJ6).mul ((cJ11).mul (cJ12))))).widenAll cQ18_cJ17v cQ18_cJ17d0 cQ18_cJ17d1 cQ18_cJ17d2 (by
    norm_num [cJ11, cJ12, cJ8, cJ6, cQ18_cJ17v, cQ18_cJ17d0, cQ18_cJ17d1, cQ18_cJ17d2])
private abbrev cQ19_cJ18v : LeanSuffixReflective.QInterval := ⟨(2534214456090899882025553880849 / 1267650600228229401496703205376 : ℚ), (1267107228045449941012776940429 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d0 : LeanSuffixReflective.QInterval := ⟨(-85665148583144411400475791407 / 1267650600228229401496703205376 : ℚ), (-42832574291572205700237895699 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d1 : LeanSuffixReflective.QInterval := ⟨(-1885842773996779245650555 / 1267650600228229401496703205376 : ℚ), (-942921386998389622825275 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ18 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul (cJ8)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).widenAll cQ19_cJ18v cQ19_cJ18d0 cQ19_cJ18d1 cQ19_cJ18d2 (by
    norm_num [cJ8, cJ0, cQ19_cJ18v, cQ19_cJ18d0, cQ19_cJ18d1, cQ19_cJ18d2])
private abbrev cQ20_cJ19v : LeanSuffixReflective.QInterval := ⟨(996704596511750429792676941155 / 1267650600228229401496703205376 : ℚ), (996704596511750429792676941165 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d0 : LeanSuffixReflective.QInterval := ⟨(43723340325887637405444986025 / 633825300114114700748351602688 : ℚ), (43723340325887637405444986037 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d1 : LeanSuffixReflective.QInterval := ⟨(-1233389445102479669891374047 / 633825300114114700748351602688 : ℚ), (-2466778890204959339782748083 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ19 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ15).invPos (by norm_num [cJ15])).widenAll cQ20_cJ19v cQ20_cJ19d0 cQ20_cJ19d1 cQ20_cJ19d2 (by
    norm_num [cJ15, NearOneScalarInterval.Jet3.invPos, cQ20_cJ19v, cQ20_cJ19d0, cQ20_cJ19d1, cQ20_cJ19d2])
private abbrev cQ21_cJ20v : LeanSuffixReflective.QInterval := ⟨(996277363998236529159533031775 / 633825300114114700748351602688 : ℚ), (996277363998236529159533031789 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d0 : LeanSuffixReflective.QInterval := ⟨(53731601936166375088275621305 / 633825300114114700748351602688 : ℚ), (107463203872332750176551242667 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d1 : LeanSuffixReflective.QInterval := ⟨(-4932925800352697366958784601 / 1267650600228229401496703205376 : ℚ), (-2466462900176348683479392287 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ20 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ18).mul (cJ19)).widenAll cQ21_cJ20v cQ21_cJ20d0 cQ21_cJ20d1 cQ21_cJ20d2 (by
    norm_num [cJ18, cJ19, cQ21_cJ20v, cQ21_cJ20d0, cQ21_cJ20d1, cQ21_cJ20d2])
private abbrev cQ22_cJ21v : LeanSuffixReflective.QInterval := ⟨(736975118368153180011663461093 / 1267650600228229401496703205376 : ℚ), (368487559184076590005831730549 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d0 : LeanSuffixReflective.QInterval := ⟨(14212234675977380040578156423 / 1267650600228229401496703205376 : ℚ), (14212234675977380040578156429 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d1 : LeanSuffixReflective.QInterval := ⟨(-607762623685488474660676931 / 1267650600228229401496703205376 : ℚ), (-607762623685488474660676927 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ21 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ16).invPos (by norm_num [cJ16])).widenAll cQ22_cJ21v cQ22_cJ21d0 cQ22_cJ21d1 cQ22_cJ21d2 (by
    norm_num [cJ16, NearOneScalarInterval.Jet3.invPos, cQ22_cJ21v, cQ22_cJ21d0, cQ22_cJ21d1, cQ22_cJ21d2])
private abbrev cQ23_cJ22v : LeanSuffixReflective.QInterval := ⟨(736659217615493293434537154013 / 633825300114114700748351602688 : ℚ), (736659217615493293434537154021 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d0 : LeanSuffixReflective.QInterval := ⟨(-21390935675010132082291092945 / 1267650600228229401496703205376 : ℚ), (-10695467837505066041145546463 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d1 : LeanSuffixReflective.QInterval := ⟨(-608050296248642383415437943 / 633825300114114700748351602688 : ℚ), (-1216100592497284766830875875 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ22 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ18).mul (cJ21)).widenAll cQ23_cJ22v cQ23_cJ22d0 cQ23_cJ22d1 cQ23_cJ22d2 (by
    norm_num [cJ18, cJ21, cQ23_cJ22v, cQ23_cJ22d0, cQ23_cJ22d1, cQ23_cJ22d2])
private abbrev cQ24_cJ23v : LeanSuffixReflective.QInterval := ⟨(736980761370680191096620892831 / 1267650600228229401496703205376 : ℚ), (736980761370680191096620892837 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d0 : LeanSuffixReflective.QInterval := ⟨(14901573436462249792468736447 / 1267650600228229401496703205376 : ℚ), (1862696679557781224058592057 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d1 : LeanSuffixReflective.QInterval := ⟨(-151941857537135936533021911 / 316912650057057350374175801344 : ℚ), (-75970928768567968266510955 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ23 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ17).invPos (by norm_num [cJ17])).widenAll cQ24_cJ23v cQ24_cJ23d0 cQ24_cJ23d1 cQ24_cJ23d2 (by
    norm_num [cJ17, NearOneScalarInterval.Jet3.invPos, cQ24_cJ23v, cQ24_cJ23d0, cQ24_cJ23d1, cQ24_cJ23d2])
private abbrev cQ25_cJ24v : LeanSuffixReflective.QInterval := ⟨(184206391871580882751277862597 / 158456325028528675187087900672 : ℚ), (1473651134972647062010222900791 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d0 : LeanSuffixReflective.QInterval := ⟨(5563732610381287581499721771 / 1267650600228229401496703205376 : ℚ), (5563732610381287581499721793 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d1 : LeanSuffixReflective.QInterval := ⟨(-303956800747046162339230459 / 316912650057057350374175801344 : ℚ), (-607913601494092324678460913 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ24 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).mul (cJ23)).widenAll cQ25_cJ24v cQ25_cJ24d0 cQ25_cJ24d1 cQ25_cJ24d2 (by
    norm_num [cJ8, cJ0, cJ23, cQ25_cJ24v, cQ25_cJ24d0, cQ25_cJ24d1, cQ25_cJ24d2])
private abbrev cQ26_cJ25v : LeanSuffixReflective.QInterval := ⟨(316981787067615312649860108427 / 316912650057057350374175801344 : ℚ), (1267927148270461250599440433711 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d0 : LeanSuffixReflective.QInterval := ⟨(22010135848335272954207741031 / 1267650600228229401496703205376 : ℚ), (11005067924167636477103870517 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d1 : LeanSuffixReflective.QInterval := ⟨(471765766463299142387569 / 1267650600228229401496703205376 : ℚ), (471765766463299142387571 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ25 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ8).invPos (by norm_num [cJ8])).widenAll cQ26_cJ25v cQ26_cJ25d0 cQ26_cJ25d1 cQ26_cJ25d2 (by
    norm_num [cJ8, NearOneScalarInterval.Jet3.invPos, cQ26_cJ25v, cQ26_cJ25d0, cQ26_cJ25d1, cQ26_cJ25d2])
private abbrev cQ27_cJ26v : LeanSuffixReflective.QInterval := ⟨(27379558552074120029188355863 / 1267650600228229401496703205376 : ℚ), (3422444819009265003648544483 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d0 : LeanSuffixReflective.QInterval := ⟨(1126742034057039956996827440649 / 1267650600228229401496703205376 : ℚ), (70421377128564997312301715041 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d1 : LeanSuffixReflective.QInterval := ⟨(1365486412698368041909779 / 79228162514264337593543950336 : ℚ), (21847782603173888670556465 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ26 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ0).mul (cJ12)).mul (cJ25)).widenAll cQ27_cJ26v cQ27_cJ26d0 cQ27_cJ26d1 cQ27_cJ26d2 (by
    norm_num [cJ0, cJ12, cJ25, cQ27_cJ26v, cQ27_cJ26d0, cQ27_cJ26d1, cQ27_cJ26d2])
private abbrev cQ28_cJ27v : LeanSuffixReflective.QInterval := ⟨(449400324033952515324986385 / 633825300114114700748351602688 : ℚ), (224700162016976257662493193 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d0 : LeanSuffixReflective.QInterval := ⟨(9098908235228354117789788595 / 158456325028528675187087900672 : ℚ), (72791265881826832942318308763 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d1 : LeanSuffixReflective.QInterval := ⟨(-370775094610384926352227 / 633825300114114700748351602688 : ℚ), (-741550189220769852704453 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ27 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ6).mul (cJ24)).widenAll cQ28_cJ27v cQ28_cJ27d0 cQ28_cJ27d1 cQ28_cJ27d2 (by
    norm_num [cJ6, cJ24, cQ28_cJ27v, cQ28_cJ27d0, cQ28_cJ27d1, cQ28_cJ27d2])
private abbrev cQ29_cJ28v : LeanSuffixReflective.QInterval := ⟨(1267453479605672079334761700605 / 1267650600228229401496703205376 : ℚ), (1267460871629017978915834507035 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d0 : LeanSuffixReflective.QInterval := ⟨(-16276644016378160208225004333 / 1267650600228229401496703205376 : ℚ), (-15563115428982119402246658669 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d1 : LeanSuffixReflective.QInterval := ⟨(-157803902415288291286085 / 633825300114114700748351602688 : ℚ), (-301772324314732718424873 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ28 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ26).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ26]) (by norm_num [cJ26])).widenAll cQ29_cJ28v cQ29_cJ28d0 cQ29_cJ28d1 cQ29_cJ28d2 (by
    norm_num [cJ26, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ29_cJ28v, cQ29_cJ28d0, cQ29_cJ28d1, cQ29_cJ28d2])
private abbrev cQ30_cJ29v : LeanSuffixReflective.QInterval := ⟨(316912596950769964491380700153 / 316912650057057350374175801344 : ℚ), (9903518716945491920687047389 / 9903520314283042199192993792 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d0 : LeanSuffixReflective.QInterval := ⟨(-34411056774099479344591251 / 1267650600228229401496703205376 : ℚ), (-33113460622025063129599645 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d1 : LeanSuffixReflective.QInterval := ⟨(337338452526454894409 / 1267650600228229401496703205376 : ℚ), (350557520232531957199 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ29 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ27).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ27]) (by norm_num [cJ27])).widenAll cQ30_cJ29v cQ30_cJ29d0 cQ30_cJ29d1 cQ30_cJ29d2 (by
    norm_num [cJ27, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ30_cJ29v, cQ30_cJ29d0, cQ30_cJ29d1, cQ30_cJ29d2])
private abbrev cQ31_cJ30v : LeanSuffixReflective.QInterval := ⟨(316981787067615312649860108427 / 316912650057057350374175801344 : ℚ), (1267927148270461250599440433711 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d0 : LeanSuffixReflective.QInterval := ⟨(22010135848335272954207741031 / 1267650600228229401496703205376 : ℚ), (11005067924167636477103870517 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d1 : LeanSuffixReflective.QInterval := ⟨(471765766463299142387569 / 1267650600228229401496703205376 : ℚ), (471765766463299142387571 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ30 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ8).invPos (by norm_num [cJ8])).widenAll cQ31_cJ30v cQ31_cJ30d0 cQ31_cJ30d1 cQ31_cJ30d2 (by
    norm_num [cJ8, NearOneScalarInterval.Jet3.invPos, cQ31_cJ30v, cQ31_cJ30d0, cQ31_cJ30d1, cQ31_cJ30d2])
private abbrev cQ32_cJ31v : LeanSuffixReflective.QInterval := ⟨(1474326960495020970725094307771 / 1267650600228229401496703205376 : ℚ), (737163486849227791155757983423 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d0 : LeanSuffixReflective.QInterval := ⟨(60712537050890683850674368665 / 1267650600228229401496703205376 : ℚ), (30357374037096613538437797705 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d1 : LeanSuffixReflective.QInterval := ⟨(-1215287304537043037115685111 / 1267650600228229401496703205376 : ℚ), (-1215287271003193228673825531 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ31 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ6).mul (cJ12)).mul (cJ30)).mul (cJ28)).add ((cJ24).mul (cJ29))).widenAll cQ32_cJ31v cQ32_cJ31d0 cQ32_cJ31d1 cQ32_cJ31d2 (by
    norm_num [cJ6, cJ12, cJ30, cJ28, cJ24, cJ29, cQ32_cJ31v, cQ32_cJ31d0, cQ32_cJ31d1, cQ32_cJ31d2])
private abbrev cQ33_cJ32v : LeanSuffixReflective.QInterval := ⟨(919852570953953325888999849207 / 633825300114114700748351602688 : ℚ), (114981571369244165736124981151 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d0 : LeanSuffixReflective.QInterval := ⟨(-184661232162741407027738098303 / 158456325028528675187087900672 : ℚ), (-738644928650965628110952393211 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d2 : LeanSuffixReflective.QInterval := ⟨(96644751424660417504606049 / 79228162514264337593543950336 : ℚ), (773158011397283340036848393 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ32 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ4)).widenAll cQ33_cJ32v cQ33_cJ32d0 cQ33_cJ32d1 cQ33_cJ32d2 (by
    norm_num [cJ4, cQ33_cJ32v, cQ33_cJ32d0, cQ33_cJ32d1, cQ33_cJ32d2])
private abbrev cQ34_cJ33v : LeanSuffixReflective.QInterval := ⟨(96644751424660417504606049 / 158456325028528675187087900672 : ℚ), (773158011397283340036848393 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d0 : LeanSuffixReflective.QInterval := ⟨(62612912956323329153984105637 / 1267650600228229401496703205376 : ℚ), (31306456478161664576992052819 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ33 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ34_cJ33v cQ34_cJ33d0 cQ34_cJ33d1 cQ34_cJ33d2 (by
    norm_num [cJ0, cQ34_cJ33v, cQ34_cJ33d0, cQ34_cJ33d1, cQ34_cJ33d2])
private abbrev cQ35_cJ34v : LeanSuffixReflective.QInterval := ⟨(1334955786930972395280224537829 / 633825300114114700748351602688 : ℚ), (2669911573861944790560449075665 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d0 : LeanSuffixReflective.QInterval := ⟨(-133996788334136023980352770729 / 39614081257132168796771975168 : ℚ), (-1071974306673088191842822165829 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d2 : LeanSuffixReflective.QInterval := ⟨(4488248635132698175921038423 / 1267650600228229401496703205376 : ℚ), (2244124317566349087960519215 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ34 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ32).mul (cJ32)).widenAll cQ35_cJ34v cQ35_cJ34d0 cQ35_cJ34d1 cQ35_cJ34d2 (by
    norm_num [cJ32, cQ35_cJ34v, cQ35_cJ34d0, cQ35_cJ34d1, cQ35_cJ34d2])
private abbrev cQ36_cJ35v : LeanSuffixReflective.QInterval := ⟨(158316067258680778369090368221 / 158456325028528675187087900672 : ℚ), (1266528538069446226952722945771 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d0 : LeanSuffixReflective.QInterval := ⟨(-2811478558413446433386085125 / 39614081257132168796771975168 : ℚ), (-89967313869230285868354723997 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d2 : LeanSuffixReflective.QInterval := ⟨(-943119989814508603116689 / 1267650600228229401496703205376 : ℚ), (-58944999363406787694793 / 79228162514264337593543950336 : ℚ), by norm_num⟩
@[simp] private abbrev cJ35 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ33).mul (cJ32)).neg)).widenAll cQ36_cJ35v cQ36_cJ35d0 cQ36_cJ35d1 cQ36_cJ35d2 (by
    norm_num [cJ33, cJ32, cQ36_cJ35v, cQ36_cJ35d0, cQ36_cJ35d1, cQ36_cJ35d2])
private abbrev cQ37_cJ36v : LeanSuffixReflective.QInterval := ⟨(3677781867024402452947134808873 / 1267650600228229401496703205376 : ℚ), (229861366689025153309195925555 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d0 : LeanSuffixReflective.QInterval := ⟨(-385479885665887259852501956379 / 158456325028528675187087900672 : ℚ), (-1541919542663549039410007825511 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d2 : LeanSuffixReflective.QInterval := ⟨(1544947299666612099240924629 / 633825300114114700748351602688 : ℚ), (3089894599333224198481849263 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ36 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ32)).add (((cJ33).mul (cJ34)).neg)).widenAll cQ37_cJ36v cQ37_cJ36d0 cQ37_cJ36d1 cQ37_cJ36d2 (by
    norm_num [cJ32, cJ33, cJ34, cQ37_cJ36v, cQ37_cJ36d0, cQ37_cJ36d1, cQ37_cJ36d2])
private abbrev cQ38_cJ37v : LeanSuffixReflective.QInterval := ⟨(1870197625770360344677710236427 / 633825300114114700748351602688 : ℚ), (3740395251540720689355420472861 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d0 : LeanSuffixReflective.QInterval := ⟨(-548461507870130797538233507161 / 1267650600228229401496703205376 : ℚ), (-274230753935065398769116753575 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d2 : LeanSuffixReflective.QInterval := ⟨(1544947299666612099240924629 / 633825300114114700748351602688 : ℚ), (3089894599333224198481849263 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ37 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ32)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ0))).add (((cJ33).mul (cJ34)).neg)).add (((cJ0).mul (cJ0)).mul ((cJ0).mul (cJ0)))).widenAll cQ38_cJ37v cQ38_cJ37d0 cQ38_cJ37d1 cQ38_cJ37d2 (by
    norm_num [cJ32, cJ0, cJ33, cJ34, cQ38_cJ37v, cQ38_cJ37d0, cQ38_cJ37d1, cQ38_cJ37d2])
private abbrev cQ38_root38 : LeanSuffixReflective.QInterval := ⟨(269899934907654188171642967577 / 158456325028528675187087900672 : ℚ), (2159199479261233505373143740619 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38v : LeanSuffixReflective.QInterval := ⟨(269899934907654188171642967577 / 158456325028528675187087900672 : ℚ), (2159199479261233505373143740619 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d0 : LeanSuffixReflective.QInterval := ⟨(-452624978038123010553720598817 / 633825300114114700748351602688 : ℚ), (-226312489019061505276860299407 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d2 : LeanSuffixReflective.QInterval := ⟨(907027530598258839163394757 / 1267650600228229401496703205376 : ℚ), (113378441324782354895424345 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ38 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ36).sqrt cQ38_root38 (by norm_num [cQ38_root38]) (by norm_num [cJ36, cQ38_root38]) (by norm_num [cJ36, cQ38_root38])).widenAll cQ39_cJ38v cQ39_cJ38d0 cQ39_cJ38d1 cQ39_cJ38d2 (by
    norm_num [cJ36, cQ38_root38, NearOneScalarInterval.Jet3.sqrt, cQ39_cJ38v, cQ39_cJ38d0, cQ39_cJ38d1, cQ39_cJ38d2])
private abbrev cQ39_root39 : LeanSuffixReflective.QInterval := ⟨(1088750922583583126755756794801 / 633825300114114700748351602688 : ℚ), (2177501845167166253511513589605 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39v : LeanSuffixReflective.QInterval := ⟨(1088750922583583126755756794801 / 633825300114114700748351602688 : ℚ), (2177501845167166253511513589605 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d0 : LeanSuffixReflective.QInterval := ⟨(-79822843915922873329960712641 / 633825300114114700748351602688 : ℚ), (-159645687831845746659921425277 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d2 : LeanSuffixReflective.QInterval := ⟨(899403771386018304962744937 / 1267650600228229401496703205376 : ℚ), (899403771386018304962744939 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ39 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ37).sqrt cQ39_root39 (by norm_num [cQ39_root39]) (by norm_num [cJ37, cQ39_root39]) (by norm_num [cJ37, cQ39_root39])).widenAll cQ40_cJ39v cQ40_cJ39d0 cQ40_cJ39d1 cQ40_cJ39d2 (by
    norm_num [cJ37, cQ39_root39, NearOneScalarInterval.Jet3.sqrt, cQ40_cJ39v, cQ40_cJ39d0, cQ40_cJ39d1, cQ40_cJ39d2])
private abbrev cQ41_cJ40v : LeanSuffixReflective.QInterval := ⟨(1267669694478356521068797138655 / 1267650600228229401496703205376 : ℚ), (39614677952448641283399910583 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d0 : LeanSuffixReflective.QInterval := ⟨(289934254273981252513818147 / 158456325028528675187087900672 : ℚ), (2319474034191850020110545177 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ40 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0))).widenAll cQ41_cJ40v cQ41_cJ40d0 cQ41_cJ40d1 cQ41_cJ40d2 (by
    norm_num [cJ0, cQ41_cJ40v, cQ41_cJ40d0, cQ41_cJ40d1, cQ41_cJ40d2])
private abbrev cQ42_cJ41v : LeanSuffixReflective.QInterval := ⟨(2168366923909230015320417234257 / 633825300114114700748351602688 : ℚ), (2168366923909230015320417234261 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d0 : LeanSuffixReflective.QInterval := ⟨(-132619812576971065103445285509 / 158456325028528675187087900672 : ℚ), (-530479250307884260413781142029 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d2 : LeanSuffixReflective.QInterval := ⟨(225805620534326298285273599 / 158456325028528675187087900672 : ℚ), (903222482137305193141094399 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ41 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ39).add ((cJ40).mul (cJ38))).widenAll cQ42_cJ41v cQ42_cJ41d0 cQ42_cJ41d1 cQ42_cJ41d2 (by
    norm_num [cJ39, cJ40, cJ38, cQ42_cJ41v, cQ42_cJ41d0, cQ42_cJ41d1, cQ42_cJ41d2])
private abbrev cQ43_cJ42v : LeanSuffixReflective.QInterval := ⟨(6344317947653243934608099112081 / 633825300114114700748351602688 : ℚ), (12688635895306487869216198224221 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d0 : LeanSuffixReflective.QInterval := ⟨(-2338557343030225298887521380485 / 316912650057057350374175801344 : ℚ), (-9354229372120901195550085521805 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d2 : LeanSuffixReflective.QInterval := ⟨(7928270423223784651969600489 / 633825300114114700748351602688 : ℚ), (7928270423223784651969600513 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ42 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ38).mul (cJ39)).mul (cJ41)).widenAll cQ43_cJ42v cQ43_cJ42d0 cQ43_cJ42d1 cQ43_cJ42d2 (by
    norm_num [cJ38, cJ39, cJ41, cQ43_cJ42v, cQ43_cJ42d0, cQ43_cJ42d1, cQ43_cJ42d2])
private abbrev cQ44_cJ43v : LeanSuffixReflective.QInterval := ⟨(4336799170771653980742659506713 / 1267650600228229401496703205376 : ℚ), (4336799170771653980742659506725 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d0 : LeanSuffixReflective.QInterval := ⟨(-263259843946008493029294996241 / 316912650057057350374175801344 : ℚ), (-65814960986502123257323749059 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d2 : LeanSuffixReflective.QInterval := ⟨(1806472174226613347412943361 / 1267650600228229401496703205376 : ℚ), (225809021778326668426617921 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ43 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ40).mul (cJ41)).widenAll cQ44_cJ43v cQ44_cJ43d0 cQ44_cJ43d1 cQ44_cJ43d2 (by
    norm_num [cJ40, cJ41, cQ44_cJ43v, cQ44_cJ43d0, cQ44_cJ43d1, cQ44_cJ43d2])
private abbrev cQ45_cJ44v : LeanSuffixReflective.QInterval := ⟨(1084191592924602652956313284855 / 316912650057057350374175801344 : ℚ), (4336766371698410611825253139457 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d0 : LeanSuffixReflective.QInterval := ⟨(-1057021238509982375271968745301 / 1267650600228229401496703205376 : ℚ), (-1057021238509982375271968745243 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d2 : LeanSuffixReflective.QInterval := ⟨(1806458626770734710685417007 / 1267650600228229401496703205376 : ℚ), (451614656692683677671354255 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ44 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ38).add (cJ39)).mul (((cJ35).mul (cJ35)).add ((cJ33).mul ((cJ38).mul (cJ39))))).widenAll cQ45_cJ44v cQ45_cJ44d0 cQ45_cJ44d1 cQ45_cJ44d2 (by
    norm_num [cJ38, cJ39, cJ35, cJ33, cQ45_cJ44v, cQ45_cJ44d0, cQ45_cJ44d1, cQ45_cJ44d2])
private abbrev cQ46_cJ45v : LeanSuffixReflective.QInterval := ⟨(2530833998672642516749637918485 / 1267650600228229401496703205376 : ℚ), (1265416999336321258374818959249 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d0 : LeanSuffixReflective.QInterval := ⟨(-89309513769447125854374987533 / 316912650057057350374175801344 : ℚ), (-178619027538894251708749975059 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d2 : LeanSuffixReflective.QInterval := ⟨(-3769169131693860659783293 / 1267650600228229401496703205376 : ℚ), (-471146141461732582472911 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ45 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ35).mul (cJ35)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).widenAll cQ46_cJ45v cQ46_cJ45d0 cQ46_cJ45d1 cQ46_cJ45d2 (by
    norm_num [cJ35, cJ0, cQ46_cJ45v, cQ46_cJ45d0, cQ46_cJ45d1, cQ46_cJ45d2])
private abbrev cQ47_cJ46v : LeanSuffixReflective.QInterval := ⟨(63321938525062211327468754297 / 633825300114114700748351602688 : ℚ), (126643877050124422654937508595 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d0 : LeanSuffixReflective.QInterval := ⟨(46681766435576611545036398555 / 633825300114114700748351602688 : ℚ), (93363532871153223090072797113 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d2 : LeanSuffixReflective.QInterval := ⟨(-19782798422608495726169621 / 158456325028528675187087900672 : ℚ), (-158262387380867965809356967 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ46 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ42).invPos (by norm_num [cJ42])).widenAll cQ47_cJ46v cQ47_cJ46d0 cQ47_cJ46d1 cQ47_cJ46d2 (by
    norm_num [cJ42, NearOneScalarInterval.Jet3.invPos, cQ47_cJ46v, cQ47_cJ46d0, cQ47_cJ46d1, cQ47_cJ46d2])
private abbrev cQ48_cJ47v : LeanSuffixReflective.QInterval := ⟨(252841460970765161838960117203 / 1267650600228229401496703205376 : ℚ), (252841460970765161838960117207 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d0 : LeanSuffixReflective.QInterval := ⟨(150708397777125890084821106813 / 1267650600228229401496703205376 : ℚ), (150708397777125890084821106823 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d2 : LeanSuffixReflective.QInterval := ⟨(-316343614568949267938174775 / 1267650600228229401496703205376 : ℚ), (-316343614568949267938174771 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ47 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ45).mul (cJ46)).widenAll cQ48_cJ47v cQ48_cJ47d0 cQ48_cJ47d1 cQ48_cJ47d2 (by
    norm_num [cJ45, cJ46, cQ48_cJ47v, cQ48_cJ47d0, cQ48_cJ47d1, cQ48_cJ47d2])
private abbrev cQ49_cJ48v : LeanSuffixReflective.QInterval := ⟨(370535498874176616029290670737 / 1267650600228229401496703205376 : ℚ), (370535498874176616029290670739 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d0 : LeanSuffixReflective.QInterval := ⟨(89971533168980401426445772109 / 1267650600228229401496703205376 : ℚ), (5623220823061275089152860757 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d2 : LeanSuffixReflective.QInterval := ⟨(-154344723359711386766026383 / 1267650600228229401496703205376 : ℚ), (-154344723359711386766026381 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ48 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ43).invPos (by norm_num [cJ43])).widenAll cQ49_cJ48v cQ49_cJ48d0 cQ49_cJ48d1 cQ49_cJ48d2 (by
    norm_num [cJ43, NearOneScalarInterval.Jet3.invPos, cQ49_cJ48v, cQ49_cJ48d0, cQ49_cJ48d1, cQ49_cJ48d2])
private abbrev cQ50_cJ49v : LeanSuffixReflective.QInterval := ⟨(369882615168982154405648132445 / 633825300114114700748351602688 : ℚ), (739765230337964308811296264899 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d0 : LeanSuffixReflective.QInterval := ⟨(18801244223863031463215528261 / 316912650057057350374175801344 : ℚ), (2350155527982878932901941033 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d2 : LeanSuffixReflective.QInterval := ⟨(-309247267573931805207130467 / 1267650600228229401496703205376 : ℚ), (-309247267573931805207130461 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ49 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ45).mul (cJ48)).widenAll cQ50_cJ49v cQ50_cJ49d0 cQ50_cJ49d1 cQ50_cJ49d2 (by
    norm_num [cJ45, cJ48, cQ50_cJ49v, cQ50_cJ49d0, cQ50_cJ49d1, cQ50_cJ49d2])
private abbrev cQ51_cJ50v : LeanSuffixReflective.QInterval := ⟨(23158643827717656321176361603 / 79228162514264337593543950336 : ℚ), (92634575310870625284705446413 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d0 : LeanSuffixReflective.QInterval := ⟨(90313109014074482653316250317 / 1267650600228229401496703205376 : ℚ), (90313109014074482653316250325 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d2 : LeanSuffixReflective.QInterval := ⟨(-38586475121100396376356371 / 316912650057057350374175801344 : ℚ), (-77172950242200792752712741 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ50 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ44).invPos (by norm_num [cJ44])).widenAll cQ51_cJ50v cQ51_cJ50d0 cQ51_cJ50d1 cQ51_cJ50d2 (by
    norm_num [cJ44, NearOneScalarInterval.Jet3.invPos, cQ51_cJ50v, cQ51_cJ50d0, cQ51_cJ50d1, cQ51_cJ50d2])
private abbrev cQ52_cJ51v : LeanSuffixReflective.QInterval := ⟨(740426214182937896334130370317 / 1267650600228229401496703205376 : ℚ), (740426214182937896334130370327 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d0 : LeanSuffixReflective.QInterval := ⟨(128549225276180908467307573479 / 1267650600228229401496703205376 : ℚ), (128549225276180908467307573499 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d2 : LeanSuffixReflective.QInterval := ⟨(-308972243027175647641741659 / 1267650600228229401496703205376 : ℚ), (-154486121513587823820870827 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ51 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ35).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).mul (cJ50)).widenAll cQ52_cJ51v cQ52_cJ51d0 cQ52_cJ51d1 cQ52_cJ51d2 (by
    norm_num [cJ35, cJ0, cJ50, cQ52_cJ51v, cQ52_cJ51d0, cQ52_cJ51d1, cQ52_cJ51d2])
private abbrev cQ53_cJ52v : LeanSuffixReflective.QInterval := ⟨(1268773656461326994783999602305 / 1267650600228229401496703205376 : ℚ), (1268773656461326994783999602309 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d0 : LeanSuffixReflective.QInterval := ⟨(22531698723871984397078947979 / 316912650057057350374175801344 : ℚ), (5632924680967996099269736995 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d2 : LeanSuffixReflective.QInterval := ⟨(236197954090851943744241 / 316912650057057350374175801344 : ℚ), (472395908181703887488483 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ52 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ35).invPos (by norm_num [cJ35])).widenAll cQ53_cJ52v cQ53_cJ52d0 cQ53_cJ52d1 cQ53_cJ52d2 (by
    norm_num [cJ35, NearOneScalarInterval.Jet3.invPos, cQ53_cJ52v, cQ53_cJ52d0, cQ53_cJ52d1, cQ53_cJ52d2])
private abbrev cQ54_cJ53v : LeanSuffixReflective.QInterval := ⟨(26912092660285844769306350559 / 633825300114114700748351602688 : ℚ), (53824185320571689538612701119 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d0 : LeanSuffixReflective.QInterval := ⟨(272413521947555618630727631251 / 158456325028528675187087900672 : ℚ), (2179308175580444949045821050019 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d2 : LeanSuffixReflective.QInterval := ⟨(11135914763239019411513747 / 633825300114114700748351602688 : ℚ), (2783978690809754852878437 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ53 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ0).mul (cJ39)).mul (cJ52)).widenAll cQ54_cJ53v cQ54_cJ53d0 cQ54_cJ53d1 cQ54_cJ53d2 (by
    norm_num [cJ0, cJ39, cJ52, cQ54_cJ53v, cQ54_cJ53d0, cQ54_cJ53d1, cQ54_cJ53d2])
private abbrev cQ55_cJ54v : LeanSuffixReflective.QInterval := ⟨(112899102331713422308349175 / 316912650057057350374175801344 : ℚ), (225798204663426844616698351 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d0 : LeanSuffixReflective.QInterval := ⟨(36650186537388810315093866915 / 1267650600228229401496703205376 : ℚ), (36650186537388810315093866917 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d2 : LeanSuffixReflective.QInterval := ⟨(-188446536413772239090959 / 1267650600228229401496703205376 : ℚ), (-94223268206886119545479 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ54 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ33).mul (cJ51)).widenAll cQ55_cJ54v cQ55_cJ54d0 cQ55_cJ54d1 cQ55_cJ54d2 (by
    norm_num [cJ33, cJ51, cQ55_cJ54v, cQ55_cJ54d0, cQ55_cJ54d1, cQ55_cJ54d2])
private abbrev cQ56_cJ55v : LeanSuffixReflective.QInterval := ⟨(633444406130012449213952480465 / 633825300114114700748351602688 : ℚ), (633458689654416283646492447549 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d0 : LeanSuffixReflective.QInterval := ⟨(-62081546196851984454160720571 / 1267650600228229401496703205376 : ℚ), (-58982435428143479968241920795 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d2 : LeanSuffixReflective.QInterval := ⟨(-634453460565848204696177 / 1267650600228229401496703205376 : ℚ), (-602781543992615362874913 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ55 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ53).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ53]) (by norm_num [cJ53])).widenAll cQ56_cJ55v cQ56_cJ55d0 cQ56_cJ55d1 cQ56_cJ55d2 (by
    norm_num [cJ53, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ56_cJ55v, cQ56_cJ55d0, cQ56_cJ55d1, cQ56_cJ55d2])
private abbrev cQ57_cJ56v : LeanSuffixReflective.QInterval := ⟨(19807039790650698183666149119 / 19807040628566084398385987584 : ℚ), (1267650548612641610669961155933 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d0 : LeanSuffixReflective.QInterval := ⟨(-8704805082943260928781683 / 1267650600228229401496703205376 : ℚ), (-8377462067003887579898755 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d2 : LeanSuffixReflective.QInterval := ⟨(43074916108656742649 / 1267650600228229401496703205376 : ℚ), (11189508997206652543 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ56 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ54).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ54]) (by norm_num [cJ54])).widenAll cQ57_cJ56v cQ57_cJ56d0 cQ57_cJ56d1 cQ57_cJ56d2 (by
    norm_num [cJ54, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ57_cJ56v, cQ57_cJ56d0, cQ57_cJ56d1, cQ57_cJ56d2])
private abbrev cQ58_cJ57v : LeanSuffixReflective.QInterval := ⟨(1268773656461326994783999602305 / 1267650600228229401496703205376 : ℚ), (1268773656461326994783999602309 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d0 : LeanSuffixReflective.QInterval := ⟨(22531698723871984397078947979 / 316912650057057350374175801344 : ℚ), (5632924680967996099269736995 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d2 : LeanSuffixReflective.QInterval := ⟨(236197954090851943744241 / 316912650057057350374175801344 : ℚ), (472395908181703887488483 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ57 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ35).invPos (by norm_num [cJ35])).widenAll cQ58_cJ57v cQ58_cJ57d0 cQ58_cJ57d1 cQ58_cJ57d2 (by
    norm_num [cJ35, NearOneScalarInterval.Jet3.invPos, cQ58_cJ57v, cQ58_cJ57d0, cQ58_cJ57d1, cQ58_cJ57d2])
private abbrev cQ59_cJ58v : LeanSuffixReflective.QInterval := ⟨(741754649786352743202397731903 / 1267650600228229401496703205376 : ℚ), (92719335114566868801152247631 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d0 : LeanSuffixReflective.QInterval := ⟨(236059685492714503711910791877 / 1267650600228229401496703205376 : ℚ), (236065552474721075979364787827 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d2 : LeanSuffixReflective.QInterval := ⟨(-308423166226358178088229075 / 1267650600228229401496703205376 : ℚ), (-308423119146480176820055881 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ58 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ33).mul (cJ39)).mul (cJ57)).mul (cJ55)).add ((cJ51).mul (cJ56))).widenAll cQ59_cJ58v cQ59_cJ58d0 cQ59_cJ58d1 cQ59_cJ58d2 (by
    norm_num [cJ33, cJ39, cJ57, cJ55, cJ51, cJ56, cQ59_cJ58v, cQ59_cJ58d0, cQ59_cJ58d1, cQ59_cJ58d2])
private abbrev cQ60_cJ59v : LeanSuffixReflective.QInterval := ⟨(316772392287209453556178268893 / 316912650057057350374175801344 : ℚ), (633544784574418907112356537787 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d0 : LeanSuffixReflective.QInterval := ⟨(-2811478558413446433386085125 / 79228162514264337593543950336 : ℚ), (-22491828467307571467088680999 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d2 : LeanSuffixReflective.QInterval := ⟨(-471559994907254301558345 / 1267650600228229401496703205376 : ℚ), (-58944999363406787694793 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ59 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ5).mul (cJ4)).neg)).widenAll cQ60_cJ59v cQ60_cJ59d0 cQ60_cJ59d1 cQ60_cJ59d2 (by
    norm_num [cJ5, cJ4, cQ60_cJ59v, cQ60_cJ59d0, cQ60_cJ59d1, cQ60_cJ59d2])
private abbrev cQ61_cJ60v : LeanSuffixReflective.QInterval := ⟨(2956261657462897969817 / 316912650057057350374175801344 : ℚ), (11833099591169221750959 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d0 : LeanSuffixReflective.QInterval := ⟨(-29343495243178669078139 / 1267650600228229401496703205376 : ℚ), (-27342805241256589132835 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d1 : LeanSuffixReflective.QInterval := ⟨(-2465924939077100784459771921 / 633825300114114700748351602688 : ℚ), (-4931849878133748800130003417 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ60 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul (cJ20)).add ((((NearOneScalarInterval.Jet3.pi).mul (NearOneScalarInterval.Jet3.rational (1 / 2 : ℚ))).add ((cJ5).mul (cJ31))).neg)).widenAll cQ61_cJ60v cQ61_cJ60d0 cQ61_cJ60d1 cQ61_cJ60d2 (by
    norm_num [cJ8, cJ20, cJ5, cJ31, cQ61_cJ60v, cQ61_cJ60d0, cQ61_cJ60d1, cQ61_cJ60d2])
private abbrev cQ62_cJ61v : LeanSuffixReflective.QInterval := ⟨(-12302704992781333461263 / 633825300114114700748351602688 : ℚ), (32894694401951354676891 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d0 : LeanSuffixReflective.QInterval := ⟨(-4928572657751241975103381 / 1267650600228229401496703205376 : ℚ), (5356937247630244081257913 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d1 : LeanSuffixReflective.QInterval := ⟨(9024607809996343785 / 1267650600228229401496703205376 : ℚ), (38028055516083198669 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d2 : LeanSuffixReflective.QInterval := ⟨(3624226379155599668644439479 / 1267650600228229401496703205376 : ℚ), (3624226426234580456162075425 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ61 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.pi).mul ((cJ4).add ((cJ3).neg))).mul ((cJ8).add (cJ59))).add (((cJ8).mul (cJ8)).mul ((cJ58).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ59)).add (NearOneScalarInterval.Jet3.rational (1 : ℚ))).mul (cJ49))))).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul ((cJ59).mul (cJ59))).mul ((cJ31).add ((cJ8).mul (cJ22)))).neg)).widenAll cQ62_cJ61v cQ62_cJ61d0 cQ62_cJ61d1 cQ62_cJ61d2 (by
    norm_num [cJ4, cJ3, cJ8, cJ59, cJ58, cJ49, cJ31, cJ22, cQ62_cJ61v, cQ62_cJ61d0, cQ62_cJ61d1, cQ62_cJ61d2])
private abbrev cQ63_cJ62v : LeanSuffixReflective.QInterval := ⟨(-252292973260580683140090599 / 1267650600228229401496703205376 : ℚ), (-63073243315145170785022639 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d0 : LeanSuffixReflective.QInterval := ⟨(-10275555677603909614567076845 / 633825300114114700748351602688 : ℚ), (-20551111355207819229134153627 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d1 : LeanSuffixReflective.QInterval := ⟨(907726046832662447339360111 / 633825300114114700748351602688 : ℚ), (907726046832662447339360123 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d2 : LeanSuffixReflective.QInterval := ⟨(-906655530821427556244585765 / 1267650600228229401496703205376 : ℚ), (-906655530821427556244585755 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ62 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ3).add ((cJ4).neg)).mul (cJ20)).add ((cJ59).mul (cJ22))).add (((cJ8).mul (cJ49)).neg)).widenAll cQ63_cJ62v cQ63_cJ62d0 cQ63_cJ62d1 cQ63_cJ62d2 (by
    norm_num [cJ3, cJ4, cJ20, cJ59, cJ22, cJ8, cJ49, cQ63_cJ62v, cQ63_cJ62d0, cQ63_cJ62d1, cQ63_cJ62d2])
private abbrev cQ64_cJ63v : LeanSuffixReflective.QInterval := ⟨(116632547820741250709643418997 / 316912650057057350374175801344 : ℚ), (233265095641482501419286837995 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d0 : LeanSuffixReflective.QInterval := ⟨(-98617262410056593419099821617 / 1267650600228229401496703205376 : ℚ), (-98617262410056593419099821615 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d1 : LeanSuffixReflective.QInterval := ⟨(-773158011397283340036848393 / 1267650600228229401496703205376 : ℚ), (-96644751424660417504606049 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d2 : LeanSuffixReflective.QInterval := ⟨(96644751424660417504606049 / 158456325028528675187087900672 : ℚ), (773158011397283340036848393 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ63 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ4).add ((cJ3).neg)).widenAll cQ64_cJ63v cQ64_cJ63d0 cQ64_cJ63d1 cQ64_cJ63d2 (by
    norm_num [cJ4, cJ3, cQ64_cJ63v, cQ64_cJ63d0, cQ64_cJ63d1, cQ64_cJ63d2])
def centerModel : SourceJet.Model centerBox :=
  { a := cJ3
    b := cJ4
    hFour := cJ8
    hThree := cJ59
    shapeThree := cJ35
    bSubA := cJ63
    fold := cJ60
    area := cJ61
    gap := cJ62 }
@[simp] theorem centerA_value (s e4 e3 : ℝ) :
    centerModel.a.value s e4 e3 = aAt s e4 := by
  simp [centerModel, aAt, bAt, cJ0, cJ1, cJ2, cJ3, cJ4, cJ5, cJ6, cJ7, cJ8, cJ9, cJ10, cJ11, cJ12, cJ13, cJ14, cJ15, cJ16, cJ17, cJ18, cJ19, cJ20, cJ21, cJ22, cJ23, cJ24, cJ25, cJ26, cJ27, cJ28, cJ29, cJ30, cJ31, cJ32, cJ33, cJ34, cJ35, cJ36, cJ37, cJ38, cJ39, cJ40, cJ41, cJ42, cJ43, cJ44, cJ45, cJ46, cJ47, cJ48, cJ49, cJ50, cJ51, cJ52, cJ53, cJ54, cJ55, cJ56, cJ57, cJ58, cJ59, cJ60, cJ61, cJ62, cJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem centerB_value (s e4 e3 : ℝ) :
    centerModel.b.value s e4 e3 = bAt s e3 := by
  simp [centerModel, aAt, bAt, cJ0, cJ1, cJ2, cJ3, cJ4, cJ5, cJ6, cJ7, cJ8, cJ9, cJ10, cJ11, cJ12, cJ13, cJ14, cJ15, cJ16, cJ17, cJ18, cJ19, cJ20, cJ21, cJ22, cJ23, cJ24, cJ25, cJ26, cJ27, cJ28, cJ29, cJ30, cJ31, cJ32, cJ33, cJ34, cJ35, cJ36, cJ37, cJ38, cJ39, cJ40, cJ41, cJ42, cJ43, cJ44, cJ45, cJ46, cJ47, cJ48, cJ49, cJ50, cJ51, cJ52, cJ53, cJ54, cJ55, cJ56, cJ57, cJ58, cJ59, cJ60, cJ61, cJ62, cJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem centerFold_value (s e4 e3 : ℝ) :
    centerModel.fold.value s e4 e3 = F s (aAt s e4) := by
  simp [centerModel, aAt, bAt, cJ0, cJ1, cJ2, cJ3, cJ4, cJ5, cJ6, cJ7, cJ8, cJ9, cJ10, cJ11, cJ12, cJ13, cJ14, cJ15, cJ16, cJ17, cJ18, cJ19, cJ20, cJ21, cJ22, cJ23, cJ24, cJ25, cJ26, cJ27, cJ28, cJ29, cJ30, cJ31, cJ32, cJ33, cJ34, cJ35, cJ36, cJ37, cJ38, cJ39, cJ40, cJ41, cJ42, cJ43, cJ44, cJ45, cJ46, cJ47, cJ48, cJ49, cJ50, cJ51, cJ52, cJ53, cJ54, cJ55, cJ56, cJ57, cJ58, cJ59, cJ60, cJ61, cJ62, cJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem centerArea_value (s e4 e3 : ℝ) :
    centerModel.area.value s e4 e3 = E s (aAt s e4) (bAt s e3) := by
  simp [centerModel, aAt, bAt, cJ0, cJ1, cJ2, cJ3, cJ4, cJ5, cJ6, cJ7, cJ8, cJ9, cJ10, cJ11, cJ12, cJ13, cJ14, cJ15, cJ16, cJ17, cJ18, cJ19, cJ20, cJ21, cJ22, cJ23, cJ24, cJ25, cJ26, cJ27, cJ28, cJ29, cJ30, cJ31, cJ32, cJ33, cJ34, cJ35, cJ36, cJ37, cJ38, cJ39, cJ40, cJ41, cJ42, cJ43, cJ44, cJ45, cJ46, cJ47, cJ48, cJ49, cJ50, cJ51, cJ52, cJ53, cJ54, cJ55, cJ56, cJ57, cJ58, cJ59, cJ60, cJ61, cJ62, cJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem centerGap_value (s e4 e3 : ℝ) :
    centerModel.gap.value s e4 e3 = J s (aAt s e4) (bAt s e3) := by
  simp [centerModel, aAt, bAt, cJ0, cJ1, cJ2, cJ3, cJ4, cJ5, cJ6, cJ7, cJ8, cJ9, cJ10, cJ11, cJ12, cJ13, cJ14, cJ15, cJ16, cJ17, cJ18, cJ19, cJ20, cJ21, cJ22, cJ23, cJ24, cJ25, cJ26, cJ27, cJ28, cJ29, cJ30, cJ31, cJ32, cJ33, cJ34, cJ35, cJ36, cJ37, cJ38, cJ39, cJ40, cJ41, cJ42, cJ43, cJ44, cJ45, cJ46, cJ47, cJ48, cJ49, cJ50, cJ51, cJ52, cJ53, cJ54, cJ55, cJ56, cJ57, cJ58, cJ59, cJ60, cJ61, cJ62, cJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem centerHFour_value (s e4 e3 : ℝ) :
    centerModel.hFour.value s e4 e3 = hFour s (aAt s e4) := by
  simp [centerModel, aAt, bAt, cJ0, cJ1, cJ2, cJ3, cJ4, cJ5, cJ6, cJ7, cJ8, cJ9, cJ10, cJ11, cJ12, cJ13, cJ14, cJ15, cJ16, cJ17, cJ18, cJ19, cJ20, cJ21, cJ22, cJ23, cJ24, cJ25, cJ26, cJ27, cJ28, cJ29, cJ30, cJ31, cJ32, cJ33, cJ34, cJ35, cJ36, cJ37, cJ38, cJ39, cJ40, cJ41, cJ42, cJ43, cJ44, cJ45, cJ46, cJ47, cJ48, cJ49, cJ50, cJ51, cJ52, cJ53, cJ54, cJ55, cJ56, cJ57, cJ58, cJ59, cJ60, cJ61, cJ62, cJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem centerShape_value (s e4 e3 : ℝ) :
    centerModel.shapeThree.value s e4 e3 = xCoord s (2 * bAt s e3) := by
  simp [centerModel, aAt, bAt, cJ0, cJ1, cJ2, cJ3, cJ4, cJ5, cJ6, cJ7, cJ8, cJ9, cJ10, cJ11, cJ12, cJ13, cJ14, cJ15, cJ16, cJ17, cJ18, cJ19, cJ20, cJ21, cJ22, cJ23, cJ24, cJ25, cJ26, cJ27, cJ28, cJ29, cJ30, cJ31, cJ32, cJ33, cJ34, cJ35, cJ36, cJ37, cJ38, cJ39, cJ40, cJ41, cJ42, cJ43, cJ44, cJ45, cJ46, cJ47, cJ48, cJ49, cJ50, cJ51, cJ52, cJ53, cJ54, cJ55, cJ56, cJ57, cJ58, cJ59, cJ60, cJ61, cJ62, cJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring
@[simp] theorem centerBSubA_value (s e4 e3 : ℝ) :
    centerModel.bSubA.value s e4 e3 = bAt s e3 - aAt s e4 := by
  simp [centerModel, aAt, bAt, cJ0, cJ1, cJ2, cJ3, cJ4, cJ5, cJ6, cJ7, cJ8, cJ9, cJ10, cJ11, cJ12, cJ13, cJ14, cJ15, cJ16, cJ17, cJ18, cJ19, cJ20, cJ21, cJ22, cJ23, cJ24, cJ25, cJ26, cJ27, cJ28, cJ29, cJ30, cJ31, cJ32, cJ33, cJ34, cJ35, cJ36, cJ37, cJ38, cJ39, cJ40, cJ41, cJ42, cJ43, cJ44, cJ45, cJ46, cJ47, cJ48, cJ49, cJ50, cJ51, cJ52, cJ53, cJ54, cJ55, cJ56, cJ57, cJ58, cJ59, cJ60, cJ61, cJ62, cJ63, NearOneScalarNormalization.F, NearOneScalarNormalization.E, NearOneScalarNormalization.J, NearOneScalarNormalization.hFour, NearOneScalarNormalization.hThree, NearOneScalarNormalization.K, NearOneScalarNormalization.D, NearOneScalarNormalization.H, NearOneScalarNormalization.rho, NearOneScalarNormalization.U, NearOneScalarNormalization.V, NearOneScalarNormalization.uInner, NearOneScalarNormalization.vInner, NearOneScalarNormalization.xCoord, NearOneScalarNormalization.lam, div_eq_mul_inv, mul_inv_rev] <;> ring

def foldLoRange : LeanSuffixReflective.QInterval := centeredRange wholeModel.fold centerModel.fold tDisp e4LoDisp zeroDisp
def foldHiRange : LeanSuffixReflective.QInterval := centeredRange wholeModel.fold centerModel.fold tDisp e4HiDisp zeroDisp
def areaLoRange : LeanSuffixReflective.QInterval := centeredRange wholeModel.area centerModel.area tDisp e4FullDisp e3LoDisp
def areaHiRange : LeanSuffixReflective.QInterval := centeredRange wholeModel.area centerModel.area tDisp e4FullDisp e3HiDisp
def hFourRange : LeanSuffixReflective.QInterval := centeredRange wholeModel.hFour centerModel.hFour tDisp e4FullDisp e3FullDisp
def shapeRange : LeanSuffixReflective.QInterval := centeredRange wholeModel.shapeThree centerModel.shapeThree tDisp e4FullDisp e3FullDisp
def bSubARange : LeanSuffixReflective.QInterval := centeredRange wholeModel.bSubA centerModel.bSubA tDisp e4FullDisp e3FullDisp
def gapRange : LeanSuffixReflective.QInterval := centeredRange wholeModel.gap centerModel.gap tDisp e4FullDisp e3FullDisp

theorem foldLoRange_lo : foldLoRange.lo = (142379760554363627912140833541613 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [foldLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldLoRange_hi : foldLoRange.hi = (61618735560572305011458006058529 / 81995453915767364202846465406961451008 : ℚ) := by norm_num [foldLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldHiRange_lo : foldHiRange.lo = (-60088455499292845955247523975713 / 81995453915767364202846465406961451008 : ℚ) := by norm_num [foldHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldHiRange_hi : foldHiRange.hi = (-130137520064127955462456976879085 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [foldHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaLoRange_lo : areaLoRange.lo = (-1751734980677383865139172615807381 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [areaLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaLoRange_hi : areaLoRange.hi = (-75474214655185077177265213315175 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [areaLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaHiRange_lo : areaHiRange.lo = (79763621456941435746265959954535 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [areaHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaHiRange_hi : areaHiRange.hi = (1756024387479140223708173362446741 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [areaHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem hFourRange_lo : hFourRange.lo = (327909554477981189695013552364997424557 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [hFourRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem hFourRange_hi : hFourRange.hi = (327911004386726491443028241712908536403 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [hFourRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem shapeRange_lo : shapeRange.lo = (40961067273958857879082104474305729965 / 40997726957883682101423232703480725504 : ℚ) := by norm_num [shapeRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem shapeRange_hi : shapeRange.hi = (40961808286215436974470689448686404691 / 40997726957883682101423232703480725504 : ℚ) := by norm_num [shapeRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem bSubARange_lo : bSubARange.lo = (2807045308842000709581334961566923293 / 7627484085187661786311299107624321024 : ℚ) := by norm_num [bSubARange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem bSubARange_hi : bSubARange.hi = (2807201406506381716898196906821150179 / 7627484085187661786311299107624321024 : ℚ) := by norm_num [bSubARange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem gapRange_lo : gapRange.lo = (-66209304948614892057618146916347441 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [gapRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem gapRange_hi : gapRange.hi = (-64343242313448519239949404644909519 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [gapRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]

theorem checks :
    0 < foldLoRange.lo ∧ foldHiRange.hi < 0 ∧
    areaLoRange.hi < 0 ∧ 0 < areaHiRange.lo ∧ gapRange.hi < 0 ∧
    0 < hFourRange.lo ∧ hFourRange.hi < 1 ∧
    0 < shapeRange.lo ∧ shapeRange.hi < 1 ∧ 0 < bSubARange.lo := by
  rw [foldLoRange_lo, foldHiRange_hi, areaLoRange_hi, areaHiRange_lo,
    gapRange_hi, hFourRange_lo, hFourRange_hi, shapeRange_lo, shapeRange_hi,
    bSubARange_lo]
  norm_num

theorem wholeCenter : wholeBox.Contains (tCenter : ℝ) 0 0 := by norm_num [Box3.Contains, wholeBox, tCenter, LeanSuffixReflective.QInterval.RealContains]
theorem centerCenter : centerBox.Contains (tCenter : ℝ) 0 0 := by norm_num [Box3.Contains, centerBox, tCenter, LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.point]
theorem tDisp_contains {t : ℝ} (ht : wholeBox.t.RealContains t) : tDisp.RealContains (t - (tCenter : ℝ)) := by
  norm_num [wholeBox, tDisp, tCenter, LeanSuffixReflective.QInterval.RealContains] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]
theorem e4_contains {e4 : ℝ} (he4 : e4 ∈ Icc (-1 / 8192 : ℝ) (1 / 8192 : ℝ)) : wholeBox.e4.RealContains e4 := by simpa [wholeBox, LeanSuffixReflective.QInterval.RealContains] using he4
theorem e3_contains {e3 : ℝ} (he3 : e3 ∈ Icc (-1 / 2048 : ℝ) (1 / 2048 : ℝ)) : wholeBox.e3.RealContains e3 := by simpa [wholeBox, LeanSuffixReflective.QInterval.RealContains] using he3
theorem replay_sound (whole : NearOneScalarInterval.Jet3 wholeBox) (center : NearOneScalarInterval.Jet3 centerBox)
    (hsame : ∀ t e4 e3, center.value t e4 e3 = whole.value t e4 e3)
    {t e4 e3 : ℝ} (hwhole : wholeBox.Contains t e4 e3)
    (e4d e3d : LeanSuffixReflective.QInterval) (he4d : e4d.RealContains (e4 - 0))
    (he3d : e3d.RealContains (e3 - 0)) :
    (centeredRange whole center tDisp e4d e3d).RealContains (whole.value t e4 e3) :=
  centeredRange_sound whole center (tCenter : ℝ) 0 0 t e4 e3 tDisp e4d e3d
    wholeCenter hwhole centerCenter hsame (tDisp_contains hwhole.1) he4d he3d
private theorem pos_of_mem {i : LeanSuffixReflective.QInterval} {x : ℝ} (hx : i.RealContains x) (hi : 0 < i.lo) : 0 < x := by
  have : (0 : ℝ) < (i.lo : ℝ) := by exact_mod_cast hi
  exact this.trans_le hx.1
private theorem neg_of_mem {i : LeanSuffixReflective.QInterval} {x : ℝ} (hx : i.RealContains x) (hi : i.hi < 0) : x < 0 := by
  have : (i.hi : ℝ) < 0 := by exact_mod_cast hi
  exact hx.2.trans_lt this
private theorem lt_one_of_mem {i : LeanSuffixReflective.QInterval} {x : ℝ} (hx : i.RealContains x) (hi : i.hi < 1) : x < 1 := by
  have : (i.hi : ℝ) < 1 := by exact_mod_cast hi
  exact hx.2.trans_lt this
def certificate {t : ℝ} (ht : wholeBox.t.RealContains t) :
    Certificate t (aAt t) (bAt t) (-1 / 8192 : ℝ) (1 / 8192 : ℝ)
      (-1 / 2048 : ℝ) (1 / 2048 : ℝ) := by
  rcases checks with ⟨hFoldLo, hFoldHi, hAreaLo, hAreaHi, hGap, hH4Lo, hH4Hi, hShapeLo, hShapeHi, hBA⟩
  refine {
    tPos := ?_
    tLtOne := ?_
    e4Ordered := by norm_num
    e3Ordered := by norm_num
    foldLo := ?_
    foldHi := ?_
    areaLo := ?_
    areaHi := ?_
    hFourRegular := ?_
    shapeThreeRegular := ?_
    bAboveA := ?_
    gapNeg := ?_
    foldContinuous := ?_
    areaContinuous := ?_ }
  · exact lt_of_lt_of_le (by norm_num [wholeBox] : (0 : ℝ) < (wholeBox.t.lo : ℝ)) ht.1
  · exact lt_of_le_of_lt ht.2 (by norm_num [wholeBox] : (wholeBox.t.hi : ℝ) < 1)
  · have hm : foldLoRange.RealContains (F t (aAt t (-1 / 8192 : ℝ))) := by
      simpa [foldLoRange] using replay_sound wholeModel.fold centerModel.fold (by simp)
        ⟨ht, by norm_num [wholeBox, LeanSuffixReflective.QInterval.RealContains], by norm_num [wholeBox, LeanSuffixReflective.QInterval.RealContains]⟩
        e4LoDisp zeroDisp (by norm_num [e4LoDisp, LeanSuffixReflective.QInterval.RealContains])
        (by norm_num [zeroDisp, LeanSuffixReflective.QInterval.RealContains])
    exact pos_of_mem hm hFoldLo
  · have hm : foldHiRange.RealContains (F t (aAt t (1 / 8192 : ℝ))) := by
      simpa [foldHiRange] using replay_sound wholeModel.fold centerModel.fold (by simp)
        ⟨ht, by norm_num [wholeBox, LeanSuffixReflective.QInterval.RealContains], by norm_num [wholeBox, LeanSuffixReflective.QInterval.RealContains]⟩
        e4HiDisp zeroDisp (by norm_num [e4HiDisp, LeanSuffixReflective.QInterval.RealContains])
        (by norm_num [zeroDisp, LeanSuffixReflective.QInterval.RealContains])
    exact neg_of_mem hm hFoldHi
  · intro e4 he4
    have hm : areaLoRange.RealContains (E t (aAt t e4) (bAt t (-1 / 2048 : ℝ))) := by
      simpa [areaLoRange] using replay_sound wholeModel.area centerModel.area (by simp)
        ⟨ht, e4_contains he4, by norm_num [wholeBox, LeanSuffixReflective.QInterval.RealContains]⟩
        e4FullDisp e3LoDisp (by simpa [e4FullDisp, wholeBox] using e4_contains he4)
        (by norm_num [e3LoDisp, LeanSuffixReflective.QInterval.RealContains])
    exact neg_of_mem hm hAreaLo
  · intro e4 he4
    have hm : areaHiRange.RealContains (E t (aAt t e4) (bAt t (1 / 2048 : ℝ))) := by
      simpa [areaHiRange] using replay_sound wholeModel.area centerModel.area (by simp)
        ⟨ht, e4_contains he4, by norm_num [wholeBox, LeanSuffixReflective.QInterval.RealContains]⟩
        e4FullDisp e3HiDisp (by simpa [e4FullDisp, wholeBox] using e4_contains he4)
        (by norm_num [e3HiDisp, LeanSuffixReflective.QInterval.RealContains])
    exact pos_of_mem hm hAreaHi
  · intro e4 he4
    have hm : hFourRange.RealContains (hFour t (aAt t e4)) := by
      simpa [hFourRange] using replay_sound wholeModel.hFour centerModel.hFour (by simp)
        ⟨ht, e4_contains he4, by norm_num [wholeBox, LeanSuffixReflective.QInterval.RealContains]⟩
        e4FullDisp e3FullDisp (by simpa [e4FullDisp, wholeBox] using e4_contains he4)
        (by norm_num [e3FullDisp, LeanSuffixReflective.QInterval.RealContains])
    exact ⟨pos_of_mem hm hH4Lo, lt_one_of_mem hm hH4Hi⟩
  · intro e3 he3
    have hm : shapeRange.RealContains (xCoord t (2 * bAt t e3)) := by
      simpa [shapeRange] using replay_sound wholeModel.shapeThree centerModel.shapeThree (by simp)
        ⟨ht, by norm_num [wholeBox, LeanSuffixReflective.QInterval.RealContains], e3_contains he3⟩
        e4FullDisp e3FullDisp (by norm_num [e4FullDisp, LeanSuffixReflective.QInterval.RealContains])
        (by simpa [e3FullDisp, wholeBox] using e3_contains he3)
    exact ⟨pos_of_mem hm hShapeLo, lt_one_of_mem hm hShapeHi⟩
  · intro e4 he4 e3 he3
    have hm : bSubARange.RealContains (bAt t e3 - aAt t e4) := by
      simpa [bSubARange] using replay_sound wholeModel.bSubA centerModel.bSubA (by simp)
        ⟨ht, e4_contains he4, e3_contains he3⟩ e4FullDisp e3FullDisp
        (by simpa [e4FullDisp, wholeBox] using e4_contains he4)
        (by simpa [e3FullDisp, wholeBox] using e3_contains he3)
    linarith [pos_of_mem hm hBA]
  · intro e4 he4 e3 he3
    have hm : gapRange.RealContains (J t (aAt t e4) (bAt t e3)) := by
      simpa [gapRange] using replay_sound wholeModel.gap centerModel.gap (by simp)
        ⟨ht, e4_contains he4, e3_contains he3⟩ e4FullDisp e3FullDisp
        (by simpa [e4FullDisp, wholeBox] using e4_contains he4)
        (by simpa [e3FullDisp, wholeBox] using e3_contains he3)
    exact neg_of_mem hm hGap
  · intro e4 he4
    have hd := wholeModel.fold.hasDerivAt_e4
      ⟨ht, e4_contains he4, by norm_num [wholeBox, LeanSuffixReflective.QInterval.RealContains]⟩
    simpa using hd.continuousAt.continuousWithinAt
  · intro e4 he4 e3 he3
    have hd := wholeModel.area.hasDerivAt_e3 ⟨ht, e4_contains he4, e3_contains he3⟩
    simpa using hd.continuousAt.continuousWithinAt
theorem stress_exclusion {t : ℝ} (ht : wholeBox.t.RealContains t) :=
  (certificate ht).stationaryEqualAreaPair_strictImprovement
theorem candidate_exclusion {t : ℝ} (ht : wholeBox.t.RealContains t)
    (candidate : FourArcCandidate (lam t))
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer :=
  (certificate ht).candidate_not_isWeightedPerimeterMinimizer candidate hcandidate
end Band10Cell33
end
end NearOneScalarStress

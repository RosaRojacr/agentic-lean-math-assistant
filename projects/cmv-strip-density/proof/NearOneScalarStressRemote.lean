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
namespace Remote
def wholeBox : Box3 := { t := ⟨(1 / 10 : ℚ), (101 / 1000 : ℚ), by norm_num⟩, e4 := ⟨(-1 / 8192 : ℚ), (1 / 8192 : ℚ), by norm_num⟩, e3 := ⟨(-1 / 1024 : ℚ), (1 / 1024 : ℚ), by norm_num⟩ }
def centerBox : Box3 := { t := ⟨(201 / 2000 : ℚ), (201 / 2000 : ℚ), by norm_num⟩, e4 := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩, e3 := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩ }
def aAt (t e4 : ℝ) : ℝ := ((246309387612851321557664008517088691 / 664613997892457936451903530140172288 : ℚ) : ℝ) + ((-85449082611111897527428630004824171 / 166153499473114484112975882535043072 : ℚ) : ℝ) * t + t ^ 2 * e4
def bAt (t e3 : ℝ) : ℝ := ((491428936655935943218204634130007581 / 664613997892457936451903530140172288 : ℚ) : ℝ) + ((-762754965044736485022862217735664531 / 1329227995784915872903807060280344576 : ℚ) : ℝ) * t + t ^ 2 * e3

def tCenter : ℚ := (201 / 2000 : ℚ)
def tDisp : LeanSuffixReflective.QInterval := ⟨(-1 / 2000 : ℚ), (1 / 2000 : ℚ), by norm_num⟩
def zeroDisp : LeanSuffixReflective.QInterval := LeanSuffixReflective.QInterval.point 0
def e4LoDisp : LeanSuffixReflective.QInterval := LeanSuffixReflective.QInterval.point (-1 / 8192 : ℚ)
def e4HiDisp : LeanSuffixReflective.QInterval := LeanSuffixReflective.QInterval.point (1 / 8192 : ℚ)
def e3LoDisp : LeanSuffixReflective.QInterval := LeanSuffixReflective.QInterval.point (-1 / 1024 : ℚ)
def e3HiDisp : LeanSuffixReflective.QInterval := LeanSuffixReflective.QInterval.point (1 / 1024 : ℚ)
def e4FullDisp : LeanSuffixReflective.QInterval := wholeBox.e4
def e3FullDisp : LeanSuffixReflective.QInterval := wholeBox.e3

@[simp] private abbrev wJ0 : NearOneScalarInterval.Jet3 wholeBox := NearOneScalarInterval.Jet3.tVar wholeBox
@[simp] private abbrev wJ1 : NearOneScalarInterval.Jet3 wholeBox := NearOneScalarInterval.Jet3.e4Var wholeBox
@[simp] private abbrev wJ2 : NearOneScalarInterval.Jet3 wholeBox := NearOneScalarInterval.Jet3.e3Var wholeBox
private abbrev wQ4_wJ3v : LeanSuffixReflective.QInterval := ⟨(201975947031517646364043105365 / 633825300114114700748351602688 : ℚ), (404606975883194026850609846609 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d0 : LeanSuffixReflective.QInterval := ⟨(-651956021559538537329515589521 / 1267650600228229401496703205376 : ℚ), (-325946752793777312812816591873 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d1 : LeanSuffixReflective.QInterval := ⟨(12676506002282294014967032053 / 1267650600228229401496703205376 : ℚ), (12931303772928168124667869399 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ3 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (246309387612851321557664008517088691 / 664613997892457936451903530140172288 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-85449082611111897527428630004824171 / 166153499473114484112975882535043072 : ℚ)).mul (wJ0))).add (((wJ0).mul (wJ0)).mul (wJ1))).widenAll wQ4_wJ3v wQ4_wJ3d0 wQ4_wJ3d1 wQ4_wJ3d2 (by
    norm_num [wJ0, wJ1, wQ4_wJ3v, wQ4_wJ3d0, wQ4_wJ3d1, wQ4_wJ3d2])
private abbrev wQ5_wJ4v : LeanSuffixReflective.QInterval := ⟨(863844280421533606533947491045 / 1267650600228229401496703205376 : ℚ), (864596956694089619043619829545 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d0 : LeanSuffixReflective.QInterval := ⟨(-181917470940611957029844047499 / 316912650057057350374175801344 : ℚ), (-11362027437290258351379952247 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d2 : LeanSuffixReflective.QInterval := ⟨(12676506002282294014967032053 / 1267650600228229401496703205376 : ℚ), (12931303772928168124667869399 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ4 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (491428936655935943218204634130007581 / 664613997892457936451903530140172288 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-762754965044736485022862217735664531 / 1329227995784915872903807060280344576 : ℚ)).mul (wJ0))).add (((wJ0).mul (wJ0)).mul (wJ2))).widenAll wQ5_wJ4v wQ5_wJ4d0 wQ5_wJ4d1 wQ5_wJ4d2 (by
    norm_num [wJ0, wJ2, wQ5_wJ4v, wQ5_wJ4d0, wQ5_wJ4d1, wQ5_wJ4d2])
private abbrev wQ6_wJ5v : LeanSuffixReflective.QInterval := ⟨(12676506002282294014967032053 / 1267650600228229401496703205376 : ℚ), (12931303772928168124667869399 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d0 : LeanSuffixReflective.QInterval := ⟨(253530120045645880299340641075 / 1267650600228229401496703205376 : ℚ), (128032710623051169551167023743 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ5 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ6_wJ5v wQ6_wJ5d0 wQ6_wJ5d1 wQ6_wJ5d2 (by
    norm_num [wJ0, wQ6_wJ5v, wQ6_wJ5d0, wQ6_wJ5d1, wQ6_wJ5d2])
private abbrev wQ7_wJ6v : LeanSuffixReflective.QInterval := ⟨(12676506002282294014967032053 / 1267650600228229401496703205376 : ℚ), (12931303772928168124667869399 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d0 : LeanSuffixReflective.QInterval := ⟨(253530120045645880299340641075 / 1267650600228229401496703205376 : ℚ), (128032710623051169551167023743 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ6 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ7_wJ6v wQ7_wJ6d0 wQ7_wJ6d1 wQ7_wJ6d2 (by
    norm_num [wJ0, wQ7_wJ6v, wQ7_wJ6d0, wQ7_wJ6d1, wQ7_wJ6d2])
private abbrev wQ8_wJ7v : LeanSuffixReflective.QInterval := ⟨(32181015156647871357780061567 / 316912650057057350374175801344 : ℚ), (129141898330556996304887659767 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d0 : LeanSuffixReflective.QInterval := ⟨(-52022606671852437188810270103 / 158456325028528675187087900672 : ℚ), (-207733594937022597361567948305 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d1 : LeanSuffixReflective.QInterval := ⟨(4039518940630352927280862107 / 633825300114114700748351602688 : ℚ), (2063697880492231133951535523 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ7 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ3).mul (wJ3)).widenAll wQ8_wJ7v wQ8_wJ7d0 wQ8_wJ7d1 wQ8_wJ7d2 (by
    norm_num [wJ3, wQ8_wJ7v, wQ8_wJ7d0, wQ8_wJ7d1, wQ8_wJ7d2])
private abbrev wQ9_wJ8v : LeanSuffixReflective.QInterval := ⟨(631761602233622469614400067165 / 633825300114114700748351602688 : ℚ), (1263611081287599048569422343269 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d0 : LeanSuffixReflective.QInterval := ⟨(-37605837036264823583783428589 / 633825300114114700748351602688 : ℚ), (-4633735964792387870394928351 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d1 : LeanSuffixReflective.QInterval := ⟨(-16489028723455030379967117 / 158456325028528675187087900672 : ℚ), (-7922816251426433759354395 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ8 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ6).mul (wJ3)).neg)).widenAll wQ9_wJ8v wQ9_wJ8d0 wQ9_wJ8d1 wQ9_wJ8d2 (by
    norm_num [wJ6, wJ3, wQ9_wJ8v, wQ9_wJ8d0, wQ9_wJ8d1, wQ9_wJ8d2])
private abbrev wQ10_wJ9v : LeanSuffixReflective.QInterval := ⟨(403293205810600286768433131221 / 633825300114114700748351602688 : ℚ), (201981677790030534711727122689 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d0 : LeanSuffixReflective.QInterval := ⟨(-662922017341554567982693563675 / 633825300114114700748351602688 : ℚ), (-662643181207575507321692994111 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d1 : LeanSuffixReflective.QInterval := ⟨(12634402438124491515372152825 / 633825300114114700748351602688 : ℚ), (6445454291760932297697530389 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ9 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ3)).add (((wJ6).mul (wJ7)).neg)).widenAll wQ10_wJ9v wQ10_wJ9d0 wQ10_wJ9d1 wQ10_wJ9d2 (by
    norm_num [wJ3, wJ6, wJ7, wQ10_wJ9v, wQ10_wJ9d0, wQ10_wJ9d1, wQ10_wJ9d2])
private abbrev wQ11_wJ10v : LeanSuffixReflective.QInterval := ⟨(530121648363434638388178286919 / 633825300114114700748351602688 : ℚ), (532062022318006059096141137589 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d0 : LeanSuffixReflective.QInterval := ⟨(37953992755445705769812690507 / 39614081257132168796771975168 : ℚ), (1215239084765570768272386241767 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d1 : LeanSuffixReflective.QInterval := ⟨(12634402438124491515372152825 / 633825300114114700748351602688 : ℚ), (6445454291760932297697530389 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ10 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ3)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ0))).add (((wJ6).mul (wJ7)).neg)).add (((wJ0).mul (wJ0)).mul ((wJ0).mul (wJ0)))).widenAll wQ11_wJ10v wQ11_wJ10d0 wQ11_wJ10d1 wQ11_wJ10d2 (by
    norm_num [wJ3, wJ0, wJ6, wJ7, wQ11_wJ10v, wQ11_wJ10d0, wQ11_wJ10d1, wQ11_wJ10d2])
private abbrev wQ11_root11 : LeanSuffixReflective.QInterval := ⟨(1011172462455118787410618600743 / 1267650600228229401496703205376 : ℚ), (506006121589094057059764822039 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11v : LeanSuffixReflective.QInterval := ⟨(1011172462455118787410618600743 / 1267650600228229401496703205376 : ℚ), (506006121589094057059764822039 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d0 : LeanSuffixReflective.QInterval := ⟨(-415534206275336392674389537129 / 633825300114114700748351602688 : ℚ), (-415014755037417605624131222471 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d1 : LeanSuffixReflective.QInterval := ⟨(1978237904503484450312634535 / 158456325028528675187087900672 : ℚ), (8080307074281126439108206341 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ11 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ9).sqrt wQ11_root11 (by norm_num [wQ11_root11]) (by norm_num [wJ9, wQ11_root11]) (by norm_num [wJ9, wQ11_root11])).widenAll wQ12_wJ11v wQ12_wJ11d0 wQ12_wJ11d1 wQ12_wJ11d2 (by
    norm_num [wJ9, wQ11_root11, NearOneScalarInterval.Jet3.sqrt, wQ12_wJ11v, wQ12_wJ11d0, wQ12_wJ11d1, wQ12_wJ11d2])
private abbrev wQ12_root12 : LeanSuffixReflective.QInterval := ⟨(579658962555521211506250310185 / 633825300114114700748351602688 : ℚ), (1161437679731517896417465564837 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12v : LeanSuffixReflective.QInterval := ⟨(579658962555521211506250310185 / 633825300114114700748351602688 : ℚ), (1161437679731517896417465564837 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d0 : LeanSuffixReflective.QInterval := ⟨(662797875937628677400894948541 / 1267650600228229401496703205376 : ℚ), (664398661426858839568187517175 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d1 : LeanSuffixReflective.QInterval := ⟨(13789812500241799042503689095 / 1267650600228229401496703205376 : ℚ), (14095501889029730507187727957 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ12 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ10).sqrt wQ12_root12 (by norm_num [wQ12_root12]) (by norm_num [wJ10, wQ12_root12]) (by norm_num [wJ10, wQ12_root12])).widenAll wQ13_wJ12v wQ13_wJ12d0 wQ13_wJ12d1 wQ13_wJ12d2 (by
    norm_num [wJ10, wQ12_root12, NearOneScalarInterval.Jet3.sqrt, wQ13_wJ12v, wQ13_wJ12d0, wQ13_wJ12d1, wQ13_wJ12d2])
private abbrev wQ14_wJ13v : LeanSuffixReflective.QInterval := ⟨(1268918250828457630898199908581 / 1267650600228229401496703205376 : ℚ), (634478330954647573238647330093 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d0 : LeanSuffixReflective.QInterval := ⟨(38029518006846882044901096161 / 1267650600228229401496703205376 : ℚ), (38793911318784504374003608195 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ13 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0))).widenAll wQ14_wJ13v wQ14_wJ13d0 wQ14_wJ13d1 wQ14_wJ13d2 (by
    norm_num [wJ0, wQ14_wJ13v, wQ14_wJ13d0, wQ14_wJ13d1, wQ14_wJ13d2])
private abbrev wQ15_wJ14v : LeanSuffixReflective.QInterval := ⟨(2171501560028616329210529839713 / 1267650600228229401496703205376 : ℚ), (543623150033966185232290168607 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d0 : LeanSuffixReflective.QInterval := ⟨(-138791613355909915046983200125 / 1267650600228229401496703205376 : ℚ), (-135490267480069116034923224513 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d1 : LeanSuffixReflective.QInterval := ⟨(29631541639505702520607266451 / 1267650600228229401496703205376 : ℚ), (1892047895906866326444176243 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ14 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ12).add ((wJ13).mul (wJ11))).widenAll wQ15_wJ14v wQ15_wJ14d0 wQ15_wJ14d1 wQ15_wJ14d2 (by
    norm_num [wJ12, wJ13, wJ11, wQ15_wJ14v, wQ15_wJ14d0, wQ15_wJ14d1, wQ15_wJ14d2])
private abbrev wQ16_wJ15v : LeanSuffixReflective.QInterval := ⟨(1584122628127887233503496977499 / 1267650600228229401496703205376 : ℚ), (397631231259173847243167750401 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d0 : LeanSuffixReflective.QInterval := ⟨(-500751935723334631545461719659 / 1267650600228229401496703205376 : ℚ), (-30660974244545461664518705009 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d1 : LeanSuffixReflective.QInterval := ⟨(65252311269904424600852631069 / 1267650600228229401496703205376 : ℚ), (33422342394798543322395159529 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ15 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ11).mul (wJ12)).mul (wJ14)).widenAll wQ16_wJ15v wQ16_wJ15d0 wQ16_wJ15d1 wQ16_wJ15d2 (by
    norm_num [wJ11, wJ12, wJ14, wQ16_wJ15v, wQ16_wJ15d0, wQ16_wJ15d1, wQ16_wJ15d2])
private abbrev wQ17_wJ16v : LeanSuffixReflective.QInterval := ⟨(135854566349290309096233773097 / 79228162514264337593543950336 : ℚ), (1088366491018138661253802364801 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d0 : LeanSuffixReflective.QInterval := ⟨(-73789563693083632512050126773 / 1267650600228229401496703205376 : ℚ), (-2158742522049728640134470113 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d1 : LeanSuffixReflective.QInterval := ⟨(29661173181145208223127873717 / 1267650600228229401496703205376 : ℚ), (7575989098984268266908712017 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ16 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ13).mul (wJ14)).widenAll wQ17_wJ16v wQ17_wJ16d0 wQ17_wJ16d1 wQ17_wJ16d2 (by
    norm_num [wJ13, wJ14, wQ17_wJ16v, wQ17_wJ16d0, wQ17_wJ16d1, wQ17_wJ16d2])
private abbrev wQ18_wJ17v : LeanSuffixReflective.QInterval := ⟨(2172213269023513062620960238967 / 1267650600228229401496703205376 : ℚ), (2175837246366099182925989335385 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d0 : LeanSuffixReflective.QInterval := ⟨(-112579832776971119553297421635 / 1267650600228229401496703205376 : ℚ), (-25489023957870115126670566963 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d1 : LeanSuffixReflective.QInterval := ⟨(7406269029456547582568852455 / 316912650057057350374175801344 : ℚ), (1894491184444999801571178821 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ17 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ11).add (wJ12)).mul (((wJ8).mul (wJ8)).add ((wJ6).mul ((wJ11).mul (wJ12))))).widenAll wQ18_wJ17v wQ18_wJ17d0 wQ18_wJ17d1 wQ18_wJ17d2 (by
    norm_num [wJ11, wJ12, wJ8, wJ6, wQ18_wJ17v, wQ18_wJ17d0, wQ18_wJ17d1, wQ18_wJ17d2])
private abbrev wQ19_wJ18v : LeanSuffixReflective.QInterval := ⟨(2520077903775237298560924296729 / 1267650600228229401496703205376 : ℚ), (2520466620608773192539241383501 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d0 : LeanSuffixReflective.QInterval := ⟨(-262260222663276375225531500171 / 1267650600228229401496703205376 : ℚ), (-257194257066719404892958193081 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d1 : LeanSuffixReflective.QInterval := ⟨(-526238455729637133213606549 / 1267650600228229401496703205376 : ℚ), (-505661986427791424679365811 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ18 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul (wJ8)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).widenAll wQ19_wJ18v wQ19_wJ18d0 wQ19_wJ18d1 wQ19_wJ18d2 (by
    norm_num [wJ8, wJ0, wQ19_wJ18v, wQ19_wJ18d0, wQ19_wJ18d1, wQ19_wJ18d2])
private abbrev wQ20_wJ19v : LeanSuffixReflective.QInterval := ⟨(505159654829651982815488883535 / 633825300114114700748351602688 : ℚ), (1014402556800836973394858354623 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d0 : LeanSuffixReflective.QInterval := ⟨(311619127442632771710571105133 / 1267650600228229401496703205376 : ℚ), (320659546742937353824534234711 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d1 : LeanSuffixReflective.QInterval := ⟨(-42804400338153092537000531513 / 1267650600228229401496703205376 : ℚ), (-41449001545425558867851585945 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ19 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ15).invPos (by norm_num [wJ15])).widenAll wQ20_wJ19v wQ20_wJ19d0 wQ20_wJ19d1 wQ20_wJ19d2 (by
    norm_num [wJ15, NearOneScalarInterval.Jet3.invPos, wQ20_wJ19v, wQ20_wJ19d0, wQ20_wJ19d1, wQ20_wJ19d2])
private abbrev wQ21_wJ20v : LeanSuffixReflective.QInterval := ⟨(2008505630472200744042314475739 / 1267650600228229401496703205376 : ℚ), (504233537186110468630113200231 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d0 : LeanSuffixReflective.QInterval := ⟨(204814732447420711092991317391 / 633825300114114700748351602688 : ℚ), (216291208239241444517094941531 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d1 : LeanSuffixReflective.QInterval := ⟨(-21382248366180040188884179875 / 316912650057057350374175801344 : ℚ), (-41401626354424143125952812049 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ20 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ18).mul (wJ19)).widenAll wQ21_wJ20v wQ21_wJ20d0 wQ21_wJ20d1 wQ21_wJ20d2 (by
    norm_num [wJ18, wJ19, wQ21_wJ20v, wQ21_wJ20d0, wQ21_wJ20d1, wQ21_wJ20d2])
private abbrev wQ22_wJ21v : LeanSuffixReflective.QInterval := ⟨(369116942114724002201416699537 / 633825300114114700748351602688 : ℚ), (739273109951755019700921234609 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d0 : LeanSuffixReflective.QInterval := ⟨(23428238781783459717583092985 / 1267650600228229401496703205376 : ℚ), (1568504056490339610577137959 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d1 : LeanSuffixReflective.QInterval := ⟨(-5153235894705676960707526461 / 633825300114114700748351602688 : ℚ), (-2514879324775424760375902793 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ21 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ16).invPos (by norm_num [wJ16])).widenAll wQ22_wJ21v wQ22_wJ21d0 wQ22_wJ21d1 wQ22_wJ21d2 (by
    norm_num [wJ16, NearOneScalarInterval.Jet3.invPos, wQ22_wJ21v, wQ22_wJ21d0, wQ22_wJ21d1, wQ22_wJ21d2])
private abbrev wQ23_wJ22v : LeanSuffixReflective.QInterval := ⟨(5732821370278190935463729949 / 4951760157141521099596496896 : ℚ), (734947467705835009862069728057 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d0 : LeanSuffixReflective.QInterval := ⟨(-106370748787008468095283409201 / 1267650600228229401496703205376 : ℚ), (-24970548168853001051546845533 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d1 : LeanSuffixReflective.QInterval := ⟨(-20799226582193668750090091327 / 1267650600228229401496703205376 : ℚ), (-2536588559559246914367655487 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ22 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ18).mul (wJ21)).widenAll wQ23_wJ22v wQ23_wJ22d0 wQ23_wJ22d1 wQ23_wJ22d2 (by
    norm_num [wJ18, wJ21, wQ23_wJ22v, wQ23_wJ22d0, wQ23_wJ22d1, wQ23_wJ22d2])
private abbrev wQ24_wJ23v : LeanSuffixReflective.QInterval := ⟨(184634448985415082820923362679 / 316912650057057350374175801344 : ℚ), (739769923687726087176014581109 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d0 : LeanSuffixReflective.QInterval := ⟨(17303323220510955643275828377 / 633825300114114700748351602688 : ℚ), (9585059566876187877724062985 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d1 : LeanSuffixReflective.QInterval := ⟨(-5161510129524126193151844213 / 633825300114114700748351602688 : ℚ), (-10055549171797726205263016277 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ23 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ17).invPos (by norm_num [wJ17])).widenAll wQ24_wJ23v wQ24_wJ23d0 wQ24_wJ23d1 wQ24_wJ23d2 (by
    norm_num [wJ17, NearOneScalarInterval.Jet3.invPos, wQ24_wJ23v, wQ24_wJ23d0, wQ24_wJ23d1, wQ24_wJ23d2])
private abbrev wQ25_wJ24v : LeanSuffixReflective.QInterval := ⟨(1473002453833202719548535591321 / 1267650600228229401496703205376 : ℚ), (1475584875122534793954985827937 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d0 : LeanSuffixReflective.QInterval := ⟨(3314657690778108483886047537 / 1267650600228229401496703205376 : ℚ), (6286778859668983575548675657 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d1 : LeanSuffixReflective.QInterval := ⟨(-20744892210985106174987125925 / 1267650600228229401496703205376 : ℚ), (-20203422012665168355765886703 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ24 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).mul (wJ23)).widenAll wQ25_wJ24v wQ25_wJ24d0 wQ25_wJ24d1 wQ25_wJ24d2 (by
    norm_num [wJ8, wJ0, wJ23, wQ25_wJ24v, wQ25_wJ24d0, wQ25_wJ24d1, wQ25_wJ24d2])
private abbrev wQ26_wJ25v : LeanSuffixReflective.QInterval := ⟨(635851516362750895054575265847 / 633825300114114700748351602688 : ℚ), (1271791478445022797922602725043 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d0 : LeanSuffixReflective.QInterval := ⟨(74614554006868719079089254561 / 1267650600228229401496703205376 : ℚ), (37851923030317150333184887277 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d1 : LeanSuffixReflective.QInterval := ⟨(127576842006154599222670681 / 1267650600228229401496703205376 : ℚ), (132775440255835545300105267 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ25 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ8).invPos (by norm_num [wJ8])).widenAll wQ26_wJ25v wQ26_wJ25d0 wQ26_wJ25d1 wQ26_wJ25d2 (by
    norm_num [wJ8, NearOneScalarInterval.Jet3.invPos, wQ26_wJ25v, wQ26_wJ25d0, wQ26_wJ25d1, wQ26_wJ25d2])
private abbrev wQ27_wJ26v : LeanSuffixReflective.QInterval := ⟨(116302403910928810795902265249 / 1267650600228229401496703205376 : ℚ), (58844196066218071520073193211 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d0 : LeanSuffixReflective.QInterval := ⟨(618169757052693779497141927693 / 633825300114114700748351602688 : ℚ), (619780257635915472209015503769 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d1 : LeanSuffixReflective.QInterval := ⟨(697528502485479611083496925 / 633825300114114700748351602688 : ℚ), (1440582845044467730645221353 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ26 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ0).mul (wJ12)).mul (wJ25)).widenAll wQ27_wJ26v wQ27_wJ26d0 wQ27_wJ26d1 wQ27_wJ26d2 (by
    norm_num [wJ0, wJ12, wJ25, wQ27_wJ26v, wQ27_wJ26d0, wQ27_wJ26d1, wQ27_wJ26d2])
private abbrev wQ28_wJ27v : LeanSuffixReflective.QInterval := ⟨(1841253067291503399435669489 / 158456325028528675187087900672 : ℚ), (235194395486327772392731413 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d0 : LeanSuffixReflective.QInterval := ⟨(294633637343548324994545978739 / 1267650600228229401496703205376 : ℚ), (298196407637046994981815481325 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d1 : LeanSuffixReflective.QInterval := ⟨(-26452330680532383511380459 / 158456325028528675187087900672 : ℚ), (-202034220126651683557658867 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ27 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ6).mul (wJ24)).widenAll wQ28_wJ27v wQ28_wJ27d0 wQ28_wJ27d1 wQ28_wJ27d2 (by
    norm_num [wJ6, wJ24, wQ28_wJ27v, wQ28_wJ27d0, wQ28_wJ27d1, wQ28_wJ27d2])
private abbrev wQ29_wJ28v : LeanSuffixReflective.QInterval := ⟨(1264008545748279278092782923929 / 1267650600228229401496703205376 : ℚ), (1264227202958301581659004954413 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d0 : LeanSuffixReflective.QInterval := ⟨(-77788748247654412096756030525 / 1267650600228229401496703205376 : ℚ), (-71715667940197562547597542685 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d1 : LeanSuffixReflective.QInterval := ⟨(-90403925328711573438794175 / 1267650600228229401496703205376 : ℚ), (-80886199282627387914902019 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ28 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ26).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ26]) (by norm_num [wJ26])).widenAll wQ29_wJ28v wQ29_wJ28d0 wQ29_wJ28d1 wQ29_wJ28d2 (by
    norm_num [wJ26, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ29_wJ28v, wQ29_wJ28d0, wQ29_wJ28d1, wQ29_wJ28d2])
private abbrev wQ30_wJ29v : LeanSuffixReflective.QInterval := ⟨(1267591021248189720529721920811 / 1267650600228229401496703205376 : ℚ), (633797842875239950946258732923 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d0 : LeanSuffixReflective.QInterval := ⟨(-2364783446034583306295294925 / 1267650600228229401496703205376 : ℚ), (-2192621727981777997902712633 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d1 : LeanSuffixReflective.QInterval := ⟨(751704655028241621448095 / 633825300114114700748351602688 : ℚ), (1678196842089232071630439 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ29 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ27).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ27]) (by norm_num [wJ27])).widenAll wQ30_wJ29v wQ30_wJ29d0 wQ30_wJ29d1 wQ30_wJ29d2 (by
    norm_num [wJ27, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ30_wJ29v, wQ30_wJ29d0, wQ30_wJ29d1, wQ30_wJ29d2])
private abbrev wQ31_wJ30v : LeanSuffixReflective.QInterval := ⟨(635851516362750895054575265847 / 633825300114114700748351602688 : ℚ), (1271791478445022797922602725043 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d0 : LeanSuffixReflective.QInterval := ⟨(74614554006868719079089254561 / 1267650600228229401496703205376 : ℚ), (37851923030317150333184887277 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d1 : LeanSuffixReflective.QInterval := ⟨(127576842006154599222670681 / 1267650600228229401496703205376 : ℚ), (132775440255835545300105267 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ30 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ8).invPos (by norm_num [wJ8])).widenAll wQ31_wJ30v wQ31_wJ30d0 wQ31_wJ30d1 wQ31_wJ30d2 (by
    norm_num [wJ8, NearOneScalarInterval.Jet3.invPos, wQ31_wJ30v, wQ31_wJ30d0, wQ31_wJ30d1, wQ31_wJ30d2])
private abbrev wQ32_wJ31v : LeanSuffixReflective.QInterval := ⟨(1484530049258173879411299227999 / 1267650600228229401496703205376 : ℚ), (1487375379991895363942099738989 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d0 : LeanSuffixReflective.QInterval := ⟨(119539704807249370237718032723 / 633825300114114700748351602688 : ℚ), (125797654755925464206651701713 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d1 : LeanSuffixReflective.QInterval := ⟨(-5150997350698077741813408737 / 316912650057057350374175801344 : ℚ), (-20056155154367030102946577977 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ31 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ6).mul (wJ12)).mul (wJ30)).mul (wJ28)).add ((wJ24).mul (wJ29))).widenAll wQ32_wJ31v wQ32_wJ31d0 wQ32_wJ31d1 wQ32_wJ31d2 (by
    norm_num [wJ6, wJ12, wJ30, wJ28, wJ24, wJ29, wQ32_wJ31v, wQ32_wJ31d0, wQ32_wJ31d1, wQ32_wJ31d2])
private abbrev wQ33_wJ32v : LeanSuffixReflective.QInterval := ⟨(863844280421533606533947491045 / 633825300114114700748351602688 : ℚ), (864596956694089619043619829545 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d0 : LeanSuffixReflective.QInterval := ⟨(-181917470940611957029844047499 / 158456325028528675187087900672 : ℚ), (-11362027437290258351379952247 / 9903520314283042199192993792 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d2 : LeanSuffixReflective.QInterval := ⟨(12676506002282294014967032053 / 633825300114114700748351602688 : ℚ), (12931303772928168124667869399 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ32 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ4)).widenAll wQ33_wJ32v wQ33_wJ32d0 wQ33_wJ32d1 wQ33_wJ32d2 (by
    norm_num [wJ4, wQ33_wJ32v, wQ33_wJ32d0, wQ33_wJ32d1, wQ33_wJ32d2])
private abbrev wQ34_wJ33v : LeanSuffixReflective.QInterval := ⟨(12676506002282294014967032053 / 1267650600228229401496703205376 : ℚ), (12931303772928168124667869399 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d0 : LeanSuffixReflective.QInterval := ⟨(253530120045645880299340641075 / 1267650600228229401496703205376 : ℚ), (128032710623051169551167023743 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ33 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ34_wJ33v wQ34_wJ33d0 wQ34_wJ33d1 wQ34_wJ33d2 (by
    norm_num [wJ0, wQ34_wJ33v, wQ34_wJ33d0, wQ34_wJ33d1, wQ34_wJ33d2])
private abbrev wQ35_wJ34v : LeanSuffixReflective.QInterval := ⟨(1177338520066405611995999352609 / 633825300114114700748351602688 : ℚ), (1179391067838559964934676726083 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d0 : LeanSuffixReflective.QInterval := ⟨(-3970438963958573241920664601525 / 1267650600228229401496703205376 : ℚ), (-1982127991708224378528373334981 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d2 : LeanSuffixReflective.QInterval := ⟨(69107542433722688522715799279 / 1267650600228229401496703205376 : ℚ), (70558028441891265630911727055 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ34 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ32).mul (wJ32)).widenAll wQ35_wJ34v wQ35_wJ34d0 wQ35_wJ34d1 wQ35_wJ34d2 (by
    norm_num [wJ32, wQ35_wJ34v, wQ35_wJ34d0, wQ35_wJ34d1, wQ35_wJ34d2])
private abbrev wQ36_wJ35v : LeanSuffixReflective.QInterval := ⟨(312502773279439146272243818403 / 316912650057057350374175801344 : ℚ), (1250373714619798729366024255557 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d0 : LeanSuffixReflective.QInterval := ⟨(-334753775384680675403856072261 / 1267650600228229401496703205376 : ℚ), (-82672947800022995506071870847 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d2 : LeanSuffixReflective.QInterval := ⟨(-16489028723455030379967117 / 79228162514264337593543950336 : ℚ), (-253530120045645880299340641 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ35 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ33).mul (wJ32)).neg)).widenAll wQ36_wJ35v wQ36_wJ35d0 wQ36_wJ35d1 wQ36_wJ35d2 (by
    norm_num [wJ33, wJ32, wQ36_wJ35v, wQ36_wJ35d0, wQ36_wJ35d1, wQ36_wJ35d2])
private abbrev wQ37_wJ36v : LeanSuffixReflective.QInterval := ⟨(857828796280023031432798172403 / 316912650057057350374175801344 : ℚ), (1717420528187515181967279665565 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d0 : LeanSuffixReflective.QInterval := ⟨(-3347510966622405050740546690625 / 1267650600228229401496703205376 : ℚ), (-104347249503172718034713588021 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d2 : LeanSuffixReflective.QInterval := ⟨(12496565390248360814791799421 / 316912650057057350374175801344 : ℚ), (12758534916843861403361079901 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ36 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ32)).add (((wJ33).mul (wJ34)).neg)).widenAll wQ37_wJ36v wQ37_wJ36d0 wQ37_wJ36d1 wQ37_wJ36d2 (by
    norm_num [wJ32, wJ33, wJ34, wQ37_wJ36v, wQ37_wJ36d0, wQ37_wJ36d1, wQ37_wJ36d2])
private abbrev wQ38_wJ37v : LeanSuffixReflective.QInterval := ⟨(230310754389110051810667687563 / 79228162514264337593543950336 : ℚ), (3691038389850920343279933115551 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d0 : LeanSuffixReflective.QInterval := ⟨(-807139163765033330141153467051 / 1267650600228229401496703205376 : ℚ), (-798586536920805194195062586683 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d2 : LeanSuffixReflective.QInterval := ⟨(12496565390248360814791799421 / 316912650057057350374175801344 : ℚ), (12758534916843861403361079901 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ37 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ32)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ0))).add (((wJ33).mul (wJ34)).neg)).add (((wJ0).mul (wJ0)).mul ((wJ0).mul (wJ0)))).widenAll wQ38_wJ37v wQ38_wJ37d0 wQ38_wJ37d1 wQ38_wJ37d2 (by
    norm_num [wJ32, wJ0, wJ33, wJ34, wQ38_wJ37v, wQ38_wJ37d0, wQ38_wJ37d1, wQ38_wJ37d2])
private abbrev wQ38_root38 : LeanSuffixReflective.QInterval := ⟨(2085595539405884629464626868213 / 1267650600228229401496703205376 : ℚ), (2086666798222076658628878377475 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38v : LeanSuffixReflective.QInterval := ⟨(2085595539405884629464626868213 / 1267650600228229401496703205376 : ℚ), (2086666798222076658628878377475 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d0 : LeanSuffixReflective.QInterval := ⟨(-254332288184115862506776407441 / 316912650057057350374175801344 : ℚ), (-507127840736493287228570618507 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d2 : LeanSuffixReflective.QInterval := ⟨(7591666590582192426204085119 / 633825300114114700748351602688 : ℚ), (15509588642462465472972272137 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ38 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ36).sqrt wQ38_root38 (by norm_num [wQ38_root38]) (by norm_num [wJ36, wQ38_root38]) (by norm_num [wJ36, wQ38_root38])).widenAll wQ39_wJ38v wQ39_wJ38d0 wQ39_wJ38d1 wQ39_wJ38d2 (by
    norm_num [wJ36, wQ38_root38, NearOneScalarInterval.Jet3.sqrt, wQ39_wJ38v, wQ39_wJ38d0, wQ39_wJ38d1, wQ39_wJ38d2])
private abbrev wQ39_root39 : LeanSuffixReflective.QInterval := ⟨(135081819196823188798374417097 / 79228162514264337593543950336 : ℚ), (2163087383893668907440851106479 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39v : LeanSuffixReflective.QInterval := ⟨(135081819196823188798374417097 / 79228162514264337593543950336 : ℚ), (2163087383893668907440851106479 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d0 : LeanSuffixReflective.QInterval := ⟨(-236701553246135843819179347421 / 1267650600228229401496703205376 : ℚ), (-117000440019163474851301144979 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d2 : LeanSuffixReflective.QInterval := ⟨(7323457542997885478641216755 / 633825300114114700748351602688 : ℚ), (14966266872120922543346744121 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ39 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ37).sqrt wQ39_root39 (by norm_num [wQ39_root39]) (by norm_num [wJ37, wQ39_root39]) (by norm_num [wJ37, wQ39_root39])).widenAll wQ40_wJ39v wQ40_wJ39d0 wQ40_wJ39d1 wQ40_wJ39d2 (by
    norm_num [wJ37, wQ39_root39, NearOneScalarInterval.Jet3.sqrt, wQ40_wJ39v, wQ40_wJ39d0, wQ40_wJ39d1, wQ40_wJ39d2])
private abbrev wQ41_wJ40v : LeanSuffixReflective.QInterval := ⟨(1268918250828457630898199908581 / 1267650600228229401496703205376 : ℚ), (634478330954647573238647330093 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d0 : LeanSuffixReflective.QInterval := ⟨(38029518006846882044901096161 / 1267650600228229401496703205376 : ℚ), (38793911318784504374003608195 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ40 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0))).widenAll wQ41_wJ40v wQ41_wJ40d0 wQ41_wJ40d1 wQ41_wJ40d2 (by
    norm_num [wJ0, wQ41_wJ40v, wQ41_wJ40d0, wQ41_wJ40d1, wQ41_wJ40d2])
private abbrev wQ42_wJ41v : LeanSuffixReflective.QInterval := ⟨(531123780261807691858510271079 / 158456325028528675187087900672 : ℚ), (4251904077004620569873191475977 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d0 : LeanSuffixReflective.QInterval := ⟨(-596255497521908142995686274049 / 633825300114114700748351602688 : ℚ), (-1185412553166796298750181103221 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d2 : LeanSuffixReflective.QInterval := ⟨(14922715800170660097271505959 / 633825300114114700748351602688 : ℚ), (30491835059271305736958285063 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ41 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ39).add ((wJ40).mul (wJ38))).widenAll wQ42_wJ41v wQ42_wJ41d0 wQ42_wJ41d1 wQ42_wJ41d2 (by
    norm_num [wJ39, wJ40, wJ38, wQ42_wJ41v, wQ42_wJ41d0, wQ42_wJ41d1, wQ42_wJ41d2])
private abbrev wQ43_wJ42v : LeanSuffixReflective.QInterval := ⟨(5959414290355830701751695431749 / 633825300114114700748351602688 : ℚ), (373217085721602881776550371321 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d0 : LeanSuffixReflective.QInterval := ⟨(-2619777070255402439076757001275 / 316912650057057350374175801344 : ℚ), (-10411927104346081381078654672181 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d2 : LeanSuffixReflective.QInterval := ⟨(125630949526032678793516648977 / 633825300114114700748351602688 : ℚ), (257047851559579330839970073739 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ42 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ38).mul (wJ39)).mul (wJ41)).widenAll wQ43_wJ42v wQ43_wJ42d0 wQ43_wJ42d1 wQ43_wJ42d2 (by
    norm_num [wJ38, wJ39, wJ41, wQ43_wJ42v, wQ43_wJ42d0, wQ43_wJ42d1, wQ43_wJ42d2])
private abbrev wQ44_wJ43v : LeanSuffixReflective.QInterval := ⟨(4253239232336555996402950250799 / 1267650600228229401496703205376 : ℚ), (4256284818027062507450952395031 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d0 : LeanSuffixReflective.QInterval := ⟨(-1066269933051687078908603280169 / 1267650600228229401496703205376 : ℚ), (-1056476945251390691749102005581 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d2 : LeanSuffixReflective.QInterval := ⟨(29875277031941661514737554929 / 1267650600228229401496703205376 : ℚ), (15261625413712354011265189461 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ43 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ40).mul (wJ41)).widenAll wQ44_wJ43v wQ44_wJ43d0 wQ44_wJ43d1 wQ44_wJ43d2 (by
    norm_num [wJ40, wJ41, wQ44_wJ43v, wQ44_wJ43d0, wQ44_wJ43d1, wQ44_wJ43d2])
private abbrev wQ45_wJ44v : LeanSuffixReflective.QInterval := ⟨(4248664404910885474645009364055 / 1267650600228229401496703205376 : ℚ), (1064117917946480564043429781469 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d0 : LeanSuffixReflective.QInterval := ⟨(-144810718906285888565931130751 / 158456325028528675187087900672 : ℚ), (-1094810175763709159790475630949 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d2 : LeanSuffixReflective.QInterval := ⟨(29773520084515727738367571693 / 1267650600228229401496703205376 : ℚ), (7648839448323715449788438041 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ44 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ38).add (wJ39)).mul (((wJ35).mul (wJ35)).add ((wJ33).mul ((wJ38).mul (wJ39))))).widenAll wQ45_wJ44v wQ45_wJ44d0 wQ45_wJ44d1 wQ45_wJ44d2 (by
    norm_num [wJ38, wJ39, wJ35, wJ33, wQ45_wJ44v, wQ45_wJ44d0, wQ45_wJ44d1, wQ45_wJ44d2])
private abbrev wQ46_wJ45v : LeanSuffixReflective.QInterval := ⟨(1233233350343105063170768475965 / 633825300114114700748351602688 : ℚ), (2467935296929400830823780333739 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d0 : LeanSuffixReflective.QInterval := ⟨(-642233733341959022100147031935 / 633825300114114700748351602688 : ℚ), (-1267269216290823639347114469815 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d2 : LeanSuffixReflective.QInterval := ⟨(-1041451349090682245716183465 / 1267650600228229401496703205376 : ℚ), (-15632951233303943292268997 / 19807040628566084398385987584 : ℚ), by norm_num⟩
@[simp] private abbrev wJ45 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ35).mul (wJ35)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).widenAll wQ46_wJ45v wQ46_wJ45d0 wQ46_wJ45d1 wQ46_wJ45d2 (by
    norm_num [wJ35, wJ0, wQ46_wJ45v, wQ46_wJ45d0, wQ46_wJ45d1, wQ46_wJ45d2])
private abbrev wQ47_wJ46v : LeanSuffixReflective.QInterval := ⟨(134551219127604778976446378577 / 1267650600228229401496703205376 : ℚ), (67411744089495144107495798743 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d0 : LeanSuffixReflective.QInterval := ⟨(58651248954447769971529778841 / 633825300114114700748351602688 : ℚ), (118537650062277980321870864071 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d2 : LeanSuffixReflective.QInterval := ⟨(-1453837839075143141214600405 / 633825300114114700748351602688 : ℚ), (-2830758234547888181112861245 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ46 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ42).invPos (by norm_num [wJ42])).widenAll wQ47_wJ46v wQ47_wJ46d0 wQ47_wJ46d1 wQ47_wJ46d2 (by
    norm_num [wJ42, NearOneScalarInterval.Jet3.invPos, wQ47_wJ46v, wQ47_wJ46d0, wQ47_wJ46d1, wQ47_wJ46d2])
private abbrev wQ48_wJ47v : LeanSuffixReflective.QInterval := ⟨(261796193253267942036171468515 / 1267650600228229401496703205376 : ℚ), (131241071187978697598954753667 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d0 : LeanSuffixReflective.QInterval := ⟨(91623291676694421669528746277 / 1267650600228229401496703205376 : ℚ), (12033149411101162349997551719 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d2 : LeanSuffixReflective.QInterval := ⟨(-5771596321940838281081754831 / 1267650600228229401496703205376 : ℚ), (-5614000112753933049337479899 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ47 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ45).mul (wJ46)).widenAll wQ48_wJ47v wQ48_wJ47d0 wQ48_wJ47d1 wQ48_wJ47d2 (by
    norm_num [wJ45, wJ46, wQ48_wJ47v, wQ48_wJ47d0, wQ48_wJ47d1, wQ48_wJ47d2])
private abbrev wQ49_wJ48v : LeanSuffixReflective.QInterval := ⟨(377544763323395846948571060997 / 1267650600228229401496703205376 : ℚ), (188907554510659880872320814443 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d0 : LeanSuffixReflective.QInterval := ⟨(23428139522183665213690899995 / 316912650057057350374175801344 : ℚ), (23679181266084552300809178895 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d2 : LeanSuffixReflective.QInterval := ⟨(-1355689711899095884495883237 / 633825300114114700748351602688 : ℚ), (-331252925922425378288217439 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev wJ48 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ43).invPos (by norm_num [wJ43])).widenAll wQ49_wJ48v wQ49_wJ48d0 wQ49_wJ48d1 wQ49_wJ48d2 (by
    norm_num [wJ43, NearOneScalarInterval.Jet3.invPos, wQ49_wJ48v, wQ49_wJ48d0, wQ49_wJ48d1, wQ49_wJ48d2])
private abbrev wQ50_wJ49v : LeanSuffixReflective.QInterval := ⟨(183647131667818704808752154057 / 316912650057057350374175801344 : ℚ), (735552243732673722851894726025 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d0 : LeanSuffixReflective.QInterval := ⟨(-200490822906389829971769357529 / 1267650600228229401496703205376 : ℚ), (-193031192736903226785034441457 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d2 : LeanSuffixReflective.QInterval := ⟨(-698633463854429329387012707 / 158456325028528675187087900672 : ℚ), (-5454130165673919263617749923 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ49 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ45).mul (wJ48)).widenAll wQ50_wJ49v wQ50_wJ49d0 wQ50_wJ49d1 wQ50_wJ49d2 (by
    norm_num [wJ45, wJ48, wQ50_wJ49v, wQ50_wJ49d0, wQ50_wJ49d1, wQ50_wJ49d2])
private abbrev wQ51_wJ50v : LeanSuffixReflective.QInterval := ⟨(377528189582606638007627965709 / 1267650600228229401496703205376 : ℚ), (378221928378618396236516104351 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d0 : LeanSuffixReflective.QInterval := ⟨(97104300336919135570039792609 / 1267650600228229401496703205376 : ℚ), (12891248668951601920915029003 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d2 : LeanSuffixReflective.QInterval := ⟨(-85113771361288605272460011 / 39614081257132168796771975168 : ℚ), (-2640765404246752184867098491 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ50 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ44).invPos (by norm_num [wJ44])).widenAll wQ51_wJ50v wQ51_wJ50d0 wQ51_wJ50d1 wQ51_wJ50d2 (by
    norm_num [wJ44, NearOneScalarInterval.Jet3.invPos, wQ51_wJ50v, wQ51_wJ50d0, wQ51_wJ50d1, wQ51_wJ50d2])
private abbrev wQ52_wJ51v : LeanSuffixReflective.QInterval := ⟨(93115244466887540338269494617 / 158456325028528675187087900672 : ℚ), (746518609759901654874835266131 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d0 : LeanSuffixReflective.QInterval := ⟨(2930500152095516912992408583 / 1267650600228229401496703205376 : ℚ), (17879776062352328829227225051 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d2 : LeanSuffixReflective.QInterval := ⟨(-21614534265712339603593551 / 4951760157141521099596496896 : ℚ), (-5361728486780357927181609243 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ51 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ35).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).mul (wJ50)).widenAll wQ52_wJ51v wQ52_wJ51d0 wQ52_wJ51d1 wQ52_wJ51d2 (by
    norm_num [wJ35, wJ0, wJ50, wQ52_wJ51v, wQ52_wJ51d0, wQ52_wJ51d1, wQ52_wJ51d2])
private abbrev wQ53_wJ52v : LeanSuffixReflective.QInterval := ⟨(1285166207086824518261902184437 / 1267650600228229401496703205376 : ℚ), (642769513449273681659953407597 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d0 : LeanSuffixReflective.QInterval := ⟨(42486689183621223570999323163 / 158456325028528675187087900672 : ℚ), (172134089460475471119860259549 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d2 : LeanSuffixReflective.QInterval := ⟨(32573095842430264219997533 / 158456325028528675187087900672 : ℚ), (271322903374019228583222271 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ52 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ35).invPos (by norm_num [wJ35])).widenAll wQ53_wJ52v wQ53_wJ52d0 wQ53_wJ52d1 wQ53_wJ52d2 (by
    norm_num [wJ35, NearOneScalarInterval.Jet3.invPos, wQ53_wJ52v, wQ53_wJ52d0, wQ53_wJ52d1, wQ53_wJ52d2])
private abbrev wQ54_wJ53v : LeanSuffixReflective.QInterval := ⟨(13694829568361647153836550163 / 79228162514264337593543950336 : ℚ), (221554786672874247324781037413 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d0 : LeanSuffixReflective.QInterval := ⟨(278110805641592177175302251987 / 158456325028528675187087900672 : ℚ), (2229213965836585999713262775263 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d2 : LeanSuffixReflective.QInterval := ⟨(764679341951158607379246659 / 633825300114114700748351602688 : ℚ), (789842305511397800750897153 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ53 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ0).mul (wJ39)).mul (wJ52)).widenAll wQ54_wJ53v wQ54_wJ53d0 wQ54_wJ53d1 wQ54_wJ53d2 (by
    norm_num [wJ0, wJ39, wJ52, wQ54_wJ53v, wQ54_wJ53d0, wQ54_wJ53d1, wQ54_wJ53d2])
private abbrev wQ55_wJ54v : LeanSuffixReflective.QInterval := ⟨(465576222334437701691347473 / 79228162514264337593543950336 : ℚ), (7615236338160756781378194551 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d0 : LeanSuffixReflective.QInterval := ⟨(9313356009283813731897569717 / 79228162514264337593543950336 : ℚ), (75489575383556095195551835341 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d2 : LeanSuffixReflective.QInterval := ⟨(-56445405195400083531842001 / 1267650600228229401496703205376 : ℚ), (-13404321216950894817954023 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ54 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ33).mul (wJ51)).widenAll wQ55_wJ54v wQ55_wJ54d0 wQ55_wJ54d1 wQ55_wJ54d2 (by
    norm_num [wJ33, wJ51, wQ55_wJ54v, wQ55_wJ54d0, wQ55_wJ54d1, wQ55_wJ54d2])
private abbrev wQ56_wJ55v : LeanSuffixReflective.QInterval := ⟨(1254743120441389816247444446753 / 1267650600228229401496703205376 : ℚ), (156937376144748621663920684275 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d0 : LeanSuffixReflective.QInterval := ⟨(-266551427209739440854950108411 / 1267650600228229401496703205376 : ℚ), (-239961650800609285475359912473 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d2 : LeanSuffixReflective.QInterval := ⟨(-47221486369453203948434829 / 316912650057057350374175801344 : ℚ), (-82400974472970142076878607 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ55 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ53).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ53]) (by norm_num [wJ53])).widenAll wQ56_wJ55v wQ56_wJ55d0 wQ56_wJ55d1 wQ56_wJ55d2 (by
    norm_num [wJ53, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ56_wJ55v, wQ56_wJ55d0, wQ56_wJ55d1, wQ56_wJ55d2])
private abbrev wQ57_wJ56v : LeanSuffixReflective.QInterval := ⟨(633817675533588120956923688745 / 633825300114114700748351602688 : ℚ), (1267636555883964114225844036203 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d0 : LeanSuffixReflective.QInterval := ⟨(-2364072232905760073902423 / 4951760157141521099596496896 : ℚ), (-561339411038430766467472537 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d2 : LeanSuffixReflective.QInterval := ⟨(201970391490246724257909 / 1267650600228229401496703205376 : ℚ), (28282795746471206893133 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev wJ56 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ54).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ54]) (by norm_num [wJ54])).widenAll wQ57_wJ56v wQ57_wJ56d0 wQ57_wJ56d1 wQ57_wJ56d2 (by
    norm_num [wJ54, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ57_wJ56v, wQ57_wJ56d0, wQ57_wJ56d1, wQ57_wJ56d2])
private abbrev wQ58_wJ57v : LeanSuffixReflective.QInterval := ⟨(1285166207086824518261902184437 / 1267650600228229401496703205376 : ℚ), (642769513449273681659953407597 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d0 : LeanSuffixReflective.QInterval := ⟨(42486689183621223570999323163 / 158456325028528675187087900672 : ℚ), (172134089460475471119860259549 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d2 : LeanSuffixReflective.QInterval := ⟨(32573095842430264219997533 / 158456325028528675187087900672 : ℚ), (271322903374019228583222271 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ57 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ35).invPos (by norm_num [wJ35])).widenAll wQ58_wJ57v wQ58_wJ57d0 wQ58_wJ57d1 wQ58_wJ57d2 (by
    norm_num [wJ35, NearOneScalarInterval.Jet3.invPos, wQ58_wJ57v, wQ58_wJ57d0, wQ58_wJ57d1, wQ58_wJ57d2])
private abbrev wQ59_wJ58v : LeanSuffixReflective.QInterval := ⟨(766601612304984479578391319479 / 1267650600228229401496703205376 : ℚ), (768672868165120066161296360031 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d0 : LeanSuffixReflective.QInterval := ⟨(108738550666757177402213688765 / 316912650057057350374175801344 : ℚ), (455848722272810914519397975223 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d2 : LeanSuffixReflective.QInterval := ⟨(-5385096422491434553544684453 / 1267650600228229401496703205376 : ℚ), (-5206360663514757040236607653 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ58 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ33).mul (wJ39)).mul (wJ57)).mul (wJ55)).add ((wJ51).mul (wJ56))).widenAll wQ59_wJ58v wQ59_wJ58d0 wQ59_wJ58d1 wQ59_wJ58d2 (by
    norm_num [wJ33, wJ39, wJ57, wJ55, wJ51, wJ56, wQ59_wJ58v, wQ59_wJ58d0, wQ59_wJ58d1, wQ59_wJ58d2])
private abbrev wQ60_wJ59v : LeanSuffixReflective.QInterval := ⟨(629415423336496496646419619747 / 633825300114114700748351602688 : ℚ), (1259012157424014065431363730467 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d0 : LeanSuffixReflective.QInterval := ⟨(-167376887692340337701928036131 / 1267650600228229401496703205376 : ℚ), (-82672947800022995506071870847 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d2 : LeanSuffixReflective.QInterval := ⟨(-16489028723455030379967117 / 158456325028528675187087900672 : ℚ), (-7922816251426433759354395 / 79228162514264337593543950336 : ℚ), by norm_num⟩
@[simp] private abbrev wJ59 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ5).mul (wJ4)).neg)).widenAll wQ60_wJ59v wQ60_wJ59d0 wQ60_wJ59d1 wQ60_wJ59d2 (by
    norm_num [wJ5, wJ4, wQ60_wJ59v, wQ60_wJ59d0, wQ60_wJ59d1, wQ60_wJ59d2])
private abbrev wQ61_wJ60v : LeanSuffixReflective.QInterval := ⟨(-4427568421690401651543065461 / 1267650600228229401496703205376 : ℚ), (555092743107526767400643585 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d0 : LeanSuffixReflective.QInterval := ⟨(-1798555364304754795963003145 / 158456325028528675187087900672 : ℚ), (3609434147661960996854857643 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d1 : LeanSuffixReflective.QInterval := ⟨(-85265766610794454492885575785 / 1267650600228229401496703205376 : ℚ), (-10315539932204295557779102759 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ60 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul (wJ20)).add ((((NearOneScalarInterval.Jet3.pi).mul (NearOneScalarInterval.Jet3.rational (1 / 2 : ℚ))).add ((wJ5).mul (wJ31))).neg)).widenAll wQ61_wJ60v wQ61_wJ60d0 wQ61_wJ60d1 wQ61_wJ60d2 (by
    norm_num [wJ8, wJ20, wJ5, wJ31, wQ61_wJ60v, wQ61_wJ60d0, wQ61_wJ60d1, wQ61_wJ60d2])
private abbrev wQ62_wJ61v : LeanSuffixReflective.QInterval := ⟨(-6663325307828780677219021805 / 633825300114114700748351602688 : ℚ), (13313687299329607253733584907 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d0 : LeanSuffixReflective.QInterval := ⟨(-60733475942829138614197937161 / 1267650600228229401496703205376 : ℚ), (60355942877269692611084876407 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d1 : LeanSuffixReflective.QInterval := ⟨(-467848760271928839320432673 / 316912650057057350374175801344 : ℚ), (1876241512467981847730329485 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d2 : LeanSuffixReflective.QInterval := ⟨(58174473365014359140911077595 / 1267650600228229401496703205376 : ℚ), (60420735206131058927275737463 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ61 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.pi).mul ((wJ4).add ((wJ3).neg))).mul ((wJ8).add (wJ59))).add (((wJ8).mul (wJ8)).mul ((wJ58).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ59)).add (NearOneScalarInterval.Jet3.rational (1 : ℚ))).mul (wJ49))))).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul ((wJ59).mul (wJ59))).mul ((wJ31).add ((wJ8).mul (wJ22)))).neg)).widenAll wQ62_wJ61v wQ62_wJ61d0 wQ62_wJ61d1 wQ62_wJ61d2 (by
    norm_num [wJ4, wJ3, wJ8, wJ59, wJ58, wJ49, wJ31, wJ22, wQ62_wJ61v, wQ62_wJ61d0, wQ62_wJ61d1, wQ62_wJ61d2])
private abbrev wQ63_wJ62v : LeanSuffixReflective.QInterval := ⟨(-2185088343024021911199986549 / 316912650057057350374175801344 : ℚ), (51459563521334532378944895 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d0 : LeanSuffixReflective.QInterval := ⟨(-12797949909181733215315138727 / 158456325028528675187087900672 : ℚ), (-74952374395139533822105813887 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d1 : LeanSuffixReflective.QInterval := ⟨(29498520555476143310399440557 / 1267650600228229401496703205376 : ℚ), (15789854734180863182207313161 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d2 : LeanSuffixReflective.QInterval := ⟨(-15291331268952714338567591409 / 1267650600228229401496703205376 : ℚ), (-14660559047911763425193123741 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ62 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ3).add ((wJ4).neg)).mul (wJ20)).add ((wJ59).mul (wJ22))).add (((wJ8).mul (wJ49)).neg)).widenAll wQ63_wJ62v wQ63_wJ62d0 wQ63_wJ62d1 wQ63_wJ62d2 (by
    norm_num [wJ3, wJ4, wJ20, wJ59, wJ22, wJ8, wJ49, wQ63_wJ62v, wQ63_wJ62d0, wQ63_wJ62d1, wQ63_wJ62d2])
private abbrev wQ64_wJ63v : LeanSuffixReflective.QInterval := ⟨(114809326134584894920834411109 / 316912650057057350374175801344 : ℚ), (460645062631054326315533618815 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d0 : LeanSuffixReflective.QInterval := ⟨(-37888189087446601246871503125 / 633825300114114700748351602688 : ℚ), (-75213734427037997158801354287 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d1 : LeanSuffixReflective.QInterval := ⟨(-12931303772928168124667869399 / 1267650600228229401496703205376 : ℚ), (-12676506002282294014967032053 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d2 : LeanSuffixReflective.QInterval := ⟨(12676506002282294014967032053 / 1267650600228229401496703205376 : ℚ), (12931303772928168124667869399 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
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
private abbrev cQ4_cJ3v : LeanSuffixReflective.QInterval := ⟨(404279434973114659789348028669 / 1267650600228229401496703205376 : ℚ), (202139717486557329894674014335 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d0 : LeanSuffixReflective.QInterval := ⟨(-325962381786773290738787193317 / 633825300114114700748351602688 : ℚ), (-651924763573546581477574386633 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d1 : LeanSuffixReflective.QInterval := ⟨(6401793987477587006233538275 / 633825300114114700748351602688 : ℚ), (12803587974955174012467076551 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ3 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (246309387612851321557664008517088691 / 664613997892457936451903530140172288 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-85449082611111897527428630004824171 / 166153499473114484112975882535043072 : ℚ)).mul (cJ0))).add (((cJ0).mul (cJ0)).mul (cJ1))).widenAll cQ4_cJ3v cQ4_cJ3d0 cQ4_cJ3d1 cQ4_cJ3d2 (by
    norm_num [cJ0, cJ1, cQ4_cJ3v, cQ4_cJ3d0, cQ4_cJ3d1, cQ4_cJ3d2])
private abbrev cQ5_cJ4v : LeanSuffixReflective.QInterval := ⟨(864220618557811612788783660295 / 1267650600228229401496703205376 : ℚ), (108027577319726451598597957537 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d0 : LeanSuffixReflective.QInterval := ⟨(-363709909937256090651923283451 / 633825300114114700748351602688 : ℚ), (-727419819874512181303846566901 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d2 : LeanSuffixReflective.QInterval := ⟨(6401793987477587006233538275 / 633825300114114700748351602688 : ℚ), (12803587974955174012467076551 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ4 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (491428936655935943218204634130007581 / 664613997892457936451903530140172288 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-762754965044736485022862217735664531 / 1329227995784915872903807060280344576 : ℚ)).mul (cJ0))).add (((cJ0).mul (cJ0)).mul (cJ2))).widenAll cQ5_cJ4v cQ5_cJ4d0 cQ5_cJ4d1 cQ5_cJ4d2 (by
    norm_num [cJ0, cJ2, cQ5_cJ4v, cQ5_cJ4d0, cQ5_cJ4d1, cQ5_cJ4d2])
private abbrev cQ6_cJ5v : LeanSuffixReflective.QInterval := ⟨(6401793987477587006233538275 / 633825300114114700748351602688 : ℚ), (12803587974955174012467076551 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d0 : LeanSuffixReflective.QInterval := ⟨(31849721330734263712604668035 / 158456325028528675187087900672 : ℚ), (254797770645874109700837344281 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ5 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ6_cJ5v cQ6_cJ5d0 cQ6_cJ5d1 cQ6_cJ5d2 (by
    norm_num [cJ0, cQ6_cJ5v, cQ6_cJ5d0, cQ6_cJ5d1, cQ6_cJ5d2])
private abbrev cQ7_cJ6v : LeanSuffixReflective.QInterval := ⟨(6401793987477587006233538275 / 633825300114114700748351602688 : ℚ), (12803587974955174012467076551 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d0 : LeanSuffixReflective.QInterval := ⟨(31849721330734263712604668035 / 158456325028528675187087900672 : ℚ), (254797770645874109700837344281 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ6 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ7_cJ6v cQ7_cJ6d0 cQ7_cJ6d1 cQ7_cJ6d2 (by
    norm_num [cJ0, cQ7_cJ6v, cQ7_cJ6d0, cQ7_cJ6d1, cQ7_cJ6d2])
private abbrev cQ8_cJ7v : LeanSuffixReflective.QInterval := ⟨(128932894847172057723338792399 / 1267650600228229401496703205376 : ℚ), (128932894847172057723338792401 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d0 : LeanSuffixReflective.QInterval := ⟨(-207912002735645880574011646331 / 633825300114114700748351602688 : ℚ), (-415824005471291761148023292659 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d1 : LeanSuffixReflective.QInterval := ⟨(8166646726174402685074724853 / 1267650600228229401496703205376 : ℚ), (4083323363087201342537362427 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ7 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ3).mul (cJ3)).widenAll cQ8_cJ7v cQ8_cJ7d0 cQ8_cJ7d1 cQ8_cJ7d2 (by
    norm_num [cJ3, cQ8_cJ7v, cQ8_cJ7d0, cQ8_cJ7d1, cQ8_cJ7d2])
private abbrev cQ9_cJ8v : LeanSuffixReflective.QInterval := ⟨(1263567276865142200154165842949 / 1267650600228229401496703205376 : ℚ), (631783638432571100077082921475 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d0 : LeanSuffixReflective.QInterval := ⟨(-74675563336312332758090083065 / 1267650600228229401496703205376 : ℚ), (-74675563336312332758090083063 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d1 : LeanSuffixReflective.QInterval := ⟨(-64659719722020498159710295 / 633825300114114700748351602688 : ℚ), (-129319439444040996319420589 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ8 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ6).mul (cJ3)).neg)).widenAll cQ9_cJ8v cQ9_cJ8d0 cQ9_cJ8d1 cQ9_cJ8d2 (by
    norm_num [cJ6, cJ3, cQ9_cJ8v, cQ9_cJ8d0, cQ9_cJ8d1, cQ9_cJ8d2])
private abbrev cQ10_cJ9v : LeanSuffixReflective.QInterval := ⟨(807256615475049170002675904699 / 1267650600228229401496703205376 : ℚ), (807256615475049170002675904703 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d0 : LeanSuffixReflective.QInterval := ⟨(-1325565112600113331947004548279 / 1267650600228229401496703205376 : ℚ), (-331391278150028332986751137069 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d1 : LeanSuffixReflective.QInterval := ⟨(12762345388157152507107113555 / 633825300114114700748351602688 : ℚ), (25524690776314305014214227113 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ9 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ3)).add (((cJ6).mul (cJ7)).neg)).widenAll cQ10_cJ9v cQ10_cJ9d0 cQ10_cJ9d1 cQ10_cJ9d2 (by
    norm_num [cJ3, cJ6, cJ7, cQ10_cJ9v, cQ10_cJ9d0, cQ10_cJ9d1, cQ10_cJ9d2])
private abbrev cQ11_cJ10v : LeanSuffixReflective.QInterval := ⟨(531091852780183660349916334785 / 633825300114114700748351602688 : ℚ), (1062183705560367320699832669573 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d0 : LeanSuffixReflective.QInterval := ⟨(607441565111138725499706813623 / 633825300114114700748351602688 : ℚ), (607441565111138725499706813625 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d1 : LeanSuffixReflective.QInterval := ⟨(12762345388157152507107113555 / 633825300114114700748351602688 : ℚ), (25524690776314305014214227113 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ10 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ3)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ0))).add (((cJ6).mul (cJ7)).neg)).add (((cJ0).mul (cJ0)).mul ((cJ0).mul (cJ0)))).widenAll cQ11_cJ10v cQ11_cJ10d0 cQ11_cJ10d1 cQ11_cJ10d2 (by
    norm_num [cJ3, cJ0, cJ6, cJ7, cQ11_cJ10v, cQ11_cJ10d0, cQ11_cJ10d1, cQ11_cJ10d2])
private abbrev cQ11_root11 : LeanSuffixReflective.QInterval := ⟨(1011592473847623611108587735147 / 1267650600228229401496703205376 : ℚ), (1011592473847623611108587735151 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11v : LeanSuffixReflective.QInterval := ⟨(1011592473847623611108587735147 / 1267650600228229401496703205376 : ℚ), (1011592473847623611108587735151 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d0 : LeanSuffixReflective.QInterval := ⟨(-207637148119273936522641551317 / 316912650057057350374175801344 : ℚ), (-830548592477095746090566205261 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d1 : LeanSuffixReflective.QInterval := ⟨(15992798691041185654735619125 / 1267650600228229401496703205376 : ℚ), (1999099836380148206841952391 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ11 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ9).sqrt cQ11_root11 (by norm_num [cQ11_root11]) (by norm_num [cJ9, cQ11_root11]) (by norm_num [cJ9, cQ11_root11])).widenAll cQ12_cJ11v cQ12_cJ11d0 cQ12_cJ11d1 cQ12_cJ11d2 (by
    norm_num [cJ9, cQ11_root11, NearOneScalarInterval.Jet3.sqrt, cQ12_cJ11v, cQ12_cJ11d0, cQ12_cJ11d1, cQ12_cJ11d2])
private abbrev cQ12_root12 : LeanSuffixReflective.QInterval := ⟨(580189152756720478853124270671 / 633825300114114700748351602688 : ℚ), (36261822047295029928320266917 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12v : LeanSuffixReflective.QInterval := ⟨(580189152756720478853124270671 / 633825300114114700748351602688 : ℚ), (36261822047295029928320266917 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d0 : LeanSuffixReflective.QInterval := ⟨(663597088085848151456605228231 / 1267650600228229401496703205376 : ℚ), (165899272021462037864151307059 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d1 : LeanSuffixReflective.QInterval := ⟨(6971086375343301161572761119 / 633825300114114700748351602688 : ℚ), (217846449229478161299148785 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ12 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ10).sqrt cQ12_root12 (by norm_num [cQ12_root12]) (by norm_num [cJ10, cQ12_root12]) (by norm_num [cJ10, cQ12_root12])).widenAll cQ13_cJ12v cQ13_cJ12d0 cQ13_cJ12d1 cQ13_cJ12d2 (by
    norm_num [cJ10, cQ12_root12, NearOneScalarInterval.Jet3.sqrt, cQ13_cJ12v, cQ13_cJ12d0, cQ13_cJ12d1, cQ13_cJ12d2])
private abbrev cQ14_cJ13v : LeanSuffixReflective.QInterval := ⟨(1268937360819712396484956146569 / 1267650600228229401496703205376 : ℚ), (634468680409856198242478073285 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d0 : LeanSuffixReflective.QInterval := ⟨(19205381962432761018700614825 / 633825300114114700748351602688 : ℚ), (38410763924865522037401229651 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ13 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0))).widenAll cQ14_cJ13v cQ14_cJ13d0 cQ14_cJ13d1 cQ14_cJ13d2 (by
    norm_num [cJ0, cQ14_cJ13v, cQ14_cJ13d0, cQ14_cJ13d1, cQ14_cJ13d2])
private abbrev cQ15_cJ14v : LeanSuffixReflective.QInterval := ⟨(543249405429476126145708819393 / 316912650057057350374175801344 : ℚ), (543249405429476126145708819395 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d0 : LeanSuffixReflective.QInterval := ⟨(-137142562955636475523762286975 / 1267650600228229401496703205376 : ℚ), (-8571410184727279720235142935 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d1 : LeanSuffixReflective.QInterval := ⟨(3743900666732274555723721291 / 158456325028528675187087900672 : ℚ), (14975602666929098222894885167 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ14 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ12).add ((cJ13).mul (cJ11))).widenAll cQ15_cJ14v cQ15_cJ14d0 cQ15_cJ14d1 cQ15_cJ14d2 (by
    norm_num [cJ12, cJ13, cJ11, cQ15_cJ14v, cQ15_cJ14d0, cQ15_cJ14d1, cQ15_cJ14d2])
private abbrev cQ16_cJ15v : LeanSuffixReflective.QInterval := ⟨(1587322997272655628319719172943 / 1267650600228229401496703205376 : ℚ), (1587322997272655628319719172959 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d0 : LeanSuffixReflective.QInterval := ⟨(-247831135390658318836124124261 / 633825300114114700748351602688 : ℚ), (-123915567695329159418062062121 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d1 : LeanSuffixReflective.QInterval := ⟨(66045464928328692772097111063 / 1267650600228229401496703205376 : ℚ), (16511366232082173193024277769 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ15 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ11).mul (cJ12)).mul (cJ14)).widenAll cQ16_cJ15v cQ16_cJ15d0 cQ16_cJ15d1 cQ16_cJ15d2 (by
    norm_num [cJ11, cJ12, cJ14, cQ16_cJ15v, cQ16_cJ15d0, cQ16_cJ15d1, cQ16_cJ15d2])
private abbrev cQ17_cJ16v : LeanSuffixReflective.QInterval := ⟨(2175203377550394509212562762163 / 1267650600228229401496703205376 : ℚ), (1087601688775197254606281381087 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d0 : LeanSuffixReflective.QInterval := ⟨(-71438315273602693671370783383 / 1267650600228229401496703205376 : ℚ), (-71438315273602693671370783365 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d1 : LeanSuffixReflective.QInterval := ⟨(14990804028678181610639627467 / 633825300114114700748351602688 : ℚ), (29981608057356363221279254941 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ16 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ13).mul (cJ14)).widenAll cQ17_cJ16v cQ17_cJ16d0 cQ17_cJ16d1 cQ17_cJ16d2 (by
    norm_num [cJ13, cJ14, cQ17_cJ16v, cQ17_cJ16d0, cQ17_cJ16d1, cQ17_cJ16d2])
private abbrev cQ18_cJ17v : LeanSuffixReflective.QInterval := ⟨(543506376599219541235809743053 / 316912650057057350374175801344 : ℚ), (2174025506396878164943238972223 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d0 : LeanSuffixReflective.QInterval := ⟨(-13409031138940933511707403295 / 158456325028528675187087900672 : ℚ), (-3352257784735233377926850823 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d1 : LeanSuffixReflective.QInterval := ⟨(29967455704608688424590262703 / 1267650600228229401496703205376 : ℚ), (29967455704608688424590262713 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ17 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ11).add (cJ12)).mul (((cJ8).mul (cJ8)).add ((cJ6).mul ((cJ11).mul (cJ12))))).widenAll cQ18_cJ17v cQ18_cJ17d0 cQ18_cJ17d1 cQ18_cJ17d2 (by
    norm_num [cJ11, cJ12, cJ8, cJ6, cQ18_cJ17v, cQ18_cJ17d0, cQ18_cJ17d1, cQ18_cJ17d2])
private abbrev cQ19_cJ18v : LeanSuffixReflective.QInterval := ⟨(2520272697378471949591963901389 / 1267650600228229401496703205376 : ℚ), (1260136348689235974795981950697 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d0 : LeanSuffixReflective.QInterval := ⟨(-259727488686302550305050653337 / 1267650600228229401496703205376 : ℚ), (-259727488686302550305050653327 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d1 : LeanSuffixReflective.QInterval := ⟨(-515873208238978359789068121 / 1267650600228229401496703205376 : ℚ), (-128968302059744589947267029 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ18 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul (cJ8)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).widenAll cQ19_cJ18v cQ19_cJ18d0 cQ19_cJ18d1 cQ19_cJ18d2 (by
    norm_num [cJ8, cJ0, cQ19_cJ18v, cQ19_cJ18d0, cQ19_cJ18d1, cQ19_cJ18d2])
private abbrev cQ20_cJ19v : LeanSuffixReflective.QInterval := ⟨(1012357312922472171744779984571 / 1267650600228229401496703205376 : ℚ), (506178656461236085872389992291 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d0 : LeanSuffixReflective.QInterval := ⟨(158060875268422803552499774067 / 633825300114114700748351602688 : ℚ), (158060875268422803552499774083 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d1 : LeanSuffixReflective.QInterval := ⟨(-42122245768781830448865024911 / 1267650600228229401496703205376 : ℚ), (-42122245768781830448865024901 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ19 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ15).invPos (by norm_num [cJ15])).widenAll cQ20_cJ19v cQ20_cJ19d0 cQ20_cJ19d1 cQ20_cJ19d2 (by
    norm_num [cJ15, NearOneScalarInterval.Jet3.invPos, cQ20_cJ19v, cQ20_cJ19d0, cQ20_cJ19d1, cQ20_cJ19d2])
private abbrev cQ21_cJ20v : LeanSuffixReflective.QInterval := ⟨(1006356363216560035216914281319 / 633825300114114700748351602688 : ℚ), (2012712726433120070433828562665 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d0 : LeanSuffixReflective.QInterval := ⟨(421075014117321879761011922211 / 1267650600228229401496703205376 : ℚ), (421075014117321879761011922287 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d1 : LeanSuffixReflective.QInterval := ⟨(-84157096568266598059809331585 / 1267650600228229401496703205376 : ℚ), (-10519637071033324757476166445 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ20 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ18).mul (cJ19)).widenAll cQ21_cJ20v cQ21_cJ20d0 cQ21_cJ20d1 cQ21_cJ20d2 (by
    norm_num [cJ18, cJ19, cQ21_cJ20v, cQ21_cJ20d0, cQ21_cJ20d1, cQ21_cJ20d2])
private abbrev cQ22_cJ21v : LeanSuffixReflective.QInterval := ⟨(92344126349500460683566266145 / 158456325028528675187087900672 : ℚ), (738753010796003685468530129165 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d0 : LeanSuffixReflective.QInterval := ⟨(6065555873906489795552010217 / 316912650057057350374175801344 : ℚ), (24262223495625959182208040875 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d1 : LeanSuffixReflective.QInterval := ⟨(-10182497622737621237463364199 / 1267650600228229401496703205376 : ℚ), (-2545624405684405309365841049 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ21 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ16).invPos (by norm_num [cJ16])).widenAll cQ22_cJ21v cQ22_cJ21d0 cQ22_cJ21d1 cQ22_cJ21d2 (by
    norm_num [cJ16, NearOneScalarInterval.Jet3.invPos, cQ22_cJ21v, cQ22_cJ21d0, cQ22_cJ21d1, cQ22_cJ21d2])
private abbrev cQ23_cJ22v : LeanSuffixReflective.QInterval := ⟨(1468747810224757660970159242907 / 1267650600228229401496703205376 : ℚ), (1468747810224757660970159242921 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d0 : LeanSuffixReflective.QInterval := ⟨(-51562727448807328017190479841 / 633825300114114700748351602688 : ℚ), (-25781363724403664008595239915 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d1 : LeanSuffixReflective.QInterval := ⟨(-5136228711364434400364639477 / 316912650057057350374175801344 : ℚ), (-10272457422728868800729278949 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ22 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ18).mul (cJ21)).widenAll cQ23_cJ22v cQ23_cJ22d0 cQ23_cJ22d1 cQ23_cJ22d2 (by
    norm_num [cJ18, cJ21, cQ23_cJ22v, cQ23_cJ22d0, cQ23_cJ22d1, cQ23_cJ22d2])
private abbrev cQ24_cJ23v : LeanSuffixReflective.QInterval := ⟨(369576630892948798134423895365 / 633825300114114700748351602688 : ℚ), (739153261785897596268847790735 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d0 : LeanSuffixReflective.QInterval := ⟨(9117951076998544272101849949 / 316912650057057350374175801344 : ℚ), (36471804307994177088407399805 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d1 : LeanSuffixReflective.QInterval := ⟨(-10188722517886703527248889451 / 1267650600228229401496703205376 : ℚ), (-5094361258943351763624444723 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ23 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ17).invPos (by norm_num [cJ17])).widenAll cQ24_cJ23v cQ24_cJ23d0 cQ24_cJ23d1 cQ24_cJ23d2 (by
    norm_num [cJ17, NearOneScalarInterval.Jet3.invPos, cQ24_cJ23v, cQ24_cJ23d0, cQ24_cJ23d1, cQ24_cJ23d2])
private abbrev cQ25_cJ24v : LeanSuffixReflective.QInterval := ⟨(1474292520046053545538482017763 / 1267650600228229401496703205376 : ℚ), (1474292520046053545538482017775 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d0 : LeanSuffixReflective.QInterval := ⟨(3970543090302512453716142355 / 633825300114114700748351602688 : ℚ), (1985271545151256226858071183 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d1 : LeanSuffixReflective.QInterval := ⟨(-5118250199040438741911167207 / 316912650057057350374175801344 : ℚ), (-1279562549760109685477791801 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ24 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).mul (cJ23)).widenAll cQ25_cJ24v cQ25_cJ24d0 cQ25_cJ24d1 cQ25_cJ24d2 (by
    norm_num [cJ8, cJ0, cJ23, cQ25_cJ24v, cQ25_cJ24d0, cQ25_cJ24d1, cQ25_cJ24d2])
private abbrev cQ26_cJ25v : LeanSuffixReflective.QInterval := ⟨(635873559596184166613442101627 / 633825300114114700748351602688 : ℚ), (158968389899046041653360525407 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d0 : LeanSuffixReflective.QInterval := ⟨(75158983843452465507962035005 / 1267650600228229401496703205376 : ℚ), (1174359122553944773561906797 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d1 : LeanSuffixReflective.QInterval := ⟨(65078301559278072749098981 / 633825300114114700748351602688 : ℚ), (32539150779639036374549491 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ25 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ8).invPos (by norm_num [cJ8])).widenAll cQ26_cJ25v cQ26_cJ25d0 cQ26_cJ25d1 cQ26_cJ25d2 (by
    norm_num [cJ8, NearOneScalarInterval.Jet3.invPos, cQ26_cJ25v, cQ26_cJ25d0, cQ26_cJ25d1, cQ26_cJ25d2])
private abbrev cQ27_cJ26v : LeanSuffixReflective.QInterval := ⟨(14624360073855069769431539257 / 158456325028528675187087900672 : ℚ), (58497440295420279077726157029 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d0 : LeanSuffixReflective.QInterval := ⟨(309487368036705232545448503507 / 316912650057057350374175801344 : ℚ), (618974736073410465090897007017 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d1 : LeanSuffixReflective.QInterval := ⟨(1417690227177604350457306175 / 1267650600228229401496703205376 : ℚ), (1417690227177604350457306177 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ26 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ0).mul (cJ12)).mul (cJ25)).widenAll cQ27_cJ26v cQ27_cJ26d0 cQ27_cJ26d1 cQ27_cJ26d2 (by
    norm_num [cJ0, cJ12, cJ25, cQ27_cJ26v, cQ27_cJ26d0, cQ27_cJ26d1, cQ27_cJ26d2])
private abbrev cQ28_cJ27v : LeanSuffixReflective.QInterval := ⟨(14890723025595152323325052999 / 1267650600228229401496703205376 : ℚ), (7445361512797576161662526501 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d0 : LeanSuffixReflective.QInterval := ⟨(296413003484952418556056178503 / 1267650600228229401496703205376 : ℚ), (74103250871238104639014044627 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d1 : LeanSuffixReflective.QInterval := ⟨(-206782426291432765611953067 / 1267650600228229401496703205376 : ℚ), (-103391213145716382805976533 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ27 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ6).mul (cJ24)).widenAll cQ28_cJ27v cQ28_cJ27d0 cQ28_cJ27d1 cQ28_cJ27d2 (by
    norm_num [cJ6, cJ24, cQ28_cJ27v, cQ28_cJ27d0, cQ28_cJ27d1, cQ28_cJ27d2])
private abbrev cQ29_cJ28v : LeanSuffixReflective.QInterval := ⟨(632025671456975176692046014067 / 633825300114114700748351602688 : ℚ), (1264186315063235817688314947281 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d0 : LeanSuffixReflective.QInterval := ⟨(-77223600391897640901796131267 / 1267650600228229401496703205376 : ℚ), (-18064575599518574375902657425 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d1 : LeanSuffixReflective.QInterval := ⟨(-88435874037092901309338295 / 1267650600228229401496703205376 : ℚ), (-41374826455778238354715967 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ28 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ26).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ26]) (by norm_num [cJ26])).widenAll cQ29_cJ28v cQ29_cJ28d0 cQ29_cJ28d1 cQ29_cJ28d2 (by
    norm_num [cJ26, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ29_cJ28v, cQ29_cJ28d0, cQ29_cJ28d1, cQ29_cJ28d2])
private abbrev cQ30_cJ29v : LeanSuffixReflective.QInterval := ⟨(633796147281808876040473443587 / 633825300114114700748351602688 : ℚ), (316898620256510172233509437277 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d0 : LeanSuffixReflective.QInterval := ⟨(-2325341639096559940196865997 / 1267650600228229401496703205376 : ℚ), (-2230114584669353029112367725 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d1 : LeanSuffixReflective.QInterval := ⟨(777881704419303866427797 / 633825300114114700748351602688 : ℚ), (405548829197446101340021 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ29 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ27).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ27]) (by norm_num [cJ27])).widenAll cQ30_cJ29v cQ30_cJ29d0 cQ30_cJ29d1 cQ30_cJ29d2 (by
    norm_num [cJ27, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ30_cJ29v, cQ30_cJ29d0, cQ30_cJ29d1, cQ30_cJ29d2])
private abbrev cQ31_cJ30v : LeanSuffixReflective.QInterval := ⟨(635873559596184166613442101627 / 633825300114114700748351602688 : ℚ), (158968389899046041653360525407 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d0 : LeanSuffixReflective.QInterval := ⟨(75158983843452465507962035005 / 1267650600228229401496703205376 : ℚ), (1174359122553944773561906797 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d1 : LeanSuffixReflective.QInterval := ⟨(65078301559278072749098981 / 633825300114114700748351602688 : ℚ), (32539150779639036374549491 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ30 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ8).invPos (by norm_num [cJ8])).widenAll cQ31_cJ30v cQ31_cJ30d0 cQ31_cJ30d1 cQ31_cJ30d2 (by
    norm_num [cJ8, NearOneScalarInterval.Jet3.invPos, cQ31_cJ30v, cQ31_cJ30d0, cQ31_cJ30d1, cQ31_cJ30d2])
private abbrev cQ32_cJ31v : LeanSuffixReflective.QInterval := ⟨(1485949310767865763302591616189 / 1267650600228229401496703205376 : ℚ), (371488276393006133872496466793 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d0 : LeanSuffixReflective.QInterval := ⟨(245243407672660337125952749045 / 1267650600228229401496703205376 : ℚ), (245425930572613893755921805153 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d1 : LeanSuffixReflective.QInterval := ⟨(-10164516015618539706423314279 / 633825300114114700748351602688 : ℚ), (-20328851545729908659629781829 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ31 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ6).mul (cJ12)).mul (cJ30)).mul (cJ28)).add ((cJ24).mul (cJ29))).widenAll cQ32_cJ31v cQ32_cJ31d0 cQ32_cJ31d1 cQ32_cJ31d2 (by
    norm_num [cJ6, cJ12, cJ30, cJ28, cJ24, cJ29, cQ32_cJ31v, cQ32_cJ31d0, cQ32_cJ31d1, cQ32_cJ31d2])
private abbrev cQ33_cJ32v : LeanSuffixReflective.QInterval := ⟨(864220618557811612788783660295 / 633825300114114700748351602688 : ℚ), (108027577319726451598597957537 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d0 : LeanSuffixReflective.QInterval := ⟨(-363709909937256090651923283451 / 316912650057057350374175801344 : ℚ), (-727419819874512181303846566901 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d2 : LeanSuffixReflective.QInterval := ⟨(6401793987477587006233538275 / 316912650057057350374175801344 : ℚ), (12803587974955174012467076551 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ32 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ4)).widenAll cQ33_cJ32v cQ33_cJ32d0 cQ33_cJ32d1 cQ33_cJ32d2 (by
    norm_num [cJ4, cQ33_cJ32v, cQ33_cJ32d0, cQ33_cJ32d1, cQ33_cJ32d2])
private abbrev cQ34_cJ33v : LeanSuffixReflective.QInterval := ⟨(6401793987477587006233538275 / 633825300114114700748351602688 : ℚ), (12803587974955174012467076551 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d0 : LeanSuffixReflective.QInterval := ⟨(31849721330734263712604668035 / 158456325028528675187087900672 : ℚ), (254797770645874109700837344281 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ33 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ34_cJ33v cQ34_cJ33d0 cQ34_cJ33d1 cQ34_cJ33d2 (by
    norm_num [cJ0, cQ34_cJ33v, cQ34_cJ33d0, cQ34_cJ33d1, cQ34_cJ33d2])
private abbrev cQ35_cJ34v : LeanSuffixReflective.QInterval := ⟨(2356729140998246038585033268963 / 1267650600228229401496703205376 : ℚ), (1178364570499123019292516634485 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d0 : LeanSuffixReflective.QInterval := ⟨(-3967346879778889685760084722419 / 1267650600228229401496703205376 : ℚ), (-495918359972361210720010590301 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d2 : LeanSuffixReflective.QInterval := ⟨(34915377210354146968279648659 / 633825300114114700748351602688 : ℚ), (69830754420708293936559297325 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ34 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ32).mul (cJ32)).widenAll cQ35_cJ34v cQ35_cJ34d0 cQ35_cJ34d1 cQ35_cJ34d2 (by
    norm_num [cJ32, cQ35_cJ34v, cQ35_cJ34d0, cQ35_cJ34d1, cQ35_cJ34d2])
private abbrev cQ36_cJ35v : LeanSuffixReflective.QInterval := ⟨(312548227905763082003140845261 / 316912650057057350374175801344 : ℚ), (1250192911623052328012563381047 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d0 : LeanSuffixReflective.QInterval := ⟨(-166361222294432592511331339433 / 633825300114114700748351602688 : ℚ), (-166361222294432592511331339431 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d2 : LeanSuffixReflective.QInterval := ⟨(-64659719722020498159710295 / 316912650057057350374175801344 : ℚ), (-258638878888081992638841179 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ35 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ33).mul (cJ32)).neg)).widenAll cQ36_cJ35v cQ36_cJ35d0 cQ36_cJ35d1 cQ36_cJ35d2 (by
    norm_num [cJ33, cJ32, cQ36_cJ35v, cQ36_cJ35d0, cQ36_cJ35d1, cQ36_cJ35d2])
private abbrev cQ37_cJ36v : LeanSuffixReflective.QInterval := ⟨(3433078920724878916603916158903 / 1267650600228229401496703205376 : ℚ), (1716539460362439458301958079455 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d0 : LeanSuffixReflective.QInterval := ⟨(-3343310641516209448422379658955 / 1267650600228229401496703205376 : ℚ), (-52239228773690772631599682171 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d2 : LeanSuffixReflective.QInterval := ⟨(50509043822482937104035573157 / 1267650600228229401496703205376 : ℚ), (25254521911241468552017786581 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ36 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ32)).add (((cJ33).mul (cJ34)).neg)).widenAll cQ37_cJ36v cQ37_cJ36d0 cQ37_cJ36d1 cQ37_cJ36d2 (by
    norm_num [cJ32, cJ33, cJ34, cQ37_cJ36v, cQ37_cJ36d0, cQ37_cJ36d1, cQ37_cJ36d2])
private abbrev cQ38_cJ37v : LeanSuffixReflective.QInterval := ⟨(3688006010810197067301072923773 / 1267650600228229401496703205376 : ℚ), (922001502702549266825268230945 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d0 : LeanSuffixReflective.QInterval := ⟨(-401431199346909332737980741715 / 633825300114114700748351602688 : ℚ), (-401431199346909332737980741709 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d2 : LeanSuffixReflective.QInterval := ⟨(50509043822482937104035573157 / 1267650600228229401496703205376 : ℚ), (25254521911241468552017786581 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ37 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ32)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ0))).add (((cJ33).mul (cJ34)).neg)).add (((cJ0).mul (cJ0)).mul ((cJ0).mul (cJ0)))).widenAll cQ38_cJ37v cQ38_cJ37d0 cQ38_cJ37d1 cQ38_cJ37d2 (by
    norm_num [cJ32, cJ0, cJ33, cJ34, cQ38_cJ37v, cQ38_cJ37d0, cQ38_cJ37d1, cQ38_cJ37d2])
private abbrev cQ38_root38 : LeanSuffixReflective.QInterval := ⟨(2086131480632938135933714135417 / 1267650600228229401496703205376 : ℚ), (521532870158234533983428533855 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38v : LeanSuffixReflective.QInterval := ⟨(2086131480632938135933714135417 / 1267650600228229401496703205376 : ℚ), (521532870158234533983428533855 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d0 : LeanSuffixReflective.QInterval := ⟨(-1015791617358073494527219022971 / 1267650600228229401496703205376 : ℚ), (-1015791617358073494527219022965 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d2 : LeanSuffixReflective.QInterval := ⟨(239782269811299154301881737 / 19807040628566084398385987584 : ℚ), (7673032633961572937660215585 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ38 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ36).sqrt cQ38_root38 (by norm_num [cQ38_root38]) (by norm_num [cJ36, cQ38_root38]) (by norm_num [cJ36, cQ38_root38])).widenAll cQ39_cJ38v cQ39_cJ38d0 cQ39_cJ38d1 cQ39_cJ38d2 (by
    norm_num [cJ36, cQ38_root38, NearOneScalarInterval.Jet3.sqrt, cQ39_cJ38v, cQ39_cJ38d0, cQ39_cJ38d1, cQ39_cJ38d2])
private abbrev cQ39_root39 : LeanSuffixReflective.QInterval := ⟨(540549664302970419197761001331 / 316912650057057350374175801344 : ℚ), (2162198657211881676791044005327 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39v : LeanSuffixReflective.QInterval := ⟨(540549664302970419197761001331 / 316912650057057350374175801344 : ℚ), (2162198657211881676791044005327 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d0 : LeanSuffixReflective.QInterval := ⟨(-235350484149607521907154221107 / 1267650600228229401496703205376 : ℚ), (-117675242074803760953577110551 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d2 : LeanSuffixReflective.QInterval := ⟨(14806183396924133697081699081 / 1267650600228229401496703205376 : ℚ), (3701545849231033424270424771 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ39 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ37).sqrt cQ39_root39 (by norm_num [cQ39_root39]) (by norm_num [cJ37, cQ39_root39]) (by norm_num [cJ37, cQ39_root39])).widenAll cQ40_cJ39v cQ40_cJ39d0 cQ40_cJ39d1 cQ40_cJ39d2 (by
    norm_num [cJ37, cQ39_root39, NearOneScalarInterval.Jet3.sqrt, cQ40_cJ39v, cQ40_cJ39d0, cQ40_cJ39d1, cQ40_cJ39d2])
private abbrev cQ41_cJ40v : LeanSuffixReflective.QInterval := ⟨(1268937360819712396484956146569 / 1267650600228229401496703205376 : ℚ), (634468680409856198242478073285 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d0 : LeanSuffixReflective.QInterval := ⟨(19205381962432761018700614825 / 633825300114114700748351602688 : ℚ), (38410763924865522037401229651 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ40 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0))).widenAll cQ41_cJ40v cQ41_cJ40d0 cQ41_cJ40d1 cQ41_cJ40d2 (by
    norm_num [cJ0, cQ41_cJ40v, cQ41_cJ40d0, cQ41_cJ40d1, cQ41_cJ40d2])
private abbrev cQ42_cJ41v : LeanSuffixReflective.QInterval := ⟨(265652982376143107967638020163 / 79228162514264337593543950336 : ℚ), (531305964752286215935276040327 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d0 : LeanSuffixReflective.QInterval := ⟨(-297240464462214053708549039789 / 316912650057057350374175801344 : ℚ), (-594480928924428107417098079571 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d2 : LeanSuffixReflective.QInterval := ⟨(15083913036983687409095957185 / 633825300114114700748351602688 : ℚ), (3770978259245921852273989297 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ41 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ39).add ((cJ40).mul (cJ38))).widenAll cQ42_cJ41v cQ42_cJ41d0 cQ42_cJ41d1 cQ42_cJ41d2 (by
    norm_num [cJ39, cJ40, cJ38, cQ42_cJ41v, cQ42_cJ41d0, cQ42_cJ41d1, cQ42_cJ41d2])
private abbrev cQ43_cJ42v : LeanSuffixReflective.QInterval := ⟨(2982722323278625619307213854605 / 316912650057057350374175801344 : ℚ), (11930889293114502477228855418477 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d0 : LeanSuffixReflective.QInterval := ⟨(-10445493646467821050312616287319 / 1267650600228229401496703205376 : ℚ), (-652843352904238815644538517949 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d2 : LeanSuffixReflective.QInterval := ⟨(127073155702457121801312295321 / 633825300114114700748351602688 : ℚ), (254146311404914243602624590689 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ42 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ38).mul (cJ39)).mul (cJ41)).widenAll cQ43_cJ42v cQ43_cJ42d0 cQ43_cJ42d1 cQ43_cJ42d2 (by
    norm_num [cJ38, cJ39, cJ41, cQ43_cJ42v, cQ43_cJ42d0, cQ43_cJ42d1, cQ43_cJ42d2])
private abbrev cQ44_cJ43v : LeanSuffixReflective.QInterval := ⟨(4254762241766963107679618541155 / 1267650600228229401496703205376 : ℚ), (4254762241766963107679618541167 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d0 : LeanSuffixReflective.QInterval := ⟨(-1061376989763589682327569483847 / 1267650600228229401496703205376 : ℚ), (-265344247440897420581892370957 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d2 : LeanSuffixReflective.QInterval := ⟨(30198448683790385510431412379 / 1267650600228229401496703205376 : ℚ), (15099224341895192755215706193 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ43 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ40).mul (cJ41)).widenAll cQ44_cJ43v cQ44_cJ43d0 cQ44_cJ43d1 cQ44_cJ43d2 (by
    norm_num [cJ40, cJ41, cQ44_cJ43v, cQ44_cJ43d0, cQ44_cJ43d1, cQ44_cJ43d2])
private abbrev cQ45_cJ44v : LeanSuffixReflective.QInterval := ⟨(1063141861923679731183766165637 / 316912650057057350374175801344 : ℚ), (4252567447694718924735064662585 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d0 : LeanSuffixReflective.QInterval := ⟨(-1126654332303985632671594865713 / 1267650600228229401496703205376 : ℚ), (-563327166151992816335797432819 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d2 : LeanSuffixReflective.QInterval := ⟨(7545854823831994955200832615 / 316912650057057350374175801344 : ℚ), (15091709647663989910401665237 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ44 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ38).add (cJ39)).mul (((cJ35).mul (cJ35)).add ((cJ33).mul ((cJ38).mul (cJ39))))).widenAll cQ45_cJ44v cQ45_cJ44d0 cQ45_cJ44d1 cQ45_cJ44d2 (by
    norm_num [cJ38, cJ39, cJ35, cJ33, cQ45_cJ44v, cQ45_cJ44d0, cQ45_cJ44d1, cQ45_cJ44d2])
private abbrev cQ46_cJ45v : LeanSuffixReflective.QInterval := ⟨(1233601426312591636048329775171 / 633825300114114700748351602688 : ℚ), (1233601426312591636048329775177 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d0 : LeanSuffixReflective.QInterval := ⟨(-637933633424085406269761142403 / 633825300114114700748351602688 : ℚ), (-637933633424085406269761142393 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d2 : LeanSuffixReflective.QInterval := ⟨(-63801611521299975693177405 / 79228162514264337593543950336 : ℚ), (-1020825784340799611090838475 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ45 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ35).mul (cJ35)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).widenAll cQ46_cJ45v cQ46_cJ45d0 cQ46_cJ45d1 cQ46_cJ45d2 (by
    norm_num [cJ35, cJ0, cQ46_cJ45v, cQ46_cJ45d0, cQ46_cJ45d1, cQ46_cJ45d2])
private abbrev cQ47_cJ46v : LeanSuffixReflective.QInterval := ⟨(134687197641367659093994498497 / 1267650600228229401496703205376 : ℚ), (134687197641367659093994498499 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d0 : LeanSuffixReflective.QInterval := ⟨(3684957572785956575043311007 / 39614081257132168796771975168 : ℚ), (29479660582287652600346488057 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d2 : LeanSuffixReflective.QInterval := ⟨(-1434522340835609645532575685 / 633825300114114700748351602688 : ℚ), (-358630585208902411383143921 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ46 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ42).invPos (by norm_num [cJ42])).widenAll cQ47_cJ46v cQ47_cJ46d0 cQ47_cJ46d1 cQ47_cJ46d2 (by
    norm_num [cJ42, NearOneScalarInterval.Jet3.invPos, cQ47_cJ46v, cQ47_cJ46d0, cQ47_cJ46d1, cQ47_cJ46d2])
private abbrev cQ48_cJ47v : LeanSuffixReflective.QInterval := ⟨(262138982281905062477840979281 / 1267650600228229401496703205376 : ℚ), (262138982281905062477840979287 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d0 : LeanSuffixReflective.QInterval := ⟨(46971233231222185713201138345 / 633825300114114700748351602688 : ℚ), (2935702076951386607075071147 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d2 : LeanSuffixReflective.QInterval := ⟨(-5692426119470205380570300997 / 1267650600228229401496703205376 : ℚ), (-5692426119470205380570300991 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ47 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ45).mul (cJ46)).widenAll cQ48_cJ47v cQ48_cJ47d0 cQ48_cJ47d1 cQ48_cJ47d2 (by
    norm_num [cJ45, cJ46, cQ48_cJ47v, cQ48_cJ47d0, cQ48_cJ47d1, cQ48_cJ47d2])
private abbrev cQ49_cJ48v : LeanSuffixReflective.QInterval := ⟨(94419967142020836002628883939 / 316912650057057350374175801344 : ℚ), (188839934284041672005257767879 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d0 : LeanSuffixReflective.QInterval := ⟨(94214599833580070955414609789 / 1267650600228229401496703205376 : ℚ), (736051561199844304339176639 / 9903520314283042199192993792 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d2 : LeanSuffixReflective.QInterval := ⟨(-1340303580055912629957792255 / 633825300114114700748351602688 : ℚ), (-2680607160111825259915584509 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ48 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ43).invPos (by norm_num [cJ43])).widenAll cQ49_cJ48v cQ49_cJ48d0 cQ49_cJ48d1 cQ49_cJ48d2 (by
    norm_num [cJ43, NearOneScalarInterval.Jet3.invPos, cQ49_cJ48v, cQ49_cJ48d0, cQ49_cJ48d1, cQ49_cJ48d2])
private abbrev cQ50_cJ49v : LeanSuffixReflective.QInterval := ⟨(735070727645705185896292158465 / 1267650600228229401496703205376 : ℚ), (367535363822852592948146079237 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d0 : LeanSuffixReflective.QInterval := ⟨(-196759936957614031106744701859 / 1267650600228229401496703205376 : ℚ), (-196759936957614031106744701843 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d2 : LeanSuffixReflective.QInterval := ⟨(-5521353422619762320949678359 / 1267650600228229401496703205376 : ℚ), (-2760676711309881160474839177 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ49 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ45).mul (cJ48)).widenAll cQ50_cJ49v cQ50_cJ49d0 cQ50_cJ49d1 cQ50_cJ49d2 (by
    norm_num [cJ45, cJ48, cQ50_cJ49v, cQ50_cJ49d0, cQ50_cJ49d1, cQ50_cJ49d2])
private abbrev cQ51_cJ50v : LeanSuffixReflective.QInterval := ⟨(377874793057097280090440948177 / 1267650600228229401496703205376 : ℚ), (377874793057097280090440948181 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d0 : LeanSuffixReflective.QInterval := ⟨(12514036458640933884060597037 / 158456325028528675187087900672 : ℚ), (100112291669127471072484776305 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d2 : LeanSuffixReflective.QInterval := ⟨(-1341019685197528376789650171 / 633825300114114700748351602688 : ℚ), (-670509842598764188394825085 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ50 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ44).invPos (by norm_num [cJ44])).widenAll cQ51_cJ50v cQ51_cJ50d0 cQ51_cJ50d1 cQ51_cJ50d2 (by
    norm_num [cJ44, NearOneScalarInterval.Jet3.invPos, cQ51_cJ50v, cQ51_cJ50d0, cQ51_cJ50d1, cQ51_cJ50d2])
private abbrev cQ52_cJ51v : LeanSuffixReflective.QInterval := ⟨(745719927459258062452741158349 / 1267650600228229401496703205376 : ℚ), (93214990932407257806592644795 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d0 : LeanSuffixReflective.QInterval := ⟨(2599000778676049906755948947 / 316912650057057350374175801344 : ℚ), (2599000778676049906755948953 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d2 : LeanSuffixReflective.QInterval := ⟨(-5447165224007921046222351067 / 1267650600228229401496703205376 : ℚ), (-2723582612003960523111175531 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ51 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ35).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).mul (cJ50)).widenAll cQ52_cJ51v cQ52_cJ51d0 cQ52_cJ51d1 cQ52_cJ51d2 (by
    norm_num [cJ35, cJ0, cJ50, cQ52_cJ51v, cQ52_cJ51d0, cQ52_cJ51d1, cQ52_cJ51d2])
private abbrev cQ53_cJ52v : LeanSuffixReflective.QInterval := ⟨(1285352067924298666340754281161 / 1267650600228229401496703205376 : ℚ), (1285352067924298666340754281165 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d0 : LeanSuffixReflective.QInterval := ⟨(342079592854124139130547859075 / 1267650600228229401496703205376 : ℚ), (342079592854124139130547859081 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d2 : LeanSuffixReflective.QInterval := ⟨(66478144039552343154492767 / 316912650057057350374175801344 : ℚ), (132956288079104686308985535 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ52 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ35).invPos (by norm_num [cJ35])).widenAll cQ53_cJ52v cQ53_cJ52d0 cQ53_cJ52d1 cQ53_cJ52d2 (by
    norm_num [cJ35, NearOneScalarInterval.Jet3.invPos, cQ53_cJ52v, cQ53_cJ52d0, cQ53_cJ52d1, cQ53_cJ52d2])
private abbrev cQ54_cJ53v : LeanSuffixReflective.QInterval := ⟨(220335354819704736729828732983 / 1267650600228229401496703205376 : ℚ), (220335354819704736729828732985 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d0 : LeanSuffixReflective.QInterval := ⟨(2227047944590240624753996982353 / 1267650600228229401496703205376 : ℚ), (2227047944590240624753996982365 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d2 : LeanSuffixReflective.QInterval := ⟨(777191476506711127573769115 / 633825300114114700748351602688 : ℚ), (194297869126677781893442279 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ53 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ0).mul (cJ39)).mul (cJ52)).widenAll cQ54_cJ53v cQ54_cJ53d0 cQ54_cJ53d1 cQ54_cJ53d2 (by
    norm_num [cJ0, cJ39, cJ52, cQ54_cJ53v, cQ54_cJ53d0, cQ54_cJ53d1, cQ54_cJ53d2])
private abbrev cQ55_cJ54v : LeanSuffixReflective.QInterval := ⟨(1882989424330092811322074721 / 316912650057057350374175801344 : ℚ), (3765978848660185622644149443 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d0 : LeanSuffixReflective.QInterval := ⟨(149994707649770161645283819921 / 1267650600228229401496703205376 : ℚ), (149994707649770161645283819925 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d2 : LeanSuffixReflective.QInterval := ⟨(-27508865276893002273553651 / 633825300114114700748351602688 : ℚ), (-55017730553786004547107301 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ54 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ33).mul (cJ51)).widenAll cQ55_cJ54v cQ55_cJ54d0 cQ55_cJ54d1 cQ55_cJ54d2 (by
    norm_num [cJ33, cJ51, cQ55_cJ54v, cQ55_cJ54d0, cQ55_cJ54d1, cQ55_cJ54d2])
private abbrev cQ56_cJ55v : LeanSuffixReflective.QInterval := ⟨(1254884814299839617458054916535 / 1267650600228229401496703205376 : ℚ), (1255363531272154234359504227367 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d0 : LeanSuffixReflective.QInterval := ⟨(-264789528372113702354595011621 / 1267650600228229401496703205376 : ℚ), (-241655830995837841097970888419 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d2 : LeanSuffixReflective.QInterval := ⟨(-2887681496413951139870293 / 19807040628566084398385987584 : ℚ), (-168665297533742636744011751 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ55 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ53).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ53]) (by norm_num [cJ53])).widenAll cQ56_cJ55v cQ56_cJ55d0 cQ56_cJ55d1 cQ56_cJ55d2 (by
    norm_num [cJ53, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ56_cJ55v, cQ56_cJ55d0, cQ56_cJ55d1, cQ56_cJ55d2])
private abbrev cQ57_cJ56v : LeanSuffixReflective.QInterval := ⟨(633817841383406621595301304223 / 633825300114114700748351602688 : ℚ), (39613632567863010910221293151 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d0 : LeanSuffixReflective.QInterval := ⟨(-594675265542528620441229221 / 1267650600228229401496703205376 : ℚ), (-571335735727239299790874565 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d2 : LeanSuffixReflective.QInterval := ⟨(209564697691775565722617 / 1267650600228229401496703205376 : ℚ), (109062793078720054728341 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ56 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ54).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ54]) (by norm_num [cJ54])).widenAll cQ57_cJ56v cQ57_cJ56d0 cQ57_cJ56d1 cQ57_cJ56d2 (by
    norm_num [cJ54, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ57_cJ56v, cQ57_cJ56d0, cQ57_cJ56d1, cQ57_cJ56d2])
private abbrev cQ58_cJ57v : LeanSuffixReflective.QInterval := ⟨(1285352067924298666340754281161 / 1267650600228229401496703205376 : ℚ), (1285352067924298666340754281165 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d0 : LeanSuffixReflective.QInterval := ⟨(342079592854124139130547859075 / 1267650600228229401496703205376 : ℚ), (342079592854124139130547859081 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d2 : LeanSuffixReflective.QInterval := ⟨(66478144039552343154492767 / 316912650057057350374175801344 : ℚ), (132956288079104686308985535 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ57 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ35).invPos (by norm_num [cJ35])).widenAll cQ58_cJ57v cQ58_cJ57d0 cQ58_cJ57d1 cQ58_cJ57d2 (by
    norm_num [cJ35, NearOneScalarInterval.Jet3.invPos, cQ58_cJ57v, cQ58_cJ57d0, cQ58_cJ57d1, cQ58_cJ57d2])
private abbrev cQ59_cJ58v : LeanSuffixReflective.QInterval := ⟨(767631858533817307339473547753 / 1267650600228229401496703205376 : ℚ), (383820274993499048941385812601 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d0 : LeanSuffixReflective.QInterval := ⟨(445101483225034511843390323901 / 1267650600228229401496703205376 : ℚ), (222843527415364489821489810995 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d2 : LeanSuffixReflective.QInterval := ⟨(-5295566261486875329354605753 / 1267650600228229401496703205376 : ℚ), (-2647608889718960524737746393 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ58 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ33).mul (cJ39)).mul (cJ57)).mul (cJ55)).add ((cJ51).mul (cJ56))).widenAll cQ59_cJ58v cQ59_cJ58d0 cQ59_cJ58d1 cQ59_cJ58d2 (by
    norm_num [cJ33, cJ39, cJ57, cJ55, cJ51, cJ56, cQ59_cJ58v, cQ59_cJ58d0, cQ59_cJ58d1, cQ59_cJ58d2])
private abbrev cQ60_cJ59v : LeanSuffixReflective.QInterval := ⟨(629460877962820432377316646605 / 633825300114114700748351602688 : ℚ), (314730438981410216188658323303 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d0 : LeanSuffixReflective.QInterval := ⟨(-166361222294432592511331339433 / 1267650600228229401496703205376 : ℚ), (-166361222294432592511331339431 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d2 : LeanSuffixReflective.QInterval := ⟨(-64659719722020498159710295 / 633825300114114700748351602688 : ℚ), (-129319439444040996319420589 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ59 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ5).mul (cJ4)).neg)).widenAll cQ60_cJ59v cQ60_cJ59d0 cQ60_cJ59d1 cQ60_cJ59d2 (by
    norm_num [cJ5, cJ4, cQ60_cJ59v, cQ60_cJ59d0, cQ60_cJ59d1, cQ60_cJ59d2])
private abbrev cQ61_cJ60v : LeanSuffixReflective.QInterval := ⟨(23845740481684003689579 / 1267650600228229401496703205376 : ℚ), (62174211186322789418393 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d0 : LeanSuffixReflective.QInterval := ⟨(-2933626875353033475855229 / 1267650600228229401496703205376 : ℚ), (-327344319183913457765739 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d1 : LeanSuffixReflective.QInterval := ⟨(-83886012409764044439582490345 / 1267650600228229401496703205376 : ℚ), (-41943005293407650319091155931 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ60 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul (cJ20)).add ((((NearOneScalarInterval.Jet3.pi).mul (NearOneScalarInterval.Jet3.rational (1 / 2 : ℚ))).add ((cJ5).mul (cJ31))).neg)).widenAll cQ61_cJ60v cQ61_cJ60d0 cQ61_cJ60d1 cQ61_cJ60d2 (by
    norm_num [cJ8, cJ20, cJ5, cJ31, cQ61_cJ60v, cQ61_cJ60d0, cQ61_cJ60d1, cQ61_cJ60d2])
private abbrev cQ62_cJ61v : LeanSuffixReflective.QInterval := ⟨(-1369053828690161700232225 / 158456325028528675187087900672 : ℚ), (5168565824191905560464377 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d0 : LeanSuffixReflective.QInterval := ⟨(-41450168292876664320499725 / 79228162514264337593543950336 : ℚ), (281637389613118867500707699 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d1 : LeanSuffixReflective.QInterval := ⟨(-12191786642333957005999 / 158456325028528675187087900672 : ℚ), (65062565571332913780717 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d2 : LeanSuffixReflective.QInterval := ⟨(14824088582368937919938993547 / 316912650057057350374175801344 : ℚ), (29648351053971776832253050891 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ61 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.pi).mul ((cJ4).add ((cJ3).neg))).mul ((cJ8).add (cJ59))).add (((cJ8).mul (cJ8)).mul ((cJ58).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ59)).add (NearOneScalarInterval.Jet3.rational (1 : ℚ))).mul (cJ49))))).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul ((cJ59).mul (cJ59))).mul ((cJ31).add ((cJ8).mul (cJ22)))).neg)).widenAll cQ62_cJ61v cQ62_cJ61d0 cQ62_cJ61d1 cQ62_cJ61d2 (by
    norm_num [cJ4, cJ3, cJ8, cJ59, cJ58, cJ49, cJ31, cJ22, cQ62_cJ61v, cQ62_cJ61d0, cQ62_cJ61d1, cQ62_cJ61d2])
private abbrev cQ63_cJ62v : LeanSuffixReflective.QInterval := ⟨(-1085121362525177847457072575 / 316912650057057350374175801344 : ℚ), (-1085121362525177847457072565 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d0 : LeanSuffixReflective.QInterval := ⟨(-44325384710118459663995573901 / 633825300114114700748351602688 : ℚ), (-22162692355059229831997786931 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d1 : LeanSuffixReflective.QInterval := ⟨(30535131461898054440074509017 / 1267650600228229401496703205376 : ℚ), (1908445716368628402504656815 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d2 : LeanSuffixReflective.QInterval := ⟨(-14975167914923724240352635473 / 1267650600228229401496703205376 : ℚ), (-1871895989365465530044079433 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ62 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ3).add ((cJ4).neg)).mul (cJ20)).add ((cJ59).mul (cJ22))).add (((cJ8).mul (cJ49)).neg)).widenAll cQ63_cJ62v cQ63_cJ62d0 cQ63_cJ62d1 cQ63_cJ62d2 (by
    norm_num [cJ3, cJ4, cJ20, cJ59, cJ22, cJ8, cJ49, cQ63_cJ62v, cQ63_cJ62d0, cQ63_cJ62d1, cQ63_cJ62d2])
private abbrev cQ64_cJ63v : LeanSuffixReflective.QInterval := ⟨(459941183584696952999435631625 / 1267650600228229401496703205376 : ℚ), (459941183584696952999435631627 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d0 : LeanSuffixReflective.QInterval := ⟨(-75495056300965599826272180269 / 1267650600228229401496703205376 : ℚ), (-75495056300965599826272180267 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d1 : LeanSuffixReflective.QInterval := ⟨(-12803587974955174012467076551 / 1267650600228229401496703205376 : ℚ), (-6401793987477587006233538275 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d2 : LeanSuffixReflective.QInterval := ⟨(6401793987477587006233538275 / 633825300114114700748351602688 : ℚ), (12803587974955174012467076551 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
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

theorem foldLoRange_lo : foldLoRange.lo = (368479604505730481999810400267 / 162259276829213363391578010288128000 : ℚ) := by norm_num [foldLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldLoRange_hi : foldLoRange.hi = (18114008353015797469533879857989 / 1298074214633706907132624082305024000 : ℚ) := by norm_num [foldLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldHiRange_lo : foldHiRange.lo = (-18025923922507758513391316529989 / 1298074214633706907132624082305024000 : ℚ) := by norm_num [foldHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldHiRange_hi : foldHiRange.hi = (-357469050692225612481989984267 / 162259276829213363391578010288128000 : ℚ) := by norm_num [foldHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaLoRange_lo : areaLoRange.lo = (-102966094042547880277013759675057 / 1298074214633706907132624082305024000 : ℚ) := by norm_num [areaLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaLoRange_hi : areaLoRange.hi = (-21551792089254831145559920534943 / 1298074214633706907132624082305024000 : ℚ) := by norm_num [areaLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaHiRange_lo : areaHiRange.lo = (15629114528597537791173055382943 / 1298074214633706907132624082305024000 : ℚ) := by norm_num [areaHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaHiRange_hi : areaHiRange.hi = (97043416481890586922626894523057 / 1298074214633706907132624082305024000 : ℚ) := by norm_num [areaHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem hFourRange_lo : hFourRange.lo = (161731795830468969290435706122722983 / 162259276829213363391578010288128000 : ℚ) := by norm_num [hFourRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem hFourRange_hi : hFourRange.hi = (161741427047007433949030749672349017 / 162259276829213363391578010288128000 : ℚ) := by norm_num [hFourRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem shapeRange_lo : shapeRange.lo = (10000202216754289469520094128173331 / 10141204801825835211973625643008000 : ℚ) := by norm_num [shapeRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem shapeRange_hi : shapeRange.hi = (10002884369214547778680919968554669 / 10141204801825835211973625643008000 : ℚ) := by norm_num [shapeRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem bSubARange_lo : bSubARange.lo = (3767411414146876722900840312093809 / 10384593717069655257060992658440192 : ℚ) := by norm_num [bSubARange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem bSubARange_hi : bSubARange.hi = (3768264937704798155041913076466575 / 10384593717069655257060992658440192 : ℚ) := by norm_num [bSubARange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem gapRange_lo : gapRange.lo = (-2258158149341817386284109747562521 / 649037107316853453566312041152512000 : ℚ) := by norm_num [gapRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem gapRange_hi : gapRange.hi = (-2186498951561311076900059499157479 / 649037107316853453566312041152512000 : ℚ) := by norm_num [gapRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]

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
theorem e3_contains {e3 : ℝ} (he3 : e3 ∈ Icc (-1 / 1024 : ℝ) (1 / 1024 : ℝ)) : wholeBox.e3.RealContains e3 := by simpa [wholeBox, LeanSuffixReflective.QInterval.RealContains] using he3
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
      (-1 / 1024 : ℝ) (1 / 1024 : ℝ) := by
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
    have hm : areaLoRange.RealContains (E t (aAt t e4) (bAt t (-1 / 1024 : ℝ))) := by
      simpa [areaLoRange] using replay_sound wholeModel.area centerModel.area (by simp)
        ⟨ht, e4_contains he4, by norm_num [wholeBox, LeanSuffixReflective.QInterval.RealContains]⟩
        e4FullDisp e3LoDisp (by simpa [e4FullDisp, wholeBox] using e4_contains he4)
        (by norm_num [e3LoDisp, LeanSuffixReflective.QInterval.RealContains])
    exact neg_of_mem hm hAreaLo
  · intro e4 he4
    have hm : areaHiRange.RealContains (E t (aAt t e4) (bAt t (1 / 1024 : ℝ))) := by
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
end Remote
end
end NearOneScalarStress

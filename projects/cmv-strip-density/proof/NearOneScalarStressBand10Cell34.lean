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
namespace Band10Cell34
def wholeBox : Box3 := { t := ⟨(1568 / 63167 : ℚ), (1584 / 63167 : ℚ), by norm_num⟩, e4 := ⟨(-1 / 8192 : ℚ), (1 / 8192 : ℚ), by norm_num⟩, e3 := ⟨(-1 / 2048 : ℚ), (1 / 2048 : ℚ), by norm_num⟩ }
def centerBox : Box3 := { t := ⟨(1576 / 63167 : ℚ), (1576 / 63167 : ℚ), by norm_num⟩, e4 := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩, e3 := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩ }
def aAt (t e4 : ℝ) : ℝ := ((245959353840664566522803882837862649 / 664613997892457936451903530140172288 : ℚ) : ℝ) + ((-671179027940108607872218308138538755 / 1329227995784915872903807060280344576 : ℚ) : ℝ) * t + t ^ 2 * e4
def bAt (t e3 : ℝ) : ℝ := ((983662892817771003774008778661554167 / 1329227995784915872903807060280344576 : ℚ) : ℝ) + ((-96813376801866084990530125871242057 / 166153499473114484112975882535043072 : ℚ) : ℝ) * t + t ^ 2 * e3

def tCenter : ℚ := (1576 / 63167 : ℚ)
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
private abbrev wQ4_wJ3v : LeanSuffixReflective.QInterval := ⟨(453079092083062987076256066713 / 1267650600228229401496703205376 : ℚ), (453241418491830111354358143557 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d0 : LeanSuffixReflective.QInterval := ⟨(-320046980711098557480877237223 / 633825300114114700748351602688 : ℚ), (-160019609972947944099020947571 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d1 : LeanSuffixReflective.QInterval := ⟨(781108170041762966228943269 / 1267650600228229401496703205376 : ℚ), (797130484650074847148050083 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ3 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (245959353840664566522803882837862649 / 664613997892457936451903530140172288 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-671179027940108607872218308138538755 / 1329227995784915872903807060280344576 : ℚ)).mul (wJ0))).add (((wJ0).mul (wJ0)).mul (wJ1))).widenAll wQ4_wJ3v wQ4_wJ3d0 wQ4_wJ3d1 wQ4_wJ3d2 (by
    norm_num [wJ0, wJ1, wQ4_wJ3v, wQ4_wJ3d0, wQ4_wJ3d1, wQ4_wJ3d2])
private abbrev wQ5_wJ4v : LeanSuffixReflective.QInterval := ⟨(919571541544708723091797899537 / 1267650600228229401496703205376 : ℚ), (229939852993348283390431666137 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d0 : LeanSuffixReflective.QInterval := ⟨(-738658490584813400752939618683 / 1267650600228229401496703205376 : ℚ), (-369298202231596023245128441019 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d2 : LeanSuffixReflective.QInterval := ⟨(781108170041762966228943269 / 1267650600228229401496703205376 : ℚ), (797130484650074847148050083 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ4 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (983662892817771003774008778661554167 / 1329227995784915872903807060280344576 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-96813376801866084990530125871242057 / 166153499473114484112975882535043072 : ℚ)).mul (wJ0))).add (((wJ0).mul (wJ0)).mul (wJ2))).widenAll wQ5_wJ4v wQ5_wJ4d0 wQ5_wJ4d1 wQ5_wJ4d2 (by
    norm_num [wJ0, wJ2, wQ5_wJ4v, wQ5_wJ4d0, wQ5_wJ4d1, wQ5_wJ4d2])
private abbrev wQ6_wJ5v : LeanSuffixReflective.QInterval := ⟨(781108170041762966228943269 / 1267650600228229401496703205376 : ℚ), (797130484650074847148050083 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d0 : LeanSuffixReflective.QInterval := ⟨(62934004817637807765030177973 / 1267650600228229401496703205376 : ℚ), (63576188540266764987122322647 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ5 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ6_wJ5v wQ6_wJ5d0 wQ6_wJ5d1 wQ6_wJ5d2 (by
    norm_num [wJ0, wQ6_wJ5v, wQ6_wJ5d0, wQ6_wJ5d1, wQ6_wJ5d2])
private abbrev wQ7_wJ6v : LeanSuffixReflective.QInterval := ⟨(781108170041762966228943269 / 1267650600228229401496703205376 : ℚ), (797130484650074847148050083 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d0 : LeanSuffixReflective.QInterval := ⟨(62934004817637807765030177973 / 1267650600228229401496703205376 : ℚ), (63576188540266764987122322647 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ6 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ7_wJ6v wQ7_wJ6d0 wQ7_wJ6d1 wQ7_wJ6d2 (by
    norm_num [wJ0, wQ7_wJ6v, wQ7_wJ6d0, wQ7_wJ6d1, wQ7_wJ6d2])
private abbrev wQ8_wJ7v : LeanSuffixReflective.QInterval := ⟨(161937890177193685530346736649 / 1267650600228229401496703205376 : ℚ), (162053947199252540907666102387 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d0 : LeanSuffixReflective.QInterval := ⟨(-457724068431503690827625517829 / 1267650600228229401496703205376 : ℚ), (-57193630160373716456140038769 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d1 : LeanSuffixReflective.QInterval := ⟨(279180856647302864708636935 / 633825300114114700748351602688 : ℚ), (570019138587292695851985077 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ7 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ3).mul (wJ3)).widenAll wQ8_wJ7v wQ8_wJ7d0 wQ8_wJ7d1 wQ8_wJ7d2 (by
    norm_num [wJ3, wQ8_wJ7v, wQ8_wJ7d0, wQ8_wJ7d1, wQ8_wJ7d2])
private abbrev wQ9_wJ8v : LeanSuffixReflective.QInterval := ⟨(1267365590658935755148777212837 / 1267650600228229401496703205376 : ℚ), (1267371419371582098631994568441 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d0 : LeanSuffixReflective.QInterval := ⟨(-22336905273684673033427876861 / 1267650600228229401496703205376 : ℚ), (-22091137218090332329337291707 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d1 : LeanSuffixReflective.QInterval := ⟨(-501255637353117599912271 / 1267650600228229401496703205376 : ℚ), (-481307683044636372052697 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ8 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ6).mul (wJ3)).neg)).widenAll wQ9_wJ8v wQ9_wJ8d0 wQ9_wJ8d1 wQ9_wJ8d2 (by
    norm_num [wJ6, wJ3, wQ9_wJ8v, wQ9_wJ8d0, wQ9_wJ8d1, wQ9_wJ8d2])
private abbrev wQ10_wJ9v : LeanSuffixReflective.QInterval := ⟨(906056280580510868205359230039 / 1267650600228229401496703205376 : ℚ), (453191526585876705052018891071 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d0 : LeanSuffixReflective.QInterval := ⟨(-161004180244062586105053428959 / 158456325028528675187087900672 : ℚ), (-1287908648409966579437394048239 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d1 : LeanSuffixReflective.QInterval := ⟨(780928948877776572924156271 / 633825300114114700748351602688 : ℚ), (796958457399026959961921297 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ9 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ3)).add (((wJ6).mul (wJ7)).neg)).widenAll wQ10_wJ9v wQ10_wJ9d0 wQ10_wJ9d1 wQ10_wJ9d2 (by
    norm_num [wJ3, wJ6, wJ7, wQ10_wJ9v, wQ10_wJ9d0, wQ10_wJ9d1, wQ10_wJ9d2])
private abbrev wQ11_wJ10v : LeanSuffixReflective.QInterval := ⟨(484495383352915860303380730355 / 633825300114114700748351602688 : ℚ), (969959742967657528208760017059 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d0 : LeanSuffixReflective.QInterval := ⟨(1247345316571343013504288807507 / 1267650600228229401496703205376 : ℚ), (623736254324817682964159790303 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d1 : LeanSuffixReflective.QInterval := ⟨(780928948877776572924156271 / 633825300114114700748351602688 : ℚ), (796958457399026959961921297 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ10 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ3)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ0))).add (((wJ6).mul (wJ7)).neg)).add (((wJ0).mul (wJ0)).mul ((wJ0).mul (wJ0)))).widenAll wQ11_wJ10v wQ11_wJ10d0 wQ11_wJ10d1 wQ11_wJ10d2 (by
    norm_num [wJ3, wJ0, wJ6, wJ7, wQ11_wJ10v, wQ11_wJ10d0, wQ11_wJ10d1, wQ11_wJ10d2])
private abbrev wQ11_root11 : LeanSuffixReflective.QInterval := ⟨(535855108195872672560396476217 / 633825300114114700748351602688 : ℚ), (1071903457121894152127785875473 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11v : LeanSuffixReflective.QInterval := ⟨(535855108195872672560396476217 / 633825300114114700748351602688 : ℚ), (1071903457121894152127785875473 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d0 : LeanSuffixReflective.QInterval := ⟨(-761762060691360568565585099499 / 1267650600228229401496703205376 : ℚ), (-761550940221645627219916493683 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d1 : LeanSuffixReflective.QInterval := ⟨(230884844200091915706773011 / 316912650057057350374175801344 : ℚ), (471333039205420464491075599 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ11 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ9).sqrt wQ11_root11 (by norm_num [wQ11_root11]) (by norm_num [wJ9, wQ11_root11]) (by norm_num [wJ9, wQ11_root11])).widenAll wQ12_wJ11v wQ12_wJ11d0 wQ12_wJ11d1 wQ12_wJ11d2 (by
    norm_num [wJ9, wQ11_root11, NearOneScalarInterval.Jet3.sqrt, wQ12_wJ11v, wQ12_wJ11d0, wQ12_wJ11d1, wQ12_wJ11d2])
private abbrev wQ12_root12 : LeanSuffixReflective.QInterval := ⟨(138538223912564322905411718835 / 158456325028528675187087900672 : ℚ), (554429898718081891702742756301 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12v : LeanSuffixReflective.QInterval := ⟨(138538223912564322905411718835 / 158456325028528675187087900672 : ℚ), (554429898718081891702742756301 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d0 : LeanSuffixReflective.QInterval := ⟨(712983752724862477246561631243 / 1267650600228229401496703205376 : ℚ), (713412889642269951384955689909 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d1 : LeanSuffixReflective.QInterval := ⟨(446379719541371564094043271 / 633825300114114700748351602688 : ℚ), (911539824846867831973910351 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ12 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ10).sqrt wQ12_root12 (by norm_num [wQ12_root12]) (by norm_num [wJ10, wQ12_root12]) (by norm_num [wJ10, wQ12_root12])).widenAll wQ13_wJ12v wQ13_wJ12d0 wQ13_wJ12d1 wQ13_wJ12d2 (by
    norm_num [wJ10, wQ12_root12, NearOneScalarInterval.Jet3.sqrt, wQ13_wJ12v, wQ13_wJ12d0, wQ13_wJ12d1, wQ13_wJ12d2])
private abbrev wQ14_wJ13v : LeanSuffixReflective.QInterval := ⟨(633834994872537813167265331241 / 633825300114114700748351602688 : ℚ), (316917647344753796772445002475 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d0 : LeanSuffixReflective.QInterval := ⟨(2343324510125288898686829809 / 1267650600228229401496703205376 : ℚ), (2391391453950224541444150247 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ13 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0))).widenAll wQ14_wJ13v wQ14_wJ13d0 wQ14_wJ13d1 wQ14_wJ13d2 (by
    norm_num [wJ0, wQ14_wJ13v, wQ14_wJ13d0, wQ14_wJ13d1, wQ14_wJ13d2])
private abbrev wQ15_wJ14v : LeanSuffixReflective.QInterval := ⟨(2180032400177138062580004321481 / 1267650600228229401496703205376 : ℚ), (545195039259694909933131511313 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d0 : LeanSuffixReflective.QInterval := ⟨(-46809202409589116656657490725 / 1267650600228229401496703205376 : ℚ), (-46127579664458375997272646381 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d1 : LeanSuffixReflective.QInterval := ⟨(1816312942001381392331855325 / 1267650600228229401496703205376 : ℚ), (1854220767838200110031385595 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ14 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ12).add ((wJ13).mul (wJ11))).widenAll wQ15_wJ14v wQ15_wJ14d0 wQ15_wJ14d1 wQ15_wJ14d2 (by
    norm_num [wJ12, wJ13, wJ11, wQ15_wJ14v, wQ15_wJ14d0, wQ15_wJ14d1, wQ15_wJ14d2])
private abbrev wQ16_wJ15v : LeanSuffixReflective.QInterval := ⟨(1611390462476663016857385420063 / 1267650600228229401496703205376 : ℚ), (201629965943112528764607427057 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d0 : LeanSuffixReflective.QInterval := ⟨(-17996502012967279673036187645 / 158456325028528675187087900672 : ℚ), (-35426558901700574058240560455 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d1 : LeanSuffixReflective.QInterval := ⟨(251822009062241667940205345 / 79228162514264337593543950336 : ℚ), (4116056475056015361891096863 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ15 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ11).mul (wJ12)).mul (wJ14)).widenAll wQ16_wJ15v wQ16_wJ15d0 wQ16_wJ15d1 wQ16_wJ15d2 (by
    norm_num [wJ11, wJ12, wJ14, wQ16_wJ15v, wQ16_wJ15d0, wQ16_wJ15d1, wQ16_wJ15d2])
private abbrev wQ17_wJ16v : LeanSuffixReflective.QInterval := ⟨(2180065745150067464642672460099 / 1267650600228229401496703205376 : ℚ), (2180814545018702379486704330853 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d0 : LeanSuffixReflective.QInterval := ⟨(-21390013084425410195120386795 / 633825300114114700748351602688 : ℚ), (-21007148736463124890227203627 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d1 : LeanSuffixReflective.QInterval := ⟨(1816340723655396001239900971 / 1267650600228229401496703205376 : ℚ), (927125003207140379305667101 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ16 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ13).mul (wJ14)).widenAll wQ17_wJ16v wQ17_wJ16d0 wQ17_wJ16d1 wQ17_wJ16d2 (by
    norm_num [wJ13, wJ14, wQ17_wJ16v, wQ17_wJ16d0, wQ17_wJ16d1, wQ17_wJ16d2])
private abbrev wQ18_wJ17v : LeanSuffixReflective.QInterval := ⟨(1090014373755369526459456535663 / 633825300114114700748351602688 : ℚ), (2180817112105121214872007096249 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d0 : LeanSuffixReflective.QInterval := ⟨(-45659422484340251067317204825 / 1267650600228229401496703205376 : ℚ), (-43297391032279024130153008917 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d1 : LeanSuffixReflective.QInterval := ⟨(1816241175450789374466024031 / 1267650600228229401496703205376 : ℚ), (927160948900403470282251227 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ17 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ11).add (wJ12)).mul (((wJ8).mul (wJ8)).add ((wJ6).mul ((wJ11).mul (wJ12))))).widenAll wQ18_wJ17v wQ18_wJ17d0 wQ18_wJ17d1 wQ18_wJ17d2 (by
    norm_num [wJ11, wJ12, wJ8, wJ6, wQ18_wJ17v, wQ18_wJ17d0, wQ18_wJ17d1, wQ18_wJ17d2])
private abbrev wQ19_wJ18v : LeanSuffixReflective.QInterval := ⟨(2534180671137367587324686629639 / 1267650600228229401496703205376 : ℚ), (2534204580347724734109890742479 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d0 : LeanSuffixReflective.QInterval := ⟨(-2718324281529091363134308691 / 39614081257132168796771975168 : ℚ), (-85955019023437948519674282629 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d1 : LeanSuffixReflective.QInterval := ⟨(-2004596778322886486516081 / 1267650600228229401496703205376 : ℚ), (-481203149364132601330819 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ18 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul (wJ8)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).widenAll wQ19_wJ18v wQ19_wJ18d0 wQ19_wJ18d1 wQ19_wJ18d2 (by
    norm_num [wJ8, wJ0, wQ19_wJ18v, wQ19_wJ18d0, wQ19_wJ18d1, wQ19_wJ18d2])
private abbrev wQ20_wJ19v : LeanSuffixReflective.QInterval := ⟨(996217276498702906609458797435 / 1267650600228229401496703205376 : ℚ), (997236909165498288705646594945 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d0 : LeanSuffixReflective.QInterval := ⟨(2734941165901215353803619993 / 39614081257132168796771975168 : ℚ), (89099576849268201997833931721 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d1 : LeanSuffixReflective.QInterval := ⟨(-1273646435398007326536298525 / 633825300114114700748351602688 : ℚ), (-2488414208245195782092297457 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ19 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ15).invPos (by norm_num [wJ15])).widenAll wQ20_wJ19v wQ20_wJ19d0 wQ20_wJ19d1 wQ20_wJ19d2 (by
    norm_num [wJ15, NearOneScalarInterval.Jet3.invPos, wQ20_wJ19v, wQ20_wJ19d0, wQ20_wJ19d1, wQ20_wJ19d2])
private abbrev wQ21_wJ20v : LeanSuffixReflective.QInterval := ⟨(248944244366467410168320691233 / 158456325028528675187087900672 : ℚ), (1993611127895977807896976965625 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d0 : LeanSuffixReflective.QInterval := ⟨(106528325302088979672341046553 / 1267650600228229401496703205376 : ℚ), (110572014702079767113109206507 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d1 : LeanSuffixReflective.QInterval := ⟨(-5093959106232515417542697701 / 1267650600228229401496703205376 : ℚ), (-1244035367227073095952880927 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ20 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ18).mul (wJ19)).widenAll wQ21_wJ20v wQ21_wJ20d0 wQ21_wJ20d1 wQ21_wJ20d2 (by
    norm_num [wJ18, wJ19, wQ21_wJ20v, wQ21_wJ20d0, wQ21_wJ20d1, wQ21_wJ20d2])
private abbrev wQ22_wJ21v : LeanSuffixReflective.QInterval := ⟨(736852222454894432874386931597 / 1267650600228229401496703205376 : ℚ), (92138164171992365188337036521 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d0 : LeanSuffixReflective.QInterval := ⟨(14195763935324114160379150313 / 1267650600228229401496703205376 : ℚ), (3616104774084578469064092741 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d1 : LeanSuffixReflective.QInterval := ⟨(-626943263108448771984977683 / 1267650600228229401496703205376 : ℚ), (-306852020502580622537531779 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ21 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ16).invPos (by norm_num [wJ16])).widenAll wQ22_wJ21v wQ22_wJ21d0 wQ22_wJ21d1 wQ22_wJ21d2 (by
    norm_num [wJ16, NearOneScalarInterval.Jet3.invPos, wQ22_wJ21v, wQ22_wJ21d0, wQ22_wJ21d1, wQ22_wJ21d2])
private abbrev wQ23_wJ22v : LeanSuffixReflective.QInterval := ⟨(736526555224922081596622715559 / 633825300114114700748351602688 : ℚ), (736786485574036232271070206145 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d0 : LeanSuffixReflective.QInterval := ⟨(-22201299082421690755752583901 / 1267650600228229401496703205376 : ℚ), (-10523542397155717029734682149 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d1 : LeanSuffixReflective.QInterval := ⟨(-1254509789714722388375265301 / 1267650600228229401496703205376 : ℚ), (-306996111679779299820930093 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ22 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ18).mul (wJ21)).widenAll wQ23_wJ22v wQ23_wJ22d0 wQ23_wJ22d1 wQ23_wJ22d2 (by
    norm_num [wJ18, wJ21, wQ23_wJ22v, wQ23_wJ22d0, wQ23_wJ22d1, wQ23_wJ22d2])
private abbrev wQ24_wJ23v : LeanSuffixReflective.QInterval := ⟨(736851355090399513480511705201 / 1267650600228229401496703205376 : ℚ), (737117822915807365166039051437 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d0 : LeanSuffixReflective.QInterval := ⟨(14629260324914336573969705219 / 1267650600228229401496703205376 : ℚ), (7719250063945350680335148937 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d1 : LeanSuffixReflective.QInterval := ⟨(-626988851340964157084775559 / 1267650600228229401496703205376 : ℚ), (-613668960993270387686714625 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ23 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ17).invPos (by norm_num [wJ17])).widenAll wQ24_wJ23v wQ24_wJ23d0 wQ24_wJ23d1 wQ24_wJ23d2 (by
    norm_num [wJ17, NearOneScalarInterval.Jet3.invPos, wQ24_wJ23v, wQ24_wJ23d0, wQ24_wJ23d1, wQ24_wJ23d2])
private abbrev wQ25_wJ24v : LeanSuffixReflective.QInterval := ⟨(368345660347422501460015857289 / 316912650057057350374175801344 : ℚ), (1473922588545843505020372327707 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d0 : LeanSuffixReflective.QInterval := ⟨(4637178571691859171627623799 / 1267650600228229401496703205376 : ℚ), (6578019495971418878066016673 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d1 : LeanSuffixReflective.QInterval := ⟨(-313573591491036971816856603 / 316912650057057350374175801344 : ℚ), (-1227630907197450864445883257 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ24 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).mul (wJ23)).widenAll wQ25_wJ24v wQ25_wJ24d0 wQ25_wJ24d1 wQ25_wJ24d2 (by
    norm_num [wJ8, wJ0, wJ23, wQ25_wJ24v, wQ25_wJ24d0, wQ25_wJ24d1, wQ25_wJ24d2])
private abbrev wQ26_wJ25v : LeanSuffixReflective.QInterval := ⟨(1267929842583778704983205153609 / 1267650600228229401496703205376 : ℚ), (633967836945731706660197758885 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d0 : LeanSuffixReflective.QInterval := ⟨(22100870910690500662346092029 / 1267650600228229401496703205376 : ℚ), (5586738201191408528188634291 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d1 : LeanSuffixReflective.QInterval := ⟨(481519754563934133610807 / 1267650600228229401496703205376 : ℚ), (125370277728776021447789 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ25 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ8).invPos (by norm_num [wJ8])).widenAll wQ26_wJ25v wQ26_wJ25d0 wQ26_wJ25d1 wQ26_wJ25d2 (by
    norm_num [wJ8, NearOneScalarInterval.Jet3.invPos, wQ26_wJ25v, wQ26_wJ25d0, wQ26_wJ25d1, wQ26_wJ25d2])
private abbrev wQ27_wJ26v : LeanSuffixReflective.QInterval := ⟨(27517632535735898673483491841 / 1267650600228229401496703205376 : ℚ), (27812448146817024294218142381 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d0 : LeanSuffixReflective.QInterval := ⟨(1126731940623439732265819992375 / 1267650600228229401496703205376 : ℚ), (140936648285432952183807693139 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d1 : LeanSuffixReflective.QInterval := ⟨(22176378162296868954820693 / 1267650600228229401496703205376 : ℚ), (22874263940338335468622443 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ26 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ0).mul (wJ12)).mul (wJ25)).widenAll wQ27_wJ26v wQ27_wJ26d0 wQ27_wJ26d1 wQ27_wJ26d2 (by
    norm_num [wJ0, wJ12, wJ25, wQ27_wJ26v, wQ27_wJ26d0, wQ27_wJ26d1, wQ27_wJ26d2])
private abbrev wQ28_wJ27v : LeanSuffixReflective.QInterval := ⟨(453938655722639799720876531 / 633825300114114700748351602688 : ℚ), (463419741659377225175766253 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d0 : LeanSuffixReflective.QInterval := ⟨(73150671307074541252906897807 / 1267650600228229401496703205376 : ℚ), (73925436477642565912394366475 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d1 : LeanSuffixReflective.QInterval := ⟨(-394365874813946277901357 / 633825300114114700748351602688 : ℚ), (-756448607554058167562937 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ27 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ6).mul (wJ24)).widenAll wQ28_wJ27v wQ28_wJ27d0 wQ28_wJ27d1 wQ28_wJ27d2 (by
    norm_num [wJ6, wJ24, wQ28_wJ27v, wQ28_wJ27d0, wQ28_wJ27d1, wQ28_wJ27d2])
private abbrev wQ29_wJ28v : LeanSuffixReflective.QInterval := ⟨(633723598552740702002160737421 / 633825300114114700748351602688 : ℚ), (316864738304239668705306564953 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d0 : LeanSuffixReflective.QInterval := ⟨(-8272928100079832493529725811 / 633825300114114700748351602688 : ℚ), (-15640012653171000757782968377 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d1 : LeanSuffixReflective.QInterval := ⟨(-20979854160410381151863 / 79228162514264337593543950336 : ℚ), (-307794412839723417110951 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ28 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ26).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ26]) (by norm_num [wJ26])).widenAll wQ29_wJ28v wQ29_wJ28d0 wQ29_wJ28d1 wQ29_wJ28d2 (by
    norm_num [wJ26, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ29_wJ28v, wQ29_wJ28d0, wQ29_wJ28d1, wQ29_wJ28d2])
private abbrev wQ30_wJ29v : LeanSuffixReflective.QInterval := ⟨(316912593585698202204416258505 / 316912650057057350374175801344 : ℚ), (633825195809326112527867230285 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d0 : LeanSuffixReflective.QInterval := ⟨(-36037547329675186746307089 / 1267650600228229401496703205376 : ℚ), (-2100798272493523135078967 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d1 : LeanSuffixReflective.QInterval := ⟨(173793619943843168149 / 633825300114114700748351602688 : ℚ), (48061870027356920091 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ29 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ27).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ27]) (by norm_num [wJ27])).widenAll wQ30_wJ29v wQ30_wJ29d0 wQ30_wJ29d1 wQ30_wJ29d2 (by
    norm_num [wJ27, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ30_wJ29v, wQ30_wJ29d0, wQ30_wJ29d1, wQ30_wJ29d2])
private abbrev wQ31_wJ30v : LeanSuffixReflective.QInterval := ⟨(1267929842583778704983205153609 / 1267650600228229401496703205376 : ℚ), (633967836945731706660197758885 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d0 : LeanSuffixReflective.QInterval := ⟨(22100870910690500662346092029 / 1267650600228229401496703205376 : ℚ), (5586738201191408528188634291 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d1 : LeanSuffixReflective.QInterval := ⟨(481519754563934133610807 / 1267650600228229401496703205376 : ℚ), (125370277728776021447789 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ30 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ8).invPos (by norm_num [wJ8])).widenAll wQ31_wJ30v wQ31_wJ30d0 wQ31_wJ30d1 wQ31_wJ30d2 (by
    norm_num [wJ8, NearOneScalarInterval.Jet3.invPos, wQ31_wJ30v, wQ31_wJ30d0, wQ31_wJ30d1, wQ31_wJ30d2])
private abbrev wQ32_wJ31v : LeanSuffixReflective.QInterval := ⟨(1474065341854902729983027525573 / 1267650600228229401496703205376 : ℚ), (1474619676203585132057485357517 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d0 : LeanSuffixReflective.QInterval := ⟨(60063868432334193574289172077 / 1267650600228229401496703205376 : ℚ), (7825993103157703709561925657 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d1 : LeanSuffixReflective.QInterval := ⟨(-313435885594876137882213415 / 316912650057057350374175801344 : ℚ), (-613528445056025209782213317 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ31 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ6).mul (wJ12)).mul (wJ30)).mul (wJ28)).add ((wJ24).mul (wJ29))).widenAll wQ32_wJ31v wQ32_wJ31d0 wQ32_wJ31d1 wQ32_wJ31d2 (by
    norm_num [wJ6, wJ12, wJ30, wJ28, wJ24, wJ29, wQ32_wJ31v, wQ32_wJ31d0, wQ32_wJ31d1, wQ32_wJ31d2])
private abbrev wQ33_wJ32v : LeanSuffixReflective.QInterval := ⟨(919571541544708723091797899537 / 633825300114114700748351602688 : ℚ), (229939852993348283390431666137 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d0 : LeanSuffixReflective.QInterval := ⟨(-738658490584813400752939618683 / 633825300114114700748351602688 : ℚ), (-369298202231596023245128441019 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d2 : LeanSuffixReflective.QInterval := ⟨(781108170041762966228943269 / 633825300114114700748351602688 : ℚ), (797130484650074847148050083 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ32 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ4)).widenAll wQ33_wJ32v wQ33_wJ32d0 wQ33_wJ32d1 wQ33_wJ32d2 (by
    norm_num [wJ4, wQ33_wJ32v, wQ33_wJ32d0, wQ33_wJ32d1, wQ33_wJ32d2])
private abbrev wQ34_wJ33v : LeanSuffixReflective.QInterval := ⟨(781108170041762966228943269 / 1267650600228229401496703205376 : ℚ), (797130484650074847148050083 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d0 : LeanSuffixReflective.QInterval := ⟨(62934004817637807765030177973 / 1267650600228229401496703205376 : ℚ), (63576188540266764987122322647 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ33 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ34_wJ33v wQ34_wJ33d0 wQ34_wJ33d1 wQ34_wJ33d2 (by
    norm_num [wJ0, wQ34_wJ33v, wQ34_wJ33d0, wQ34_wJ33d1, wQ34_wJ33d2])
private abbrev wQ35_wJ34v : LeanSuffixReflective.QInterval := ⟨(2668280423222824806998592647899 / 1267650600228229401496703205376 : ℚ), (1334685402683254655532774615495 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d0 : LeanSuffixReflective.QInterval := ⟨(-2143770842934557007101162321643 / 633825300114114700748351602688 : ℚ), (-4286305605720150785695322424367 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d2 : LeanSuffixReflective.QInterval := ⟨(4533014658197768604755080301 / 1267650600228229401496703205376 : ℚ), (4626942254882019951749976299 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ34 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ32).mul (wJ32)).widenAll wQ35_wJ34v wQ35_wJ34d0 wQ35_wJ34d1 wQ35_wJ34d2 (by
    norm_num [wJ32, wQ35_wJ34v, wQ35_wJ34d0, wQ35_wJ34d1, wQ35_wJ34d2])
private abbrev wQ36_wJ35v : LeanSuffixReflective.QInterval := ⟨(1266493864664508896508765711301 / 1267650600228229401496703205376 : ℚ), (1266517346563679959345514435301 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d0 : LeanSuffixReflective.QInterval := ⟨(-91346738748029874202708846911 / 1267650600228229401496703205376 : ℚ), (-90377447247424746011284020095 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d2 : LeanSuffixReflective.QInterval := ⟨(-1002511274706235199824541 / 1267650600228229401496703205376 : ℚ), (-481307683044636372052697 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ35 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ33).mul (wJ32)).neg)).widenAll wQ36_wJ35v wQ36_wJ35d0 wQ36_wJ35d1 wQ36_wJ35d2 (by
    norm_num [wJ33, wJ32, wQ36_wJ35v, wQ36_wJ35d0, wQ36_wJ35d1, wQ36_wJ35d2])
private abbrev wQ37_wJ36v : LeanSuffixReflective.QInterval := ⟨(3676607598880078067913487177659 / 1267650600228229401496703205376 : ℚ), (1838696745829138314012840269877 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d0 : LeanSuffixReflective.QInterval := ⟨(-3085869141218977551196579930261 / 1267650600228229401496703205376 : ℚ), (-1542079711830970522865276413071 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d2 : LeanSuffixReflective.QInterval := ⟨(48773799107083822822082151 / 19807040628566084398385987584 : ℚ), (1592864379899332205176914295 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ36 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ32)).add (((wJ33).mul (wJ34)).neg)).widenAll wQ37_wJ36v wQ37_wJ36d0 wQ37_wJ36d1 wQ37_wJ36d2 (by
    norm_num [wJ32, wJ33, wJ34, wQ37_wJ36v, wQ37_wJ36d0, wQ37_wJ36d1, wQ37_wJ36d2])
private abbrev wQ38_wJ37v : LeanSuffixReflective.QInterval := ⟨(1869771042502699460157444704165 / 633825300114114700748351602688 : ℚ), (3740970181454180746130402774671 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d0 : LeanSuffixReflective.QInterval := ⟨(-550490382695133848851863691083 / 1267650600228229401496703205376 : ℚ), (-34298641662646193772802449831 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d2 : LeanSuffixReflective.QInterval := ⟨(48773799107083822822082151 / 19807040628566084398385987584 : ℚ), (1592864379899332205176914295 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ37 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ32)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ0))).add (((wJ33).mul (wJ34)).neg)).add (((wJ0).mul (wJ0)).mul ((wJ0).mul (wJ0)))).widenAll wQ38_wJ37v wQ38_wJ37d0 wQ38_wJ37d1 wQ38_wJ37d2 (by
    norm_num [wJ32, wJ0, wJ33, wJ34, wQ38_wJ37v, wQ38_wJ37d0, wQ38_wJ37d1, wQ38_wJ37d2])
private abbrev wQ38_root38 : LeanSuffixReflective.QInterval := ⟨(1079427374759877053150214010227 / 633825300114114700748351602688 : ℚ), (2159085470048834976910243854983 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38v : LeanSuffixReflective.QInterval := ⟨(1079427374759877053150214010227 / 633825300114114700748351602688 : ℚ), (2159085470048834976910243854983 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d0 : LeanSuffixReflective.QInterval := ⟨(-226497629701708981586989792041 / 316912650057057350374175801344 : ℚ), (-905391796397059734792295044275 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d2 : LeanSuffixReflective.QInterval := ⟨(916360361957990460762389715 / 1267650600228229401496703205376 : ℚ), (935308634224110271665828513 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ38 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ36).sqrt wQ38_root38 (by norm_num [wQ38_root38]) (by norm_num [wJ36, wQ38_root38]) (by norm_num [wJ36, wQ38_root38])).widenAll wQ39_wJ38v wQ39_wJ38d0 wQ39_wJ38d1 wQ39_wJ38d2 (by
    norm_num [wJ36, wQ38_root38, NearOneScalarInterval.Jet3.sqrt, wQ39_wJ38v, wQ39_wJ38d0, wQ39_wJ38d1, wQ39_wJ38d2])
private abbrev wQ39_root39 : LeanSuffixReflective.QInterval := ⟨(272156686506017453103099677493 / 158456325028528675187087900672 : ℚ), (2177669188824670972979499079651 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39v : LeanSuffixReflective.QInterval := ⟨(272156686506017453103099677493 / 158456325028528675187087900672 : ℚ), (2177669188824670972979499079651 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d0 : LeanSuffixReflective.QInterval := ⟨(-10015908037809983470314442789 / 79228162514264337593543950336 : ℚ), (-159725614574664290414693829669 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d2 : LeanSuffixReflective.QInterval := ⟨(113567544658839013414854707 / 158456325028528675187087900672 : ℚ), (28981402123078297306194393 / 39614081257132168796771975168 : ℚ), by norm_num⟩
@[simp] private abbrev wJ39 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ37).sqrt wQ39_root39 (by norm_num [wQ39_root39]) (by norm_num [wJ37, wQ39_root39]) (by norm_num [wJ37, wQ39_root39])).widenAll wQ40_wJ39v wQ40_wJ39d0 wQ40_wJ39d1 wQ40_wJ39d2 (by
    norm_num [wJ37, wQ39_root39, NearOneScalarInterval.Jet3.sqrt, wQ40_wJ39v, wQ40_wJ39d0, wQ40_wJ39d1, wQ40_wJ39d2])
private abbrev wQ41_wJ40v : LeanSuffixReflective.QInterval := ⟨(633834994872537813167265331241 / 633825300114114700748351602688 : ℚ), (316917647344753796772445002475 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d0 : LeanSuffixReflective.QInterval := ⟨(2343324510125288898686829809 / 1267650600228229401496703205376 : ℚ), (2391391453950224541444150247 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ40 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0))).widenAll wQ41_wJ40v wQ41_wJ40d0 wQ41_wJ40d1 wQ41_wJ40d2 (by
    norm_num [wJ0, wQ41_wJ40v, wQ41_wJ40d0, wQ41_wJ40d1, wQ41_wJ40d2])
private abbrev wQ42_wJ41v : LeanSuffixReflective.QInterval := ⟨(2168070631307638026755209759787 / 633825300114114700748351602688 : ℚ), (4336788704757294775181652227745 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d0 : LeanSuffixReflective.QInterval := ⟨(-265567141851279772676264513941 / 316912650057057350374175801344 : ℚ), (-265264549564711435938482027493 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d2 : LeanSuffixReflective.QInterval := ⟨(912457367769702686947634483 / 633825300114114700748351602688 : ℚ), (931364125363037174786511575 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ41 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ39).add ((wJ40).mul (wJ38))).widenAll wQ42_wJ41v wQ42_wJ41d0 wQ42_wJ41d1 wQ42_wJ41d2 (by
    norm_num [wJ39, wJ40, wJ38, wQ42_wJ41v, wQ42_wJ41d0, wQ42_wJ41d1, wQ42_wJ41d2])
private abbrev wQ43_wJ42v : LeanSuffixReflective.QInterval := ⟨(1585428721645245976231531666647 / 158456325028528675187087900672 : ℚ), (198267211055045662675891290755 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d0 : LeanSuffixReflective.QInterval := ⟨(-9366475944811604298210036366559 / 1267650600228229401496703205376 : ℚ), (-2338340285369605113817492569561 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d2 : LeanSuffixReflective.QInterval := ⟨(16014285894289492300569691831 / 1267650600228229401496703205376 : ℚ), (8175492609415592278380847149 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ42 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ38).mul (wJ39)).mul (wJ41)).widenAll wQ43_wJ42v wQ43_wJ42d0 wQ43_wJ42d1 wQ43_wJ42d2 (by
    norm_num [wJ38, wJ39, wJ41, wQ43_wJ42v, wQ43_wJ42d0, wQ43_wJ42d1, wQ43_wJ42d2])
private abbrev wQ44_wJ43v : LeanSuffixReflective.QInterval := ⟨(4336207586635509982672125962439 / 1267650600228229401496703205376 : ℚ), (2168428545051032774312121256551 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d0 : LeanSuffixReflective.QInterval := ⟨(-1054269713263719592788138089025 / 1267650600228229401496703205376 : ℚ), (-263223295839420137828508466763 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d2 : LeanSuffixReflective.QInterval := ⟨(1824942648763286855611822473 / 1267650600228229401496703205376 : ℚ), (1862757623453756569273201761 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ43 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ40).mul (wJ41)).widenAll wQ44_wJ43v wQ44_wJ43d0 wQ44_wJ43d1 wQ44_wJ43d2 (by
    norm_num [wJ40, wJ41, wQ44_wJ43v, wQ44_wJ43d0, wQ44_wJ43d1, wQ44_wJ43d2])
private abbrev wQ45_wJ44v : LeanSuffixReflective.QInterval := ⟨(271000857063445896314357803467 / 79228162514264337593543950336 : ℚ), (542122918469510462416347104759 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d0 : LeanSuffixReflective.QInterval := ⟨(-1064917215775245481762569208147 / 1267650600228229401496703205376 : ℚ), (-1050372740643240774905583069783 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d2 : LeanSuffixReflective.QInterval := ⟨(912293609345816092039058859 / 633825300114114700748351602688 : ℚ), (465771493639163390038726615 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ44 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ38).add (wJ39)).mul (((wJ35).mul (wJ35)).add ((wJ33).mul ((wJ38).mul (wJ39))))).widenAll wQ45_wJ44v wQ45_wJ44d0 wQ45_wJ44d1 wQ45_wJ44d2 (by
    norm_num [wJ38, wJ39, wJ35, wJ33, wQ45_wJ44v, wQ45_wJ44d0, wQ45_wJ44d1, wQ45_wJ44d2])
private abbrev wQ46_wJ45v : LeanSuffixReflective.QInterval := ⟨(1265347861699491389777851502551 / 633825300114114700748351602688 : ℚ), (2530790165436354865667861603553 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d0 : LeanSuffixReflective.QInterval := ⟨(-362724134918519947513975761297 / 1267650600228229401496703205376 : ℚ), (-358795554637253398853761694819 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d2 : LeanSuffixReflective.QInterval := ⟨(-4006491788919272197871087 / 1267650600228229401496703205376 : ℚ), (-1923488662841317480951899 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ45 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ35).mul (wJ35)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).widenAll wQ46_wJ45v wQ46_wJ45d0 wQ46_wJ45d1 wQ46_wJ45d2 (by
    norm_num [wJ35, wJ0, wQ46_wJ45v, wQ46_wJ45d0, wQ46_wJ45d1, wQ46_wJ45d2])
private abbrev wQ47_wJ46v : LeanSuffixReflective.QInterval := ⟨(31659807499102540358307342749 / 316912650057057350374175801344 : ℚ), (126695860110272211033951047907 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d0 : LeanSuffixReflective.QInterval := ⟨(93348016180099220464851040507 / 1267650600228229401496703205376 : ℚ), (93562525850942529531817535411 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d2 : LeanSuffixReflective.QInterval := ⟨(-40832845945456672738860601 / 316912650057057350374175801344 : ℚ), (-159825093478276789203986017 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ46 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ42).invPos (by norm_num [wJ42])).widenAll wQ47_wJ46v wQ47_wJ46d0 wQ47_wJ46d1 wQ47_wJ46d2 (by
    norm_num [wJ42, NearOneScalarInterval.Jet3.invPos, wQ47_wJ46v, wQ47_wJ46d0, wQ47_wJ46d1, wQ47_wJ46d2])
private abbrev wQ48_wJ47v : LeanSuffixReflective.QInterval := ⟨(252818369437725811618304162753 / 1267650600228229401496703205376 : ℚ), (252940862971901358628697170081 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d0 : LeanSuffixReflective.QInterval := ⟨(150104278769119526446584331967 / 1267650600228229401496703205376 : ℚ), (37737040371594227727146508009 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d2 : LeanSuffixReflective.QInterval := ⟨(-5101280787057803833454933 / 19807040628566084398385987584 : ℚ), (-319453845350404174498593809 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ47 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ45).mul (wJ46)).widenAll wQ48_wJ47v wQ48_wJ47d0 wQ48_wJ47d1 wQ48_wJ47d2 (by
    norm_num [wJ45, wJ46, wQ48_wJ47v, wQ48_wJ47d0, wQ48_wJ47d1, wQ48_wJ47d2])
private abbrev wQ49_wJ48v : LeanSuffixReflective.QInterval := ⟨(370530550320986452343858098461 / 1267650600228229401496703205376 : ℚ), (185293025316832599273676692409 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d0 : LeanSuffixReflective.QInterval := ⟨(44978319847006440699080382957 / 633825300114114700748351602688 : ℚ), (45050616412512803355594651761 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d2 : LeanSuffixReflective.QInterval := ⟨(-79598586687946942202314833 / 633825300114114700748351602688 : ℚ), (-4872458541850590470171703 / 39614081257132168796771975168 : ℚ), by norm_num⟩
@[simp] private abbrev wJ48 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ43).invPos (by norm_num [wJ43])).widenAll wQ49_wJ48v wQ49_wJ48d0 wQ49_wJ48d1 wQ49_wJ48d2 (by
    norm_num [wJ43, NearOneScalarInterval.Jet3.invPos, wQ49_wJ48v, wQ49_wJ48d0, wQ49_wJ48d1, wQ49_wJ48d2])
private abbrev wQ50_wJ49v : LeanSuffixReflective.QInterval := ⟨(739714933213590010117460632059 / 1267650600228229401496703205376 : ℚ), (739853341467059332761478305073 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d0 : LeanSuffixReflective.QInterval := ⟨(73547378685600640602624491005 / 1267650600228229401496703205376 : ℚ), (75006945602898959551039292015 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d2 : LeanSuffixReflective.QInterval := ⟨(-318999092211312313749729917 / 1267650600228229401496703205376 : ℚ), (-156197670861301999587319897 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ49 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ45).mul (wJ48)).widenAll wQ50_wJ49v wQ50_wJ49d0 wQ50_wJ49d1 wQ50_wJ49d2 (by
    norm_num [wJ45, wJ48, wQ50_wJ49v, wQ50_wJ49d0, wQ50_wJ49d1, wQ50_wJ49d2])
private abbrev wQ51_wJ50v : LeanSuffixReflective.QInterval := ⟨(92629940871827742464773609775 / 316912650057057350374175801344 : ℚ), (92650655107221373834818039451 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d0 : LeanSuffixReflective.QInterval := ⟨(22434018546440375315820536415 / 316912650057057350374175801344 : ℚ), (45509670497755796248853815223 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d2 : LeanSuffixReflective.QInterval := ⟨(-159239474308505194151709059 / 1267650600228229401496703205376 : ℚ), (-155879229990904631712104963 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ50 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ44).invPos (by norm_num [wJ44])).widenAll wQ51_wJ50v wQ51_wJ50d0 wQ51_wJ50d1 wQ51_wJ50d2 (by
    norm_num [wJ44, NearOneScalarInterval.Jet3.invPos, wQ51_wJ50v, wQ51_wJ50d0, wQ51_wJ50d1, wQ51_wJ50d2])
private abbrev wQ52_wJ51v : LeanSuffixReflective.QInterval := ⟨(740368988001791583953145067439 / 1267650600228229401496703205376 : ℚ), (740548457240737566572850366107 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d0 : LeanSuffixReflective.QInterval := ⟨(31645657633018331713889341451 / 316912650057057350374175801344 : ℚ), (64871368716375059317464544215 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d2 : LeanSuffixReflective.QInterval := ⟨(-79695731132800972001436777 / 316912650057057350374175801344 : ℚ), (-156019544308578879689049879 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ51 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ35).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).mul (wJ50)).widenAll wQ52_wJ51v wQ52_wJ51d0 wQ52_wJ51d1 wQ52_wJ51d2 (by
    norm_num [wJ35, wJ0, wJ50, wQ52_wJ51v, wQ52_wJ51d0, wQ52_wJ51d1, wQ52_wJ51d2])
private abbrev wQ53_wJ52v : LeanSuffixReflective.QInterval := ⟨(1268784867904842475630141572987 / 1267650600228229401496703205376 : ℚ), (317202098070302180892783811721 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d0 : LeanSuffixReflective.QInterval := ⟨(90539255367107709383416280505 / 1267650600228229401496703205376 : ℚ), (22878418910012130553399779205 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d2 : LeanSuffixReflective.QInterval := ⟨(964338793637944416826945 / 1267650600228229401496703205376 : ℚ), (502171686019478561926727 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ52 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ35).invPos (by norm_num [wJ35])).widenAll wQ53_wJ52v wQ53_wJ52d0 wQ53_wJ52d1 wQ53_wJ52d2 (by
    norm_num [wJ35, NearOneScalarInterval.Jet3.invPos, wQ53_wJ52v, wQ53_wJ52d0, wQ53_wJ52d1, wQ53_wJ52d2])
private abbrev wQ54_wJ53v : LeanSuffixReflective.QInterval := ⟨(54094514429489847721129981741 / 1267650600228229401496703205376 : ℚ), (27328973078705276242406362063 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d0 : LeanSuffixReflective.QInterval := ⟨(2179039585674389783885516286863 / 1267650600228229401496703205376 : ℚ), (1089815936010450597527630782621 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d2 : LeanSuffixReflective.QInterval := ⟨(11307035746200728044389283 / 633825300114114700748351602688 : ℚ), (11660233578671426526391477 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ53 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ0).mul (wJ39)).mul (wJ52)).widenAll wQ54_wJ53v wQ54_wJ53d0 wQ54_wJ53d1 wQ54_wJ53d2 (by
    norm_num [wJ0, wJ39, wJ52, wQ54_wJ53v, wQ54_wJ53d0, wQ54_wJ53d1, wQ54_wJ53d2])
private abbrev wQ55_wJ54v : LeanSuffixReflective.QInterval := ⟨(228102390859765317672762365 / 633825300114114700748351602688 : ℚ), (116418859921040848956105193 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d0 : LeanSuffixReflective.QInterval := ⟨(287769433570048102122269681 / 9903520314283042199192993792 : ℚ), (18611070835849886591116576559 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d2 : LeanSuffixReflective.QInterval := ⟨(-100229348325152144023529 / 633825300114114700748351602688 : ℚ), (-24034252956548616453107 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev wJ54 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ33).mul (wJ51)).widenAll wQ55_wJ54v wQ55_wJ54d0 wQ55_wJ54d1 wQ55_wJ54d2 (by
    norm_num [wJ33, wJ51, wQ55_wJ54v, wQ55_wJ54d0, wQ55_wJ54d1, wQ55_wJ54d2])
private abbrev wQ56_wJ55v : LeanSuffixReflective.QInterval := ⟨(1266865028589480648660804794877 / 1267650600228229401496703205376 : ℚ), (1266909995687191275151954362317 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d0 : LeanSuffixReflective.QInterval := ⟨(-63058762471832644432790655183 / 1267650600228229401496703205376 : ℚ), (-1851905116442774166015535145 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d2 : LeanSuffixReflective.QInterval := ⟨(-337341323111500990595817 / 633825300114114700748351602688 : ℚ), (-614880060746298665852923 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ55 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ53).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ53]) (by norm_num [wJ53])).widenAll wQ56_wJ55v wQ56_wJ55d0 wQ56_wJ55d1 wQ56_wJ55d2 (by
    norm_num [wJ53, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ56_wJ55v, wQ56_wJ55d0, wQ56_wJ55d1, wQ56_wJ55d2])
private abbrev wQ57_wJ56v : LeanSuffixReflective.QInterval := ⟨(1267650543205783025501008377005 / 1267650600228229401496703205376 : ℚ), (1267650547553831130051905526667 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d0 : LeanSuffixReflective.QInterval := ⟨(-2279070735230455760228445 / 316912650057057350374175801344 : ℚ), (-8505478087663984544394935 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d2 : LeanSuffixReflective.QInterval := ⟨(44398050402820316561 / 1267650600228229401496703205376 : ℚ), (24547730390564875101 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ56 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ54).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ54]) (by norm_num [wJ54])).widenAll wQ57_wJ56v wQ57_wJ56d0 wQ57_wJ56d1 wQ57_wJ56d2 (by
    norm_num [wJ54, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ57_wJ56v, wQ57_wJ56d0, wQ57_wJ56d1, wQ57_wJ56d2])
private abbrev wQ58_wJ57v : LeanSuffixReflective.QInterval := ⟨(1268784867904842475630141572987 / 1267650600228229401496703205376 : ℚ), (317202098070302180892783811721 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d0 : LeanSuffixReflective.QInterval := ⟨(90539255367107709383416280505 / 1267650600228229401496703205376 : ℚ), (22878418910012130553399779205 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d2 : LeanSuffixReflective.QInterval := ⟨(964338793637944416826945 / 1267650600228229401496703205376 : ℚ), (502171686019478561926727 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ57 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ35).invPos (by norm_num [wJ35])).widenAll wQ58_wJ57v wQ58_wJ57d0 wQ58_wJ57d1 wQ58_wJ57d2 (by
    norm_num [wJ35, NearOneScalarInterval.Jet3.invPos, wQ58_wJ57v, wQ58_wJ57d0, wQ58_wJ57d1, wQ58_wJ57d2])
private abbrev wQ59_wJ58v : LeanSuffixReflective.QInterval := ⟨(741710915452373462264453556121 / 1267650600228229401496703205376 : ℚ), (185479562348838881439056580105 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d0 : LeanSuffixReflective.QInterval := ⟨(234626062755039547639168693193 / 1267650600228229401496703205376 : ℚ), (238927363365941462640034592219 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d2 : LeanSuffixReflective.QInterval := ⟨(-318222611628640006632222413 / 1267650600228229401496703205376 : ℚ), (-155727622937597429354038957 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ58 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ33).mul (wJ39)).mul (wJ57)).mul (wJ55)).add ((wJ51).mul (wJ56))).widenAll wQ59_wJ58v wQ59_wJ58d0 wQ59_wJ58d1 wQ59_wJ58d2 (by
    norm_num [wJ33, wJ39, wJ57, wJ55, wJ51, wJ56, wQ59_wJ58v, wQ59_wJ58d0, wQ59_wJ58d1, wQ59_wJ58d2])
private abbrev wQ60_wJ59v : LeanSuffixReflective.QInterval := ⟨(633536116223184574501367229169 / 633825300114114700748351602688 : ℚ), (1267083973395954680421108820339 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d0 : LeanSuffixReflective.QInterval := ⟨(-1427292792937966784417325733 / 39614081257132168796771975168 : ℚ), (-45188723623712373005642010047 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d2 : LeanSuffixReflective.QInterval := ⟨(-501255637353117599912271 / 1267650600228229401496703205376 : ℚ), (-481307683044636372052697 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ59 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ5).mul (wJ4)).neg)).widenAll wQ60_wJ59v wQ60_wJ59d0 wQ60_wJ59d1 wQ60_wJ59d2 (by
    norm_num [wJ5, wJ4, wQ60_wJ59v, wQ60_wJ59d0, wQ60_wJ59d1, wQ60_wJ59d2])
private abbrev wQ61_wJ60v : LeanSuffixReflective.QInterval := ⟨(-1041996260422666009737448097 / 1267650600228229401496703205376 : ℚ), (521430371102600850268641253 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d0 : LeanSuffixReflective.QInterval := ⟨(-655025576112345879204569491 / 316912650057057350374175801344 : ℚ), (1311231902291543272751021053 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d1 : LeanSuffixReflective.QInterval := ⟨(-2546434729798152377600831271 / 633825300114114700748351602688 : ℚ), (-2487495222986557091911293873 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ60 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul (wJ20)).add ((((NearOneScalarInterval.Jet3.pi).mul (NearOneScalarInterval.Jet3.rational (1 / 2 : ℚ))).add ((wJ5).mul (wJ31))).neg)).widenAll wQ61_wJ60v wQ61_wJ60d0 wQ61_wJ60d1 wQ61_wJ60d2 (by
    norm_num [wJ8, wJ20, wJ5, wJ31, wQ61_wJ60v, wQ61_wJ60d0, wQ61_wJ60d1, wQ61_wJ60d2])
private abbrev wQ62_wJ61v : LeanSuffixReflective.QInterval := ⟨(-2576185444878331616375578071 / 1267650600228229401496703205376 : ℚ), (2575708911142318813844927087 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d0 : LeanSuffixReflective.QInterval := ⟨(-12231503421551818220900839305 / 1267650600228229401496703205376 : ℚ), (6116110132478815256363394967 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d1 : LeanSuffixReflective.QInterval := ⟨(-51799640870701775622158203 / 633825300114114700748351602688 : ℚ), (103655595234996706455123187 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d2 : LeanSuffixReflective.QInterval := ⟨(3635111622123109833307645731 / 1267650600228229401496703205376 : ℚ), (3762595517752084079661315225 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ61 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.pi).mul ((wJ4).add ((wJ3).neg))).mul ((wJ8).add (wJ59))).add (((wJ8).mul (wJ8)).mul ((wJ58).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ59)).add (NearOneScalarInterval.Jet3.rational (1 : ℚ))).mul (wJ49))))).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul ((wJ59).mul (wJ59))).mul ((wJ31).add ((wJ8).mul (wJ22)))).neg)).widenAll wQ62_wJ61v wQ62_wJ61d0 wQ62_wJ61d1 wQ62_wJ61d2 (by
    norm_num [wJ4, wJ3, wJ8, wJ59, wJ58, wJ49, wJ31, wJ22, wQ62_wJ61v, wQ62_wJ61d0, wQ62_wJ61d1, wQ62_wJ61d2])
private abbrev wQ63_wJ62v : LeanSuffixReflective.QInterval := ⟨(-19516483328668367955340723 / 19807040628566084398385987584 : ℚ), (733515410139807794996255025 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d0 : LeanSuffixReflective.QInterval := ⟨(-23337125438449197699350195355 / 1267650600228229401496703205376 : ℚ), (-9097944900960038246449350623 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d1 : LeanSuffixReflective.QInterval := ⟨(1804070072505566893583293229 / 1267650600228229401496703205376 : ℚ), (1901820999176520595123049465 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d2 : LeanSuffixReflective.QInterval := ⟨(-235472561277138817681155497 / 316912650057057350374175801344 : ℚ), (-227199380605004141749094055 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ62 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ3).add ((wJ4).neg)).mul (wJ20)).add ((wJ59).mul (wJ22))).add (((wJ8).mul (wJ49)).neg)).widenAll wQ63_wJ62v wQ63_wJ62d0 wQ63_wJ62d1 wQ63_wJ62d2 (by
    norm_num [wJ3, wJ4, wJ20, wJ59, wJ22, wJ8, wJ49, wQ63_wJ62v, wQ63_wJ62d0, wQ63_wJ62d1, wQ63_wJ62d2])
private abbrev wQ64_wJ63v : LeanSuffixReflective.QInterval := ⟨(116582530763219652934359938995 / 316912650057057350374175801344 : ℚ), (466680319890330146485470597835 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d0 : LeanSuffixReflective.QInterval := ⟨(-98580050693021624356855828399 / 1267650600228229401496703205376 : ℚ), (-12312805380124366441062800949 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d1 : LeanSuffixReflective.QInterval := ⟨(-797130484650074847148050083 / 1267650600228229401496703205376 : ℚ), (-781108170041762966228943269 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d2 : LeanSuffixReflective.QInterval := ⟨(781108170041762966228943269 / 1267650600228229401496703205376 : ℚ), (797130484650074847148050083 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
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
private abbrev cQ4_cJ3v : LeanSuffixReflective.QInterval := ⟨(453160255287446549215307105135 / 1267650600228229401496703205376 : ℚ), (28322515955465409325956694071 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d0 : LeanSuffixReflective.QInterval := ⟨(-640086200656994445678919132365 / 1267650600228229401496703205376 : ℚ), (-160021550164248611419729783091 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d1 : LeanSuffixReflective.QInterval := ⟨(789098994459360135266010499 / 1267650600228229401496703205376 : ℚ), (197274748614840033816502625 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ3 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (245959353840664566522803882837862649 / 664613997892457936451903530140172288 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-671179027940108607872218308138538755 / 1329227995784915872903807060280344576 : ℚ)).mul (cJ0))).add (((cJ0).mul (cJ0)).mul (cJ1))).widenAll cQ4_cJ3v cQ4_cJ3d0 cQ4_cJ3d1 cQ4_cJ3d2 (by
    norm_num [cJ0, cJ1, cQ4_cJ3v, cQ4_cJ3d0, cQ4_cJ3d1, cQ4_cJ3d2])
private abbrev cQ5_cJ4v : LeanSuffixReflective.QInterval := ⟨(459832738379525464163381141021 / 633825300114114700748351602688 : ℚ), (919665476759050928326762282043 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d0 : LeanSuffixReflective.QInterval := ⟨(-738627447524002723621598250361 / 1267650600228229401496703205376 : ℚ), (-92328430940500340452699781295 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d2 : LeanSuffixReflective.QInterval := ⟨(789098994459360135266010499 / 1267650600228229401496703205376 : ℚ), (197274748614840033816502625 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ4 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (983662892817771003774008778661554167 / 1329227995784915872903807060280344576 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-96813376801866084990530125871242057 / 166153499473114484112975882535043072 : ℚ)).mul (cJ0))).add (((cJ0).mul (cJ0)).mul (cJ2))).widenAll cQ5_cJ4v cQ5_cJ4d0 cQ5_cJ4d1 cQ5_cJ4d2 (by
    norm_num [cJ0, cJ2, cQ5_cJ4v, cQ5_cJ4d0, cQ5_cJ4d1, cQ5_cJ4d2])
private abbrev cQ6_cJ5v : LeanSuffixReflective.QInterval := ⟨(789098994459360135266010499 / 1267650600228229401496703205376 : ℚ), (197274748614840033816502625 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d0 : LeanSuffixReflective.QInterval := ⟨(31627548339476143188038125155 / 633825300114114700748351602688 : ℚ), (63255096678952286376076250311 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ5 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ6_cJ5v cQ6_cJ5d0 cQ6_cJ5d1 cQ6_cJ5d2 (by
    norm_num [cJ0, cQ6_cJ5v, cQ6_cJ5d0, cQ6_cJ5d1, cQ6_cJ5d2])
private abbrev cQ7_cJ6v : LeanSuffixReflective.QInterval := ⟨(789098994459360135266010499 / 1267650600228229401496703205376 : ℚ), (197274748614840033816502625 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d0 : LeanSuffixReflective.QInterval := ⟨(31627548339476143188038125155 / 633825300114114700748351602688 : ℚ), (63255096678952286376076250311 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ6 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ7_cJ6v cQ7_cJ6d0 cQ7_cJ6d1 cQ7_cJ6d2 (by
    norm_num [cJ0, cQ7_cJ6v, cQ7_cJ6d0, cQ7_cJ6d1, cQ7_cJ6d2])
private abbrev cQ8_cJ7v : LeanSuffixReflective.QInterval := ⟨(161995913491628921868594214483 / 1267650600228229401496703205376 : ℚ), (161995913491628921868594214485 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d0 : LeanSuffixReflective.QInterval := ⟨(-457636553863457772545521552961 / 1267650600228229401496703205376 : ℚ), (-228818276931728886272760776479 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d1 : LeanSuffixReflective.QInterval := ⟨(564174862871346983678760629 / 1267650600228229401496703205376 : ℚ), (564174862871346983678760631 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ7 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ3).mul (cJ3)).widenAll cQ8_cJ7v cQ8_cJ7d0 cQ8_cJ7d1 cQ8_cJ7d2 (by
    norm_num [cJ3, cQ8_cJ7v, cQ8_cJ7d0, cQ8_cJ7d1, cQ8_cJ7d2])
private abbrev cQ9_cJ8v : LeanSuffixReflective.QInterval := ⟨(316842128199198432001215956265 / 316912650057057350374175801344 : ℚ), (633684256398396864002431912531 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d0 : LeanSuffixReflective.QInterval := ⟨(-11107005501709419579671724753 / 633825300114114700748351602688 : ℚ), (-694187843856838723729482797 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d1 : LeanSuffixReflective.QInterval := ⟨(-245602858920536025644847 / 633825300114114700748351602688 : ℚ), (-491205717841072051289693 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ8 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ6).mul (cJ3)).neg)).widenAll cQ9_cJ8v cQ9_cJ8d0 cQ9_cJ8d1 cQ9_cJ8d2 (by
    norm_num [cJ6, cJ3, cQ9_cJ8v, cQ9_cJ8d0, cQ9_cJ8d1, cQ9_cJ8d2])
private abbrev cQ10_cJ9v : LeanSuffixReflective.QInterval := ⟨(906219669844474357608141591805 / 1267650600228229401496703205376 : ℚ), (3539920585329977959406803093 / 4951760157141521099596496896 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d0 : LeanSuffixReflective.QInterval := ⟨(-321992759529393510617172525529 / 316912650057057350374175801344 : ℚ), (-1287971038117574042468690102113 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d1 : LeanSuffixReflective.QInterval := ⟨(1577846796076693552155977611 / 1267650600228229401496703205376 : ℚ), (788923398038346776077988807 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ9 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ3)).add (((cJ6).mul (cJ7)).neg)).widenAll cQ10_cJ9v cQ10_cJ9d0 cQ10_cJ9d1 cQ10_cJ9d2 (by
    norm_num [cJ3, cJ6, cJ7, cQ10_cJ9v, cQ10_cJ9d0, cQ10_cJ9d1, cQ10_cJ9d2])
private abbrev cQ11_cJ10v : LeanSuffixReflective.QInterval := ⟨(969475257729144485056269131809 / 1267650600228229401496703205376 : ℚ), (242368814432286121264067282953 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d0 : LeanSuffixReflective.QInterval := ⟨(623704456793273429752540662037 / 633825300114114700748351602688 : ℚ), (623704456793273429752540662039 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d1 : LeanSuffixReflective.QInterval := ⟨(1577846796076693552155977611 / 1267650600228229401496703205376 : ℚ), (788923398038346776077988807 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ10 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ3)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ0))).add (((cJ6).mul (cJ7)).neg)).add (((cJ0).mul (cJ0)).mul ((cJ0).mul (cJ0)))).widenAll cQ11_cJ10v cQ11_cJ10d0 cQ11_cJ10d1 cQ11_cJ10d2 (by
    norm_num [cJ3, cJ0, cJ6, cJ7, cQ11_cJ10v, cQ11_cJ10d0, cQ11_cJ10d1, cQ11_cJ10d2])
private abbrev cQ11_root11 : LeanSuffixReflective.QInterval := ⟨(1071806842867209818682826968135 / 1267650600228229401496703205376 : ℚ), (535903421433604909341413484069 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11v : LeanSuffixReflective.QInterval := ⟨(1071806842867209818682826968135 / 1267650600228229401496703205376 : ℚ), (535903421433604909341413484069 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d0 : LeanSuffixReflective.QInterval := ⟨(-95207060302643978212752221471 / 158456325028528675187087900672 : ℚ), (-761656482421151825702017771763 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d1 : LeanSuffixReflective.QInterval := ⟨(933077844868087117510067749 / 1267650600228229401496703205376 : ℚ), (933077844868087117510067751 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ11 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ9).sqrt cQ11_root11 (by norm_num [cQ11_root11]) (by norm_num [cJ9, cQ11_root11]) (by norm_num [cJ9, cQ11_root11])).widenAll cQ12_cJ11v cQ12_cJ11d0 cQ12_cJ11d1 cQ12_cJ11d2 (by
    norm_num [cJ9, cQ11_root11, NearOneScalarInterval.Jet3.sqrt, cQ12_cJ11v, cQ12_cJ11d0, cQ12_cJ11d1, cQ12_cJ11d2])
private abbrev cQ12_root12 : LeanSuffixReflective.QInterval := ⟨(277145707657403495664960998635 / 316912650057057350374175801344 : ℚ), (1108582830629613982659843994543 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12v : LeanSuffixReflective.QInterval := ⟨(277145707657403495664960998635 / 316912650057057350374175801344 : ℚ), (1108582830629613982659843994543 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d0 : LeanSuffixReflective.QInterval := ⟨(713198244798699657598793535131 / 1267650600228229401496703205376 : ℚ), (22287445149959364299962297973 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d1 : LeanSuffixReflective.QInterval := ⟨(902124037487947310683497131 / 1267650600228229401496703205376 : ℚ), (451062018743973655341748567 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ12 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ10).sqrt cQ12_root12 (by norm_num [cQ12_root12]) (by norm_num [cJ10, cQ12_root12]) (by norm_num [cJ10, cQ12_root12])).widenAll cQ13_cJ12v cQ13_cJ12d0 cQ13_cJ12d1 cQ13_cJ12d2 (by
    norm_num [cJ10, cQ12_root12, NearOneScalarInterval.Jet3.sqrt, cQ13_cJ12v, cQ13_cJ12d0, cQ13_cJ12d1, cQ13_cJ12d2])
private abbrev cQ14_cJ13v : LeanSuffixReflective.QInterval := ⟨(1267670288040144926241794459235 / 1267650600228229401496703205376 : ℚ), (316917572010036231560448614809 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d0 : LeanSuffixReflective.QInterval := ⟨(2367296983378080405798031499 / 1267650600228229401496703205376 : ℚ), (591824245844520101449507875 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ13 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0))).widenAll cQ14_cJ13v cQ14_cJ13d0 cQ14_cJ13d1 cQ14_cJ13d2 (by
    norm_num [cJ0, cQ14_cJ13v, cQ14_cJ13d0, cQ14_cJ13d1, cQ14_cJ13d2])
private abbrev cQ15_cJ14v : LeanSuffixReflective.QInterval := ⟨(1090203159835044898307059760209 / 633825300114114700748351602688 : ℚ), (1090203159835044898307059760213 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d0 : LeanSuffixReflective.QInterval := ⟨(-23234250921028554063173039603 / 633825300114114700748351602688 : ℚ), (-23234250921028554063173039597 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d1 : LeanSuffixReflective.QInterval := ⟨(458804093484211157078809533 / 316912650057057350374175801344 : ℚ), (917608186968422314157619069 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ14 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ12).add ((cJ13).mul (cJ11))).widenAll cQ15_cJ14v cQ15_cJ14d0 cQ15_cJ14d1 cQ15_cJ14d2 (by
    norm_num [cJ12, cJ13, cJ11, cQ15_cJ14v, cQ15_cJ14d0, cQ15_cJ14d1, cQ15_cJ14d2])
private abbrev cQ16_cJ15v : LeanSuffixReflective.QInterval := ⟨(806107528492623736318720615835 / 633825300114114700748351602688 : ℚ), (806107528492623736318720615843 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d0 : LeanSuffixReflective.QInterval := ⟨(-142839082809032335402430218293 / 1267650600228229401496703205376 : ℚ), (-142839082809032335402430218261 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d1 : LeanSuffixReflective.QInterval := ⟨(1018119494907218801424381017 / 316912650057057350374175801344 : ℚ), (4072477979628875205697524081 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ15 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ11).mul (cJ12)).mul (cJ14)).widenAll cQ16_cJ15v cQ16_cJ15d0 cQ16_cJ15d1 cQ16_cJ15d2 (by
    norm_num [cJ11, cJ12, cJ14, cQ16_cJ15v, cQ16_cJ15d0, cQ16_cJ15d1, cQ16_cJ15d2])
private abbrev cQ17_cJ16v : LeanSuffixReflective.QInterval := ⟨(545110045860250152974699666227 / 316912650057057350374175801344 : ℚ), (2180440183441000611898798664919 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d0 : LeanSuffixReflective.QInterval := ⟨(-42397384422919614948401876159 / 1267650600228229401496703205376 : ℚ), (-2649836526432475934275117259 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d1 : LeanSuffixReflective.QInterval := ⟨(1835244876581649004840086291 / 1267650600228229401496703205376 : ℚ), (917622438290824502420043149 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ16 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ13).mul (cJ14)).widenAll cQ17_cJ16v cQ17_cJ16d0 cQ17_cJ16d1 cQ17_cJ16d2 (by
    norm_num [cJ13, cJ14, cQ17_cJ16v, cQ17_cJ16d0, cQ17_cJ16d1, cQ17_cJ16d2])
private abbrev cQ18_cJ17v : LeanSuffixReflective.QInterval := ⟨(2180422966101886595495921622497 / 1267650600228229401496703205376 : ℚ), (136276435381367912218495101407 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d0 : LeanSuffixReflective.QInterval := ⟨(-22239352036494118763599364325 / 633825300114114700748351602688 : ℚ), (-22239352036494118763599364315 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d1 : LeanSuffixReflective.QInterval := ⟨(229403858217840346854983971 / 158456325028528675187087900672 : ℚ), (1835230865742722774839871777 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ17 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ11).add (cJ12)).mul (((cJ8).mul (cJ8)).add ((cJ6).mul ((cJ11).mul (cJ12))))).widenAll cQ18_cJ17v cQ18_cJ17d0 cQ18_cJ17d1 cQ18_cJ17d2 (by
    norm_num [cJ11, cJ12, cJ8, cJ6, cQ18_cJ17v, cQ18_cJ17d0, cQ18_cJ17d1, cQ18_cJ17d2])
private abbrev cQ19_cJ18v : LeanSuffixReflective.QInterval := ⟨(2534192655325998582416848691337 / 1267650600228229401496703205376 : ℚ), (1267096327662999291208424345673 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d0 : LeanSuffixReflective.QInterval := ⟨(-86470717411985447590938493455 / 1267650600228229401496703205376 : ℚ), (-86470717411985447590938493445 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d1 : LeanSuffixReflective.QInterval := ⟨(-982200449070623951190869 / 633825300114114700748351602688 : ℚ), (-1964400898141247902381733 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ18 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul (cJ8)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).widenAll cQ19_cJ18v cQ19_cJ18d0 cQ19_cJ18d1 cQ19_cJ18d2 (by
    norm_num [cJ8, cJ0, cQ19_cJ18v, cQ19_cJ18d0, cQ19_cJ18d1, cQ19_cJ18d2])
private abbrev cQ20_cJ19v : LeanSuffixReflective.QInterval := ⟨(124590856946829652682606109165 / 158456325028528675187087900672 : ℚ), (996726855574637221460848873331 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d0 : LeanSuffixReflective.QInterval := ⟨(88308038834247648190525500621 / 1267650600228229401496703205376 : ℚ), (88308038834247648190525500643 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d1 : LeanSuffixReflective.QInterval := ⟨(-78679565604580804535685343 / 39614081257132168796771975168 : ℚ), (-1258873049673292872570965483 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ19 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ15).invPos (by norm_num [cJ15])).widenAll cQ20_cJ19v cQ20_cJ19d0 cQ20_cJ19d1 cQ20_cJ19d2 (by
    norm_num [cJ15, NearOneScalarInterval.Jet3.invPos, cQ20_cJ19v, cQ20_cJ19d0, cQ20_cJ19d1, cQ20_cJ19d2])
private abbrev cQ21_cJ20v : LeanSuffixReflective.QInterval := ⟨(1992582085559425583098013001337 / 1267650600228229401496703205376 : ℚ), (1992582085559425583098013001367 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d0 : LeanSuffixReflective.QInterval := ⟨(54274378574777680387459882297 / 633825300114114700748351602688 : ℚ), (13568594643694420096864970581 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d1 : LeanSuffixReflective.QInterval := ⟨(-2517417513517129439423494783 / 633825300114114700748351602688 : ℚ), (-5034835027034258878846989541 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ20 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ18).mul (cJ19)).widenAll cQ21_cJ20v cQ21_cJ20d0 cQ21_cJ20d1 cQ21_cJ20d2 (by
    norm_num [cJ18, cJ19, cQ21_cJ20v, cQ21_cJ20d0, cQ21_cJ20d1, cQ21_cJ20d2])
private abbrev cQ22_cJ21v : LeanSuffixReflective.QInterval := ⟨(46061170826383494374522089785 / 79228162514264337593543950336 : ℚ), (736978733222135909992353436565 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d0 : LeanSuffixReflective.QInterval := ⟨(14330120542277505636977168917 / 1267650600228229401496703205376 : ℚ), (14330120542277505636977168923 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d1 : LeanSuffixReflective.QInterval := ⟨(-620304310371445885667186259 / 1267650600228229401496703205376 : ℚ), (-38769019398215367854199141 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ21 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ16).invPos (by norm_num [cJ16])).widenAll cQ22_cJ21v cQ22_cJ21d0 cQ22_cJ21d1 cQ22_cJ21d2 (by
    norm_num [cJ16, NearOneScalarInterval.Jet3.invPos, cQ22_cJ21v, cQ22_cJ21d0, cQ22_cJ21d1, cQ22_cJ21d2])
private abbrev cQ23_cJ22v : LeanSuffixReflective.QInterval := ⟨(1473312987448388370954487714157 / 1267650600228229401496703205376 : ℚ), (1473312987448388370954487714173 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d0 : LeanSuffixReflective.QInterval := ⟨(-21624092274309025927761231125 / 1267650600228229401496703205376 : ℚ), (-21624092274309025927761231105 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d1 : LeanSuffixReflective.QInterval := ⟨(-1241208223159085921662290443 / 1267650600228229401496703205376 : ℚ), (-1241208223159085921662290433 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ22 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ18).mul (cJ21)).widenAll cQ23_cJ22v cQ23_cJ22d0 cQ23_cJ22d1 cQ23_cJ22d2 (by
    norm_num [cJ18, cJ21, cQ23_cJ22v, cQ23_cJ22d0, cQ23_cJ22d1, cQ23_cJ22d2])
private abbrev cQ24_cJ23v : LeanSuffixReflective.QInterval := ⟨(368492276324680169539966669785 / 633825300114114700748351602688 : ℚ), (92123069081170042384991667447 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d0 : LeanSuffixReflective.QInterval := ⟨(15033834413447822622268312891 / 1267650600228229401496703205376 : ℚ), (15033834413447822622268312899 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d1 : LeanSuffixReflective.QInterval := ⟨(-620309370991324267119139865 / 1267650600228229401496703205376 : ℚ), (-620309370991324267119139861 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ23 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ17).invPos (by norm_num [cJ17])).widenAll cQ24_cJ23v cQ24_cJ23d0 cQ24_cJ23d1 cQ24_cJ23d2 (by
    norm_num [cJ17, NearOneScalarInterval.Jet3.invPos, cQ24_cJ23v, cQ24_cJ23d0, cQ24_cJ23d1, cQ24_cJ23d2])
private abbrev cQ25_cJ24v : LeanSuffixReflective.QInterval := ⟨(1473652549794868638993420708205 / 1267650600228229401496703205376 : ℚ), (368413137448717159748355177055 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d0 : LeanSuffixReflective.QInterval := ⟨(5607511664844625499191161489 / 1267650600228229401496703205376 : ℚ), (1401877916211156374797790377 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d1 : LeanSuffixReflective.QInterval := ⟨(-310230864715911903555456731 / 316912650057057350374175801344 : ℚ), (-1240923458863647614221826913 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ24 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).mul (cJ23)).widenAll cQ25_cJ24v cQ25_cJ24d0 cQ25_cJ24d1 cQ25_cJ24d2 (by
    norm_num [cJ8, cJ0, cJ23, cQ25_cJ24v, cQ25_cJ24d0, cQ25_cJ24d1, cQ25_cJ24d2])
private abbrev cQ26_cJ25v : LeanSuffixReflective.QInterval := ⟨(1267932750445917195435812646039 / 1267650600228229401496703205376 : ℚ), (633966375222958597717906323021 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d0 : LeanSuffixReflective.QInterval := ⟨(22223900772037527847446541319 / 1267650600228229401496703205376 : ℚ), (11111950386018763923723270661 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d1 : LeanSuffixReflective.QInterval := ⟨(491424404637116107882463 / 1267650600228229401496703205376 : ℚ), (491424404637116107882465 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ25 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ8).invPos (by norm_num [cJ8])).widenAll cQ26_cJ25v cQ26_cJ25d0 cQ26_cJ25d1 cQ26_cJ25d2 (by
    norm_num [cJ8, NearOneScalarInterval.Jet3.invPos, cQ26_cJ25v, cQ26_cJ25d0, cQ26_cJ25d1, cQ26_cJ25d2])
private abbrev cQ27_cJ26v : LeanSuffixReflective.QInterval := ⟨(27665005647550842118032035945 / 1267650600228229401496703205376 : ℚ), (13832502823775421059016017973 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d0 : LeanSuffixReflective.QInterval := ⟨(1127112547715820386439631707747 / 1267650600228229401496703205376 : ℚ), (563556273857910193219815853877 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d1 : LeanSuffixReflective.QInterval := ⟨(22523489044096631015530311 / 1267650600228229401496703205376 : ℚ), (2815436130512078876941289 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ26 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ0).mul (cJ12)).mul (cJ25)).widenAll cQ27_cJ26v cQ27_cJ26d0 cQ27_cJ26d1 cQ27_cJ26d2 (by
    norm_num [cJ0, cJ12, cJ25, cQ27_cJ26v, cQ27_cJ26d0, cQ27_cJ26d1, cQ27_cJ26d2])
private abbrev cQ28_cJ27v : LeanSuffixReflective.QInterval := ⟨(458666506770966944419419229 / 633825300114114700748351602688 : ℚ), (917333013541933888838838461 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d0 : LeanSuffixReflective.QInterval := ⟨(73537975979730995161766526727 / 1267650600228229401496703205376 : ℚ), (36768987989865497580883263365 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d1 : LeanSuffixReflective.QInterval := ⟨(-772461633682054839982637 / 1267650600228229401496703205376 : ℚ), (-193115408420513709995659 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ27 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ6).mul (cJ24)).widenAll cQ28_cJ27v cQ28_cJ27d0 cQ28_cJ27d1 cQ28_cJ27d2 (by
    norm_num [cJ6, cJ24, cQ28_cJ27v, cQ28_cJ27d0, cQ28_cJ27d1, cQ28_cJ27d2])
private abbrev cQ29_cJ28v : LeanSuffixReflective.QInterval := ⟨(633724673998193217736135797167 / 633825300114114700748351602688 : ℚ), (1267456894955080546698187779749 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d0 : LeanSuffixReflective.QInterval := ⟨(-16452299108521938465037028851 / 1267650600228229401496703205376 : ℚ), (-15729986726668177628537628615 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d1 : LeanSuffixReflective.QInterval := ⟨(-164386058638052259382049 / 633825300114114700748351602688 : ℚ), (-78584473311893371597431 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ28 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ26).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ26]) (by norm_num [cJ26])).widenAll cQ29_cJ28v cQ29_cJ28d0 cQ29_cJ28d1 cQ29_cJ28d2 (by
    norm_num [cJ26, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ29_cJ28v, cQ29_cJ28d0, cQ29_cJ28d1, cQ29_cJ28d2])
private abbrev cQ30_cJ29v : LeanSuffixReflective.QInterval := ⟨(316912594738195724096058411121 / 316912650057057350374175801344 : ℚ), (1267650387250612140325951253019 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d0 : LeanSuffixReflective.QInterval := ⟨(-35480931191358140921452641 / 1267650600228229401496703205376 : ℚ), (-8535709701203496314564085 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d1 : LeanSuffixReflective.QInterval := ⟨(358645076782899852559 / 1267650600228229401496703205376 : ℚ), (93175185023420276669 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ29 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ27).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ27]) (by norm_num [cJ27])).widenAll cQ30_cJ29v cQ30_cJ29d0 cQ30_cJ29d1 cQ30_cJ29d2 (by
    norm_num [cJ27, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ30_cJ29v, cQ30_cJ29d0, cQ30_cJ29d1, cQ30_cJ29d2])
private abbrev cQ31_cJ30v : LeanSuffixReflective.QInterval := ⟨(1267932750445917195435812646039 / 1267650600228229401496703205376 : ℚ), (633966375222958597717906323021 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d0 : LeanSuffixReflective.QInterval := ⟨(22223900772037527847446541319 / 1267650600228229401496703205376 : ℚ), (11111950386018763923723270661 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d1 : LeanSuffixReflective.QInterval := ⟨(491424404637116107882463 / 1267650600228229401496703205376 : ℚ), (491424404637116107882465 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ30 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ8).invPos (by norm_num [cJ8])).widenAll cQ31_cJ30v cQ31_cJ30d0 cQ31_cJ30d1 cQ31_cJ30d2 (by
    norm_num [cJ8, NearOneScalarInterval.Jet3.invPos, cQ31_cJ30v, cQ31_cJ30d0, cQ31_cJ30d1, cQ31_cJ30d2])
private abbrev cQ32_cJ31v : LeanSuffixReflective.QInterval := ⟨(1474342417577752108288426354631 / 1267650600228229401496703205376 : ℚ), (737171215666673937143510792225 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d0 : LeanSuffixReflective.QInterval := ⟨(61334615605388270988960881889 / 1267650600228229401496703205376 : ℚ), (61336896605120540869932591207 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d1 : LeanSuffixReflective.QInterval := ⟨(-1240361146566450467167828461 / 1267650600228229401496703205376 : ℚ), (-1240361110898745261038568807 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ31 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ6).mul (cJ12)).mul (cJ30)).mul (cJ28)).add ((cJ24).mul (cJ29))).widenAll cQ32_cJ31v cQ32_cJ31d0 cQ32_cJ31d1 cQ32_cJ31d2 (by
    norm_num [cJ6, cJ12, cJ30, cJ28, cJ24, cJ29, cQ32_cJ31v, cQ32_cJ31d0, cQ32_cJ31d1, cQ32_cJ31d2])
private abbrev cQ33_cJ32v : LeanSuffixReflective.QInterval := ⟨(459832738379525464163381141021 / 316912650057057350374175801344 : ℚ), (919665476759050928326762282043 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d0 : LeanSuffixReflective.QInterval := ⟨(-738627447524002723621598250361 / 633825300114114700748351602688 : ℚ), (-92328430940500340452699781295 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d2 : LeanSuffixReflective.QInterval := ⟨(789098994459360135266010499 / 633825300114114700748351602688 : ℚ), (197274748614840033816502625 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ32 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ4)).widenAll cQ33_cJ32v cQ33_cJ32d0 cQ33_cJ32d1 cQ33_cJ32d2 (by
    norm_num [cJ4, cQ33_cJ32v, cQ33_cJ32d0, cQ33_cJ32d1, cQ33_cJ32d2])
private abbrev cQ34_cJ33v : LeanSuffixReflective.QInterval := ⟨(789098994459360135266010499 / 1267650600228229401496703205376 : ℚ), (197274748614840033816502625 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d0 : LeanSuffixReflective.QInterval := ⟨(31627548339476143188038125155 / 633825300114114700748351602688 : ℚ), (63255096678952286376076250311 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ33 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ34_cJ33v cQ34_cJ33d0 cQ34_cJ33d1 cQ34_cJ33d2 (by
    norm_num [cJ0, cQ34_cJ33v, cQ34_cJ33d0, cQ34_cJ33d1, cQ34_cJ33d2])
private abbrev cQ35_cJ34v : LeanSuffixReflective.QInterval := ⟨(333603198306448293645809174177 / 158456325028528675187087900672 : ℚ), (2668825586451586349166473393423 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d0 : LeanSuffixReflective.QInterval := ⟨(-2143461813695927203466822498119 / 633825300114114700748351602688 : ℚ), (-2143461813695927203466822498113 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d2 : LeanSuffixReflective.QInterval := ⟨(2289927848632416251449506689 / 633825300114114700748351602688 : ℚ), (4579855697264832502899013385 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ34 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ32).mul (cJ32)).widenAll cQ35_cJ34v cQ35_cJ34d0 cQ35_cJ34d1 cQ35_cJ34d2 (by
    norm_num [cJ32, cQ35_cJ34v, cQ35_cJ34d0, cQ35_cJ34d1, cQ35_cJ34d2])
private abbrev cQ36_cJ35v : LeanSuffixReflective.QInterval := ⟨(1266505636303913193370978452029 / 1267650600228229401496703205376 : ℚ), (19789150567248643646421538313 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d0 : LeanSuffixReflective.QInterval := ⟨(-90862069498012372293264130615 / 1267650600228229401496703205376 : ℚ), (-90862069498012372293264130611 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d2 : LeanSuffixReflective.QInterval := ⟨(-245602858920536025644847 / 316912650057057350374175801344 : ℚ), (-982411435682144102579387 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ35 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ33).mul (cJ32)).neg)).widenAll cQ36_cJ35v cQ36_cJ35d0 cQ36_cJ35d1 cQ36_cJ35d2 (by
    norm_num [cJ33, cJ32, cQ36_cJ35v, cQ36_cJ35d0, cQ36_cJ35d1, cQ36_cJ35d2])
private abbrev cQ37_cJ36v : LeanSuffixReflective.QInterval := ⟨(919250147884856967100636794831 / 316912650057057350374175801344 : ℚ), (919250147884856967100636794833 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d0 : LeanSuffixReflective.QInterval := ⟨(-1542507107817349261627880483445 / 633825300114114700748351602688 : ℚ), (-96406694238584328851742530215 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d2 : LeanSuffixReflective.QInterval := ⟨(3153545066454737776427149065 / 1267650600228229401496703205376 : ℚ), (1576772533227368888213574535 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ36 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ32)).add (((cJ33).mul (cJ34)).neg)).widenAll cQ37_cJ36v cQ37_cJ36d0 cQ37_cJ36d1 cQ37_cJ36d2 (by
    norm_num [cJ32, cJ33, cJ34, cQ37_cJ36v, cQ37_cJ36d0, cQ37_cJ36d1, cQ37_cJ36d2])
private abbrev cQ38_cJ37v : LeanSuffixReflective.QInterval := ⟨(116883005607003062370333584979 / 39614081257132168796771975168 : ℚ), (3740256179424097995850674719335 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d0 : LeanSuffixReflective.QInterval := ⟨(-137408565982644405320497385175 / 316912650057057350374175801344 : ℚ), (-549634263930577621281989540689 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d2 : LeanSuffixReflective.QInterval := ⟨(3153545066454737776427149065 / 1267650600228229401496703205376 : ℚ), (1576772533227368888213574535 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ37 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ32)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ0))).add (((cJ33).mul (cJ34)).neg)).add (((cJ0).mul (cJ0)).mul ((cJ0).mul (cJ0)))).widenAll cQ38_cJ37v cQ38_cJ37d0 cQ38_cJ37d1 cQ38_cJ37d2 (by
    norm_num [cJ32, cJ0, cJ33, cJ34, cQ38_cJ37v, cQ38_cJ37d0, cQ38_cJ37d1, cQ38_cJ37d2])
private abbrev cQ38_root38 : LeanSuffixReflective.QInterval := ⟨(1079485063225113632390364610089 / 633825300114114700748351602688 : ℚ), (2158970126450227264780729220181 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38v : LeanSuffixReflective.QInterval := ⟨(1079485063225113632390364610089 / 633825300114114700748351602688 : ℚ), (2158970126450227264780729220181 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d0 : LeanSuffixReflective.QInterval := ⟨(-226422778750529839717903866985 / 316912650057057350374175801344 : ℚ), (-905691115002119358871615467935 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d2 : LeanSuffixReflective.QInterval := ⟨(462905119362507322538337975 / 633825300114114700748351602688 : ℚ), (57863139920313415317292247 / 79228162514264337593543950336 : ℚ), by norm_num⟩
@[simp] private abbrev cJ38 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ36).sqrt cQ38_root38 (by norm_num [cQ38_root38]) (by norm_num [cJ36, cQ38_root38]) (by norm_num [cJ36, cQ38_root38])).widenAll cQ39_cJ38v cQ39_cJ38d0 cQ39_cJ38d1 cQ39_cJ38d2 (by
    norm_num [cJ36, cQ38_root38, NearOneScalarInterval.Jet3.sqrt, cQ39_cJ38v, cQ39_cJ38d0, cQ39_cJ38d1, cQ39_cJ38d2])
private abbrev cQ39_root39 : LeanSuffixReflective.QInterval := ⟨(1088730681901440434023512369653 / 633825300114114700748351602688 : ℚ), (2177461363802880868047024739309 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39v : LeanSuffixReflective.QInterval := ⟨(1088730681901440434023512369653 / 633825300114114700748351602688 : ℚ), (2177461363802880868047024739309 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d0 : LeanSuffixReflective.QInterval := ⟨(-159990026955231883860130891449 / 1267650600228229401496703205376 : ℚ), (-39997506738807970965032722861 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d2 : LeanSuffixReflective.QInterval := ⟨(28685879939653275737992737 / 39614081257132168796771975168 : ℚ), (458974079034452411807883793 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ39 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ37).sqrt cQ39_root39 (by norm_num [cQ39_root39]) (by norm_num [cJ37, cQ39_root39]) (by norm_num [cJ37, cQ39_root39])).widenAll cQ40_cJ39v cQ40_cJ39d0 cQ40_cJ39d1 cQ40_cJ39d2 (by
    norm_num [cJ37, cQ39_root39, NearOneScalarInterval.Jet3.sqrt, cQ40_cJ39v, cQ40_cJ39d0, cQ40_cJ39d1, cQ40_cJ39d2])
private abbrev cQ41_cJ40v : LeanSuffixReflective.QInterval := ⟨(1267670288040144926241794459235 / 1267650600228229401496703205376 : ℚ), (316917572010036231560448614809 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d0 : LeanSuffixReflective.QInterval := ⟨(2367296983378080405798031499 / 1267650600228229401496703205376 : ℚ), (591824245844520101449507875 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ40 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0))).widenAll cQ41_cJ40v cQ41_cJ40d0 cQ41_cJ40d1 cQ41_cJ40d2 (by
    norm_num [cJ0, cQ41_cJ40v, cQ41_cJ40d0, cQ41_cJ40d1, cQ41_cJ40d2])
private abbrev cQ42_cJ41v : LeanSuffixReflective.QInterval := ⟨(4336465021099678265027375564463 / 1267650600228229401496703205376 : ℚ), (542058127637459783128421945559 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d0 : LeanSuffixReflective.QInterval := ⟨(-1061663400483236588855230553011 / 1267650600228229401496703205376 : ℚ), (-530831700241618294427615276499 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d2 : LeanSuffixReflective.QInterval := ⟨(1843772775501937437924809973 / 1267650600228229401496703205376 : ℚ), (921886387750968718962404989 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ41 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ39).add ((cJ40).mul (cJ38))).widenAll cQ42_cJ41v cQ42_cJ41d0 cQ42_cJ41d1 cQ42_cJ41d2 (by
    norm_num [cJ39, cJ40, cJ38, cQ42_cJ41v, cQ42_cJ41d0, cQ42_cJ41d1, cQ42_cJ41d2])
private abbrev cQ43_cJ42v : LeanSuffixReflective.QInterval := ⟨(3171566444538574205425736805253 / 316912650057057350374175801344 : ℚ), (6343132889077148410851473610537 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d0 : LeanSuffixReflective.QInterval := ⟨(-9359917442326393831305947200405 / 1267650600228229401496703205376 : ℚ), (-9359917442326393831305947200277 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d2 : LeanSuffixReflective.QInterval := ⟨(16182183468557796604409429333 / 1267650600228229401496703205376 : ℚ), (4045545867139449151102357343 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ42 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ38).mul (cJ39)).mul (cJ41)).widenAll cQ43_cJ42v cQ43_cJ42d0 cQ43_cJ42d1 cQ43_cJ42d2 (by
    norm_num [cJ38, cJ39, cJ41, cQ43_cJ42v, cQ43_cJ42d0, cQ43_cJ42d1, cQ43_cJ42d2])
private abbrev cQ44_cJ43v : LeanSuffixReflective.QInterval := ⟨(2168266185249988484155836160371 / 633825300114114700748351602688 : ℚ), (1084133092624994242077918080189 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d0 : LeanSuffixReflective.QInterval := ⟨(-526790839640210053317618366209 / 633825300114114700748351602688 : ℚ), (-65848854955026256664702295775 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d2 : LeanSuffixReflective.QInterval := ⟨(921900705517872513945015671 / 633825300114114700748351602688 : ℚ), (460950352758936256972507837 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ43 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ40).mul (cJ41)).widenAll cQ44_cJ43v cQ44_cJ43d0 cQ44_cJ43d1 cQ44_cJ43d2 (by
    norm_num [cJ40, cJ41, cQ44_cJ43v, cQ44_cJ43d0, cQ44_cJ43d1, cQ44_cJ43d2])
private abbrev cQ45_cJ44v : LeanSuffixReflective.QInterval := ⟨(4336498552467014135453466432507 / 1267650600228229401496703205376 : ℚ), (4336498552467014135453466432545 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d0 : LeanSuffixReflective.QInterval := ⟨(-1057645533992015190717269607979 / 1267650600228229401496703205376 : ℚ), (-1057645533992015190717269607915 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d2 : LeanSuffixReflective.QInterval := ⟨(1843787154433270332417385185 / 1267650600228229401496703205376 : ℚ), (1843787154433270332417385197 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ44 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ38).add (cJ39)).mul (((cJ35).mul (cJ35)).add ((cJ33).mul ((cJ38).mul (cJ39))))).widenAll cQ45_cJ44v cQ45_cJ44d0 cQ45_cJ44d1 cQ45_cJ44d2 (by
    norm_num [cJ38, cJ39, cJ35, cJ33, cQ45_cJ44v, cQ45_cJ44d0, cQ45_cJ44d1, cQ45_cJ44d2])
private abbrev cQ46_cJ45v : LeanSuffixReflective.QInterval := ⟨(632685766331206207729596465915 / 316912650057057350374175801344 : ℚ), (2530743065324824830918385863673 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d0 : LeanSuffixReflective.QInterval := ⟨(-360759802478677110095655444285 / 1267650600228229401496703205376 : ℚ), (-360759802478677110095655444267 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d2 : LeanSuffixReflective.QInterval := ⟨(-1963063453396105122038087 / 633825300114114700748351602688 : ℚ), (-3926126906792210244076169 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ45 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ35).mul (cJ35)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).widenAll cQ46_cJ45v cQ46_cJ45d0 cQ46_cJ45d1 cQ46_cJ45d2 (by
    norm_num [cJ35, cJ0, cQ46_cJ45v, cQ46_cJ45d0, cQ46_cJ45d1, cQ46_cJ45d2])
private abbrev cQ47_cJ46v : LeanSuffixReflective.QInterval := ⟨(126667537347840504710908866619 / 1267650600228229401496703205376 : ℚ), (126667537347840504710908866621 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d0 : LeanSuffixReflective.QInterval := ⟨(93455214712604960946849905345 / 1267650600228229401496703205376 : ℚ), (23363803678151240236712476337 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d2 : LeanSuffixReflective.QInterval := ⟨(-161572945476424316411241731 / 1267650600228229401496703205376 : ℚ), (-161572945476424316411241729 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ46 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ42).invPos (by norm_num [cJ42])).widenAll cQ47_cJ46v cQ47_cJ46d0 cQ47_cJ46d1 cQ47_cJ46d2 (by
    norm_num [cJ42, NearOneScalarInterval.Jet3.invPos, cQ47_cJ46v, cQ47_cJ46d0, cQ47_cJ46d1, cQ47_cJ46d2])
private abbrev cQ48_cJ47v : LeanSuffixReflective.QInterval := ⟨(63219902962043730536290024107 / 316912650057057350374175801344 : ℚ), (252879611848174922145160096435 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d0 : LeanSuffixReflective.QInterval := ⟨(150526162937914954573207065075 / 1267650600228229401496703205376 : ℚ), (150526162937914954573207065085 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d2 : LeanSuffixReflective.QInterval := ⟨(-322957228167964416507114065 / 1267650600228229401496703205376 : ℚ), (-80739307041991104126778515 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ47 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ45).mul (cJ46)).widenAll cQ48_cJ47v cQ48_cJ47d0 cQ48_cJ47d1 cQ48_cJ47d2 (by
    norm_num [cJ45, cJ46, cQ48_cJ47v, cQ48_cJ47d0, cQ48_cJ47d1, cQ48_cJ47d2])
private abbrev cQ49_cJ48v : LeanSuffixReflective.QInterval := ⟨(370558295653566091632414535735 / 1267650600228229401496703205376 : ℚ), (185279147826783045816207267869 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d0 : LeanSuffixReflective.QInterval := ⟨(45014472169264836283305937791 / 633825300114114700748351602688 : ℚ), (90028944338529672566611875585 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d2 : LeanSuffixReflective.QInterval := ⟨(-9847094550776304015341237 / 79228162514264337593543950336 : ℚ), (-78776756406210432122729895 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ48 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ43).invPos (by norm_num [cJ43])).widenAll cQ49_cJ48v cQ49_cJ48d0 cQ49_cJ48d1 cQ49_cJ48d2 (by
    norm_num [cJ43, NearOneScalarInterval.Jet3.invPos, cQ49_cJ48v, cQ49_cJ48d0, cQ49_cJ48d1, cQ49_cJ48d2])
private abbrev cQ50_cJ49v : LeanSuffixReflective.QInterval := ⟨(369892081009943934122866086955 / 633825300114114700748351602688 : ℚ), (23118255063121495882679130435 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d0 : LeanSuffixReflective.QInterval := ⟨(37138620452465620114089130015 / 633825300114114700748351602688 : ℚ), (18569310226232810057044565011 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d2 : LeanSuffixReflective.QInterval := ⟨(-315688186311473559160544931 / 1267650600228229401496703205376 : ℚ), (-78922046577868389790136231 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ49 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ45).mul (cJ48)).widenAll cQ50_cJ49v cQ50_cJ49d0 cQ50_cJ49d1 cQ50_cJ49d2 (by
    norm_num [cJ45, cJ48, cQ50_cJ49v, cQ50_cJ49d0, cQ50_cJ49d1, cQ50_cJ49d2])
private abbrev cQ51_cJ50v : LeanSuffixReflective.QInterval := ⟨(185280592719765880356658252783 / 633825300114114700748351602688 : ℚ), (185280592719765880356658252785 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d0 : LeanSuffixReflective.QInterval := ⟨(90377611824162811602356629647 / 1267650600228229401496703205376 : ℚ), (90377611824162811602356629655 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d2 : LeanSuffixReflective.QInterval := ⟨(-19694343990276552498634493 / 158456325028528675187087900672 : ℚ), (-78777375961106209994537971 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ50 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ44).invPos (by norm_num [cJ44])).widenAll cQ51_cJ50v cQ51_cJ50d0 cQ51_cJ50d1 cQ51_cJ50d2 (by
    norm_num [cJ44, NearOneScalarInterval.Jet3.invPos, cQ51_cJ50v, cQ51_cJ50d0, cQ51_cJ50d1, cQ51_cJ50d2])
private abbrev cQ52_cJ51v : LeanSuffixReflective.QInterval := ⟨(370229363158004248551039306999 / 633825300114114700748351602688 : ℚ), (740458726316008497102078614009 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d0 : LeanSuffixReflective.QInterval := ⟨(32040628544659239249798865303 / 316912650057057350374175801344 : ℚ), (8010157136164809812449716327 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d2 : LeanSuffixReflective.QInterval := ⟨(-315401700163173171091191689 / 1267650600228229401496703205376 : ℚ), (-315401700163173171091191683 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ51 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ35).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).mul (cJ50)).widenAll cQ52_cJ51v cQ52_cJ51d0 cQ52_cJ51d1 cQ52_cJ51d2 (by
    norm_num [cJ35, cJ0, cJ50, cQ52_cJ51v, cQ52_cJ51d0, cQ52_cJ51d1, cQ52_cJ51d2])
private abbrev cQ53_cJ52v : LeanSuffixReflective.QInterval := ⟨(634398299619326071964320003995 / 633825300114114700748351602688 : ℚ), (634398299619326071964320003997 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d0 : LeanSuffixReflective.QInterval := ⟨(91026428524476009784673767553 / 1267650600228229401496703205376 : ℚ), (45513214262238004892336883779 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d2 : LeanSuffixReflective.QInterval := ⟨(984188504904180628787783 / 1267650600228229401496703205376 : ℚ), (984188504904180628787785 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ52 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ35).invPos (by norm_num [cJ35])).widenAll cQ53_cJ52v cQ53_cJ52d0 cQ53_cJ52d1 cQ53_cJ52d2 (by
    norm_num [cJ35, NearOneScalarInterval.Jet3.invPos, cQ53_cJ52v, cQ53_cJ52d0, cQ53_cJ52d1, cQ53_cJ52d2])
private abbrev cQ54_cJ53v : LeanSuffixReflective.QInterval := ⟨(54376200600256640428721781133 / 1267650600228229401496703205376 : ℚ), (27188100300128320214360890567 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d0 : LeanSuffixReflective.QInterval := ⟨(1089667810188406363915999432463 / 633825300114114700748351602688 : ℚ), (1089667810188406363915999432469 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d2 : LeanSuffixReflective.QInterval := ⟨(22965448167004059559160715 / 1267650600228229401496703205376 : ℚ), (22965448167004059559160717 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ53 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ0).mul (cJ39)).mul (cJ52)).widenAll cQ54_cJ53v cQ54_cJ53d0 cQ54_cJ53d1 cQ54_cJ53d2 (by
    norm_num [cJ0, cJ39, cJ52, cQ54_cJ53v, cQ54_cJ53d0, cQ54_cJ53d1, cQ54_cJ53d2])
private abbrev cQ55_cJ54v : LeanSuffixReflective.QInterval := ⟨(28807979317675529331094951 / 79228162514264337593543950336 : ℚ), (230463834541404234648759609 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d0 : LeanSuffixReflective.QInterval := ⟨(18514139946175938689652934185 / 633825300114114700748351602688 : ℚ), (37028279892351877379305868373 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d2 : LeanSuffixReflective.QInterval := ⟨(-196334198401928193945025 / 1267650600228229401496703205376 : ℚ), (-3067721850030128030391 / 19807040628566084398385987584 : ℚ), by norm_num⟩
@[simp] private abbrev cJ54 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ33).mul (cJ51)).widenAll cQ55_cJ54v cQ55_cJ54d0 cQ55_cJ54d1 cQ55_cJ54d2 (by
    norm_num [cJ33, cJ51, cQ55_cJ54v, cQ55_cJ54d0, cQ55_cJ54d1, cQ55_cJ54d2])
private abbrev cQ56_cJ55v : LeanSuffixReflective.QInterval := ⟨(316718276623821422309372494221 / 316912650057057350374175801344 : ℚ), (633451131255135539223605236477 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d0 : LeanSuffixReflective.QInterval := ⟨(-62723108797483166542388174999 / 1267650600228229401496703205376 : ℚ), (-59584032743639694158785000645 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d2 : LeanSuffixReflective.QInterval := ⟨(-165241219674197773460917 / 316912650057057350374175801344 : ℚ), (-627885857855402141854423 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ55 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ53).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ53]) (by norm_num [cJ53])).widenAll cQ56_cJ55v cQ56_cJ55d0 cQ56_cJ55d1 cQ56_cJ55d2 (by
    norm_num [cJ53, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ56_cJ55v, cQ56_cJ55d0, cQ56_cJ55d1, cQ56_cJ55d2])
private abbrev cQ57_cJ56v : LeanSuffixReflective.QInterval := ⟨(633825272181297344522531262759 / 633825300114114700748351602688 : ℚ), (633825273228777995380999525507 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d0 : LeanSuffixReflective.QInterval := ⟨(-8976337597345253840595689 / 1267650600228229401496703205376 : ℚ), (-8638764189135418121164253 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d2 : LeanSuffixReflective.QInterval := ⟨(11451280259223631267 / 316912650057057350374175801344 : ℚ), (23797514384726835729 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ56 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ54).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ54]) (by norm_num [cJ54])).widenAll cQ57_cJ56v cQ57_cJ56d0 cQ57_cJ56d1 cQ57_cJ56d2 (by
    norm_num [cJ54, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ57_cJ56v, cQ57_cJ56d0, cQ57_cJ56d1, cQ57_cJ56d2])
private abbrev cQ58_cJ57v : LeanSuffixReflective.QInterval := ⟨(634398299619326071964320003995 / 633825300114114700748351602688 : ℚ), (634398299619326071964320003997 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d0 : LeanSuffixReflective.QInterval := ⟨(91026428524476009784673767553 / 1267650600228229401496703205376 : ℚ), (45513214262238004892336883779 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d2 : LeanSuffixReflective.QInterval := ⟨(984188504904180628787783 / 1267650600228229401496703205376 : ℚ), (984188504904180628787785 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ57 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ35).invPos (by norm_num [cJ35])).widenAll cQ58_cJ57v cQ58_cJ57d0 cQ58_cJ57d1 cQ58_cJ57d2 (by
    norm_num [cJ35, NearOneScalarInterval.Jet3.invPos, cQ58_cJ57v, cQ58_cJ57d0, cQ58_cJ57d1, cQ58_cJ57d2])
private abbrev cQ59_cJ58v : LeanSuffixReflective.QInterval := ⟨(370907266731203865874856896197 / 633825300114114700748351602688 : ℚ), (741814565889622141970039572215 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d0 : LeanSuffixReflective.QInterval := ⟨(118386743576921446908608482619 / 633825300114114700748351602688 : ℚ), (118389772661568578505390985133 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d2 : LeanSuffixReflective.QInterval := ⟨(-157414868480744208419580779 / 633825300114114700748351602688 : ℚ), (-314829686814111442734232749 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ58 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ33).mul (cJ39)).mul (cJ57)).mul (cJ55)).add ((cJ51).mul (cJ56))).widenAll cQ59_cJ58v cQ59_cJ58d0 cQ59_cJ58d1 cQ59_cJ58d2 (by
    norm_num [cJ33, cJ39, cJ57, cJ55, cJ51, cJ56, cQ59_cJ58v, cQ59_cJ58d0, cQ59_cJ58d1, cQ59_cJ58d2])
private abbrev cQ60_cJ59v : LeanSuffixReflective.QInterval := ⟨(633539059133035648716920414351 / 633825300114114700748351602688 : ℚ), (39596191195814728044807525897 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d0 : LeanSuffixReflective.QInterval := ⟨(-11357758687251546536658016327 / 316912650057057350374175801344 : ℚ), (-45431034749006186146632065305 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d2 : LeanSuffixReflective.QInterval := ⟨(-245602858920536025644847 / 633825300114114700748351602688 : ℚ), (-491205717841072051289693 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ59 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ5).mul (cJ4)).neg)).widenAll cQ60_cJ59v cQ60_cJ59d0 cQ60_cJ59d1 cQ60_cJ59d2 (by
    norm_num [cJ5, cJ4, cQ60_cJ59v, cQ60_cJ59d0, cQ60_cJ59d1, cQ60_cJ59d2])
private abbrev cQ61_cJ60v : LeanSuffixReflective.QInterval := ⟨(1475360397556398295667 / 158456325028528675187087900672 : ℚ), (2952861473069558624319 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d0 : LeanSuffixReflective.QInterval := ⟨(-29483334662459185000717 / 1267650600228229401496703205376 : ℚ), (-6844259912825513820925 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d1 : LeanSuffixReflective.QInterval := ⟨(-5033714636548185693995881837 / 1267650600228229401496703205376 : ℚ), (-5033714636525982927470340655 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ60 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul (cJ20)).add ((((NearOneScalarInterval.Jet3.pi).mul (NearOneScalarInterval.Jet3.rational (1 / 2 : ℚ))).add ((cJ5).mul (cJ31))).neg)).widenAll cQ61_cJ60v cQ61_cJ60d0 cQ61_cJ60d1 cQ61_cJ60d2 (by
    norm_num [cJ8, cJ20, cJ5, cJ31, cQ61_cJ60v, cQ61_cJ60d0, cQ61_cJ60d1, cQ61_cJ60d2])
private abbrev cQ62_cJ61v : LeanSuffixReflective.QInterval := ⟨(-25733512517058647279013 / 1267650600228229401496703205376 : ℚ), (4270702518550705691405 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d0 : LeanSuffixReflective.QInterval := ⟨(-2546490540857792987807513 / 633825300114114700748351602688 : ℚ), (5523479493933183533507249 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d1 : LeanSuffixReflective.QInterval := ⟨(1037601181932985651 / 158456325028528675187087900672 : ℚ), (19899232021374457233 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d2 : LeanSuffixReflective.QInterval := ⟨(1849380757407576343043441567 / 633825300114114700748351602688 : ℚ), (3698761564961524936762252659 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ61 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.pi).mul ((cJ4).add ((cJ3).neg))).mul ((cJ8).add (cJ59))).add (((cJ8).mul (cJ8)).mul ((cJ58).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ59)).add (NearOneScalarInterval.Jet3.rational (1 : ℚ))).mul (cJ49))))).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul ((cJ59).mul (cJ59))).mul ((cJ31).add ((cJ8).mul (cJ22)))).neg)).widenAll cQ62_cJ61v cQ62_cJ61d0 cQ62_cJ61d1 cQ62_cJ61d2 (by
    norm_num [cJ4, cJ3, cJ8, cJ59, cJ58, cJ49, cJ31, cJ22, cQ62_cJ61v, cQ62_cJ61d0, cQ62_cJ61d1, cQ62_cJ61d2])
private abbrev cQ63_cJ62v : LeanSuffixReflective.QInterval := ⟨(-257525678520664680932078155 / 1267650600228229401496703205376 : ℚ), (-128762839260332340466039055 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d0 : LeanSuffixReflective.QInterval := ⟨(-20765697816127043017334051463 / 1267650600228229401496703205376 : ℚ), (-20765697816127043017334051397 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d1 : LeanSuffixReflective.QInterval := ⟨(1852858315582363779813292139 / 1267650600228229401496703205376 : ℚ), (926429157791181889906646081 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d2 : LeanSuffixReflective.QInterval := ⟨(-925314082959459279843626969 / 1267650600228229401496703205376 : ℚ), (-462657041479729639921813479 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ62 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ3).add ((cJ4).neg)).mul (cJ20)).add ((cJ59).mul (cJ22))).add (((cJ8).mul (cJ49)).neg)).widenAll cQ63_cJ62v cQ63_cJ62d0 cQ63_cJ62d1 cQ63_cJ62d2 (by
    norm_num [cJ3, cJ4, cJ20, cJ59, cJ22, cJ8, cJ49, cQ63_cJ62v, cQ63_cJ62d0, cQ63_cJ62d1, cQ63_cJ62d2])
private abbrev cQ64_cJ63v : LeanSuffixReflective.QInterval := ⟨(233252610735802189555727588453 / 633825300114114700748351602688 : ℚ), (116626305367901094777863794227 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d0 : LeanSuffixReflective.QInterval := ⟨(-98541246867008277942679117997 / 1267650600228229401496703205376 : ℚ), (-98541246867008277942679117995 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d1 : LeanSuffixReflective.QInterval := ⟨(-197274748614840033816502625 / 316912650057057350374175801344 : ℚ), (-789098994459360135266010499 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d2 : LeanSuffixReflective.QInterval := ⟨(789098994459360135266010499 / 1267650600228229401496703205376 : ℚ), (197274748614840033816502625 / 316912650057057350374175801344 : ℚ), by norm_num⟩
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

theorem foldLoRange_lo : foldLoRange.lo = (74248500750550030026863861989135 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [foldLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldLoRange_hi : foldLoRange.hi = (249839535922305671879775342569497 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [foldLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldHiRange_lo : foldHiRange.lo = (-243729752577001713033808546981913 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [foldHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldHiRange_hi : foldHiRange.hi = (-68138717405246071180897066401551 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [foldHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaLoRange_lo : areaLoRange.lo = (-1772202052515927927425919475626985 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [areaLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaLoRange_hi : areaLoRange.hi = (-92598502419055336666323670733095 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [areaLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaHiRange_lo : areaHiRange.lo = (96961815102057568176121951203623 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [areaHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaHiRange_hi : areaHiRange.hi = (1776565365198930158935717756097513 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [areaHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem hFourRange_lo : hFourRange.lo = (655816197314378057619691148519136259087 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [hFourRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem hFourRange_hi : hFourRange.hi = (655819125120551719706523744846163956721 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [hFourRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem shapeRange_lo : shapeRange.lo = (163841291721888937625413396311774275293 / 163990907831534728405692930813922902016 : ℚ) := by norm_num [shapeRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem shapeRange_hi : shapeRange.hi = (163844285098475492447068788410291515683 / 163990907831534728405692930813922902016 : ℚ) := by norm_num [shapeRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem bSubARange_lo : bSubARange.lo = (241392975476007625293647104887649784815 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [bSubARange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem bSubARange_hi : bSubARange.hi = (241406400083825299936773504704620555281 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [bSubARange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem gapRange_lo : gapRange.lo = (-135147823895900932116376670908726839 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [gapRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem gapRange_hi : gapRange.hi = (-131372744487420375436376245909234121 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [gapRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]

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
end Band10Cell34
end
end NearOneScalarStress

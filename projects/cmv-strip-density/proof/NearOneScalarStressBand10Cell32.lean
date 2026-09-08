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
namespace Band10Cell32
def wholeBox : Box3 := { t := ⟨(1536 / 63167 : ℚ), (1552 / 63167 : ℚ), by norm_num⟩, e4 := ⟨(-1 / 8192 : ℚ), (1 / 8192 : ℚ), by norm_num⟩, e3 := ⟨(-1 / 2048 : ℚ), (1 / 2048 : ℚ), by norm_num⟩ }
def centerBox : Box3 := { t := ⟨(1544 / 63167 : ℚ), (1544 / 63167 : ℚ), by norm_num⟩, e4 := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩, e3 := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩ }
def aAt (t e4 : ℝ) : ℝ := ((122978918310508179754384166075116259 / 332306998946228968225951765070086144 : ℚ) : ℝ) + ((-671056157848295150335756664018267327 / 1329227995784915872903807060280344576 : ℚ) : ℝ) * t + t ^ 2 * e4
def bAt (t e3 : ℝ) : ℝ := ((983663793766682566408702377040566921 / 1329227995784915872903807060280344576 : ℚ) : ℝ) + ((-193635873602967623729946409064003075 / 332306998946228968225951765070086144 : ℚ) : ℝ) * t + t ^ 2 * e3

def tCenter : ℚ := (1544 / 63167 : ℚ)
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
private abbrev wQ4_wJ3v : LeanSuffixReflective.QInterval := ⟨(453403344741988102636336788125 / 1267650600228229401496703205376 : ℚ), (113391408421561217523201746759 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d0 : LeanSuffixReflective.QInterval := ⟨(-639976626588244735211015853965 / 1267650600228229401496703205376 : ℚ), (-639961418624110211565863769483 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d1 : LeanSuffixReflective.QInterval := ⟨(749551530102549718530397873 / 1267650600228229401496703205376 : ℚ), (191312129631480314172431467 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ3 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (122978918310508179754384166075116259 / 332306998946228968225951765070086144 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-671056157848295150335756664018267327 / 1329227995784915872903807060280344576 : ℚ)).mul (wJ0))).add (((wJ0).mul (wJ0)).mul (wJ1))).widenAll wQ4_wJ3v wQ4_wJ3d0 wQ4_wJ3d1 wQ4_wJ3d2 (by
    norm_num [wJ0, wJ1, wQ4_wJ3v, wQ4_wJ3d0, wQ4_wJ3d1, wQ4_wJ3d2])
private abbrev wQ5_wJ4v : LeanSuffixReflective.QInterval := ⟨(459972872750939894887821687423 / 633825300114114700748351602688 : ℚ), (460066796804018527249439308627 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d0 : LeanSuffixReflective.QInterval := ⟨(-369346326744208879209167299523 / 633825300114114700748351602688 : ℚ), (-369315910815939831918863130561 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d2 : LeanSuffixReflective.QInterval := ⟨(749551530102549718530397873 / 1267650600228229401496703205376 : ℚ), (191312129631480314172431467 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ4 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (983663793766682566408702377040566921 / 1329227995784915872903807060280344576 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-193635873602967623729946409064003075 / 332306998946228968225951765070086144 : ℚ)).mul (wJ0))).add (((wJ0).mul (wJ0)).mul (wJ2))).widenAll wQ5_wJ4v wQ5_wJ4d0 wQ5_wJ4d1 wQ5_wJ4d2 (by
    norm_num [wJ0, wJ2, wQ5_wJ4v, wQ5_wJ4d0, wQ5_wJ4d1, wQ5_wJ4d2])
private abbrev wQ6_wJ5v : LeanSuffixReflective.QInterval := ⟨(749551530102549718530397873 / 1267650600228229401496703205376 : ℚ), (191312129631480314172431467 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d0 : LeanSuffixReflective.QInterval := ⟨(61649637372379893320845888627 / 1267650600228229401496703205376 : ℚ), (62291821095008850542938033301 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ5 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ6_wJ5v wQ6_wJ5d0 wQ6_wJ5d1 wQ6_wJ5d2 (by
    norm_num [wJ0, wQ6_wJ5v, wQ6_wJ5d0, wQ6_wJ5d1, wQ6_wJ5d2])
private abbrev wQ7_wJ6v : LeanSuffixReflective.QInterval := ⟨(749551530102549718530397873 / 1267650600228229401496703205376 : ℚ), (191312129631480314172431467 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d0 : LeanSuffixReflective.QInterval := ⟨(61649637372379893320845888627 / 1267650600228229401496703205376 : ℚ), (62291821095008850542938033301 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ6 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ7_wJ6v wQ7_wJ6d0 wQ7_wJ6d1 wQ7_wJ6d2 (by
    norm_num [wJ0, wQ7_wJ6v, wQ7_wJ6d0, wQ7_wJ6d1, wQ7_wJ6d2])
private abbrev wQ8_wJ7v : LeanSuffixReflective.QInterval := ⟨(162169759542740092006664242709 / 1267650600228229401496703205376 : ℚ), (162285872798203589888350503657 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d0 : LeanSuffixReflective.QInterval := ⟨(-457967525326965811486595457237 / 1267650600228229401496703205376 : ℚ), (-114448195606012540578135793419 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d1 : LeanSuffixReflective.QInterval := ⟨(268093724519819698475837609 / 633825300114114700748351602688 : ℚ), (273806070198033256447560075 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ7 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ3).mul (wJ3)).widenAll wQ8_wJ7v wQ8_wJ7d0 wQ8_wJ7d1 wQ8_wJ7d2 (by
    norm_num [wJ3, wQ8_wJ7v, wQ8_wJ7d0, wQ8_wJ7d1, wQ8_wJ7d2])
private abbrev wQ9_wJ8v : LeanSuffixReflective.QInterval := ⟨(1267376794158031368240255645301 / 1267650600228229401496703205376 : ℚ), (1267382506503709581798227367767 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d0 : LeanSuffixReflective.QInterval := ⟨(-21909621817629530621863842741 / 1267650600228229401496703205376 : ℚ), (-2708002762791604064855243001 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d1 : LeanSuffixReflective.QInterval := ⟨(-230980561599814703731067 / 633825300114114700748351602688 : ℚ), (-443203747292764560578325 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ8 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ6).mul (wJ3)).neg)).widenAll wQ9_wJ8v wQ9_wJ8d0 wQ9_wJ8d1 wQ9_wJ8d2 (by
    norm_num [wJ6, wJ3, wQ9_wJ8v, wQ9_wJ8d0, wQ9_wJ8d1, wQ9_wJ8d2])
private abbrev wQ10_wJ9v : LeanSuffixReflective.QInterval := ⟨(906708721618292907167471281781 / 1267650600228229401496703205376 : ℚ), (907035377707482885332473090925 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d0 : LeanSuffixReflective.QInterval := ⟨(-643828612013999646813340751025 / 633825300114114700748351602688 : ℚ), (-1287533173958154236845327979955 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d1 : LeanSuffixReflective.QInterval := ⟨(1498772480643910059860421467 / 1267650600228229401496703205376 : ℚ), (765089996878561532325926573 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ9 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ3)).add (((wJ6).mul (wJ7)).neg)).widenAll wQ10_wJ9v wQ10_wJ9d0 wQ10_wJ9d1 wQ10_wJ9d2 (by
    norm_num [wJ3, wJ6, wJ7, wQ10_wJ9v, wQ10_wJ9d0, wQ10_wJ9d1, wQ10_wJ9d2])
private abbrev wQ11_wJ10v : LeanSuffixReflective.QInterval := ⟨(484179401097210046626438874367 / 633825300114114700748351602688 : ℚ), (969327660763614935504818586359 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d0 : LeanSuffixReflective.QInterval := ⟨(311929220572678185973841416691 / 316912650057057350374175801344 : ℚ), (1247843234483534336742875236379 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d1 : LeanSuffixReflective.QInterval := ⟨(1498772480643910059860421467 / 1267650600228229401496703205376 : ℚ), (765089996878561532325926573 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ10 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ3)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ0))).add (((wJ6).mul (wJ7)).neg)).add (((wJ0).mul (wJ0)).mul ((wJ0).mul (wJ0)))).widenAll wQ11_wJ10v wQ11_wJ10d0 wQ11_wJ10d1 wQ11_wJ10d2 (by
    norm_num [wJ3, wJ0, wJ6, wJ7, wQ11_wJ10v, wQ11_wJ10d0, wQ11_wJ10d1, wQ11_wJ10d2])
private abbrev wQ11_root11 : LeanSuffixReflective.QInterval := ⟨(1072096010248895368779249647355 / 1267650600228229401496703205376 : ℚ), (1072289112590037186316134012743 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11v : LeanSuffixReflective.QInterval := ⟨(1072096010248895368779249647355 / 1267650600228229401496703205376 : ℚ), (1072289112590037186316134012743 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d0 : LeanSuffixReflective.QInterval := ⟨(-761265519749652847968448990005 / 1267650600228229401496703205376 : ℚ), (-761055102405865842839479323917 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d1 : LeanSuffixReflective.QInterval := ⟨(885917712110629046302590435 / 1267650600228229401496703205376 : ℚ), (14135085391433375143654071 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ11 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ9).sqrt wQ11_root11 (by norm_num [wQ11_root11]) (by norm_num [wJ9, wQ11_root11]) (by norm_num [wJ9, wQ11_root11])).widenAll wQ12_wJ11v wQ12_wJ11d0 wQ12_wJ11d1 wQ12_wJ11d2 (by
    norm_num [wJ9, wQ11_root11, NearOneScalarInterval.Jet3.sqrt, wQ12_wJ11v, wQ12_wJ11d0, wQ12_wJ11d1, wQ12_wJ11d2])
private abbrev wQ12_root12 : LeanSuffixReflective.QInterval := ⟨(276986080069699294280108258099 / 316912650057057350374175801344 : ℚ), (1108498439775547001663594867537 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12v : LeanSuffixReflective.QInterval := ⟨(276986080069699294280108258099 / 316912650057057350374175801344 : ℚ), (1108498439775547001663594867537 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d0 : LeanSuffixReflective.QInterval := ⟨(356714316862498122547287755879 / 633825300114114700748351602688 : ℚ), (356928862811838881289992806049 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d1 : LeanSuffixReflective.QInterval := ⟨(856979029703689950804992013 / 1267650600228229401496703205376 : ℚ), (875375031055414949091149049 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ12 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ10).sqrt wQ12_root12 (by norm_num [wQ12_root12]) (by norm_num [wJ10, wQ12_root12]) (by norm_num [wJ10, wQ12_root12])).widenAll wQ13_wJ12v wQ13_wJ12d0 wQ13_wJ12d1 wQ13_wJ12d2 (by
    norm_num [wJ10, wQ12_root12, NearOneScalarInterval.Jet3.sqrt, wQ13_wJ12v, wQ13_wJ12d0, wQ13_wJ12d1, wQ13_wJ12d2])
private abbrev wQ14_wJ13v : LeanSuffixReflective.QInterval := ⟨(1267668826693792710128863394891 / 1267650600228229401496703205376 : ℚ), (316917350556134211036350601693 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d0 : LeanSuffixReflective.QInterval := ⟨(562163647576912288897798405 / 316912650057057350374175801344 : ℚ), (1147872777788881885034588801 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ13 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0))).widenAll wQ14_wJ13v wQ14_wJ13d0 wQ14_wJ13d1 wQ14_wJ13d2 (by
    norm_num [wJ0, wQ14_wJ13v, wQ14_wJ13d0, wQ14_wJ13d1, wQ14_wJ13d2])
private abbrev wQ15_wJ14v : LeanSuffixReflective.QInterval := ⟨(1090027872640393029591589731295 / 633825300114114700748351602688 : ℚ), (545200864182270732612246734893 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d0 : LeanSuffixReflective.QInterval := ⟨(-22973206090271893720918688011 / 633825300114114700748351602688 : ℚ), (-45266378114679453908057670589 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d1 : LeanSuffixReflective.QInterval := ⟨(1742909479668636900162405767 / 1267650600228229401496703205376 : ℚ), (1780033913953275422811083879 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ14 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ12).add ((wJ13).mul (wJ11))).widenAll wQ15_wJ14v wQ15_wJ14d0 wQ15_wJ14d1 wQ15_wJ14d2 (by
    norm_num [wJ12, wJ13, wJ11, wQ15_wJ14v, wQ15_wJ14d0, wQ15_wJ14d1, wQ15_wJ14d2])
private abbrev wQ16_wJ15v : LeanSuffixReflective.QInterval := ⟨(1611462046605326010607918239603 / 1267650600228229401496703205376 : ℚ), (1613111460497134466972933598393 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d0 : LeanSuffixReflective.QInterval := ⟨(-17649378895922877046529817067 / 158456325028528675187087900672 : ℚ), (-17366603950873447353515909827 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d1 : LeanSuffixReflective.QInterval := ⟨(3866391737552877296456672575 / 1267650600228229401496703205376 : ℚ), (3951447304498474662766338897 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ15 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ11).mul (wJ12)).mul (wJ14)).widenAll wQ16_wJ15v wQ16_wJ15d0 wQ16_wJ15d1 wQ16_wJ15d2 (by
    norm_num [wJ11, wJ12, wJ14, wQ16_wJ15v, wQ16_wJ15d0, wQ16_wJ15d1, wQ16_wJ15d2])
private abbrev wQ17_wJ16v : LeanSuffixReflective.QInterval := ⟨(1090043545220424269862002727579 / 633825300114114700748351602688 : ℚ), (545208950688626130556157376869 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d0 : LeanSuffixReflective.QInterval := ⟨(-42079945763379939153166265165 / 1267650600228229401496703205376 : ℚ), (-41317541742581895851176234429 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d1 : LeanSuffixReflective.QInterval := ⟨(435733634868953793905286191 / 316912650057057350374175801344 : ℚ), (1780060315700784749525349051 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ16 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ13).mul (wJ14)).widenAll wQ17_wJ16v wQ17_wJ16d0 wQ17_wJ16d1 wQ17_wJ16d2 (by
    norm_num [wJ13, wJ14, wQ17_wJ16v, wQ17_wJ16d0, wQ17_wJ16d1, wQ17_wJ16d2])
private abbrev wQ18_wJ17v : LeanSuffixReflective.QInterval := ⟨(136253219671557847227424750471 / 79228162514264337593543950336 : ℚ), (2180839013616954228652031872385 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d0 : LeanSuffixReflective.QInterval := ⟨(-22437597596331700711271588977 / 633825300114114700748351602688 : ℚ), (-42515742313477794097134208219 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d1 : LeanSuffixReflective.QInterval := ⟨(1742841459314318023392598799 / 1267650600228229401496703205376 : ℚ), (890064223602610023519921507 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ17 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ11).add (wJ12)).mul (((wJ8).mul (wJ8)).add ((wJ6).mul ((wJ11).mul (wJ12))))).widenAll wQ18_wJ17v wQ18_wJ17d0 wQ18_wJ17d1 wQ18_wJ17d2 (by
    norm_num [wJ11, wJ12, wJ8, wJ6, wQ18_wJ17v, wQ18_wJ17d0, wQ18_wJ17d1, wQ18_wJ17d2])
private abbrev wQ19_wJ18v : LeanSuffixReflective.QInterval := ⟨(2534224313049864847408440898619 / 1267650600228229401496703205376 : ℚ), (316780966625034267076456808373 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d0 : LeanSuffixReflective.QInterval := ⟨(-42686459610829907618120392169 / 633825300114114700748351602688 : ℚ), (-21085804842056261366474904345 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d1 : LeanSuffixReflective.QInterval := ⟨(-1847467395510393226413805 / 1267650600228229401496703205376 : ℚ), (-1772444812310617747072399 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ18 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul (wJ8)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).widenAll wQ19_wJ18v wQ19_wJ18d0 wQ19_wJ18d1 wQ19_wJ18d2 (by
    norm_num [wJ8, wJ0, wQ19_wJ18v, wQ19_wJ18d0, wQ19_wJ18d1, wQ19_wJ18d2])
private abbrev wQ20_wJ19v : LeanSuffixReflective.QInterval := ⟨(498086488011113117407991041977 / 633825300114114700748351602688 : ℚ), (62324538128439562512105990591 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d0 : LeanSuffixReflective.QInterval := ⟨(42898812549033244086718432253 / 633825300114114700748351602688 : ℚ), (43686614262249622752461544487 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d1 : LeanSuffixReflective.QInterval := ⟨(-2445204377830945749189091121 / 1267650600228229401496703205376 : ℚ), (-2387680614753550715402138517 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ19 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ15).invPos (by norm_num [wJ15])).widenAll wQ20_wJ19v wQ20_wJ19d0 wQ20_wJ19d1 wQ20_wJ19d2 (by
    norm_num [wJ15, NearOneScalarInterval.Jet3.invPos, wQ20_wJ19v, wQ20_wJ19d0, wQ20_wJ19d1, wQ20_wJ19d2])
private abbrev wQ21_wJ20v : LeanSuffixReflective.QInterval := ⟨(1991499688781945895854343013039 / 1267650600228229401496703205376 : ℚ), (1993556513870309013362100645039 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d0 : LeanSuffixReflective.QInterval := ⟨(13045509479798099627098997375 / 158456325028528675187087900672 : ℚ), (108393409385084755652242963419 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d1 : LeanSuffixReflective.QInterval := ⟨(-4889829998075603522979494903 / 1267650600228229401496703205376 : ℚ), (-4774725721930063288756779667 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ20 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ18).mul (wJ19)).widenAll wQ21_wJ20v wQ21_wJ20d0 wQ21_wJ20d1 wQ21_wJ20d2 (by
    norm_num [wJ18, wJ19, wQ21_wJ20v, wQ21_wJ20d0, wQ21_wJ20d1, wQ21_wJ20d2])
private abbrev wQ22_wJ21v : LeanSuffixReflective.QInterval := ⟨(736845039974741464145420221529 / 1267650600228229401496703205376 : ℚ), (92137262044772352198158898847 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d0 : LeanSuffixReflective.QInterval := ⟨(13960072399085581586813284015 / 1267650600228229401496703205376 : ℚ), (3556858812320500099644031137 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d1 : LeanSuffixReflective.QInterval := ⟨(-601847089439194758578535229 / 1267650600228229401496703205376 : ℚ), (-588890125882615336156229085 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ21 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ16).invPos (by norm_num [wJ16])).widenAll wQ22_wJ21v wQ22_wJ21d0 wQ22_wJ21d1 wQ22_wJ21d2 (by
    norm_num [wJ16, NearOneScalarInterval.Jet3.invPos, wQ22_wJ21v, wQ22_wJ21d0, wQ22_wJ21d1, wQ22_wJ21d2])
private abbrev wQ23_wJ22v : LeanSuffixReflective.QInterval := ⟨(1473064119496328757663691798281 / 1267650600228229401496703205376 : ℚ), (1473583635236884026973391870577 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d0 : LeanSuffixReflective.QInterval := ⟨(-339583189220362687722032241 / 19807040628566084398385987584 : ℚ), (-1286436761211026396140743213 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d1 : LeanSuffixReflective.QInterval := ⟨(-150533532904251932188397059 / 158456325028528675187087900672 : ℚ), (-1178310247024199162601206243 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ22 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ18).mul (wJ21)).widenAll wQ23_wJ22v wQ23_wJ22d0 wQ23_wJ22d1 wQ23_wJ22d2 (by
    norm_num [wJ18, wJ21, wQ23_wJ22v, wQ23_wJ22d0, wQ23_wJ22d1, wQ23_wJ22d2])
private abbrev wQ24_wJ23v : LeanSuffixReflective.QInterval := ⟨(368421977556669672796728215025 / 633825300114114700748351602688 : ℚ), (737110124871066742235431594053 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d0 : LeanSuffixReflective.QInterval := ⟨(14364869449435178032361348185 / 1267650600228229401496703205376 : ℚ), (7586508967414896825384027891 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d1 : LeanSuffixReflective.QInterval := ⟨(-601889768719297712518165641 / 1267650600228229401496703205376 : ℚ), (-294428471335625453180591805 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ23 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ17).invPos (by norm_num [wJ17])).widenAll wQ24_wJ23v wQ24_wJ23d0 wQ24_wJ23d1 wQ24_wJ23d2 (by
    norm_num [wJ17, NearOneScalarInterval.Jet3.invPos, wQ24_wJ23v, wQ24_wJ23d0, wQ24_wJ23d1, wQ24_wJ23d2])
private abbrev wQ25_wJ24v : LeanSuffixReflective.QInterval := ⟨(1473380193309115902686532461431 / 1267650600228229401496703205376 : ℚ), (92119962468912609074733053043 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d0 : LeanSuffixReflective.QInterval := ⟨(4550912147738483578416251915 / 1267650600228229401496703205376 : ℚ), (1622160658117086089736861853 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d1 : LeanSuffixReflective.QInterval := ⟨(-1204071121009885018646314835 / 1267650600228229401496703205376 : ℚ), (-1177983213461298166731578681 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ24 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).mul (wJ23)).widenAll wQ25_wJ24v wQ25_wJ24d0 wQ25_wJ24d1 wQ25_wJ24d2 (by
    norm_num [wJ8, wJ0, wJ23, wQ25_wJ24v, wQ25_wJ24d0, wQ25_wJ24d1, wQ25_wJ24d2])
private abbrev wQ26_wJ25v : LeanSuffixReflective.QInterval := ⟨(1267918750663524979956687997569 / 1267650600228229401496703205376 : ℚ), (158490558181490030249175091377 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d0 : LeanSuffixReflective.QInterval := ⟨(21673188400013976725410027735 / 1267650600228229401496703205376 : ℚ), (5479772404588415568852061487 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d1 : LeanSuffixReflective.QInterval := ⟨(443391271911318500623595 / 1267650600228229401496703205376 : ℚ), (462160750372255033978745 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ25 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ8).invPos (by norm_num [wJ8])).widenAll wQ26_wJ25v wQ26_wJ25d0 wQ26_wJ25d1 wQ26_wJ25d2 (by
    norm_num [wJ8, NearOneScalarInterval.Jet3.invPos, wQ26_wJ25v, wQ26_wJ25d0, wQ26_wJ25d1, wQ26_wJ25d2])
private abbrev wQ27_wJ26v : LeanSuffixReflective.QInterval := ⟨(26947020817892221791160564207 / 1267650600228229401496703205376 : ℚ), (6810364803592972214722995475 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d0 : LeanSuffixReflective.QInterval := ⟨(281497764966862036592565725475 / 316912650057057350374175801344 : ℚ), (1126751979404266331460656494257 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d1 : LeanSuffixReflective.QInterval := ⟨(10426278607077626981128513 / 633825300114114700748351602688 : ℚ), (5380589465106207941873463 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ26 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ0).mul (wJ12)).mul (wJ25)).widenAll wQ27_wJ26v wQ27_wJ26d0 wQ27_wJ26d1 wQ27_wJ26d2 (by
    norm_num [wJ0, wJ12, wJ25, wQ27_wJ26v, wQ27_wJ26d0, wQ27_wJ26d1, wQ27_wJ26d2])
private abbrev wQ28_wJ27v : LeanSuffixReflective.QInterval := ⟨(217799442945636077851212125 / 316912650057057350374175801344 : ℚ), (222441940368448194997263923 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d0 : LeanSuffixReflective.QInterval := ⟨(71657573274499549005907957727 / 1267650600228229401496703205376 : ℚ), (72431700777729795341161143643 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d1 : LeanSuffixReflective.QInterval := ⟨(-726867199358220084538839 / 1267650600228229401496703205376 : ℚ), (-696531930743428368950343 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ27 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ6).mul (wJ24)).widenAll wQ28_wJ27v wQ28_wJ27d0 wQ28_wJ27d1 wQ28_wJ27d2 (by
    norm_num [wJ6, wJ24, wQ28_wJ27v, wQ28_wJ27d0, wQ28_wJ27d1, wQ28_wJ27d2])
private abbrev wQ29_wJ28v : LeanSuffixReflective.QInterval := ⟨(1267455463098173038700584730219 / 1267650600228229401496703205376 : ℚ), (1267466818880166276693187183547 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d0 : LeanSuffixReflective.QInterval := ⟨(-16194425657725071993277060685 / 1267650600228229401496703205376 : ℚ), (-239167289648693446452971823 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d1 : LeanSuffixReflective.QInterval := ⟨(-309333580699707497511511 / 1267650600228229401496703205376 : ℚ), (-141719543288196156196861 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ28 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ26).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ26]) (by norm_num [wJ26])).widenAll wQ29_wJ28v wQ29_wJ28d0 wQ29_wJ28d1 wQ29_wJ28d2 (by
    norm_num [wJ26, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ29_wJ28v, wQ29_wJ28d0, wQ29_wJ28d1, wQ29_wJ28d2])
private abbrev wQ30_wJ29v : LeanSuffixReflective.QInterval := ⟨(316912598012835463605327986129 / 316912650057057350374175801344 : ℚ), (1267650408134393497794703464725 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d0 : LeanSuffixReflective.QInterval := ⟨(-8474230152200225975880257 / 316912650057057350374175801344 : ℚ), (-31596553946992309243660625 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d1 : LeanSuffixReflective.QInterval := ⟨(307126339770811827123 / 1267650600228229401496703205376 : ℚ), (170081328239102577529 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ29 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ27).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ27]) (by norm_num [wJ27])).widenAll wQ30_wJ29v wQ30_wJ29d0 wQ30_wJ29d1 wQ30_wJ29d2 (by
    norm_num [wJ27, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ30_wJ29v, wQ30_wJ29d0, wQ30_wJ29d1, wQ30_wJ29d2])
private abbrev wQ31_wJ30v : LeanSuffixReflective.QInterval := ⟨(1267918750663524979956687997569 / 1267650600228229401496703205376 : ℚ), (158490558181490030249175091377 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d0 : LeanSuffixReflective.QInterval := ⟨(21673188400013976725410027735 / 1267650600228229401496703205376 : ℚ), (5479772404588415568852061487 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d1 : LeanSuffixReflective.QInterval := ⟨(443391271911318500623595 / 1267650600228229401496703205376 : ℚ), (462160750372255033978745 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ30 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ8).invPos (by norm_num [wJ8])).widenAll wQ31_wJ30v wQ31_wJ30d0 wQ31_wJ30d1 wQ31_wJ30d2 (by
    norm_num [wJ8, NearOneScalarInterval.Jet3.invPos, wQ31_wJ30v, wQ31_wJ30d0, wQ31_wJ30d1, wQ31_wJ30d2])
private abbrev wQ32_wJ31v : LeanSuffixReflective.QInterval := ⟨(184254388444893937399916784375 / 158456325028528675187087900672 : ℚ), (1474588396080141596987711467309 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d0 : LeanSuffixReflective.QInterval := ⟨(29410880707103726136872180467 / 633825300114114700748351602688 : ℚ), (61361562169029455963597770537 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d1 : LeanSuffixReflective.QInterval := ⟨(-1203563761872437384727280433 / 1267650600228229401496703205376 : ℚ), (-294363511958533643041397841 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ31 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ6).mul (wJ12)).mul (wJ30)).mul (wJ28)).add ((wJ24).mul (wJ29))).widenAll wQ32_wJ31v wQ32_wJ31d0 wQ32_wJ31d1 wQ32_wJ31d2 (by
    norm_num [wJ6, wJ12, wJ30, wJ28, wJ24, wJ29, wQ32_wJ31v, wQ32_wJ31d0, wQ32_wJ31d1, wQ32_wJ31d2])
private abbrev wQ33_wJ32v : LeanSuffixReflective.QInterval := ⟨(459972872750939894887821687423 / 316912650057057350374175801344 : ℚ), (460066796804018527249439308627 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d0 : LeanSuffixReflective.QInterval := ⟨(-369346326744208879209167299523 / 316912650057057350374175801344 : ℚ), (-369315910815939831918863130561 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d2 : LeanSuffixReflective.QInterval := ⟨(749551530102549718530397873 / 633825300114114700748351602688 : ℚ), (191312129631480314172431467 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev wJ32 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ4)).widenAll wQ33_wJ32v wQ33_wJ32d0 wQ33_wJ32d1 wQ33_wJ32d2 (by
    norm_num [wJ4, wQ33_wJ32v, wQ33_wJ32d0, wQ33_wJ32d1, wQ33_wJ32d2])
private abbrev wQ34_wJ33v : LeanSuffixReflective.QInterval := ⟨(749551530102549718530397873 / 1267650600228229401496703205376 : ℚ), (191312129631480314172431467 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d0 : LeanSuffixReflective.QInterval := ⟨(61649637372379893320845888627 / 1267650600228229401496703205376 : ℚ), (62291821095008850542938033301 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ33 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ34_wJ33v wQ34_wJ33d0 wQ34_wJ33d1 wQ34_wJ33d2 (by
    norm_num [wJ0, wQ34_wJ33v, wQ34_wJ33d0, wQ34_wJ33d1, wQ34_wJ33d2])
private abbrev wQ35_wJ34v : LeanSuffixReflective.QInterval := ⟨(2670452487506069689000598219117 / 1267650600228229401496703205376 : ℚ), (1335771591846537386823107536499 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d0 : LeanSuffixReflective.QInterval := ⟨(-1072371086644507588292710825431 / 316912650057057350374175801344 : ℚ), (-4288255465221806634573832806795 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d2 : LeanSuffixReflective.QInterval := ⟨(271978233208787158226455355 / 79228162514264337593543950336 : ℚ), (1110922629986070043656654819 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ34 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ32).mul (wJ32)).widenAll wQ35_wJ34v wQ35_wJ34d0 wQ35_wJ34d1 wQ35_wJ34d2 (by
    norm_num [wJ32, wQ35_wJ34v, wQ35_wJ34d0, wQ35_wJ34d1, wQ35_wJ34d2])
private abbrev wQ36_wJ35v : LeanSuffixReflective.QInterval := ⟨(1266539677598243331453046550557 / 1267650600228229401496703205376 : ℚ), (316640671823848563215949345989 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d0 : LeanSuffixReflective.QInterval := ⟨(-11194558377172918353226462361 / 158456325028528675187087900672 : ℚ), (-11073445266309469245171127605 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d2 : LeanSuffixReflective.QInterval := ⟨(-923922246399258814924267 / 1267650600228229401496703205376 : ℚ), (-886407494585529121156651 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ35 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ33).mul (wJ32)).neg)).widenAll wQ36_wJ35v wQ36_wJ35d0 wQ36_wJ35d1 wQ36_wJ35d2 (by
    norm_num [wJ33, wJ32, wQ36_wJ35v, wQ36_wJ35d0, wQ36_wJ35d1, wQ36_wJ35d2])
private abbrev wQ37_wJ36v : LeanSuffixReflective.QInterval := ⟨(3678170239140414395971047125049 / 1267650600228229401496703205376 : ℚ), (3678955357510832552240522888875 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d0 : LeanSuffixReflective.QInterval := ⟨(-3083513519586649740231178988869 / 1267650600228229401496703205376 : ℚ), (-3081809919379513075442313522791 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d2 : LeanSuffixReflective.QInterval := ⟨(1497761788569775474013071817 / 633825300114114700748351602688 : ℚ), (1529210488844823759162828453 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ36 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ32)).add (((wJ33).mul (wJ34)).neg)).widenAll wQ37_wJ36v wQ37_wJ36d0 wQ37_wJ36d1 wQ37_wJ36d2 (by
    norm_num [wJ32, wJ33, wJ34, wQ37_wJ36v, wQ37_wJ36d0, wQ37_wJ36d1, wQ37_wJ36d2])
private abbrev wQ38_wJ37v : LeanSuffixReflective.QInterval := ⟨(1869910159858270791028226796001 / 633825300114114700748351602688 : ℚ), (935311910141741150603217096077 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d0 : LeanSuffixReflective.QInterval := ⟨(-548139413267937702709131820055 / 1267650600228229401496703205376 : ℚ), (-546433510937824501854110306457 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d2 : LeanSuffixReflective.QInterval := ⟨(1497761788569775474013071817 / 633825300114114700748351602688 : ℚ), (1529210488844823759162828453 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ37 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ32)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ0))).add (((wJ33).mul (wJ34)).neg)).add (((wJ0).mul (wJ0)).mul ((wJ0).mul (wJ0)))).widenAll wQ38_wJ37v wQ38_wJ37d0 wQ38_wJ37d1 wQ38_wJ37d2 (by
    norm_num [wJ32, wJ0, wJ33, wJ34, wQ38_wJ37v, wQ38_wJ37d0, wQ38_wJ37d1, wQ38_wJ37d2])
private abbrev wQ38_root38 : LeanSuffixReflective.QInterval := ⟨(2159313481500070750110152069153 / 1267650600228229401496703205376 : ℚ), (134971495358184726365179182831 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38v : LeanSuffixReflective.QInterval := ⟨(2159313481500070750110152069153 / 1267650600228229401496703205376 : ℚ), (134971495358184726365179182831 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d0 : LeanSuffixReflective.QInterval := ⟨(-113138324906408125770926862737 / 158456325028528675187087900672 : ℚ), (-904510009623545318283797167643 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d2 : LeanSuffixReflective.QInterval := ⟨(439592500911213713415399029 / 633825300114114700748351602688 : ℚ), (897741162025612733869484105 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ38 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ36).sqrt wQ38_root38 (by norm_num [wQ38_root38]) (by norm_num [wJ36, wQ38_root38]) (by norm_num [wJ36, wQ38_root38])).widenAll wQ39_wJ38v wQ39_wJ38d0 wQ39_wJ38d1 wQ39_wJ38d2 (by
    norm_num [wJ36, wQ38_root38, NearOneScalarInterval.Jet3.sqrt, wQ39_wJ38v, wQ39_wJ38d0, wQ39_wJ38d1, wQ39_wJ38d2])
private abbrev wQ39_root39 : LeanSuffixReflective.QInterval := ⟨(136083405505743556196378081269 / 79228162514264337593543950336 : ℚ), (1088874971836431701933035043317 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39v : LeanSuffixReflective.QInterval := ⟨(136083405505743556196378081269 / 79228162514264337593543950336 : ℚ), (1088874971836431701933035043317 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d0 : LeanSuffixReflective.QInterval := ⟨(-79782098253399342894463584471 / 633825300114114700748351602688 : ℚ), (-19879657503196502247149485287 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d2 : LeanSuffixReflective.QInterval := ⟨(871835003736586680220190383 / 1267650600228229401496703205376 : ℚ), (890310884552354608303882071 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ39 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ37).sqrt wQ39_root39 (by norm_num [wQ39_root39]) (by norm_num [wJ37, wQ39_root39]) (by norm_num [wJ37, wQ39_root39])).widenAll wQ40_wJ39v wQ40_wJ39d0 wQ40_wJ39d1 wQ40_wJ39d2 (by
    norm_num [wJ37, wQ39_root39, NearOneScalarInterval.Jet3.sqrt, wQ40_wJ39v, wQ40_wJ39d0, wQ40_wJ39d1, wQ40_wJ39d2])
private abbrev wQ41_wJ40v : LeanSuffixReflective.QInterval := ⟨(1267668826693792710128863394891 / 1267650600228229401496703205376 : ℚ), (316917350556134211036350601693 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d0 : LeanSuffixReflective.QInterval := ⟨(562163647576912288897798405 / 316912650057057350374175801344 : ℚ), (1147872777788881885034588801 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ40 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0))).widenAll wQ41_wJ40v wQ41_wJ40d0 wQ41_wJ40d1 wQ41_wJ40d2 (by
    norm_num [wJ0, wQ41_wJ40v, wQ41_wJ40d0, wQ41_wJ40d1, wQ41_wJ40d2])
private abbrev wQ42_wJ41v : LeanSuffixReflective.QInterval := ⟨(4336679016516730563646464516453 / 1267650600228229401496703205376 : ℚ), (4337325900104479005108265120481 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d0 : LeanSuffixReflective.QInterval := ⟨(-265213466684926167447709447687 / 316912650057057350374175801344 : ℚ), (-1059649289126613664929953045979 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d2 : LeanSuffixReflective.QInterval := ⟨(437758161652359920206478687 / 316912650057057350374175801344 : ℚ), (1788065362018365828844872035 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ41 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ39).add ((wJ40).mul (wJ38))).widenAll wQ42_wJ41v wQ42_wJ41d0 wQ42_wJ41d1 wQ42_wJ41d2 (by
    norm_num [wJ39, wJ40, wJ38, wQ42_wJ41v, wQ42_wJ41d0, wQ42_wJ41d1, wQ42_wJ41d2])
private abbrev wQ43_wJ42v : LeanSuffixReflective.QInterval := ⟨(12688170143673759786882754537653 / 1267650600228229401496703205376 : ℚ), (12693838719834679707905231650493 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d0 : LeanSuffixReflective.QInterval := ⟨(-4677531152969368201415157396979 / 633825300114114700748351602688 : ℚ), (-583874497752392014273816173379 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d2 : LeanSuffixReflective.QInterval := ⟨(1921220706441696701360450355 / 158456325028528675187087900672 : ℚ), (15699495591396157402419538313 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ42 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ38).mul (wJ39)).mul (wJ41)).widenAll wQ43_wJ42v wQ43_wJ42d0 wQ43_wJ42d1 wQ43_wJ42d2 (by
    norm_num [wJ38, wJ39, wJ41, wQ43_wJ42v, wQ43_wJ42d0, wQ43_wJ42d1, wQ43_wJ42d2])
private abbrev wQ44_wJ43v : LeanSuffixReflective.QInterval := ⟨(542092671240164959838007890799 / 158456325028528675187087900672 : ℚ), (135543444750482855125265611505 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d0 : LeanSuffixReflective.QInterval := ⟨(-526588435993310283193422785039 / 633825300114114700748351602688 : ℚ), (-525904761988727344287554403603 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d2 : LeanSuffixReflective.QInterval := ⟨(437764455803174803677710417 / 316912650057057350374175801344 : ℚ), (1788091882889596499642186811 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ43 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ40).mul (wJ41)).widenAll wQ44_wJ43v wQ44_wJ43d0 wQ44_wJ43d1 wQ44_wJ43d2 (by
    norm_num [wJ40, wJ41, wQ44_wJ43v, wQ44_wJ43d0, wQ44_wJ43d1, wQ44_wJ43d2])
private abbrev wQ45_wJ44v : LeanSuffixReflective.QInterval := ⟨(4336552699303990343539846612605 / 1267650600228229401496703205376 : ℚ), (4337515320730880048279644691341 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d0 : LeanSuffixReflective.QInterval := ⟨(-66478758756091652164228103425 / 79228162514264337593543950336 : ℚ), (-1049127012522577298128305932969 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d2 : LeanSuffixReflective.QInterval := ⟨(1750724131821284561932310885 / 1267650600228229401496703205376 : ℚ), (223550152044602750593224169 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev wJ44 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ38).add (wJ39)).mul (((wJ35).mul (wJ35)).add ((wJ33).mul ((wJ38).mul (wJ39))))).widenAll wQ45_wJ44v wQ45_wJ44d0 wQ45_wJ44d1 wQ45_wJ44d2 (by
    norm_num [wJ38, wJ39, wJ35, wJ33, wQ45_wJ44v, wQ45_wJ44d0, wQ45_wJ44d1, wQ45_wJ44d2])
private abbrev wQ46_wJ45v : LeanSuffixReflective.QInterval := ⟨(1265438825806998259449296004679 / 633825300114114700748351602688 : ℚ), (632742546445725833066678051659 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d0 : LeanSuffixReflective.QInterval := ⟨(-177838186824683559266167643123 / 633825300114114700748351602688 : ℚ), (-351750447365706129227441085471 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d2 : LeanSuffixReflective.QInterval := ⟨(-3692544685034940134679711 / 1267650600228229401496703205376 : ℚ), (-3542548185342033090733083 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ45 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ35).mul (wJ35)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).widenAll wQ46_wJ45v wQ46_wJ45d0 wQ46_wJ45d1 wQ46_wJ45d2 (by
    norm_num [wJ35, wJ0, wQ46_wJ45v, wQ46_wJ45d0, wQ46_wJ45d1, wQ46_wJ45d2])
private abbrev wQ47_wJ46v : LeanSuffixReflective.QInterval := ⟨(126591969515736725613538888449 / 1267650600228229401496703205376 : ℚ), (126648525836501276160838282405 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d0 : LeanSuffixReflective.QInterval := ⟨(23291243650352453820288775437 / 316912650057057350374175801344 : ℚ), (46689350660485009282822303043 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d2 : LeanSuffixReflective.QInterval := ⟨(-78353219988082233638719831 / 633825300114114700748351602688 : ℚ), (-19159776523932151022208829 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev wJ46 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ42).invPos (by norm_num [wJ42])).widenAll wQ47_wJ46v wQ47_wJ46d0 wQ47_wJ46d1 wQ47_wJ46d2 (by
    norm_num [wJ42, NearOneScalarInterval.Jet3.invPos, wQ47_wJ46v, wQ47_wJ46d0, wQ47_wJ46d1, wQ47_wJ46d2])
private abbrev wQ48_wJ47v : LeanSuffixReflective.QInterval := ⟨(252742188157758298637015230213 / 1267650600228229401496703205376 : ℚ), (126432174176318533157804041085 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d0 : LeanSuffixReflective.QInterval := ⟨(150469903694272771541834534169 / 1267650600228229401496703205376 : ℚ), (37827838184650763248272742267 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d2 : LeanSuffixReflective.QInterval := ⟨(-313246396735270284111050903 / 1267650600228229401496703205376 : ℚ), (-306375321241255327703768805 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ47 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ45).mul (wJ46)).widenAll wQ48_wJ47v wQ48_wJ47d0 wQ48_wJ47d1 wQ48_wJ47d2 (by
    norm_num [wJ45, wJ46, wQ48_wJ47v, wQ48_wJ47d0, wQ48_wJ47d1, wQ48_wJ47d2])
private abbrev wQ49_wJ48v : LeanSuffixReflective.QInterval := ⟨(92621251392009047207931703565 / 316912650057057350374175801344 : ℚ), (92635109359089156163616901787 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d0 : LeanSuffixReflective.QInterval := ⟨(44920982030965275235019405531 / 633825300114114700748351602688 : ℚ), (89985679466713563787843671223 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d2 : LeanSuffixReflective.QInterval := ⟨(-38194596584527837594163445 / 316912650057057350374175801344 : ℚ), (-37392339210937243285737037 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ48 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ43).invPos (by norm_num [wJ43])).widenAll wQ49_wJ48v wQ49_wJ48d0 wQ49_wJ48d1 wQ49_wJ48d2 (by
    norm_num [wJ43, NearOneScalarInterval.Jet3.invPos, wQ49_wJ48v, wQ49_wJ48d0, wQ49_wJ48d1, wQ49_wJ48d2])
private abbrev wQ50_wJ49v : LeanSuffixReflective.QInterval := ⟨(739677179722404402259991169853 / 1267650600228229401496703205376 : ℚ), (739814898213692545720821484093 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d0 : LeanSuffixReflective.QInterval := ⟨(75404484426879791784495592655 / 1267650600228229401496703205376 : ℚ), (76860931087228640317414734935 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d2 : LeanSuffixReflective.QInterval := ⟨(-38264267960229316874320253 / 158456325028528675187087900672 : ℚ), (-149826065446545480573666275 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ49 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ45).mul (wJ48)).widenAll wQ50_wJ49v wQ50_wJ49d0 wQ50_wJ49d1 wQ50_wJ49d2 (by
    norm_num [wJ45, wJ48, wQ50_wJ49v, wQ50_wJ49d0, wQ50_wJ49d1, wQ50_wJ49d2])
private abbrev wQ51_wJ50v : LeanSuffixReflective.QInterval := ⟨(370474321226885715243372849847 / 1267650600228229401496703205376 : ℚ), (46319569819735536090766631519 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d0 : LeanSuffixReflective.QInterval := ⟨(22401916137762471356419848899 / 316912650057057350374175801344 : ℚ), (90889300400517226041882447401 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d2 : LeanSuffixReflective.QInterval := ⟨(-76409056456327751385410809 / 633825300114114700748351602688 : ℚ), (-74766114518614434022756111 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ50 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ44).invPos (by norm_num [wJ44])).widenAll wQ51_wJ50v wQ51_wJ50d0 wQ51_wJ50d1 wQ51_wJ50d2 (by
    norm_num [wJ44, NearOneScalarInterval.Jet3.invPos, wQ51_wJ50v, wQ51_wJ50d0, wQ51_wJ50d1, wQ51_wJ50d2])
private abbrev wQ52_wJ51v : LeanSuffixReflective.QInterval := ⟨(740304624224660271680515575169 / 1267650600228229401496703205376 : ℚ), (370241288198310629105358826593 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d0 : LeanSuffixReflective.QInterval := ⟨(63679027856847236586291000765 / 633825300114114700748351602688 : ℚ), (65257011514238637991549416037 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d2 : LeanSuffixReflective.QInterval := ⟨(-152958175636108227461113135 / 633825300114114700748351602688 : ℚ), (-149661315369304988669729793 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ51 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ35).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).mul (wJ50)).widenAll wQ52_wJ51v wQ52_wJ51d0 wQ52_wJ51d1 wQ52_wJ51d2 (by
    norm_num [wJ35, wJ0, wJ50, wQ52_wJ51v, wQ52_wJ51d0, wQ52_wJ51d1, wQ52_wJ51d2])
private abbrev wQ53_wJ52v : LeanSuffixReflective.QInterval := ⟨(1268739447622944172784205433177 / 1267650600228229401496703205376 : ℚ), (634381248642067441659790304943 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d0 : LeanSuffixReflective.QInterval := ⟨(88739811910683442626605475857 / 1267650600228229401496703205376 : ℚ), (22428410406452858007941787351 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d2 : LeanSuffixReflective.QInterval := ⟨(887930906484214474674011 / 1267650600228229401496703205376 : ℚ), (57846485061408731022813 / 79228162514264337593543950336 : ℚ), by norm_num⟩
@[simp] private abbrev wJ52 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ35).invPos (by norm_num [wJ35])).widenAll wQ53_wJ52v wQ53_wJ52d0 wQ53_wJ52d1 wQ53_wJ52d2 (by
    norm_num [wJ35, NearOneScalarInterval.Jet3.invPos, wQ53_wJ52v, wQ53_wJ52d0, wQ53_wJ52d1, wQ53_wJ52d2])
private abbrev wQ54_wJ53v : LeanSuffixReflective.QInterval := ⟨(13247654752474127071232270111 / 316912650057057350374175801344 : ℚ), (53553793963321375049290255967 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d0 : LeanSuffixReflective.QInterval := ⟨(544746804870650632719825202623 / 316912650057057350374175801344 : ℚ), (2179576262748282090838581593997 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d2 : LeanSuffixReflective.QInterval := ⟨(21255266293825719057449639 / 1267650600228229401496703205376 : ℚ), (21933006286890841935310115 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ53 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ0).mul (wJ39)).mul (wJ52)).widenAll wQ54_wJ53v wQ54_wJ53d0 wQ54_wJ53d1 wQ54_wJ53d2 (by
    norm_num [wJ0, wJ39, wJ52, wQ54_wJ53v, wQ54_wJ53d0, wQ54_wJ53d1, wQ54_wJ53d2])
private abbrev wQ55_wJ54v : LeanSuffixReflective.QInterval := ⟨(437736126760546594609975683 / 1267650600228229401496703205376 : ℚ), (447010552024154585212376579 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d0 : LeanSuffixReflective.QInterval := ⟨(36078532243698044900826314123 / 1267650600228229401496703205376 : ℚ), (36465792567223483383593441087 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d2 : LeanSuffixReflective.QInterval := ⟨(-184673942931728147440725 / 1267650600228229401496703205376 : ℚ), (-88493523303681606903437 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ54 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ33).mul (wJ51)).widenAll wQ55_wJ54v wQ55_wJ54d0 wQ55_wJ54d1 wQ55_wJ54d2 (by
    norm_num [wJ33, wJ51, wQ55_wJ54v, wQ55_wJ54d0, wQ55_wJ54d1, wQ55_wJ54d2])
private abbrev wQ56_wJ55v : LeanSuffixReflective.QInterval := ⟨(1266896446876259619221984973591 / 1267650600228229401496703205376 : ℚ), (1266939913995313970771485802897 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d0 : LeanSuffixReflective.QInterval := ⟨(-30887653826275296189675463485 / 633825300114114700748351602688 : ℚ), (-58058180154218715230671464265 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d2 : LeanSuffixReflective.QInterval := ⟨(-621642946968764425412915 / 1267650600228229401496703205376 : ℚ), (-283108760650550985848927 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ55 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ53).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ53]) (by norm_num [wJ53])).widenAll wQ56_wJ55v wQ56_wJ55d0 wQ56_wJ55d1 wQ56_wJ55d2 (by
    norm_num [wJ53, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ56_wJ55v, wQ56_wJ55d0, wQ56_wJ55d1, wQ56_wJ55d2])
private abbrev wQ57_wJ56v : LeanSuffixReflective.QInterval := ⟨(1267650547685245926143728201979 / 1267650600228229401496703205376 : ℚ), (316912637933091417980155498409 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d0 : LeanSuffixReflective.QInterval := ⟨(-8573054369097852767868487 / 1267650600228229401496703205376 : ℚ), (-1998418947224152693846911 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d2 : LeanSuffixReflective.QInterval := ⟨(19606874021181527801 / 633825300114114700748351602688 : ℚ), (43416573227930429063 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ56 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ54).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ54]) (by norm_num [wJ54])).widenAll wQ57_wJ56v wQ57_wJ56d0 wQ57_wJ56d1 wQ57_wJ56d2 (by
    norm_num [wJ54, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ57_wJ56v, wQ57_wJ56d0, wQ57_wJ56d1, wQ57_wJ56d2])
private abbrev wQ58_wJ57v : LeanSuffixReflective.QInterval := ⟨(1268739447622944172784205433177 / 1267650600228229401496703205376 : ℚ), (634381248642067441659790304943 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d0 : LeanSuffixReflective.QInterval := ⟨(88739811910683442626605475857 / 1267650600228229401496703205376 : ℚ), (22428410406452858007941787351 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d2 : LeanSuffixReflective.QInterval := ⟨(887930906484214474674011 / 1267650600228229401496703205376 : ℚ), (57846485061408731022813 / 79228162514264337593543950336 : ℚ), by norm_num⟩
@[simp] private abbrev wJ57 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ35).invPos (by norm_num [wJ35])).widenAll wQ58_wJ57v wQ58_wJ57d0 wQ58_wJ57d1 wQ58_wJ57d2 (by
    norm_num [wJ35, NearOneScalarInterval.Jet3.invPos, wQ58_wJ57v, wQ58_wJ57d0, wQ58_wJ57d1, wQ58_wJ57d2])
private abbrev wQ59_wJ58v : LeanSuffixReflective.QInterval := ⟨(23174761657627565305172326229 / 39614081257132168796771975168 : ℚ), (741797615919925157889056536287 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d0 : LeanSuffixReflective.QInterval := ⟨(233200829323921688971735769351 / 1267650600228229401496703205376 : ℚ), (237496795195580479328448273621 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d2 : LeanSuffixReflective.QInterval := ⟨(-305400415850235667257973581 / 1267650600228229401496703205376 : ℚ), (-298784581255883946676566763 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ58 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ33).mul (wJ39)).mul (wJ57)).mul (wJ55)).add ((wJ51).mul (wJ56))).widenAll wQ59_wJ58v wQ59_wJ58d0 wQ59_wJ58d1 wQ59_wJ58d2 (by
    norm_num [wJ33, wJ39, wJ57, wJ55, wJ51, wJ56, wQ59_wJ58v, wQ59_wJ58d0, wQ59_wJ58d1, wQ59_wJ58d2])
private abbrev wQ60_wJ59v : LeanSuffixReflective.QInterval := ⟨(633547569456618183237437438983 / 633825300114114700748351602688 : ℚ), (633553321880905913590125147333 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d0 : LeanSuffixReflective.QInterval := ⟨(-11194558377172918353226462361 / 316912650057057350374175801344 : ℚ), (-11073445266309469245171127605 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d2 : LeanSuffixReflective.QInterval := ⟨(-230980561599814703731067 / 633825300114114700748351602688 : ℚ), (-443203747292764560578325 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ59 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ5).mul (wJ4)).neg)).widenAll wQ60_wJ59v wQ60_wJ59d0 wQ60_wJ59d1 wQ60_wJ59d2 (by
    norm_num [wJ5, wJ4, wQ60_wJ59v, wQ60_wJ59d0, wQ60_wJ59d1, wQ60_wJ59d2])
private abbrev wQ61_wJ60v : LeanSuffixReflective.QInterval := ⟨(-1041543118518062260401164895 / 1267650600228229401496703205376 : ℚ), (1042407763005698650960968247 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d0 : LeanSuffixReflective.QInterval := ⟨(-2612087929434946624683405485 / 1267650600228229401496703205376 : ℚ), (2614441079697892820544420901 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d1 : LeanSuffixReflective.QInterval := ⟨(-2444413066717849492815131497 / 633825300114114700748351602688 : ℚ), (-4773664124872580189843063255 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ60 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul (wJ20)).add ((((NearOneScalarInterval.Jet3.pi).mul (NearOneScalarInterval.Jet3.rational (1 / 2 : ℚ))).add ((wJ5).mul (wJ31))).neg)).widenAll wQ61_wJ60v wQ61_wJ60d0 wQ61_wJ60d1 wQ61_wJ60d2 (by
    norm_num [wJ8, wJ20, wJ5, wJ31, wQ61_wJ60v, wQ61_wJ60d0, wQ61_wJ60d1, wQ61_wJ60d2])
private abbrev wQ62_wJ61v : LeanSuffixReflective.QInterval := ⟨(-2570750608908490716919541999 / 1267650600228229401496703205376 : ℚ), (2570273832896613280393803627 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d0 : LeanSuffixReflective.QInterval := ⟨(-12206627948470009484860355651 / 1267650600228229401496703205376 : ℚ), (12207337108709524079031101519 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d1 : LeanSuffixReflective.QInterval := ⟨(-25357214732470217207254599 / 316912650057057350374175801344 : ℚ), (50741963904246968056894045 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d2 : LeanSuffixReflective.QInterval := ⟨(436014247660700712162807819 / 158456325028528675187087900672 : ℚ), (903240758938263624747650263 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ61 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.pi).mul ((wJ4).add ((wJ3).neg))).mul ((wJ8).add (wJ59))).add (((wJ8).mul (wJ8)).mul ((wJ58).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ59)).add (NearOneScalarInterval.Jet3.rational (1 : ℚ))).mul (wJ49))))).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul ((wJ59).mul (wJ59))).mul ((wJ31).add ((wJ8).mul (wJ22)))).neg)).widenAll wQ62_wJ61v wQ62_wJ61d0 wQ62_wJ61d1 wQ62_wJ61d2 (by
    norm_num [wJ4, wJ3, wJ8, wJ59, wJ58, wJ49, wJ31, wJ22, wQ62_wJ61v, wQ62_wJ61d0, wQ62_wJ61d1, wQ62_wJ61d2])
private abbrev wQ63_wJ62v : LeanSuffixReflective.QInterval := ⟨(-1237882719805683888681456213 / 1267650600228229401496703205376 : ℚ), (371582699447107183604604523 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d0 : LeanSuffixReflective.QInterval := ⟨(-5725043816095761476135706117 / 316912650057057350374175801344 : ℚ), (-17774650161785295455033357371 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d1 : LeanSuffixReflective.QInterval := ⟨(865364740526887811442095651 / 633825300114114700748351602688 : ℚ), (1826298445265563226436389819 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d2 : LeanSuffixReflective.QInterval := ⟨(-904409109235538264754262395 / 1267650600228229401496703205376 : ℚ), (-872023249599125274344622053 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ62 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ3).add ((wJ4).neg)).mul (wJ20)).add ((wJ59).mul (wJ22))).add (((wJ8).mul (wJ49)).neg)).widenAll wQ63_wJ62v wQ63_wJ62d0 wQ63_wJ62d1 wQ63_wJ62d2 (by
    norm_num [wJ3, wJ4, wJ20, wJ59, wJ22, wJ8, wJ49, wQ63_wJ62v, wQ63_wJ62d0, wQ63_wJ62d1, wQ63_wJ62d2])
private abbrev wQ64_wJ63v : LeanSuffixReflective.QInterval := ⟨(233190055907817459841418193905 / 633825300114114700748351602688 : ℚ), (466730248866048951862541829129 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d0 : LeanSuffixReflective.QInterval := ⟨(-98731234864307546852470829563 / 1267650600228229401496703205376 : ℚ), (-98655195043634928626710407157 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d1 : LeanSuffixReflective.QInterval := ⟨(-191312129631480314172431467 / 316912650057057350374175801344 : ℚ), (-749551530102549718530397873 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d2 : LeanSuffixReflective.QInterval := ⟨(749551530102549718530397873 / 1267650600228229401496703205376 : ℚ), (191312129631480314172431467 / 316912650057057350374175801344 : ℚ), by norm_num⟩
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
private abbrev cQ4_cJ3v : LeanSuffixReflective.QInterval := ⟨(113371122303529121591142971895 / 316912650057057350374175801344 : ℚ), (453484489214116486364571887581 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d0 : LeanSuffixReflective.QInterval := ⟨(-159992255651544368347109952931 / 316912650057057350374175801344 : ℚ), (-639969022606177473388439811723 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d1 : LeanSuffixReflective.QInterval := ⟨(378689845713838358093787847 / 633825300114114700748351602688 : ℚ), (757379691427676716187575695 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ3 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (122978918310508179754384166075116259 / 332306998946228968225951765070086144 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-671056157848295150335756664018267327 / 1329227995784915872903807060280344576 : ℚ)).mul (cJ0))).add (((cJ0).mul (cJ0)).mul (cJ1))).widenAll cQ4_cJ3v cQ4_cJ3d0 cQ4_cJ3d1 cQ4_cJ3d2 (by
    norm_num [cJ0, cJ1, cQ4_cJ3v, cQ4_cJ3d0, cQ4_cJ3d1, cQ4_cJ3d2])
private abbrev cQ5_cJ4v : LeanSuffixReflective.QInterval := ⟨(460019834777479211068630498025 / 633825300114114700748351602688 : ℚ), (920039669554958422137260996051 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d0 : LeanSuffixReflective.QInterval := ⟨(-738662237560148711128030430085 / 1267650600228229401496703205376 : ℚ), (-184665559390037177782007607521 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d2 : LeanSuffixReflective.QInterval := ⟨(378689845713838358093787847 / 633825300114114700748351602688 : ℚ), (757379691427676716187575695 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ4 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (983663793766682566408702377040566921 / 1329227995784915872903807060280344576 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-193635873602967623729946409064003075 / 332306998946228968225951765070086144 : ℚ)).mul (cJ0))).add (((cJ0).mul (cJ0)).mul (cJ2))).widenAll cQ5_cJ4v cQ5_cJ4d0 cQ5_cJ4d1 cQ5_cJ4d2 (by
    norm_num [cJ0, cJ2, cQ5_cJ4v, cQ5_cJ4d0, cQ5_cJ4d1, cQ5_cJ4d2])
private abbrev cQ6_cJ5v : LeanSuffixReflective.QInterval := ⟨(378689845713838358093787847 / 633825300114114700748351602688 : ℚ), (757379691427676716187575695 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d0 : LeanSuffixReflective.QInterval := ⟨(61970729233694371931891960963 / 1267650600228229401496703205376 : ℚ), (15492682308423592982972990241 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ5 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ6_cJ5v cQ6_cJ5d0 cQ6_cJ5d1 cQ6_cJ5d2 (by
    norm_num [cJ0, cQ6_cJ5v, cQ6_cJ5d0, cQ6_cJ5d1, cQ6_cJ5d2])
private abbrev cQ7_cJ6v : LeanSuffixReflective.QInterval := ⟨(378689845713838358093787847 / 633825300114114700748351602688 : ℚ), (757379691427676716187575695 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d0 : LeanSuffixReflective.QInterval := ⟨(61970729233694371931891960963 / 1267650600228229401496703205376 : ℚ), (15492682308423592982972990241 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ6 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ7_cJ6v cQ7_cJ6d0 cQ7_cJ6d1 cQ7_cJ6d2 (by
    norm_num [cJ0, cQ7_cJ6v, cQ7_cJ6d0, cQ7_cJ6d1, cQ7_cJ6d2])
private abbrev cQ8_cJ7v : LeanSuffixReflective.QInterval := ⟨(81113905488138046734501122897 / 633825300114114700748351602688 : ℚ), (40556952744069023367250561449 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d0 : LeanSuffixReflective.QInterval := ⟨(-57235019112752540336913065557 / 158456325028528675187087900672 : ℚ), (-228940076451010161347652262227 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d1 : LeanSuffixReflective.QInterval := ⟨(67735530288548787875505559 / 158456325028528675187087900672 : ℚ), (270942121154195151502022237 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ7 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ3).mul (cJ3)).widenAll cQ8_cJ7v cQ8_cJ7d0 cQ8_cJ7d1 cQ8_cJ7d2 (by
    norm_num [cJ3, cQ8_cJ7v, cQ8_cJ7d0, cQ8_cJ7d1, cQ8_cJ7d2])
private abbrev cQ9_cJ8v : LeanSuffixReflective.QInterval := ⟨(1267379658107075206345201183139 / 1267650600228229401496703205376 : ℚ), (316844914526768801586300295785 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d0 : LeanSuffixReflective.QInterval := ⟨(-21786811718411271276271570569 / 1267650600228229401496703205376 : ℚ), (-21786811718411271276271570567 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d1 : LeanSuffixReflective.QInterval := ⟨(-452509545519725085718003 / 1267650600228229401496703205376 : ℚ), (-226254772759862542859001 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ8 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ6).mul (cJ3)).neg)).widenAll cQ9_cJ8v cQ9_cJ8d0 cQ9_cJ8d1 cQ9_cJ8d2 (by
    norm_num [cJ6, cJ3, cQ9_cJ8v, cQ9_cJ8d0, cQ9_cJ8d1, cQ9_cJ8d2])
private abbrev cQ10_cJ9v : LeanSuffixReflective.QInterval := ⟨(906872052627546191895375748061 / 1267650600228229401496703205376 : ℚ), (28339751644610818496730492127 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d0 : LeanSuffixReflective.QInterval := ⟨(-1287595191919438414427921113765 / 1267650600228229401496703205376 : ℚ), (-1287595191919438414427921113761 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d1 : LeanSuffixReflective.QInterval := ⟨(757217812389337935006219017 / 633825300114114700748351602688 : ℚ), (1514435624778675870012438037 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ9 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ3)).add (((cJ6).mul (cJ7)).neg)).widenAll cQ10_cJ9v cQ10_cJ9d0 cQ10_cJ9d1 cQ10_cJ9d2 (by
    norm_num [cJ3, cJ6, cJ7, cQ10_cJ9v, cQ10_cJ9d0, cQ10_cJ9d1, cQ10_cJ9d2])
private abbrev cQ11_cJ10v : LeanSuffixReflective.QInterval := ⟨(968843234370786083552353427027 / 1267650600228229401496703205376 : ℚ), (484421617185393041776176713515 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d0 : LeanSuffixReflective.QInterval := ⟨(623890029748383049819646209431 / 633825300114114700748351602688 : ℚ), (623890029748383049819646209433 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d1 : LeanSuffixReflective.QInterval := ⟨(757217812389337935006219017 / 633825300114114700748351602688 : ℚ), (1514435624778675870012438037 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ10 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ3)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ0))).add (((cJ6).mul (cJ7)).neg)).add (((cJ0).mul (cJ0)).mul ((cJ0).mul (cJ0)))).widenAll cQ11_cJ10v cQ11_cJ10d0 cQ11_cJ10d1 cQ11_cJ10d2 (by
    norm_num [cJ3, cJ0, cJ6, cJ7, cQ11_cJ10v, cQ11_cJ10d0, cQ11_cJ10d1, cQ11_cJ10d2])
private abbrev cQ11_root11 : LeanSuffixReflective.QInterval := ⟨(1072192567519247156476296572585 / 1267650600228229401496703205376 : ℚ), (268048141879811789119074143147 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11v : LeanSuffixReflective.QInterval := ⟨(1072192567519247156476296572585 / 1267650600228229401496703205376 : ℚ), (268048141879811789119074143147 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d0 : LeanSuffixReflective.QInterval := ⟨(-380580146545913729999122722137 / 633825300114114700748351602688 : ℚ), (-190290073272956864999561361067 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d1 : LeanSuffixReflective.QInterval := ⟨(895256732286217688806059783 / 1267650600228229401496703205376 : ℚ), (447628366143108844403029893 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ11 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ9).sqrt cQ11_root11 (by norm_num [cQ11_root11]) (by norm_num [cJ9, cQ11_root11]) (by norm_num [cJ9, cQ11_root11])).widenAll cQ12_cJ11v cQ12_cJ11d0 cQ12_cJ11d1 cQ12_cJ11d2 (by
    norm_num [cJ9, cQ11_root11, NearOneScalarInterval.Jet3.sqrt, cQ12_cJ11v, cQ12_cJ11d0, cQ12_cJ11d1, cQ12_cJ11d2])
private abbrev cQ12_root12 : LeanSuffixReflective.QInterval := ⟨(277055354078520078057298521203 / 316912650057057350374175801344 : ℚ), (1108221416314080312229194084815 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12v : LeanSuffixReflective.QInterval := ⟨(277055354078520078057298521203 / 316912650057057350374175801344 : ℚ), (1108221416314080312229194084815 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d0 : LeanSuffixReflective.QInterval := ⟨(713643103304551571232976122589 / 1267650600228229401496703205376 : ℚ), (356821551652275785616488061297 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d1 : LeanSuffixReflective.QInterval := ⟨(866151475010666920127925741 / 1267650600228229401496703205376 : ℚ), (54134467188166682507995359 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ12 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ10).sqrt cQ12_root12 (by norm_num [cQ12_root12]) (by norm_num [cJ10, cQ12_root12]) (by norm_num [cJ10, cQ12_root12])).widenAll cQ13_cJ12v cQ13_cJ12d0 cQ13_cJ12d1 cQ13_cJ12d2 (by
    norm_num [cJ10, cQ12_root12, NearOneScalarInterval.Jet3.sqrt, cQ13_cJ12v, cQ13_cJ12d0, cQ13_cJ12d1, cQ13_cJ12d2])
private abbrev cQ14_cJ13v : LeanSuffixReflective.QInterval := ⟨(316917278242041457316288746461 / 316912650057057350374175801344 : ℚ), (1267669112968165829265154985845 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d0 : LeanSuffixReflective.QInterval := ⟨(1136069537141515074281363541 / 633825300114114700748351602688 : ℚ), (2272139074283030148562727083 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ13 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0))).widenAll cQ14_cJ13v cQ14_cJ13d0 cQ14_cJ13d1 cQ14_cJ13d2 (by
    norm_num [cJ0, cQ14_cJ13v, cQ14_cJ13d0, cQ14_cJ13d1, cQ14_cJ13d2])
private abbrev cQ15_cJ14v : LeanSuffixReflective.QInterval := ⟨(2180429642108691895555146294129 / 1267650600228229401496703205376 : ℚ), (2180429642108691895555146294137 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d0 : LeanSuffixReflective.QInterval := ⟨(-45606505987793358505380199613 / 1267650600228229401496703205376 : ℚ), (-45606505987793358505380199599 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d1 : LeanSuffixReflective.QInterval := ⟨(440355320401354742306298083 / 316912650057057350374175801344 : ℚ), (1761421281605418969225192339 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ14 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ12).add ((cJ13).mul (cJ11))).widenAll cQ15_cJ14v cQ15_cJ14d0 cQ15_cJ14d1 cQ15_cJ14d2 (by
    norm_num [cJ12, cJ13, cJ11, cQ15_cJ14v, cQ15_cJ14d0, cQ15_cJ14d1, cQ15_cJ14d2])
private abbrev cQ16_cJ15v : LeanSuffixReflective.QInterval := ⟨(1612286715606354428951225724959 / 1267650600228229401496703205376 : ℚ), (806143357803177214475612862487 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d0 : LeanSuffixReflective.QInterval := ⟨(-70031944420200011991827933957 / 633825300114114700748351602688 : ℚ), (-17507986105050002997956983485 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d1 : LeanSuffixReflective.QInterval := ⟨(3908793628677667809961443857 / 1267650600228229401496703205376 : ℚ), (122149800896177119061295121 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ15 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ11).mul (cJ12)).mul (cJ14)).widenAll cQ16_cJ15v cQ16_cJ15d0 cQ16_cJ15d1 cQ16_cJ15d2 (by
    norm_num [cJ11, cJ12, cJ14, cQ16_cJ15v, cQ16_cJ15d0, cQ16_cJ15d1, cQ16_cJ15d2])
private abbrev cQ17_cJ16v : LeanSuffixReflective.QInterval := ⟨(2180461485052565206537445111717 / 1267650600228229401496703205376 : ℚ), (136278842815785325408590319483 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d0 : LeanSuffixReflective.QInterval := ⟨(-41698966255406890713903238423 / 1267650600228229401496703205376 : ℚ), (-41698966255406890713903238407 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d1 : LeanSuffixReflective.QInterval := ⟨(440361751340230758202373313 / 316912650057057350374175801344 : ℚ), (440361751340230758202373315 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ16 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ13).mul (cJ14)).widenAll cQ17_cJ16v cQ17_cJ16d0 cQ17_cJ16d1 cQ17_cJ16d2 (by
    norm_num [cJ13, cJ14, cQ17_cJ16v, cQ17_cJ16d0, cQ17_cJ16d1, cQ17_cJ16d2])
private abbrev cQ18_cJ17v : LeanSuffixReflective.QInterval := ⟨(2180445300612729412310189178051 / 1267650600228229401496703205376 : ℚ), (2180445300612729412310189178063 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d0 : LeanSuffixReflective.QInterval := ⟨(-43695766218809800762446991359 / 1267650600228229401496703205376 : ℚ), (-43695766218809800762446991339 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d1 : LeanSuffixReflective.QInterval := ⟨(880717178052445113911954063 / 633825300114114700748351602688 : ℚ), (1761434356104890227823908137 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ17 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ11).add (cJ12)).mul (((cJ8).mul (cJ8)).add ((cJ6).mul ((cJ11).mul (cJ12))))).widenAll cQ18_cJ17v cQ18_cJ17d0 cQ18_cJ17d1 cQ18_cJ17d2 (by
    norm_num [cJ11, cJ12, cJ8, cJ6, cQ18_cJ17v, cQ18_cJ17d0, cQ18_cJ17d1, cQ18_cJ17d2])
private abbrev cQ19_cJ18v : LeanSuffixReflective.QInterval := ⟨(633559013154734594241020299757 / 316912650057057350374175801344 : ℚ), (2534236052618938376964081199033 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d0 : LeanSuffixReflective.QInterval := ⟨(-84858088708777925796509307827 / 1267650600228229401496703205376 : ℚ), (-42429044354388962898254653909 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d1 : LeanSuffixReflective.QInterval := ⟨(-1809664526449915312949545 / 1267650600228229401496703205376 : ℚ), (-452416131612478828237385 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ18 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul (cJ8)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).widenAll cQ19_cJ18v cQ19_cJ18d0 cQ19_cJ18d1 cQ19_cJ18d2 (by
    norm_num [cJ8, cJ0, cQ19_cJ18v, cQ19_cJ18d0, cQ19_cJ18d1, cQ19_cJ18d2])
private abbrev cQ20_cJ19v : LeanSuffixReflective.QInterval := ⟨(498341277858463094023750328129 / 633825300114114700748351602688 : ℚ), (249170638929231547011875164067 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d0 : LeanSuffixReflective.QInterval := ⟨(86584621297087586827256456011 / 1267650600228229401496703205376 : ℚ), (86584621297087586827256456035 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d1 : LeanSuffixReflective.QInterval := ⟨(-604083998505089044993054943 / 316912650057057350374175801344 : ℚ), (-1208167997010178089986109881 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ19 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ15).invPos (by norm_num [cJ15])).widenAll cQ20_cJ19v cQ20_cJ19d0 cQ20_cJ19d1 cQ20_cJ19d2 (by
    norm_num [cJ15, NearOneScalarInterval.Jet3.invPos, cQ20_cJ19v, cQ20_cJ19d0, cQ20_cJ19d1, cQ20_cJ19d2])
private abbrev cQ21_cJ20v : LeanSuffixReflective.QInterval := ⟨(1992527645440679587713043975889 / 1267650600228229401496703205376 : ℚ), (996263822720339793856521987957 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d0 : LeanSuffixReflective.QInterval := ⟨(1662145854475299308288801209 / 19807040628566084398385987584 : ℚ), (106377334686419155730483277433 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d1 : LeanSuffixReflective.QInterval := ⟨(-4832064490995862193648808299 / 1267650600228229401496703205376 : ℚ), (-2416032245497931096824404137 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ20 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ18).mul (cJ19)).widenAll cQ21_cJ20v cQ21_cJ20d0 cQ21_cJ20d1 cQ21_cJ20d2 (by
    norm_num [cJ18, cJ19, cQ21_cJ20v, cQ21_cJ20d0, cQ21_cJ20d1, cQ21_cJ20d2])
private abbrev cQ22_cJ21v : LeanSuffixReflective.QInterval := ⟨(23030360420185477597907428559 / 39614081257132168796771975168 : ℚ), (736971533445935283133037713893 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d0 : LeanSuffixReflective.QInterval := ⟨(1761722880398451723574556319 / 158456325028528675187087900672 : ℚ), (14093783043187613788596450559 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d1 : LeanSuffixReflective.QInterval := ⟨(-595349337524893439681719035 / 1267650600228229401496703205376 : ℚ), (-595349337524893439681719031 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ21 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ16).invPos (by norm_num [cJ16])).widenAll cQ22_cJ21v cQ22_cJ21d0 cQ22_cJ21d1 cQ22_cJ21d2 (by
    norm_num [cJ16, NearOneScalarInterval.Jet3.invPos, cQ22_cJ21v, cQ22_cJ21d0, cQ22_cJ21d1, cQ22_cJ21d2])
private abbrev cQ23_cJ22v : LeanSuffixReflective.QInterval := ⟨(1473323823990851373078719680389 / 1267650600228229401496703205376 : ℚ), (1473323823990851373078719680403 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d0 : LeanSuffixReflective.QInterval := ⟨(-21158056210705755019987514565 / 1267650600228229401496703205376 : ℚ), (-1322378513169109688749219659 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d1 : LeanSuffixReflective.QInterval := ⟨(-297812627948818876047785573 / 316912650057057350374175801344 : ℚ), (-148906313974409438023892785 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ22 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ18).mul (cJ21)).widenAll cQ23_cJ22v cQ23_cJ22d0 cQ23_cJ22d1 cQ23_cJ22d2 (by
    norm_num [cJ18, cJ21, cQ23_cJ22v, cQ23_cJ22d0, cQ23_cJ22d1, cQ23_cJ22d2])
private abbrev cQ24_cJ23v : LeanSuffixReflective.QInterval := ⟨(184244250911433411011501592049 / 316912650057057350374175801344 : ℚ), (736977003645733644046006368201 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d0 : LeanSuffixReflective.QInterval := ⟨(3692224571156815671594824277 / 316912650057057350374175801344 : ℚ), (3692224571156815671594824279 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d1 : LeanSuffixReflective.QInterval := ⟨(-595353900194626911245267135 / 1267650600228229401496703205376 : ℚ), (-595353900194626911245267131 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ23 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ17).invPos (by norm_num [cJ17])).widenAll cQ24_cJ23v cQ24_cJ23d0 cQ24_cJ23d1 cQ24_cJ23d2 (by
    norm_num [cJ17, NearOneScalarInterval.Jet3.invPos, cQ24_cJ23v, cQ24_cJ23d0, cQ24_cJ23d1, cQ24_cJ23d2])
private abbrev cQ25_cJ24v : LeanSuffixReflective.QInterval := ⟨(736824865636397029093898366193 / 633825300114114700748351602688 : ℚ), (736824865636397029093898366199 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d0 : LeanSuffixReflective.QInterval := ⟨(2759845373895883707827473879 / 633825300114114700748351602688 : ℚ), (5519690747791767415654947777 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d1 : LeanSuffixReflective.QInterval := ⟨(-1190988153277704672335060597 / 1267650600228229401496703205376 : ℚ), (-1190988153277704672335060587 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ24 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).mul (cJ23)).widenAll cQ25_cJ24v cQ25_cJ24d0 cQ25_cJ24d1 cQ25_cJ24d2 (by
    norm_num [cJ8, cJ0, cJ23, cQ25_cJ24v, cQ25_cJ24d0, cQ25_cJ24d1, cQ25_cJ24d2])
private abbrev cQ26_cJ25v : LeanSuffixReflective.QInterval := ⟨(633960800135876612185346604055 / 633825300114114700748351602688 : ℚ), (79245100016984576523168325507 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d0 : LeanSuffixReflective.QInterval := ⟨(21796127941713879055327507315 / 1267650600228229401496703205376 : ℚ), (10898063970856939527663753659 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d1 : LeanSuffixReflective.QInterval := ⟨(226351521197107740946457 / 633825300114114700748351602688 : ℚ), (113175760598553870473229 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ25 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ8).invPos (by norm_num [cJ8])).widenAll cQ26_cJ25v cQ26_cJ25d0 cQ26_cJ25d1 cQ26_cJ25d2 (by
    norm_num [cJ8, NearOneScalarInterval.Jet3.invPos, cQ26_cJ25v, cQ26_cJ25d0, cQ26_cJ25d1, cQ26_cJ25d2])
private abbrev cQ27_cJ26v : LeanSuffixReflective.QInterval := ⟨(27094205308595430569877166319 / 1267650600228229401496703205376 : ℚ), (1693387831787214410617322895 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d0 : LeanSuffixReflective.QInterval := ⟨(1126371504037209477407186548725 / 1267650600228229401496703205376 : ℚ), (1126371504037209477407186548731 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d1 : LeanSuffixReflective.QInterval := ⟨(21185664044236592659168243 / 1267650600228229401496703205376 : ℚ), (5296416011059148164792061 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ26 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ0).mul (cJ12)).mul (cJ25)).widenAll cQ27_cJ26v cQ27_cJ26d0 cQ27_cJ26d1 cQ27_cJ26d2 (by
    norm_num [cJ0, cJ12, cJ25, cQ27_cJ26v, cQ27_cJ26d0, cQ27_cJ26d1, cQ27_cJ26d2])
private abbrev cQ28_cJ27v : LeanSuffixReflective.QInterval := ⟨(110057177678033009257772909 / 158456325028528675187087900672 : ℚ), (880457421424264074062183275 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d0 : LeanSuffixReflective.QInterval := ⟨(72044559413489368525585680115 / 1267650600228229401496703205376 : ℚ), (36022279706744684262792840059 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d1 : LeanSuffixReflective.QInterval := ⟨(-711576391681654116948165 / 1267650600228229401496703205376 : ℚ), (-177894097920413529237041 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ27 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ6).mul (cJ24)).widenAll cQ28_cJ27v cQ28_cJ27d0 cQ28_cJ27d1 cQ28_cJ27d2 (by
    norm_num [cJ6, cJ24, cQ28_cJ27v, cQ28_cJ27d0, cQ28_cJ27d1, cQ28_cJ27d2])
private abbrev cQ29_cJ28v : LeanSuffixReflective.QInterval := ⟨(158432195878338941213371617699 / 158456325028528675187087900672 : ℚ), (1267464805771768449899087826485 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d0 : LeanSuffixReflective.QInterval := ⟨(-8050584015424203354891630763 / 633825300114114700748351602688 : ℚ), (-15396391984549670532897102885 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d1 : LeanSuffixReflective.QInterval := ⟨(-37855398440780351349125 / 158456325028528675187087900672 : ℚ), (-289587216037446063523203 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ28 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ26).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ26]) (by norm_num [cJ26])).widenAll cQ29_cJ28v cQ29_cJ28d0 cQ29_cJ28d1 cQ29_cJ28d2 (by
    norm_num [cJ26, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ29_cJ28v, cQ29_cJ28d0, cQ29_cJ28d1, cQ29_cJ28d2])
private abbrev cQ30_cJ29v : LeanSuffixReflective.QInterval := ⟨(1267650396385185479274176382243 / 1267650600228229401496703205376 : ℚ), (1267650404029299626357521138111 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d0 : LeanSuffixReflective.QInterval := ⟨(-33362913303006596191111297 / 1267650600228229401496703205376 : ℚ), (-32104983362132168284426573 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d1 : LeanSuffixReflective.QInterval := ⟨(158548739847995403897 / 633825300114114700748351602688 : ℚ), (329521918898656596851 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ29 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ27).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ27]) (by norm_num [cJ27])).widenAll cQ30_cJ29v cQ30_cJ29d0 cQ30_cJ29d1 cQ30_cJ29d2 (by
    norm_num [cJ27, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ30_cJ29v, cQ30_cJ29d0, cQ30_cJ29d1, cQ30_cJ29d2])
private abbrev cQ31_cJ30v : LeanSuffixReflective.QInterval := ⟨(633960800135876612185346604055 / 633825300114114700748351602688 : ℚ), (79245100016984576523168325507 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d0 : LeanSuffixReflective.QInterval := ⟨(21796127941713879055327507315 / 1267650600228229401496703205376 : ℚ), (10898063970856939527663753659 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d1 : LeanSuffixReflective.QInterval := ⟨(226351521197107740946457 / 633825300114114700748351602688 : ℚ), (113175760598553870473229 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ30 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ8).invPos (by norm_num [cJ8])).widenAll cQ31_cJ30v cQ31_cJ30d0 cQ31_cJ30d1 cQ31_cJ30d2 (by
    norm_num [cJ8, NearOneScalarInterval.Jet3.invPos, cQ31_cJ30v, cQ31_cJ30d0, cQ31_cJ30d1, cQ31_cJ30d2])
private abbrev cQ32_cJ31v : LeanSuffixReflective.QInterval := ⟨(1474311660985501342250869918587 / 1267650600228229401496703205376 : ℚ), (368577918413401911494234492053 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d0 : LeanSuffixReflective.QInterval := ⟨(60090439990045560060088482157 / 1267650600228229401496703205376 : ℚ), (60092582509606484451135284683 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d1 : LeanSuffixReflective.QInterval := ⟨(-148808749147197033797288861 / 158456325028528675187087900672 : ℚ), (-74404372604361953369503181 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ31 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ6).mul (cJ12)).mul (cJ30)).mul (cJ28)).add ((cJ24).mul (cJ29))).widenAll cQ32_cJ31v cQ32_cJ31d0 cQ32_cJ31d1 cQ32_cJ31d2 (by
    norm_num [cJ6, cJ12, cJ30, cJ28, cJ24, cJ29, cQ32_cJ31v, cQ32_cJ31d0, cQ32_cJ31d1, cQ32_cJ31d2])
private abbrev cQ33_cJ32v : LeanSuffixReflective.QInterval := ⟨(460019834777479211068630498025 / 316912650057057350374175801344 : ℚ), (920039669554958422137260996051 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d0 : LeanSuffixReflective.QInterval := ⟨(-738662237560148711128030430085 / 633825300114114700748351602688 : ℚ), (-184665559390037177782007607521 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d2 : LeanSuffixReflective.QInterval := ⟨(378689845713838358093787847 / 316912650057057350374175801344 : ℚ), (757379691427676716187575695 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ32 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ4)).widenAll cQ33_cJ32v cQ33_cJ32d0 cQ33_cJ32d1 cQ33_cJ32d2 (by
    norm_num [cJ4, cQ33_cJ32v, cQ33_cJ32d0, cQ33_cJ32d1, cQ33_cJ32d2])
private abbrev cQ34_cJ33v : LeanSuffixReflective.QInterval := ⟨(378689845713838358093787847 / 633825300114114700748351602688 : ℚ), (757379691427676716187575695 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d0 : LeanSuffixReflective.QInterval := ⟨(61970729233694371931891960963 / 1267650600228229401496703205376 : ℚ), (15492682308423592982972990241 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ33 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ34_cJ33v cQ34_cJ33d0 cQ34_cJ33d1 cQ34_cJ33d2 (by
    norm_num [cJ0, cQ34_cJ33v, cQ34_cJ33d0, cQ34_cJ33d1, cQ34_cJ33d2])
private abbrev cQ35_cJ34v : LeanSuffixReflective.QInterval := ⟨(667749451940776921941771266869 / 316912650057057350374175801344 : ℚ), (2670997807763107687767085067483 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d0 : LeanSuffixReflective.QInterval := ⟨(-4288869887871056214859287179389 / 1267650600228229401496703205376 : ℚ), (-4288869887871056214859287179377 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d2 : LeanSuffixReflective.QInterval := ⟨(2198774207666686172209264207 / 633825300114114700748351602688 : ℚ), (1099387103833343086104632105 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ34 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ32).mul (cJ32)).widenAll cQ35_cJ34v cQ35_cJ34d0 cQ35_cJ34d1 cQ35_cJ34d2 (by
    norm_num [cJ32, cQ35_cJ34v, cQ35_cJ34d0, cQ35_cJ34d1, cQ35_cJ34d2])
private abbrev cQ36_cJ35v : LeanSuffixReflective.QInterval := ⟨(1266551213124396058410598573271 / 1267650600228229401496703205376 : ℚ), (1266551213124396058410598573273 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d0 : LeanSuffixReflective.QInterval := ⟨(-89071991065252468532348601081 / 1267650600228229401496703205376 : ℚ), (-89071991065252468532348601077 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d2 : LeanSuffixReflective.QInterval := ⟨(-905019091039450171436005 / 1267650600228229401496703205376 : ℚ), (-226254772759862542859001 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ35 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ33).mul (cJ32)).neg)).widenAll cQ36_cJ35v cQ36_cJ35d0 cQ36_cJ35d1 cQ36_cJ35d2 (by
    norm_num [cJ33, cJ32, cQ36_cJ35v, cQ36_cJ35d0, cQ36_cJ35d1, cQ36_cJ35d2])
private abbrev cQ37_cJ36v : LeanSuffixReflective.QInterval := ⟨(3678562844561029434985568441349 / 1267650600228229401496703205376 : ℚ), (919640711140257358746392110339 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d0 : LeanSuffixReflective.QInterval := ⟨(-385332706574377977200480858365 / 158456325028528675187087900672 : ℚ), (-3082661652595023817603846866909 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d2 : LeanSuffixReflective.QInterval := ⟨(3026891374644711384305407809 / 1267650600228229401496703205376 : ℚ), (1513445687322355692152703907 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ36 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ32)).add (((cJ33).mul (cJ34)).neg)).widenAll cQ37_cJ36v cQ37_cJ36d0 cQ37_cJ36d1 cQ37_cJ36d2 (by
    norm_num [cJ32, cJ33, cJ34, cQ37_cJ36v, cQ37_cJ36d0, cQ37_cJ36d1, cQ37_cJ36d2])
private abbrev cQ38_cJ37v : LeanSuffixReflective.QInterval := ⟨(3740534026304269326642546120315 / 1267650600228229401496703205376 : ℚ), (1870267013152134663321273060161 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d0 : LeanSuffixReflective.QInterval := ⟨(-547286401178819303536633334293 / 1267650600228229401496703205376 : ℚ), (-273643200589409651768316667141 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d2 : LeanSuffixReflective.QInterval := ⟨(3026891374644711384305407809 / 1267650600228229401496703205376 : ℚ), (1513445687322355692152703907 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ37 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ32)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ0))).add (((cJ33).mul (cJ34)).neg)).add (((cJ0).mul (cJ0)).mul ((cJ0).mul (cJ0)))).widenAll cQ38_cJ37v cQ38_cJ37d0 cQ38_cJ37d1 cQ38_cJ37d2 (by
    norm_num [cJ32, cJ0, cJ33, cJ34, cQ38_cJ37v, cQ38_cJ37d0, cQ38_cJ37d1, cQ38_cJ37d2])
private abbrev cQ38_root38 : LeanSuffixReflective.QInterval := ⟨(1079714360130151725521129119667 / 633825300114114700748351602688 : ℚ), (1079714360130151725521129119669 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38v : LeanSuffixReflective.QInterval := ⟨(1079714360130151725521129119667 / 633825300114114700748351602688 : ℚ), (1079714360130151725521129119669 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d0 : LeanSuffixReflective.QInterval := ⟨(-904808261914192309430057013495 / 1267650600228229401496703205376 : ℚ), (-904808261914192309430057013489 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d2 : LeanSuffixReflective.QInterval := ⟨(444219416910354349529686815 / 633825300114114700748351602688 : ℚ), (888438833820708699059373633 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ38 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ36).sqrt cQ38_root38 (by norm_num [cQ38_root38]) (by norm_num [cJ36, cQ38_root38]) (by norm_num [cJ36, cQ38_root38])).widenAll cQ39_cJ38v cQ39_cJ38d0 cQ39_cJ38d1 cQ39_cJ38d2 (by
    norm_num [cJ36, cQ38_root38, NearOneScalarInterval.Jet3.sqrt, cQ39_cJ38v, cQ39_cJ38d0, cQ39_cJ38d1, cQ39_cJ38d2])
private abbrev cQ39_root39 : LeanSuffixReflective.QInterval := ⟨(2177542239227226250266520014673 / 1267650600228229401496703205376 : ℚ), (544385559806806562566630003669 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39v : LeanSuffixReflective.QInterval := ⟨(2177542239227226250266520014673 / 1267650600228229401496703205376 : ℚ), (544385559806806562566630003669 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d0 : LeanSuffixReflective.QInterval := ⟨(-19912585461410056807628147851 / 158456325028528675187087900672 : ℚ), (-39825170922820113615256295701 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d2 : LeanSuffixReflective.QInterval := ⟨(55065531548192279461682189 / 79228162514264337593543950336 : ℚ), (881048504771076471386915027 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ39 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ37).sqrt cQ39_root39 (by norm_num [cQ39_root39]) (by norm_num [cJ37, cQ39_root39]) (by norm_num [cJ37, cQ39_root39])).widenAll cQ40_cJ39v cQ40_cJ39d0 cQ40_cJ39d1 cQ40_cJ39d2 (by
    norm_num [cJ37, cQ39_root39, NearOneScalarInterval.Jet3.sqrt, cQ40_cJ39v, cQ40_cJ39d0, cQ40_cJ39d1, cQ40_cJ39d2])
private abbrev cQ41_cJ40v : LeanSuffixReflective.QInterval := ⟨(316917278242041457316288746461 / 316912650057057350374175801344 : ℚ), (1267669112968165829265154985845 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d0 : LeanSuffixReflective.QInterval := ⟨(1136069537141515074281363541 / 633825300114114700748351602688 : ℚ), (2272139074283030148562727083 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ40 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0))).widenAll cQ41_cJ40v cQ41_cJ40d0 cQ41_cJ40d1 cQ41_cJ40d2 (by
    norm_num [cJ0, cQ41_cJ40v, cQ41_cJ40d0, cQ41_cJ40d1, cQ41_cJ40d2])
private abbrev cQ42_cJ41v : LeanSuffixReflective.QInterval := ⟨(4337002495734427888024217791719 / 1267650600228229401496703205376 : ℚ), (4337002495734427888024217791729 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d0 : LeanSuffixReflective.QInterval := ⟨(-265062898930832752218087252317 / 316912650057057350374175801344 : ℚ), (-1060251595723331008872349009255 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d2 : LeanSuffixReflective.QInterval := ⟨(1769500313331888622241549081 / 1267650600228229401496703205376 : ℚ), (55296884791621519445048409 / 39614081257132168796771975168 : ℚ), by norm_num⟩
@[simp] private abbrev cJ41 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ39).add ((cJ40).mul (cJ38))).widenAll cQ42_cJ41v cQ42_cJ41d0 cQ42_cJ41d1 cQ42_cJ41d2 (by
    norm_num [cJ39, cJ40, cJ38, cQ42_cJ41v, cQ42_cJ41d0, cQ42_cJ41d1, cQ42_cJ41d2])
private abbrev cQ43_cJ42v : LeanSuffixReflective.QInterval := ⟨(12691004569755691729766117078955 / 1267650600228229401496703205376 : ℚ), (6345502284877845864883058539513 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d0 : LeanSuffixReflective.QInterval := ⟨(-4674263019338070012634010318953 / 633825300114114700748351602688 : ℚ), (-9348526038676140025268020637775 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d2 : LeanSuffixReflective.QInterval := ⟨(15534179179016013896723076131 / 1267650600228229401496703205376 : ℚ), (3883544794754003474180769047 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ42 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ38).mul (cJ39)).mul (cJ41)).widenAll cQ43_cJ42v cQ43_cJ42d0 cQ43_cJ42d1 cQ43_cJ42d2 (by
    norm_num [cJ38, cJ39, cJ41, cQ43_cJ42v, cQ43_cJ42d0, cQ43_cJ42d1, cQ43_cJ42d2])
private abbrev cQ44_cJ43v : LeanSuffixReflective.QInterval := ⟨(1084266458304547338809344826129 / 316912650057057350374175801344 : ℚ), (2168532916609094677618689652265 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d0 : LeanSuffixReflective.QInterval := ⟨(-1052493429023459795092686067175 / 1267650600228229401496703205376 : ℚ), (-263123357255864948773171516789 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d2 : LeanSuffixReflective.QInterval := ⟨(1769526155073384459390155729 / 1267650600228229401496703205376 : ℚ), (1769526155073384459390155737 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ43 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ40).mul (cJ41)).widenAll cQ44_cJ43v cQ44_cJ43d0 cQ44_cJ43d1 cQ44_cJ43d2 (by
    norm_num [cJ40, cJ41, cQ44_cJ43v, cQ44_cJ43d0, cQ44_cJ43d1, cQ44_cJ43d2])
private abbrev cQ45_cJ44v : LeanSuffixReflective.QInterval := ⟨(542129254055235086538373320015 / 158456325028528675187087900672 : ℚ), (542129254055235086538373320019 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d0 : LeanSuffixReflective.QInterval := ⟨(-528197066491459493101255743619 / 633825300114114700748351602688 : ℚ), (-132049266622864873275313935897 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d2 : LeanSuffixReflective.QInterval := ⟨(110594580516342179830679657 / 79228162514264337593543950336 : ℚ), (884756644130737438645437263 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ44 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ38).add (cJ39)).mul (((cJ35).mul (cJ35)).add ((cJ33).mul ((cJ38).mul (cJ39))))).widenAll cQ45_cJ44v cQ45_cJ44d0 cQ45_cJ44d1 cQ45_cJ44d2 (by
    norm_num [cJ38, cJ39, cJ35, cJ33, cQ45_cJ44v, cQ45_cJ44d0, cQ45_cJ44d1, cQ45_cJ44d2])
private abbrev cQ46_cJ45v : LeanSuffixReflective.QInterval := ⟨(2530924039600766722354171852523 / 1267650600228229401496703205376 : ℚ), (632731009900191680588542963133 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d0 : LeanSuffixReflective.QInterval := ⟨(-353713368369641454682914029457 / 1267650600228229401496703205376 : ℚ), (-2763385690387823864710265855 / 9903520314283042199192993792 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d2 : LeanSuffixReflective.QInterval := ⟨(-3616963214869087659306293 / 1267650600228229401496703205376 : ℚ), (-226060200929317978706643 / 79228162514264337593543950336 : ℚ), by norm_num⟩
@[simp] private abbrev cJ45 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ35).mul (cJ35)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).widenAll cQ46_cJ45v cQ46_cJ45d0 cQ46_cJ45d1 cQ46_cJ45d2 (by
    norm_num [cJ35, cJ0, cQ46_cJ45v, cQ46_cJ45d0, cQ46_cJ45d1, cQ46_cJ45d2])
private abbrev cQ47_cJ46v : LeanSuffixReflective.QInterval := ⟨(126620239983880539044595355173 / 1267650600228229401496703205376 : ℚ), (63310119991940269522297677587 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d0 : LeanSuffixReflective.QInterval := ⟨(93271781915016361821648036561 / 1267650600228229401496703205376 : ℚ), (23317945478754090455412009141 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d2 : LeanSuffixReflective.QInterval := ⟨(-154987060700228923596101853 / 1267650600228229401496703205376 : ℚ), (-38746765175057230899025463 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ46 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ42).invPos (by norm_num [cJ42])).widenAll cQ47_cJ46v cQ47_cJ46d0 cQ47_cJ46d1 cQ47_cJ46d2 (by
    norm_num [cJ42, NearOneScalarInterval.Jet3.invPos, cQ47_cJ46v, cQ47_cJ46d0, cQ47_cJ46d1, cQ47_cJ46d2])
private abbrev cQ48_cJ47v : LeanSuffixReflective.QInterval := ⟨(252803263941597406813245842355 / 1267650600228229401496703205376 : ℚ), (252803263941597406813245842359 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d0 : LeanSuffixReflective.QInterval := ⟨(37722642864328416330116816177 / 316912650057057350374175801344 : ℚ), (75445285728656832660233632359 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d2 : LeanSuffixReflective.QInterval := ⟨(-309800238672112562319351439 / 1267650600228229401496703205376 : ℚ), (-77450059668028140579837859 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ47 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ45).mul (cJ46)).widenAll cQ48_cJ47v cQ48_cJ47d0 cQ48_cJ47d1 cQ48_cJ47d2 (by
    norm_num [cJ45, cJ46, cQ48_cJ47v, cQ48_cJ47d0, cQ48_cJ47d1, cQ48_cJ47d2])
private abbrev cQ49_cJ48v : LeanSuffixReflective.QInterval := ⟨(46314089584230791891222768191 / 158456325028528675187087900672 : ℚ), (370512716673846335129782145531 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d0 : LeanSuffixReflective.QInterval := ⟨(89913829917470822886541623151 / 1267650600228229401496703205376 : ℚ), (44956914958735411443270811577 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d2 : LeanSuffixReflective.QInterval := ⟨(-75584734951460673470440973 / 633825300114114700748351602688 : ℚ), (-18896183737865168367610243 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ48 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ43).invPos (by norm_num [cJ43])).widenAll cQ49_cJ48v cQ49_cJ48d0 cQ49_cJ48d1 cQ49_cJ48d2 (by
    norm_num [cJ43, NearOneScalarInterval.Jet3.invPos, cQ49_cJ48v, cQ49_cJ48d0, cQ49_cJ48d1, cQ49_cJ48d2])
private abbrev cQ50_cJ49v : LeanSuffixReflective.QInterval := ⟨(369873031827064066861711981979 / 633825300114114700748351602688 : ℚ), (11558532244595752089428499437 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d0 : LeanSuffixReflective.QInterval := ⟨(76132786569763769308628626853 / 1267650600228229401496703205376 : ℚ), (38066393284881884654314313433 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d2 : LeanSuffixReflective.QInterval := ⟨(-302874132847595349099841613 / 1267650600228229401496703205376 : ℚ), (-151437066423797674549920803 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ49 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ45).mul (cJ48)).widenAll cQ50_cJ49v cQ50_cJ49d0 cQ50_cJ49d1 cQ50_cJ49d2 (by
    norm_num [cJ45, cJ48, cQ50_cJ49v, cQ50_cJ49d0, cQ50_cJ49d1, cQ50_cJ49d2])
private abbrev cQ51_cJ50v : LeanSuffixReflective.QInterval := ⟨(370515433413427884145045002131 / 1267650600228229401496703205376 : ℚ), (370515433413427884145045002135 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d0 : LeanSuffixReflective.QInterval := ⟨(90248387978913968743190169907 / 1267650600228229401496703205376 : ℚ), (90248387978913968743190169915 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d2 : LeanSuffixReflective.QInterval := ⟨(-2362040430549578029808445 / 19807040628566084398385987584 : ℚ), (-75585293777586496953870239 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ50 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ44).invPos (by norm_num [cJ44])).widenAll cQ51_cJ50v cQ51_cJ50d0 cQ51_cJ50d1 cQ51_cJ50d2 (by
    norm_num [cJ44, NearOneScalarInterval.Jet3.invPos, cQ51_cJ50v, cQ51_cJ50d0, cQ51_cJ50d1, cQ51_cJ50d2])
private abbrev cQ52_cJ51v : LeanSuffixReflective.QInterval := ⟨(740393604105323890969975621867 / 1267650600228229401496703205376 : ℚ), (370196802052661945484987810939 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d0 : LeanSuffixReflective.QInterval := ⟨(64467936030885712192352843959 / 633825300114114700748351602688 : ℚ), (64467936030885712192352843969 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d2 : LeanSuffixReflective.QInterval := ⟨(-151305111273425913697211257 / 633825300114114700748351602688 : ℚ), (-75652555636712956848605627 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ51 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ35).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).mul (cJ50)).widenAll cQ52_cJ51v cQ52_cJ51d0 cQ52_cJ51d1 cQ52_cJ51d2 (by
    norm_num [cJ35, cJ0, cJ50, cQ52_cJ51v, cQ52_cJ51d0, cQ52_cJ51d1, cQ52_cJ51d2])
private abbrev cQ53_cJ52v : LeanSuffixReflective.QInterval := ⟨(634375470808997069469447562371 / 633825300114114700748351602688 : ℚ), (1268750941617994138938895124745 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d0 : LeanSuffixReflective.QInterval := ⟨(89226690057837544170994924961 / 1267650600228229401496703205376 : ℚ), (44613345028918772085497462483 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d2 : LeanSuffixReflective.QInterval := ⟨(226647728895623273650623 / 316912650057057350374175801344 : ℚ), (453295457791246547301247 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ52 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ35).invPos (by norm_num [cJ35])).widenAll cQ53_cJ52v cQ53_cJ52d0 cQ53_cJ52d1 cQ53_cJ52d2 (by
    norm_num [cJ35, NearOneScalarInterval.Jet3.invPos, cQ53_cJ52v, cQ53_cJ52d0, cQ53_cJ52d1, cQ53_cJ52d2])
private abbrev cQ54_cJ53v : LeanSuffixReflective.QInterval := ⟨(6659022109792752399103393799 / 158456325028528675187087900672 : ℚ), (53272176878342019192827150393 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d0 : LeanSuffixReflective.QInterval := ⟨(544820408182473721990230238631 / 316912650057057350374175801344 : ℚ), (1089640816364947443980460477267 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d2 : LeanSuffixReflective.QInterval := ⟨(5398088371628672201208267 / 316912650057057350374175801344 : ℚ), (21592353486514688804833069 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ53 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ0).mul (cJ39)).mul (cJ52)).widenAll cQ54_cJ53v cQ54_cJ53d0 cQ54_cJ53d1 cQ54_cJ53d2 (by
    norm_num [cJ0, cJ39, cJ52, cQ54_cJ53v, cQ54_cJ53d0, cQ54_cJ53d1, cQ54_cJ53d2])
private abbrev cQ55_cJ54v : LeanSuffixReflective.QInterval := ⟨(221180457498050282314666469 / 633825300114114700748351602688 : ℚ), (110590228749025141157333235 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d0 : LeanSuffixReflective.QInterval := ⟨(36272128115655740905370033147 / 1267650600228229401496703205376 : ℚ), (36272128115655740905370033149 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d2 : LeanSuffixReflective.QInterval := ⟨(-180799691124771613741363 / 1267650600228229401496703205376 : ℚ), (-90399845562385806870681 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ54 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ33).mul (cJ51)).widenAll cQ55_cJ54v cQ55_cJ54d0 cQ55_cJ54d1 cQ55_cJ54d2 (by
    norm_num [cJ33, cJ51, cQ55_cJ54v, cQ55_cJ54d0, cQ55_cJ54d1, cQ55_cJ54d2])
private abbrev cQ56_cJ55v : LeanSuffixReflective.QInterval := ⟨(1266904357578284057855836914161 / 1267650600228229401496703205376 : ℚ), (1266932341677657008242369400083 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d0 : LeanSuffixReflective.QInterval := ⟨(-30720057874711637602094132939 / 633825300114114700748351602688 : ℚ), (-7297600275167505034880079003 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d2 : LeanSuffixReflective.QInterval := ⟨(-608749542780344288821431 / 1267650600228229401496703205376 : ℚ), (-289218910265066243097791 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ55 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ53).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ53]) (by norm_num [cJ53])).widenAll cQ56_cJ55v cQ56_cJ55d0 cQ56_cJ55d1 cQ56_cJ55d2 (by
    norm_num [cJ53, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ56_cJ55v, cQ56_cJ55d0, cQ56_cJ55d1, cQ56_cJ55d2])
private abbrev cQ57_cJ56v : LeanSuffixReflective.QInterval := ⟨(633825274386313065061532644309 / 633825300114114700748351602688 : ℚ), (633825275351105626399788355249 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d0 : LeanSuffixReflective.QInterval := ⟨(-8438819372422041183462569 / 1267650600228229401496703205376 : ℚ), (-8121496809706032768530131 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d2 : LeanSuffixReflective.QInterval := ⟨(20240942439105122251 / 633825300114114700748351602688 : ℚ), (21031795144838874337 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ56 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ54).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ54]) (by norm_num [cJ54])).widenAll cQ57_cJ56v cQ57_cJ56d0 cQ57_cJ56d1 cQ57_cJ56d2 (by
    norm_num [cJ54, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ57_cJ56v, cQ57_cJ56d0, cQ57_cJ56d1, cQ57_cJ56d2])
private abbrev cQ58_cJ57v : LeanSuffixReflective.QInterval := ⟨(634375470808997069469447562371 / 633825300114114700748351602688 : ℚ), (1268750941617994138938895124745 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d0 : LeanSuffixReflective.QInterval := ⟨(89226690057837544170994924961 / 1267650600228229401496703205376 : ℚ), (44613345028918772085497462483 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d2 : LeanSuffixReflective.QInterval := ⟨(226647728895623273650623 / 316912650057057350374175801344 : ℚ), (453295457791246547301247 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ57 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ35).invPos (by norm_num [cJ35])).widenAll cQ58_cJ57v cQ58_cJ57d0 cQ58_cJ57d1 cQ58_cJ57d2 (by
    norm_num [cJ35, NearOneScalarInterval.Jet3.invPos, cQ58_cJ57v, cQ58_cJ57d0, cQ58_cJ57d1, cQ58_cJ57d2])
private abbrev cQ59_cJ58v : LeanSuffixReflective.QInterval := ⟨(741694946931838109099060526975 / 1267650600228229401496703205376 : ℚ), (370847488402152888017086647441 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d0 : LeanSuffixReflective.QInterval := ⟨(117672888362938157403286625285 / 633825300114114700748351602688 : ℚ), (235351456753039840527821459111 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d2 : LeanSuffixReflective.QInterval := ⟨(-151041669054899068538126069 / 633825300114114700748351602688 : ℚ), (-37760411742223746728101127 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ58 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ33).mul (cJ39)).mul (cJ57)).mul (cJ55)).add ((cJ51).mul (cJ56))).widenAll cQ59_cJ58v cQ59_cJ58d0 cQ59_cJ58d1 cQ59_cJ58d2 (by
    norm_num [cJ33, cJ39, cJ57, cJ55, cJ51, cJ56, cQ59_cJ58v, cQ59_cJ58d0, cQ59_cJ58d1, cQ59_cJ58d2])
private abbrev cQ60_cJ59v : LeanSuffixReflective.QInterval := ⟨(1267100906676312729953650889323 / 1267650600228229401496703205376 : ℚ), (1267100906676312729953650889325 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d0 : LeanSuffixReflective.QInterval := ⟨(-44535995532626234266174300541 / 1267650600228229401496703205376 : ℚ), (-22267997766313117133087150269 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d2 : LeanSuffixReflective.QInterval := ⟨(-452509545519725085718003 / 1267650600228229401496703205376 : ℚ), (-226254772759862542859001 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ59 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ5).mul (cJ4)).neg)).widenAll cQ60_cJ59v cQ60_cJ59d0 cQ60_cJ59d1 cQ60_cJ59d2 (by
    norm_num [cJ5, cJ4, cQ60_cJ59v, cQ60_cJ59d0, cQ60_cJ59d1, cQ60_cJ59d2])
private abbrev cQ61_cJ60v : LeanSuffixReflective.QInterval := ⟨(11847150259134239187459 / 1267650600228229401496703205376 : ℚ), (11854719037503895335573 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d0 : LeanSuffixReflective.QInterval := ⟨(-29207882918219224450421 / 1267650600228229401496703205376 : ℚ), (-13654250515426452644865 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d1 : LeanSuffixReflective.QInterval := ⟨(-4831031706571306950877703595 / 1267650600228229401496703205376 : ℚ), (-150969740829765065058523595 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ60 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul (cJ20)).add ((((NearOneScalarInterval.Jet3.pi).mul (NearOneScalarInterval.Jet3.rational (1 / 2 : ℚ))).add ((cJ5).mul (cJ31))).neg)).widenAll cQ61_cJ60v cQ61_cJ60d0 cQ61_cJ60d1 cQ61_cJ60d2 (by
    norm_num [cJ8, cJ20, cJ5, cJ31, cQ61_cJ60v, cQ61_cJ60d0, cQ61_cJ60d1, cQ61_cJ60d2])
private abbrev cQ62_cJ61v : LeanSuffixReflective.QInterval := ⟨(-11756742800366265941849 / 633825300114114700748351602688 : ℚ), (15830229003735284829979 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d0 : LeanSuffixReflective.QInterval := ⟨(-4767939711836502561241185 / 1267650600228229401496703205376 : ℚ), (5193789422213030622440169 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d1 : LeanSuffixReflective.QInterval := ⟨(9688198933723533671 / 1267650600228229401496703205376 : ℚ), (72670452129044400249 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d2 : LeanSuffixReflective.QInterval := ⟨(110951448970773068655974933 / 39614081257132168796771975168 : ℚ), (3550446411235946657122533907 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ61 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.pi).mul ((cJ4).add ((cJ3).neg))).mul ((cJ8).add (cJ59))).add (((cJ8).mul (cJ8)).mul ((cJ58).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ59)).add (NearOneScalarInterval.Jet3.rational (1 : ℚ))).mul (cJ49))))).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul ((cJ59).mul (cJ59))).mul ((cJ31).add ((cJ8).mul (cJ22)))).neg)).widenAll cQ62_cJ61v cQ62_cJ61d0 cQ62_cJ61d1 cQ62_cJ61d2 (by
    norm_num [cJ4, cJ3, cJ8, cJ59, cJ58, cJ49, cJ31, cJ22, cQ62_cJ61v, cQ62_cJ61d0, cQ62_cJ61d1, cQ62_cJ61d2])
private abbrev cQ63_cJ62v : LeanSuffixReflective.QInterval := ⟨(-247114611894369053589073783 / 1267650600228229401496703205376 : ℚ), (-247114611894369053589073743 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d0 : LeanSuffixReflective.QInterval := ⟨(-10168302530552019609905394311 / 633825300114114700748351602688 : ℚ), (-5084151265276009804952697139 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d1 : LeanSuffixReflective.QInterval := ⟨(1778427613614421613419019637 / 1267650600228229401496703205376 : ℚ), (1778427613614421613419019661 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d2 : LeanSuffixReflective.QInterval := ⟨(-888186501247585166877874637 / 1267650600228229401496703205376 : ℚ), (-888186501247585166877874627 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ62 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ3).add ((cJ4).neg)).mul (cJ20)).add ((cJ59).mul (cJ22))).add (((cJ8).mul (cJ49)).neg)).widenAll cQ63_cJ62v cQ63_cJ62d0 cQ63_cJ62d1 cQ63_cJ62d2 (by
    norm_num [cJ3, cJ4, cJ20, cJ59, cJ22, cJ8, cJ49, cQ63_cJ62v, cQ63_cJ62d0, cQ63_cJ62d1, cQ63_cJ62d2])
private abbrev cQ64_cJ63v : LeanSuffixReflective.QInterval := ⟨(466555180340841935772689108469 / 1267650600228229401496703205376 : ℚ), (466555180340841935772689108471 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d0 : LeanSuffixReflective.QInterval := ⟨(-49346607476985618869795309181 / 633825300114114700748351602688 : ℚ), (-12336651869246404717448827295 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d1 : LeanSuffixReflective.QInterval := ⟨(-757379691427676716187575695 / 1267650600228229401496703205376 : ℚ), (-378689845713838358093787847 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d2 : LeanSuffixReflective.QInterval := ⟨(378689845713838358093787847 / 633825300114114700748351602688 : ℚ), (757379691427676716187575695 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
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

theorem foldLoRange_lo : foldLoRange.lo = (10486808130511955807392938494925 / 50458740871241454894059363327360892928 : ℚ) := by norm_num [foldLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldLoRange_hi : foldLoRange.hi = (18703341617713032146487778425331 / 25229370435620727447029681663680446464 : ℚ) := by norm_num [foldLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldHiRange_lo : foldHiRange.lo = (-18231616017303986353115976874483 / 25229370435620727447029681663680446464 : ℚ) := by norm_num [foldHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldHiRange_hi : foldHiRange.hi = (-9543356929693864220649335393229 / 50458740871241454894059363327360892928 : ℚ) := by norm_num [foldHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaLoRange_lo : areaLoRange.lo = (-865739004079839908991193525232811 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [areaLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaLoRange_hi : areaLoRange.hi = (-29260577065278925241749860954605 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [areaLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaHiRange_lo : areaHiRange.lo = (31368459790722188247294372114925 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [areaHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaHiRange_hi : areaHiRange.hi = (867846886805283171996738036393131 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [areaHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem hFourRange_lo : hFourRange.lo = (327910996308430772495478282937378362171 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [hFourRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem hFourRange_hi : hFourRange.hi = (327912432206586910933548108187595586757 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [hFourRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem shapeRange_lo : shapeRange.lo = (12603632088488693933509696456781354135 / 12614685217810363723514840831840223232 : ℚ) := by norm_num [shapeRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem shapeRange_hi : shapeRange.hi = (12603857834875926140749138866215988073 / 12614685217810363723514840831840223232 : ℚ) := by norm_num [shapeRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem bSubARange_lo : bSubARange.lo = (60354706889237764343208014037262449367 / 163990907831534728405692930813922902016 : ℚ) := by norm_num [bSubARange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem bSubARange_hi : bSubARange.hi = (60358062960474722290073329101449061673 / 163990907831534728405692930813922902016 : ℚ) := by norm_num [bSubARange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem gapRange_lo : gapRange.lo = (-129717594265473971297039261697885593 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [gapRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem gapRange_hi : gapRange.hi = (-126028268423811927075032529097620071 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [gapRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]

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
end Band10Cell32
end
end NearOneScalarStress
